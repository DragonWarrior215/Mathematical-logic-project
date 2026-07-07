"""Keyframe scheduling + symbolic dead-reckoning between VLM calls.

The VLM grounding is called only at *keyframes*. Between keyframes the player
position is propagated with the formalized transition model (1 px per step in
the facing direction unless a known-blocking tile clips the move — the same
axis-clamped AABB rule the engine uses), and each monster's position is
widened into an uncertainty ball growing at the monster speed (0.5 px/step).
The safety shield ("never enter a monster ball") is what makes sparse
perception sound, and is exactly the layer the Lean development can verify.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .constants import (
    ACTION_A,
    ACTION_B,
    MAP_H_PX,
    MAP_W_PX,
    MONSTER_SPEED_PX,
    MOVE_ACTION_TO_DIR,
    DIR_VECTORS,
    TILE_SIZE,
)
from .grounding.schema import Monster, SymbolicState
from .memory import Memory

# Keyframe cadence (steps between VLM calls).
SYNC_INTERVAL_CALM = 24
SYNC_INTERVAL_DANGER = 8
DANGER_RADIUS_PX = 3.5 * TILE_SIZE
CONTACT_MARGIN_PX = 6.0


@dataclass
class TrackedMonster:
    monster: Monster
    uncertainty_px: float = 0.0

    def center(self) -> tuple[float, float]:
        return (self.monster.px[0] + TILE_SIZE / 2, self.monster.px[1] + TILE_SIZE / 2)


@dataclass
class Tracker:
    memory: Memory
    player_px: tuple[float, float] = (0.0, 0.0)
    facing: str = "down"
    monsters: list[TrackedMonster] = field(default_factory=list)
    steps_since_sync: int = 10**9
    perceive_requested: bool = True
    expect_transition: str | None = None
    last_transition_result: str | None = None   # "moved" | "blocked" | None
    last_transition_dir: str | None = None      # direction actually registered
    last_move_blocked: bool = False              # reward-feedback: last move hit a wall
    _move_origin_px: tuple[float, float] | None = None
    _move_dir: str | None = None
    _prev_px: tuple[float, float] | None = None
    _last_action_was_move: bool = False

    # ------------------------------------------------------------------
    # Perceive scheduling
    # ------------------------------------------------------------------

    def should_perceive(self) -> bool:
        if self.perceive_requested or self.expect_transition:
            return True
        interval = SYNC_INTERVAL_DANGER if self._danger_nearby() else SYNC_INTERVAL_CALM
        return self.steps_since_sync >= interval

    def request_perceive(self) -> None:
        self.perceive_requested = True

    def _danger_nearby(self) -> bool:
        px, py = self.player_px
        for tracked in self.monsters:
            mx, my = tracked.center()
            reach = DANGER_RADIUS_PX + tracked.uncertainty_px
            if abs(mx - (px + TILE_SIZE / 2)) <= reach and abs(my - (py + TILE_SIZE / 2)) <= reach:
                return True
        return False

    # ------------------------------------------------------------------
    # Keyframe integration
    # ------------------------------------------------------------------

    def sync(self, state: SymbolicState) -> None:
        """Reconcile a fresh grounding snapshot with the predicted state."""
        actual = (float(state.player_px[0]), float(state.player_px[1]))
        self.last_transition_result = None

        if self.expect_transition is not None:
            jumped = (
                abs(actual[0] - self.player_px[0]) > 2 * TILE_SIZE
                or abs(actual[1] - self.player_px[1]) > 2 * TILE_SIZE
            )
            # Second, independent evidence channel: a room change swaps the
            # whole grid. The px-jump heuristic alone can misfire when
            # grounding hiccups or abyss respawns intervene.
            remembered = self.memory.state
            if not jumped and remembered is not None:
                diff = sum(
                    1
                    for row_new, row_old in zip(state.grid, remembered.grid)
                    for a, b in zip(row_new, row_old)
                    if a != b
                )
                jumped = diff >= 12
            if jumped:
                # The push can accidentally cross a DIFFERENT open exit en
                # route (flush contact teleports immediately); trust the
                # landing side over the expectation when they disagree, so
                # the odometry and UseExit's direction check stay honest.
                observed = self._landing_direction(actual)
                direction = observed or self.expect_transition
                self.memory.transition(direction, state)
                self.last_transition_dir = direction
                self.last_transition_result = "moved"
            else:
                self.memory.room.failed_exits[self.expect_transition] = (
                    self.memory.room.failed_exits.get(self.expect_transition, 0) + 1
                )
                self.memory.integrate_keyframe(state)
                self.last_transition_dir = None
                self.last_transition_result = "blocked"
            self.expect_transition = None
        else:
            # The engine teleports the player the moment it is flush on an
            # exit tile — which can happen during GoTo's alignment phase,
            # BEFORE UseExit sets expect_transition. Detect such unplanned
            # crossings here (px teleport or wholesale grid swap) and
            # register them using the last movement direction; otherwise
            # foreign-room keyframes would silently overwrite the current
            # room's memory and corrupt the odometry.
            crossed = None
            if self._move_dir is not None and self.memory.state is not None:
                teleported = (
                    abs(actual[0] - self.player_px[0]) > 2 * TILE_SIZE
                    or abs(actual[1] - self.player_px[1]) > 2 * TILE_SIZE
                )
                if teleported:
                    # Distinguish a room crossing from a same-room teleport
                    # (spike-trap respawn): crossings either swap the grid
                    # wholesale or drop us at the boundary OPPOSITE to the
                    # movement direction (the entry spawn).
                    diff = sum(
                        1
                        for row_new, row_old in zip(
                            state.grid, self.memory.state.grid
                        )
                        for a, b in zip(row_new, row_old)
                        if a != b
                    )
                    margin = 3 * TILE_SIZE
                    entry_side = {
                        "right": actual[0] < margin,
                        "left": actual[0] > MAP_W_PX - margin - TILE_SIZE,
                        "down": actual[1] < margin,
                        "up": actual[1] > MAP_H_PX - margin - TILE_SIZE,
                    }[self._move_dir]
                    if diff >= 12 or entry_side:
                        crossed = {
                            "up": "north", "down": "south",
                            "left": "west", "right": "east",
                        }.get(self._move_dir)
            if crossed is not None:
                self.memory.transition(crossed, state)
                self.last_transition_dir = crossed
                self.last_transition_result = "moved"
            else:
                # Prediction/reality divergences are resolved by trusting
                # the grounded position; hidden-wall inference from
                # divergence is unsound, so stall detection lives in the
                # navigation skill.
                self.memory.integrate_keyframe(state)

        self.player_px = actual
        self.facing = state.facing
        self.monsters = [TrackedMonster(m) for m in state.monsters]
        self.steps_since_sync = 0
        self.perceive_requested = False
        self._move_origin_px = None
        self._move_dir = None

    def _landing_direction(self, actual: tuple[float, float]) -> str | None:
        """Infer the crossing direction from the entry-spawn side: crossing
        east drops us at the WEST edge of the new room, etc. Returns None
        when ambiguous (corner/center spawns)."""
        margin = 3 * TILE_SIZE
        x, y = actual
        candidates = []
        if x < margin:
            candidates.append("east")
        if x > MAP_W_PX - margin - TILE_SIZE:
            candidates.append("west")
        if y < margin:
            candidates.append("south")
        if y > MAP_H_PX - margin - TILE_SIZE:
            candidates.append("north")
        return candidates[0] if len(candidates) == 1 else None

    # ------------------------------------------------------------------
    # Transition model (dead-reckoning)
    # ------------------------------------------------------------------

    def apply_action(self, action: int) -> None:
        """Propagate the predicted state through one env.step."""
        self.steps_since_sync += 1
        self.last_move_blocked = False

        if action in (ACTION_A, ACTION_B):
            # Interactions / attacks can change the world — verify next step.
            self.perceive_requested = True
        direction = MOVE_ACTION_TO_DIR.get(action)
        self._last_action_was_move = direction is not None
        if direction is not None:
            self.facing = direction
            self._move_dir = direction
            if self._move_origin_px is None:
                self._move_origin_px = self.player_px
            self._prev_px = self.player_px
            self.player_px = self._predict_move(self.player_px, direction)

        for tracked in self.monsters:
            tracked.uncertainty_px += MONSTER_SPEED_PX

    def note_blocked_feedback(self) -> None:
        """The env's reward for the last step carried an invalid-action
        penalty while we issued a move: the real player did not move.
        Undo the optimistic prediction (1-step-latency wall feedback)."""
        if self._last_action_was_move and self._prev_px is not None:
            self.player_px = self._prev_px
            self.last_move_blocked = True

    def _predict_move(self, px: tuple[float, float], direction: str) -> tuple[float, float]:
        dx, dy = DIR_VECTORS[direction]
        nx = min(max(px[0] + dx, 0.0), float(MAP_W_PX - TILE_SIZE))
        ny = min(max(px[1] + dy, 0.0), float(MAP_H_PX - TILE_SIZE))
        if self._rect_hits_block(nx, ny):
            return px
        return (nx, ny)

    def _rect_hits_block(self, left: float, top: float) -> bool:
        x0 = int(left // TILE_SIZE)
        y0 = int(top // TILE_SIZE)
        x1 = int((left + TILE_SIZE - 1) // TILE_SIZE)
        y1 = int((top + TILE_SIZE - 1) // TILE_SIZE)
        for ty in range(y0, y1 + 1):
            for tx in range(x0, x1 + 1):
                if self.memory.is_blocking(tx, ty):
                    return True
        return False

    # ------------------------------------------------------------------
    # Safety shield queries
    # ------------------------------------------------------------------

    def monster_clearance_px(self, left: float, top: float) -> float:
        """Smallest Chebyshev gap between the player rect at (left, top) and
        any monster's uncertainty-inflated rect. Negative means overlap."""
        best = float("inf")
        pcx, pcy = left + TILE_SIZE / 2, top + TILE_SIZE / 2
        for tracked in self.monsters:
            mcx, mcy = tracked.center()
            reach = TILE_SIZE + tracked.uncertainty_px  # rect halves + growth
            gap = max(abs(mcx - pcx), abs(mcy - pcy)) - reach
            best = min(best, gap)
        return best

    def px_is_safe(self, left: float, top: float, margin: float = CONTACT_MARGIN_PX) -> bool:
        return self.monster_clearance_px(left, top) >= margin

    def player_tile(self) -> tuple[int, int]:
        return (
            int((self.player_px[0] + TILE_SIZE / 2) // TILE_SIZE),
            int((self.player_px[1] + TILE_SIZE / 2) // TILE_SIZE),
        )

    def reset(self) -> None:
        self.player_px = (0.0, 0.0)
        self.facing = "down"
        self.monsters = []
        self.steps_since_sync = 10**9
        self.perceive_requested = True
        self.expect_transition = None
        self.last_transition_result = None
        self._move_origin_px = None
        self._move_dir = None

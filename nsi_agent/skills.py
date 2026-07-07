"""Primitive skills (temporally extended PrimitiveOps for the NSI graphs).

Each skill follows the ``graph.Skill`` protocol: ``reset(ctx, **args)`` then
``step(ctx) -> ("act", action) | ("ok", detail) | ("fail", diagnosis)``.

All navigation replans a tile-level BFS every step (the grid is 10x8, so this
is cheap) over the *remembered* symbolic grid, then drives the player with a
pixel controller (1 px per env.step). A safety shield refuses any move that
would enter a monster's uncertainty ball; when the shield stalls progress it
requests a keyframe so the ball collapses to the monster's true position.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field

from .constants import (
    ACTION_A,
    ACTION_B,
    ACTION_NOOP,
    DIR_TO_MOVE_ACTION,
    DIR_VECTORS,
    EXIT_TILES,
    GRID_H,
    GRID_W,
    TILE_SIZE,
)
from .graph import Ctx, StepResult
from .grounding import schema

Tile = tuple[int, int]


# ---------------------------------------------------------------------------
# Navigation helpers
# ---------------------------------------------------------------------------


def neighbors(tile: Tile):
    x, y = tile
    yield (x, y - 1)
    yield (x, y + 1)
    yield (x - 1, y)
    yield (x + 1, y)


def in_bounds(tile: Tile) -> bool:
    return 0 <= tile[0] < GRID_W and 0 <= tile[1] < GRID_H


def walkable(ctx: Ctx, tile: Tile, *, allow_hazard: bool = False) -> bool:
    if not in_bounds(tile):
        return False
    if ctx.memory.is_blocking(*tile):
        return False
    if not allow_hazard and ctx.memory.is_hazard(*tile):
        return False
    return True


def monster_blocked_tiles(ctx: Ctx, margin_px: float = 4.0) -> set[Tile]:
    """Tiles whose center lies inside a monster uncertainty ball."""
    blocked: set[Tile] = set()
    for tracked in ctx.tracker.monsters:
        mcx, mcy = tracked.center()
        reach = TILE_SIZE + tracked.uncertainty_px + margin_px
        x0 = max(0, int((mcx - reach) // TILE_SIZE))
        x1 = min(GRID_W - 1, int((mcx + reach) // TILE_SIZE))
        y0 = max(0, int((mcy - reach) // TILE_SIZE))
        y1 = min(GRID_H - 1, int((mcy + reach) // TILE_SIZE))
        for ty in range(y0, y1 + 1):
            for tx in range(x0, x1 + 1):
                ccx, ccy = tx * TILE_SIZE + 8, ty * TILE_SIZE + 8
                if max(abs(ccx - mcx), abs(ccy - mcy)) <= reach:
                    blocked.add((tx, ty))
    return blocked


def bfs_path(
    ctx: Ctx,
    start: Tile,
    goals: set[Tile],
    *,
    avoid_monsters: bool = True,
    allow_hazard: bool = False,
    avoid: set[Tile] | None = None,
) -> list[Tile] | None:
    if not goals:
        return None
    if start in goals:
        return [start]
    forbidden = monster_blocked_tiles(ctx) if avoid_monsters else set()
    if avoid:
        forbidden |= avoid - goals
    forbidden.discard(start)
    queue: deque[Tile] = deque([start])
    parent: dict[Tile, Tile | None] = {start: None}
    while queue:
        current = queue.popleft()
        for nxt in neighbors(current):
            if nxt in parent:
                continue
            if nxt in goals and walkable(ctx, nxt, allow_hazard=allow_hazard):
                parent[nxt] = current
                path = [nxt]
                while parent[path[-1]] is not None:
                    path.append(parent[path[-1]])
                path.reverse()
                return path
            if not walkable(ctx, nxt, allow_hazard=allow_hazard) or nxt in forbidden:
                continue
            parent[nxt] = current
            queue.append(nxt)
    return None


def reachable_tiles(ctx: Ctx, start: Tile, *, avoid_monsters: bool = False) -> set[Tile]:
    seen = {start}
    queue: deque[Tile] = deque([start])
    forbidden = monster_blocked_tiles(ctx) if avoid_monsters else set()
    while queue:
        current = queue.popleft()
        for nxt in neighbors(current):
            if nxt in seen or nxt in forbidden or not walkable(ctx, nxt):
                continue
            seen.add(nxt)
            queue.append(nxt)
    return seen


def move_toward_waypoint(ctx: Ctx, waypoint: Tile) -> int | None:
    """Pixel controller: next move action to reach the waypoint tile's
    top-left-aligned position. Aligns the perpendicular axis first so the
    16x16 player rect never straddles into off-path tiles."""
    px, py = ctx.tracker.player_px
    tx, ty = waypoint[0] * TILE_SIZE, waypoint[1] * TILE_SIZE
    dx, dy = tx - px, ty - py
    if dx == 0 and dy == 0:
        return None
    # Fix the smaller-misalignment axis first (usually the perpendicular one).
    if dx != 0 and dy != 0:
        axis = "y" if abs(dy) <= abs(dx) else "x"
    else:
        axis = "x" if dx != 0 else "y"
    if axis == "x":
        return DIR_TO_MOVE_ACTION["right" if dx > 0 else "left"]
    return DIR_TO_MOVE_ACTION["down" if dy > 0 else "up"]


def shielded(ctx: Ctx, action: int) -> int:
    """Safety shield: veto a move that would enter a monster ball."""
    direction = None
    for name, act in DIR_TO_MOVE_ACTION.items():
        if act == action:
            direction = name
            break
    if direction is None:
        return action
    ddx, ddy = DIR_VECTORS[direction]
    nx, ny = ctx.tracker.player_px[0] + ddx, ctx.tracker.player_px[1] + ddy
    if ctx.tracker.px_is_safe(nx, ny):
        return action
    ctx.tracker.request_perceive()
    return ACTION_B if ctx.inventory.has_shield else ACTION_NOOP


def adjacent_tiles(tile: Tile) -> list[Tile]:
    return [t for t in neighbors(tile) if in_bounds(t)]


def disambiguation_nudge(ctx: Ctx) -> int | None:
    """Grounded positions are rounded to integers while the engine keeps
    fractions, so when the player's center sits within ~1px of a tile
    boundary our tile estimate may differ from the engine's. Before any
    tile-sensitive interaction, nudge toward the current tile's interior
    until both axes are unambiguous."""
    px, py = ctx.tracker.player_px
    here = ctx.tracker.player_tile()
    ax = (px + TILE_SIZE / 2) % TILE_SIZE
    ay = (py + TILE_SIZE / 2) % TILE_SIZE
    if min(ax, TILE_SIZE - ax) >= 2 and min(ay, TILE_SIZE - ay) >= 2:
        return None
    return move_toward_waypoint(ctx, here)


# ---------------------------------------------------------------------------
# Skills
# ---------------------------------------------------------------------------


@dataclass
class GoToTile:
    """Navigate to a target tile (or any tile orthogonally adjacent to it).

    Stall detection compares *grounded* player positions across consecutive
    keyframes: if we commanded several moves between two syncs and the real
    position did not advance, the tile we were entering is actually blocked
    (unseen by perception) — mark it and let the per-step BFS replan.
    """

    target: Tile = (0, 0)
    adjacent: bool = False
    align: bool = False          # require exact pixel alignment on arrival
    max_steps: int = 900
    avoid: frozenset[Tile] = frozenset()   # e.g. foreign open-exit tiles
    _steps: int = 0
    _last_sync_px: tuple[float, float] | None = None
    _moves_since_sync: int = 0
    _waypoint: Tile | None = None
    _bump_streak: int = 0

    def reset(self, ctx: Ctx, *, target: Tile, adjacent: bool = False,
              align: bool = False, max_steps: int = 900,
              avoid: frozenset[Tile] = frozenset()) -> None:
        self.target = (int(target[0]), int(target[1]))
        self.adjacent = adjacent
        self.align = align
        self.max_steps = max_steps
        self.avoid = avoid
        self._steps = 0
        self._last_sync_px = None
        self._moves_since_sync = 0
        self._waypoint = None
        self._bump_streak = 0

    def _check_bump(self, ctx: Ctx) -> None:
        """Reward-feedback wall bumps: the tile we keep bumping into is
        blocked for the *real* (fractional) rect even though the grid and
        our rounded prediction call it free — reroute around it."""
        if ctx.tracker.last_move_blocked:
            self._bump_streak += 1
        else:
            self._bump_streak = 0
        if self._bump_streak >= 4 and self._waypoint is not None \
                and self._waypoint != ctx.tracker.player_tile():
            ctx.memory.mark_blocked(self._waypoint)
            self._bump_streak = 0

    def _check_stall(self, ctx: Ctx) -> None:
        if ctx.tracker.steps_since_sync != 0:
            return
        px = ctx.tracker.player_px
        if (
            self._last_sync_px is not None
            and self._moves_since_sync >= 4
            and abs(px[0] - self._last_sync_px[0]) < 2.0
            and abs(px[1] - self._last_sync_px[1]) < 2.0
            and self._waypoint is not None
            and self._waypoint != ctx.tracker.player_tile()
        ):
            ctx.memory.mark_blocked(self._waypoint)
        self._last_sync_px = px
        self._moves_since_sync = 0

    def _goals(self, ctx: Ctx) -> set[Tile]:
        if not self.adjacent:
            return {self.target}
        return {t for t in adjacent_tiles(self.target) if walkable(ctx, t)}

    def step(self, ctx: Ctx) -> StepResult:
        self._steps += 1
        if self._steps > self.max_steps:
            return ("fail", ("timeout", "goto", self.target))
        if ctx.state is None:
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)
        self._check_stall(ctx)
        self._check_bump(ctx)

        here = ctx.tracker.player_tile()
        goals = self._goals(ctx)
        if not goals:
            return ("fail", ("no_approach", self.target))
        if here in goals:
            if not self.align:
                return ("ok", here)
            action = move_toward_waypoint(ctx, here)
            if action is None:
                return ("ok", here)
            self._moves_since_sync += 1
            return ("act", shielded(ctx, action))

        path = bfs_path(ctx, here, goals, avoid=self.avoid)
        if path is None:
            # Retry ignoring monster balls once (shield still guards moves);
            # a truly disconnected target is a symbolic failure.
            path = bfs_path(ctx, here, goals, avoid_monsters=False,
                            avoid=self.avoid)
            if path is None:
                return ("fail", ("no_path", self.target))
        waypoint = path[1] if len(path) > 1 else path[0]
        self._waypoint = waypoint
        action = move_toward_waypoint(ctx, waypoint)
        if action is None:
            return ("act", ACTION_NOOP)
        self._moves_since_sync += 1
        return ("act", shielded(ctx, action))


@dataclass
class OpenChest:
    """Walk next to a chest and press A until it opens."""

    target: Tile = (0, 0)
    _nav: GoToTile = field(default_factory=GoToTile)
    _presses: int = 0
    _steps: int = 0
    _last_closed_cls: str | None = None

    def reset(self, ctx: Ctx, *, target: Tile) -> None:
        self.target = (int(target[0]), int(target[1]))
        self._nav.reset(ctx, target=self.target, adjacent=True)
        self._presses = 0
        self._steps = 0
        self._last_closed_cls = None

    def step(self, ctx: Ctx) -> StepResult:
        self._steps += 1
        if self._steps > 1200:
            return ("fail", ("timeout", "open_chest", self.target))
        state = ctx.state
        if state is None:
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)
        cls = state.tile(*self.target)
        if cls == schema.TILE_CHEST_OPEN:
            ctx.memory.room.opened_chests.add(self.target)
            if self._last_closed_cls == schema.TILE_CHEST_HEAL:
                ctx.memory.note_heal()
            return ("ok", self.target)
        if cls not in schema.CLOSED_CHEST_TILES:
            return ("fail", ("not_a_chest", self.target, cls))
        self._last_closed_cls = cls

        here = ctx.tracker.player_tile()
        if abs(here[0] - self.target[0]) + abs(here[1] - self.target[1]) == 1:
            nudge = disambiguation_nudge(ctx)
            if nudge is not None:
                return ("act", nudge)
            # Interact only on a freshly-synced step: the engine checks
            # adjacency against the *real* position, so pressing A on a
            # stale prediction can silently swing the sword instead.
            if ctx.tracker.steps_since_sync > 0:
                ctx.tracker.request_perceive()
                return ("act", ACTION_NOOP)
            if self._presses >= 4:
                return ("fail", ("chest_not_opening", self.target))
            self._presses += 1
            ctx.tracker.request_perceive()
            return ("act", ACTION_A)

        kind, payload = self._nav.step(ctx)
        if kind == "fail":
            return ("fail", ("chest_unreachable", self.target, payload))
        if kind == "ok":
            return ("act", ACTION_NOOP)   # arrived; press on next step
        return (kind, payload)


@dataclass
class PressButton:
    """Stand on a button tile (buttons trigger positionally)."""

    target: Tile = (0, 0)
    _nav: GoToTile = field(default_factory=GoToTile)
    _verifying: int = 0

    def reset(self, ctx: Ctx, *, target: Tile) -> None:
        self.target = (int(target[0]), int(target[1]))
        self._nav.reset(ctx, target=self.target)
        self._verifying = 0

    def step(self, ctx: Ctx) -> StepResult:
        state = ctx.state
        if state is None:
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)
        if state.tile(*self.target) == schema.TILE_BUTTON_PRESSED:
            return ("ok", self.target)
        if ctx.tracker.player_tile() == self.target:
            nudge = disambiguation_nudge(ctx)
            if nudge is not None:
                return ("act", nudge)
            if self._verifying >= 3:
                return ("fail", ("button_not_pressing", self.target))
            self._verifying += 1
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)
        kind, payload = self._nav.step(ctx)
        if kind == "fail":
            return ("fail", ("button_unreachable", self.target, payload))
        if kind == "ok":
            return ("act", ACTION_NOOP)
        return (kind, payload)


@dataclass
class ToggleSwitch:
    """Stand next to a lever and press A once.

    Lever effects are usually in *another* room (e.g. the rotating bridge),
    so in-room visual verification is impossible; the interaction itself is
    deterministic (adjacent + A always cycles the target). The planner
    re-perceives affected rooms afterwards and re-checks reachability.
    """

    target: Tile = (0, 0)
    _nav: GoToTile = field(default_factory=GoToTile)
    _pressed: bool = False
    _steps: int = 0

    def reset(self, ctx: Ctx, *, target: Tile) -> None:
        self.target = (int(target[0]), int(target[1]))
        self._nav.reset(ctx, target=self.target, adjacent=True)
        self._pressed = False
        self._steps = 0

    def step(self, ctx: Ctx) -> StepResult:
        self._steps += 1
        if self._steps > 900:
            return ("fail", ("timeout", "toggle_switch", self.target))
        state = ctx.state
        if state is None:
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)
        if self._pressed:
            ctx.memory.room.switch_toggles += 1
            return ("ok", self.target)

        here = ctx.tracker.player_tile()
        if abs(here[0] - self.target[0]) + abs(here[1] - self.target[1]) <= 1:
            nudge = disambiguation_nudge(ctx)
            if nudge is not None:
                return ("act", nudge)
            if ctx.tracker.steps_since_sync > 0:
                ctx.tracker.request_perceive()
                return ("act", ACTION_NOOP)
            self._pressed = True
            ctx.tracker.request_perceive()
            return ("act", ACTION_A)

        kind, payload = self._nav.step(ctx)
        if kind == "fail":
            return ("fail", ("switch_unreachable", self.target, payload))
        if kind == "ok":
            return ("act", ACTION_NOOP)
        return (kind, payload)


@dataclass
class UseExit:
    """Walk onto an exit tile and push through the room boundary."""

    direction: str = "north"
    _nav: GoToTile | None = None
    _pushes: int = 0
    _steps: int = 0

    def reset(self, ctx: Ctx, *, direction: str) -> None:
        self.direction = direction
        self._nav = None
        self._pushes = 0
        self._steps = 0

    def step(self, ctx: Ctx) -> StepResult:
        self._steps += 1
        if self._steps > 900:
            return ("fail", ("timeout", "use_exit", self.direction))
        state = ctx.state
        if state is None:
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)

        result = ctx.tracker.last_transition_result
        if result == "moved":
            ctx.tracker.last_transition_result = None
            crossed = ctx.tracker.last_transition_dir
            if crossed not in (None, self.direction):
                # We DID change rooms — but through a different open exit
                # brushed en route. Claiming success would poison the
                # opened_exits reconciliation with a lock we never opened.
                return ("fail", ("crossed_other_exit", self.direction, crossed))
            return ("ok", self.direction)
        if result == "blocked":
            ctx.tracker.last_transition_result = None
            if self._pushes >= 2:
                return ("fail", ("exit_blocked", self.direction))

        here = ctx.tracker.player_tile()
        exit_tiles = [t for t in EXIT_TILES[self.direction] if not ctx.memory.is_blocking(*t)]
        if not exit_tiles:
            return ("fail", ("exit_tiles_blocked", self.direction))

        if here in exit_tiles:
            # Align exactly, then push outward; the engine requires the rect
            # flush against the boundary on an exit tile.
            if self._pushes == 0 and self._at_exit_boundary(ctx):
                self._pushes += 1
                ctx.tracker.expect_transition = self.direction
                ctx.tracker.request_perceive()
                return ("act", ACTION_B if ctx.inventory.has_shield else ACTION_NOOP)
            px, py = ctx.tracker.player_px
            tx, ty = here[0] * TILE_SIZE, here[1] * TILE_SIZE
            if (px, py) != (tx, ty):
                action = move_toward_waypoint(ctx, here)
                if action is not None:
                    return ("act", shielded(ctx, action))
            self._pushes += 1
            ctx.tracker.expect_transition = self.direction
            return ("act", DIR_TO_MOVE_ACTION[_exit_push_dir(self.direction)])

        if self._nav is None:
            # Never path over ANOTHER direction's exit tiles: flush contact
            # teleports instantly, hijacking this goal mid-route.
            foreign = frozenset(
                t for d, tiles in EXIT_TILES.items() if d != self.direction
                for t in tiles
            )
            best_target = exit_tiles[0]
            best_path = None
            for tile in exit_tiles:
                path = bfs_path(ctx, here, {tile}, avoid=set(foreign))
                if path is None:
                    continue
                if best_path is None or len(path) < len(best_path):
                    best_target = tile
                    best_path = path
            self._nav = GoToTile()
            self._nav.reset(ctx, target=best_target, align=True, avoid=foreign)
        kind, payload = self._nav.step(ctx)
        if kind == "fail":
            return ("fail", ("exit_unreachable", self.direction, payload))
        if kind == "ok":
            return ("act", ACTION_NOOP)
        return (kind, payload)

    def _at_exit_boundary(self, ctx: Ctx) -> bool:
        px, py = ctx.tracker.player_px
        max_x = (GRID_W - 1) * TILE_SIZE
        max_y = (GRID_H - 1) * TILE_SIZE
        if self.direction == "north":
            return py <= 0
        if self.direction == "south":
            return py >= max_y
        if self.direction == "west":
            return px <= 0
        if self.direction == "east":
            return px >= max_x
        return False


def _exit_push_dir(direction: str) -> str:
    return {"north": "up", "south": "down", "west": "left", "east": "right"}[direction]


@dataclass
class KillMonster:
    """Engage and kill the nearest monster with the sword.

    Tactics: approach axis-aligned, swing when the monster is inside the
    one-tile-ahead hitbox but not yet overlapping the player, then exploit
    the 60-tick post-hit stun to chase and repeat. Perceives frequently so
    monster uncertainty stays small during combat.
    """

    max_steps: int = 700
    _steps: int = 0
    _stun_left: int = 0
    _detour_left: int = 0     # committed BFS-detour steps (vs greedy flapping)

    def reset(self, ctx: Ctx, *, max_steps: int = 700) -> None:
        self.max_steps = max_steps
        self._steps = 0
        self._stun_left = 0
        self._detour_left = 0

    def step(self, ctx: Ctx) -> StepResult:
        self._steps += 1
        if self._steps > self.max_steps:
            return ("fail", ("timeout", "kill_monster"))
        state = ctx.state
        if state is None:
            ctx.tracker.request_perceive()
            return ("act", ACTION_NOOP)
        if not ctx.tracker.monsters:
            return ("ok", "cleared")
        if not ctx.inventory.has_sword:
            return ("fail", ("no_sword",))

        # Keep combat perception tight.
        if ctx.tracker.steps_since_sync >= 6:
            ctx.tracker.request_perceive()

        self._stun_left = max(0, self._stun_left - 1)
        target = min(
            ctx.tracker.monsters,
            key=lambda t: max(
                abs(t.center()[0] - ctx.tracker.player_px[0] - 8),
                abs(t.center()[1] - ctx.tracker.player_px[1] - 8),
            ),
        )
        px, py = ctx.tracker.player_px
        mx, my = target.monster.px
        dx, dy = mx - px, my - py     # top-left deltas; hitbox is 16px ahead

        facing = _swing_facing(dx, dy)
        if facing is not None:
            if ctx.tracker.facing == facing:
                self._stun_left = 55
                ctx.tracker.request_perceive()
                return ("act", ACTION_A)
            # A 1px move sets the facing (blocked moves also set facing).
            return ("act", DIR_TO_MOVE_ACTION[facing])

        # No swing available (misaligned): shield if contact is imminent.
        if self._stun_left == 0 and max(abs(dx), abs(dy)) < 16:
            if ctx.inventory.has_shield:
                return ("act", ACTION_B)

        action = ACTION_NOOP if self._detour_left > 0 else _approach_action(dx, dy)
        if self._detour_left > 0 or (
            action != ACTION_NOOP and _move_is_blocked(ctx, action)
        ):
            # Greedy approach walks into a wall/chest: commit to a BFS
            # detour toward a tile orthogonally adjacent to the monster,
            # so the greedy and BFS controllers cannot flap against each
            # other (one authority at a time).
            self._detour_left = 10 if self._detour_left <= 0 else self._detour_left - 1
            here = ctx.tracker.player_tile()
            goals = {
                t for t in adjacent_tiles(target.monster.tile) if walkable(ctx, t)
            }
            path = bfs_path(ctx, here, goals, avoid_monsters=False)
            if path is not None and len(path) > 1:
                nav_action = move_toward_waypoint(ctx, path[1])
                if nav_action is not None:
                    return ("act", nav_action)
            self._detour_left = 0
            return ("act", ACTION_NOOP)
        return ("act", action)


def _swing_facing(dx: float, dy: float) -> str | None:
    """Facing for which the sword hitbox (player rect shifted one tile)
    overlaps the monster rect with margin.

    The lower gap bound is small on purpose: the engine resolves the sword
    before monster contact, and a hit stuns the monster, so swinging while
    nearly overlapping is safe as long as the swing lands.
    """
    if abs(dy) <= 10:
        if 4 <= dx <= 30:
            return "right"
        if -30 <= dx <= -4:
            return "left"
    if abs(dx) <= 10:
        if 4 <= dy <= 30:
            return "down"
        if -30 <= dy <= -4:
            return "up"
    return None


def _move_is_blocked(ctx: Ctx, action: int) -> bool:
    """Would this 1px move be clamped by a known blocking tile?"""
    direction = next(
        (name for name, act in DIR_TO_MOVE_ACTION.items() if act == action), None
    )
    if direction is None:
        return False
    ddx, ddy = DIR_VECTORS[direction]
    left = ctx.tracker.player_px[0] + ddx
    top = ctx.tracker.player_px[1] + ddy
    x0, y0 = int(left // TILE_SIZE), int(top // TILE_SIZE)
    x1 = int((left + TILE_SIZE - 1) // TILE_SIZE)
    y1 = int((top + TILE_SIZE - 1) // TILE_SIZE)
    for ty in range(y0, y1 + 1):
        for tx in range(x0, x1 + 1):
            if ctx.memory.is_blocking(tx, ty):
                return True
    return False


def _approach_action(dx: float, dy: float) -> int:
    """Close distance on the dominant axis after aligning the cross axis."""
    if abs(dx) >= abs(dy):
        if abs(dy) > 2:
            return DIR_TO_MOVE_ACTION["down" if dy > 0 else "up"]
        if abs(dx) > 16:
            return DIR_TO_MOVE_ACTION["right" if dx > 0 else "left"]
        return ACTION_NOOP  # in the pocket; wait for the swing window
    if abs(dx) > 2:
        return DIR_TO_MOVE_ACTION["right" if dx > 0 else "left"]
    if abs(dy) > 16:
        return DIR_TO_MOVE_ACTION["down" if dy > 0 else "up"]
    return ACTION_NOOP


@dataclass
class Wait:
    steps: int = 1
    _left: int = 0

    def reset(self, ctx: Ctx, *, steps: int = 1) -> None:
        self.steps = int(steps)
        self._left = self.steps

    def step(self, ctx: Ctx) -> StepResult:
        if self._left <= 0:
            return ("ok", self.steps)
        self._left -= 1
        return ("act", ACTION_NOOP)


SKILL_REGISTRY = {
    "goto": GoToTile,
    "open_chest": OpenChest,
    "press_button": PressButton,
    "toggle_switch": ToggleSwitch,
    "use_exit": UseExit,
    "kill_monster": KillMonster,
    "wait": Wait,
}

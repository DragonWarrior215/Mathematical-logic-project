"""Top-level goal arbitration.

Two interchangeable "global programs" drive the primitive skills:

- ``FallbackPlanner`` (this file): a hand-written priority cascade. It is the
  development baseline and the safety net for the induced programs.
- DSL programs produced by the GPT-4o induction pipeline (``induction/``),
  executed by ``graph.Interpreter``. ``load_planner`` picks the induced
  artifact when present unless explicitly asked for the fallback.

The cascade (reflective planning included — failed goals receive symbolic
diagnoses, get cooldowns, and are retried when the relevant state changes):

  0. flee when threatened and unarmed
  1. kill monsters in the current room (when armed)
  2. open the nearest reachable closed chest
  3. pass a locked exit once a key is held
  4. try a conditional exit under a not-yet-tried condition signature
  5. press unpressed buttons
  6. "unblock": pending targets unreachable -> route to a known switch, toggle
  7. route to the nearest room with pending work / frontier exits
  8. wait (retry cooled-down goals)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .constants import (
    ACTION_B,
    ACTION_NOOP,
    EXIT_DELTA,
    EXIT_TILES,
    GRID_H,
    GRID_W,
    TILE_SIZE,
)
from .graph import Ctx
from .grounding import schema
from .memory import Coord
from .skills import (
    SKILL_REGISTRY,
    bfs_path,
    monster_blocked_tiles,
    reachable_tiles,
    walkable,
)

GoalKey = tuple[Any, ...]

# Exploration direction preferences per task (hints only; the logic is task
# agnostic and falls back to a fixed order).
TASK_DIR_HINTS: dict[str, tuple[str, ...]] = {
    "mathematical_logic/task_1": ("north",),
    "mathematical_logic/task_2": ("west",),
    "mathematical_logic/task_3": ("west", "east"),
    "mathematical_logic/task_4": ("north", "east", "south"),
}
DEFAULT_DIR_ORDER = ("north", "west", "south", "east")

FAIL_COOLDOWN_STEPS = 120
THREAT_CLEARANCE_PX = 12.0
MAX_TOGGLES = 12

T5_NEED_KEY = "need_key"
T5_HAVE_KEY = "have_key"
T5_NEED_HEAL = "need_heal"
T5_CLEANUP = "cleanup"


@dataclass
class Goal:
    key: GoalKey
    skill: str
    args: dict[str, Any]


@dataclass
class FallbackPlanner:
    task_id: str | None = None
    current: Goal | None = None
    _skill: Any = None
    cooldowns: dict[GoalKey, int] = field(default_factory=dict)
    tried_conditional: set[GoalKey] = field(default_factory=set)
    stale_rooms: set[Coord] = field(default_factory=set)
    diagnoses: list[tuple[GoalKey, Any]] = field(default_factory=list)
    pending_toggle: bool = False       # persistent "go flip a switch" intent
    toggles_done: int = 0
    goal_log: list[tuple[int, str, GoalKey]] = field(default_factory=list)
    task5_phase: str = T5_NEED_KEY
    task5_ever_had_key: bool = False
    task5_unlocked: bool = False
    task5_key_source_room: Coord | None = None

    # ------------------------------------------------------------------

    def reset(self, task_id: str | None) -> None:
        self.task_id = task_id
        self.current = None
        self._skill = None
        self.cooldowns.clear()
        self.tried_conditional.clear()
        self.stale_rooms.clear()
        self.diagnoses.clear()
        self.pending_toggle = False
        self.toggles_done = 0
        self.task5_phase = T5_NEED_KEY
        self.task5_ever_had_key = False
        self.task5_unlocked = False
        self.task5_key_source_room = None

    def step(self, ctx: Ctx) -> int:
        self.stale_rooms.discard(ctx.memory.current_coord)

        # A new key is a new capability: locked doors we probed in vain
        # deserve another try (probe goal keys embed the key count too).
        keys = ctx.inventory.keys
        if keys > getattr(self, "_last_keys", 0):
            if self._task5(ctx):
                self.task5_key_source_room = ctx.memory.current_coord
            for room in ctx.memory.rooms.values():
                room.probed_dirs.clear()
        self._last_keys = keys
        self._update_task5_phase(ctx)

        if self._should_interrupt_for_combat(ctx):
            self._abandon()

        for _ in range(6):   # goal switches within one env step
            if self.current is None:
                self.current = self._choose_goal(ctx)
                if self.current is None:
                    return self._idle_action(ctx)
                self.goal_log.append(
                    (ctx.memory.step_count, "start", self.current.key)
                )
                self._skill = SKILL_REGISTRY[self.current.skill]()
                self._skill.reset(ctx, **self.current.args)

            kind, payload = self._skill.step(ctx)
            if kind == "act":
                return int(payload)
            goal = self.current
            self.current, self._skill = None, None
            self.goal_log.append((ctx.memory.step_count, kind, goal.key))
            if kind == "ok":
                self._on_success(ctx, goal)
            else:
                self._mark_probed(ctx, goal)
                self.diagnoses.append((goal.key, payload))
                self.cooldowns[goal.key] = ctx.memory.step_count + FAIL_COOLDOWN_STEPS
                if _is_reachability_failure(payload) and self._switch_known(ctx) \
                        and self.toggles_done < MAX_TOGGLES:
                    # Reflective recovery: connectivity is wrong and levers
                    # exist — commit to flipping one before retrying.
                    self.pending_toggle = True
        return ACTION_NOOP

    # ------------------------------------------------------------------
    # Goal outcomes / interrupts
    # ------------------------------------------------------------------

    def _mark_probed(self, ctx: Ctx, goal: Goal) -> None:
        if goal.key[0] == "probe":
            _, coord, direction = goal.key[0], goal.key[1], goal.key[2]
            room = ctx.memory.rooms.get(tuple(coord))
            if room is not None:
                room.probed_dirs.add(direction)

    def _on_success(self, ctx: Ctx, goal: Goal) -> None:
        self._mark_probed(ctx, goal)
        if goal.skill == "kill_monster":
            # Kills can reveal hidden chests anywhere — schedule
            # re-perception of known rooms.
            self.stale_rooms.update(ctx.memory.rooms.keys())
            self.stale_rooms.discard(ctx.memory.current_coord)
        if goal.skill == "toggle_switch":
            # Connectivity changed (not content): previously "unreachable"
            # goals deserve an immediate retry (reflective recovery).
            self.pending_toggle = False
            self.toggles_done += 1
            self.cooldowns.clear()

    def _abandon(self) -> None:
        if self.current is not None and self.current.skill != "kill_monster":
            self.current, self._skill = None, None

    def _should_interrupt_for_combat(self, ctx: Ctx) -> bool:
        if not ctx.inventory.has_sword or not ctx.tracker.monsters:
            return False
        if self.current is not None and self.current.skill == "kill_monster":
            return False
        px, py = ctx.tracker.player_px
        return ctx.tracker.monster_clearance_px(px, py) < THREAT_CLEARANCE_PX

    def _cooled(self, ctx: Ctx, key: GoalKey) -> bool:
        return ctx.memory.step_count >= self.cooldowns.get(key, 0)

    def _idle_action(self, ctx: Ctx) -> int:
        if ctx.memory.step_count % 20 == 0:
            ctx.tracker.request_perceive()
        px, py = ctx.tracker.player_px
        if ctx.tracker.monster_clearance_px(px, py) < THREAT_CLEARANCE_PX:
            return ACTION_B if ctx.inventory.has_shield else ACTION_NOOP
        return ACTION_NOOP

    # ------------------------------------------------------------------
    # Goal selection cascade
    # ------------------------------------------------------------------

    def _choose_goal(self, ctx: Ctx) -> Goal | None:
        state = ctx.state
        if state is None:
            return None
        coord = ctx.memory.current_coord
        here = ctx.tracker.player_tile()

        # 0. Unarmed and threatened: flee to the farthest safe tile.
        if not ctx.inventory.has_sword and ctx.tracker.monsters:
            px, py = ctx.tracker.player_px
            if ctx.tracker.monster_clearance_px(px, py) < 2 * TILE_SIZE:
                flee = self._flee_tile(ctx, here)
                if flee is not None:
                    return Goal(("flee", coord), "goto", {"target": flee, "max_steps": 200})

        # 1. Engage monsters when armed and they are close (chasers approach
        # on their own — waiting for them beats crossing the room), or when
        # a monster obstructs all paths to the room's pending targets.
        if ctx.inventory.has_sword and ctx.tracker.monsters:
            key = ("kill", coord)
            if self._cooled(ctx, key) and self._should_engage(ctx, here):
                return Goal(key, "kill_monster", {})

        # 1.5 Committed lever intent (reflective recovery for connectivity).
        if self.pending_toggle:
            goal = self._toggle_goal(ctx, here)
            if goal is not None:
                return goal
            self.pending_toggle = False   # no switch actually reachable

        if self._task5(ctx):
            goal = self._task5_stage_goal(ctx, here, coord)
            if goal is not None:
                return goal

        goal = self._locked_exit_goal(ctx, coord)
        if goal is not None:
            return goal

        max_chest_rank = None
        chest = self._best_reachable_chest(ctx, here, max_rank=max_chest_rank)
        if chest is not None:
            key = ("chest", coord, chest)
            if self._cooled(ctx, key):
                return Goal(key, "open_chest", {"target": chest})

        goal = self._button_goal(ctx, coord)
        if goal is not None:
            return goal

        # 5. Conditional exit under an untried condition signature.
        goal = self._conditional_exit_goal(ctx, coord)
        if goal is not None:
            return goal

        # 6. Unreachable pending targets + a known switch -> toggle it.
        goal = self._unblock_goal(ctx, here)
        if goal is not None:
            return goal

        # 7. Route toward STRONG pending work (chests/doors/frontier/stale).
        goal = self._route_goal(ctx, here)
        if goal is not None:
            return goal

        # 7.5 Blind probe (local): perception may miss a door (e.g. on an
        # abyss background). Cheaply push at untried boundary directions
        # whose fixed exit tiles look walkable — the engine answers
        # authoritatively (transition or blocked).
        for direction in self._dir_order():
            if state.exits.get(direction, "-") != "-":
                continue
            if direction in ctx.memory.room.visited_exits \
                    or direction in ctx.memory.room.probed_dirs:
                continue
            if any(
                state.is_blocking(*t) or state.is_hazard(*t)
                for t in EXIT_TILES[direction]
            ):
                continue
            key = ("probe", coord, direction, ctx.inventory.keys)
            if self._cooled(ctx, key):
                return Goal(key, "use_exit", {"direction": direction})

        # 7.6 Hazard-covered boundary directions may hide painted-over doors
        # (abyss rooms): flip a lever to re-route the bridge and expose them
        # for probing.
        if self.toggles_done < MAX_TOGGLES:
            hidden = [
                d for d in self._dir_order()
                if state.exits.get(d, "-") == "-"
                and d not in ctx.memory.room.visited_exits
                and d not in ctx.memory.room.probed_dirs
                and not any(state.tile(*t) == schema.TILE_WALL
                            for t in EXIT_TILES[d])
                and any(state.is_hazard(*t) for t in EXIT_TILES[d])
            ]
            if hidden and self._switch_known(ctx):
                goal = self._toggle_goal(ctx, here)
                if goal is not None and self._cooled(ctx, goal.key):
                    self.pending_toggle = True
                    return goal

        # 7.7 Route toward rooms that still have unprobed directions (weak
        # pending) — only when no local probe work remains.
        for target_coord, room_mem in ctx.memory.rooms.items():
            if target_coord == coord or room_mem.state is None:
                continue
            if not self._has_probe_candidates(room_mem):
                continue
            hop = self._first_hop(ctx, target_coord)
            if hop is not None:
                key = ("route_probe", coord, target_coord, hop,
                       ctx.inventory.keys)
                if self._cooled(ctx, key):
                    return Goal(key, "use_exit", {"direction": hop})

        # 8. Idle-wait, occasionally re-perceiving.
        key = ("wait", ctx.memory.step_count // 16)
        return Goal(key, "wait", {"steps": 8})

    # ------------------------------------------------------------------
    # Helper queries
    # ------------------------------------------------------------------

    def _flee_tile(self, ctx: Ctx, here: tuple[int, int]) -> tuple[int, int] | None:
        reach = reachable_tiles(ctx, here)
        danger = monster_blocked_tiles(ctx, margin_px=8.0)
        candidates = [t for t in reach if t not in danger]
        if not candidates:
            return None

        def clearance(tile: tuple[int, int]) -> float:
            cx, cy = tile[0] * TILE_SIZE + 8, tile[1] * TILE_SIZE + 8
            return min(
                (max(abs(cx - m.center()[0]), abs(cy - m.center()[1]))
                 for m in ctx.tracker.monsters),
                default=1e9,
            )

        return max(candidates, key=clearance)

    def _task5(self, ctx: Ctx) -> bool:
        return self.task_id == "mathematical_logic/task_5" \
            or ctx.memory.task_id == "mathematical_logic/task_5"

    def _completion_pressure(self, ctx: Ctx) -> bool:
        return self._task5(ctx) and (
            ctx.inventory.keys > 0
            or self.task5_phase in {T5_HAVE_KEY, T5_NEED_HEAL, T5_CLEANUP}
            or ctx.memory.hp_estimate <= 4
            or ctx.memory.step_count >= 650
        )

    def _health_critical(self, ctx: Ctx) -> bool:
        return self._task5(ctx) and (
            ctx.memory.hp_estimate <= 2
            or (ctx.memory.hp_estimate <= 3 and ctx.memory.step_count >= 450)
        )

    def _update_task5_phase(self, ctx: Ctx) -> None:
        if not self._task5(ctx):
            return
        if ctx.inventory.keys > 0:
            self.task5_ever_had_key = True
            if not self.task5_unlocked:
                self.task5_phase = T5_HAVE_KEY
        if self.task5_ever_had_key and ctx.inventory.keys == 0:
            self.task5_unlocked = True
            if self.task5_phase != T5_CLEANUP:
                self.task5_phase = T5_NEED_HEAL
        if any(
            room.state is not None and "open" in room.state.exits.values()
            for room in ctx.memory.rooms.values()
        ):
            self.task5_unlocked = True
            if self.task5_phase not in {T5_NEED_HEAL, T5_CLEANUP}:
                self.task5_phase = T5_NEED_HEAL
        if self.task5_unlocked and self._heal_has_been_collected(ctx):
            self.task5_phase = T5_CLEANUP

    def _task5_stage_goal(
        self,
        ctx: Ctx,
        here: tuple[int, int],
        coord: Coord,
    ) -> Goal | None:
        if self.task5_phase == T5_CLEANUP:
            goal = self._task5_cleanup_goal(ctx, here)
            if goal is not None:
                return goal

        if self.task5_phase == T5_NEED_HEAL:
            goal = self._heal_goal(ctx, here)
            if goal is not None:
                return goal

        if self._health_critical(ctx):
            goal = self._heal_goal(ctx, here)
            if goal is not None:
                return goal

        if ctx.inventory.keys > 0 and self.task5_key_source_room != (0, 1):
            goal = self._task5_global_goal(ctx, here)
            if goal is not None:
                return goal

        if ctx.inventory.keys > 0:
            max_rank = 1 if ctx.memory.hp_estimate <= 3 else None
            chest = self._best_reachable_chest(ctx, here, max_rank=max_rank)
            if chest is not None:
                key = ("chest", coord, chest)
                if self._cooled(ctx, key):
                    return Goal(key, "open_chest", {"target": chest})
            if ctx.memory.hp_estimate > 3 and self.task5_phase != T5_HAVE_KEY:
                goal = self._pre_unlock_cleanup_goal(ctx, coord)
                if goal is not None:
                    return goal
            for goal in (
                self._locked_exit_goal(ctx, coord),
                self._button_goal(ctx, coord),
                self._conditional_exit_goal(ctx, coord),
            ):
                if goal is not None:
                    return goal
            return self._route_goal(ctx, here)

        max_rank = None
        if self.task5_phase == T5_NEED_KEY and coord != (0, 0):
            max_rank = 3
        chest = self._best_reachable_chest(ctx, here, max_rank=max_rank)
        if chest is not None:
            key = ("chest", coord, chest)
            if self._cooled(ctx, key):
                return Goal(key, "open_chest", {"target": chest})

        goal = self._button_goal(ctx, coord)
        if goal is not None:
            return goal
        return self._route_goal(ctx, here)

    def _task5_global_goal(self, ctx: Ctx, here: tuple[int, int]) -> Goal | None:
        state = ctx.state
        if state is None:
            return None
        coord = ctx.memory.current_coord
        candidates: list[tuple[int, Goal]] = []

        # Holding a key is an expensive temporary capability in task 5: using
        # it on the east lock should outrank optional gold/button cleanup.
        for direction, exit_state in state.exits.items():
            if exit_state != "locked" or ctx.inventory.keys <= 0:
                continue
            key = ("locked_exit", coord, direction, ctx.inventory.keys)
            if not self._cooled(ctx, key):
                continue
            path_cost = self._exit_path_cost(ctx, here, direction)
            if path_cost is None:
                path_cost = 0
            candidates.append((-500 + path_cost, Goal(
                key, "use_exit", {"direction": direction}
            )))

        for chest in state.closed_chests():
            key = ("chest", coord, chest)
            if not self._cooled(ctx, key):
                continue
            goals = {t for t in _adjacent(chest) if walkable(ctx, t)}
            path = bfs_path(ctx, here, goals, avoid_monsters=False)
            if path is None:
                continue
            score = self._task5_chest_score(ctx, state.tile(*chest)) + len(path)
            candidates.append((score, Goal(
                key, "open_chest", {"target": chest}
            )))

        for button in state.tiles_of(schema.TILE_BUTTON):
            key = ("button", coord, button)
            if not self._cooled(ctx, key):
                continue
            path = bfs_path(ctx, here, {button}, avoid_monsters=False)
            if path is None:
                continue
            score = self._task5_button_score(ctx, coord) + len(path)
            candidates.append((score, Goal(
                key, "press_button", {"target": button}
            )))

        for direction, exit_state in state.exits.items():
            if exit_state == "-":
                continue
            if exit_state == "locked":
                continue
            target = _shift(coord, direction)
            unexplored = target not in ctx.memory.rooms
            pending = self._pending_in_room(ctx, target)
            stale = target in self.stale_rooms
            if not (unexplored or pending or stale):
                continue
            if exit_state == "conditional":
                signature = (
                    "cond_exit", coord, direction,
                    ctx.inventory.keys,
                    len(state.monsters),
                    tuple(sorted(state.tiles_of(schema.TILE_BUTTON_PRESSED))),
                )
                if signature in self.tried_conditional or not self._cooled(ctx, signature):
                    continue
                goal = Goal(signature, "use_exit", {"direction": direction})
            else:
                key = ("frontier", coord, direction, ctx.inventory.keys)
                if not self._cooled(ctx, key):
                    continue
                goal = Goal(key, "use_exit", {"direction": direction})
            path_cost = self._exit_path_cost(ctx, here, direction)
            if path_cost is None:
                continue
            score = self._task5_exit_score(ctx, coord, direction) + path_cost
            candidates.append((score, goal))

        for target_coord, room in ctx.memory.rooms.items():
            if target_coord == coord or room.state is None:
                continue
            if not self._pending_in_room(ctx, target_coord):
                continue
            hop = self._first_hop(ctx, target_coord)
            if hop is None:
                continue
            key = ("route", coord, target_coord, hop, ctx.inventory.keys)
            if not self._cooled(ctx, key):
                continue
            score = self._task5_room_score(ctx, target_coord)
            candidates.append((score, Goal(
                key, "use_exit", {"direction": hop}
            )))

        if not candidates:
            return None
        candidates.sort(key=lambda item: item[0])
        goal = candidates[0][1]
        if goal.key[0] == "cond_exit":
            self.tried_conditional.add(goal.key)
        return goal

    def _task5_chest_score(self, ctx: Ctx, cls: str) -> int:
        if cls == schema.TILE_CHEST_KEY:
            return -300
        if cls == schema.TILE_CHEST_HEAL:
            if self.task5_phase == T5_NEED_HEAL or self._health_critical(ctx):
                return -260
            return -40 if self._completion_pressure(ctx) else 70
        if cls == schema.TILE_CHEST_ITEM:
            return -120
        if cls == schema.TILE_CHEST_UNKNOWN:
            return -80 if self.task5_phase == T5_NEED_KEY else 20
        if cls == schema.TILE_CHEST_GOLD:
            return 35 if self.task5_phase == T5_CLEANUP else 120
        return 140

    def _task5_button_score(self, ctx: Ctx, coord: Coord) -> int:
        if ctx.inventory.keys > 0:
            return 80
        state = ctx.state
        if state is not None and any(
            exit_state == "conditional" and _shift(coord, direction) not in ctx.memory.rooms
            for direction, exit_state in state.exits.items()
        ):
            return -90
        return 30

    def _task5_exit_score(self, ctx: Ctx, coord: Coord, direction: str) -> int:
        state = ctx.state
        if state is None:
            return 200
        exit_state = state.exits.get(direction, "-")
        target = _shift(coord, direction)
        if exit_state == "open":
            return -140 if self.task5_phase in {T5_NEED_HEAL, T5_CLEANUP} else -20
        if exit_state == "conditional":
            return -70 if self.task5_phase == T5_NEED_KEY else 30
        if target in ctx.memory.rooms:
            return self._task5_room_score(ctx, target)
        if self.task5_phase == T5_NEED_KEY:
            return 0
        return 60

    def _task5_room_score(self, ctx: Ctx, coord: Coord) -> int:
        room = ctx.memory.rooms.get(coord)
        distance = self._room_distance(ctx, coord)
        if room is None or room.state is None:
            return 40 + 25 * distance
        state = room.state
        score = 130
        if coord in self.stale_rooms:
            score = min(score, 20)
        if self.task5_phase == T5_NEED_HEAL and state.tiles_of(schema.TILE_CHEST_HEAL):
            score = min(score, -240)
        if ctx.inventory.keys > 0 and "locked" in state.exits.values():
            score = min(score, -220)
        for chest in state.closed_chests():
            score = min(score, self._task5_chest_score(ctx, state.tile(*chest)))
        if state.tiles_of(schema.TILE_BUTTON):
            score = min(score, self._task5_button_score(ctx, coord))
        for direction, exit_state in state.exits.items():
            if exit_state != "-" and _shift(coord, direction) not in ctx.memory.rooms:
                score = min(score, 10)
        return score + 25 * distance

    def _exit_path_cost(
        self,
        ctx: Ctx,
        here: tuple[int, int],
        direction: str,
    ) -> int | None:
        goals = {t for t in EXIT_TILES[direction] if walkable(ctx, t)}
        path = bfs_path(ctx, here, goals, avoid_monsters=False)
        return None if path is None else len(path)

    def _task5_cleanup_goal(self, ctx: Ctx, here: tuple[int, int]) -> Goal | None:
        coord = ctx.memory.current_coord
        chest = self._best_reachable_chest(ctx, here)
        if chest is not None:
            key = ("chest", coord, chest)
            if self._cooled(ctx, key):
                return Goal(key, "open_chest", {"target": chest})
        goal = self._button_goal(ctx, coord)
        if goal is not None:
            return goal
        goal = self._conditional_exit_goal(ctx, coord)
        if goal is not None:
            return goal
        return self._route_goal(ctx, here)

    def _heal_has_been_collected(self, ctx: Ctx) -> bool:
        for room in ctx.memory.rooms.values():
            state = room.state
            if state is None:
                continue
            if room.coord == (1, 0) and state.tiles_of(schema.TILE_CHEST_OPEN):
                return True
            if not state.tiles_of(schema.TILE_CHEST_HEAL) and room.coord == (1, 0):
                return True
        return False

    def _pre_unlock_cleanup_goal(self, ctx: Ctx, coord: Coord) -> Goal | None:
        state = ctx.state
        if state is None:
            return None
        for direction in self._route_dir_order(ctx, coord):
            exit_state = state.exits.get(direction, "-")
            if exit_state not in {"normal", "conditional", "open"}:
                continue
            target = _shift(coord, direction)
            if target in ctx.memory.rooms and not self._strong_room_work(ctx, target):
                continue
            key = ("pre_unlock_cleanup", coord, direction, ctx.inventory.keys)
            if self._cooled(ctx, key):
                return Goal(key, "use_exit", {"direction": direction})
        return None

    def _strong_room_work(self, ctx: Ctx, coord: Coord) -> bool:
        room = ctx.memory.rooms.get(coord)
        if room is None or room.state is None:
            return True
        state = room.state
        if state.closed_chests() or state.tiles_of(schema.TILE_BUTTON):
            return True
        for direction, exit_state in state.exits.items():
            if exit_state == "-":
                continue
            if exit_state == "locked":
                continue
            target = _shift(coord, direction)
            if target not in ctx.memory.rooms:
                return True
        return False

    def _room_distance(self, ctx: Ctx, coord: Coord) -> int:
        here = ctx.memory.current_coord
        return abs(coord[0] - here[0]) + abs(coord[1] - here[1])

    def _heal_goal(self, ctx: Ctx, here: tuple[int, int]) -> Goal | None:
        state = ctx.state
        coord = ctx.memory.current_coord
        best: tuple[int, tuple[int, int]] | None = None
        for chest in state.tiles_of(schema.TILE_CHEST_HEAL):
            key = ("chest", coord, chest)
            if not self._cooled(ctx, key):
                continue
            goals = {t for t in _adjacent(chest) if walkable(ctx, t)}
            path = bfs_path(ctx, here, goals, avoid_monsters=False)
            if path is None:
                continue
            candidate = (len(path), chest)
            if best is None or candidate < best:
                best = candidate
        if best is not None:
            chest = best[1]
            return Goal(("chest", coord, chest), "open_chest", {"target": chest})

        heal_rooms = [
            other
            for other, room in ctx.memory.rooms.items()
            if other != coord and room.state is not None
            and room.state.tiles_of(schema.TILE_CHEST_HEAL)
        ]
        for target_coord in sorted(heal_rooms, key=lambda c: self._room_distance(ctx, c)):
            hop = self._first_hop(ctx, target_coord)
            if hop is not None:
                key = ("route_heal", coord, target_coord, hop)
                if self._cooled(ctx, key):
                    return Goal(key, "use_exit", {"direction": hop})
        return None

    def _locked_exit_goal(self, ctx: Ctx, coord: Coord) -> Goal | None:
        state = ctx.state
        if state is None or ctx.inventory.keys <= 0:
            return None
        for direction in self._dir_order():
            if state.exits.get(direction) != "locked":
                continue
            key = ("locked_exit", coord, direction, ctx.inventory.keys)
            if self._cooled(ctx, key):
                return Goal(key, "use_exit", {"direction": direction})
        for direction, exit_state in state.exits.items():
            if exit_state != "locked":
                continue
            key = ("locked_exit", coord, direction, ctx.inventory.keys)
            if self._cooled(ctx, key):
                return Goal(key, "use_exit", {"direction": direction})
        return None

    def _button_goal(self, ctx: Ctx, coord: Coord) -> Goal | None:
        state = ctx.state
        if state is None:
            return None
        here = ctx.tracker.player_tile()
        best: tuple[int, tuple[int, int]] | None = None
        for button in state.tiles_of(schema.TILE_BUTTON):
            key = ("button", coord, button)
            if not self._cooled(ctx, key):
                continue
            path = bfs_path(ctx, here, {button}, avoid_monsters=False)
            if path is None:
                continue
            candidate = (len(path), button)
            if best is None or candidate < best:
                best = candidate
        if best is None:
            return None
        button = best[1]
        return Goal(("button", coord, button), "press_button", {"target": button})

    def _conditional_exit_goal(self, ctx: Ctx, coord: Coord) -> Goal | None:
        state = ctx.state
        if state is None:
            return None
        for direction in self._dir_order():
            if state.exits.get(direction) != "conditional":
                continue
            target = _shift(coord, direction)
            if self._task5(ctx) and target in ctx.memory.rooms \
                    and not self._strong_room_work(ctx, target):
                continue
            signature = (
                "cond_exit", coord, direction,
                ctx.inventory.keys,
                len(state.monsters),
                tuple(sorted(state.tiles_of(schema.TILE_BUTTON_PRESSED))),
            )
            if signature not in self.tried_conditional and self._cooled(ctx, signature):
                self.tried_conditional.add(signature)
                return Goal(signature, "use_exit", {"direction": direction})
        for direction, exit_state in state.exits.items():
            if exit_state != "conditional":
                continue
            target = _shift(coord, direction)
            if self._task5(ctx) and target in ctx.memory.rooms \
                    and not self._strong_room_work(ctx, target):
                continue
            signature = (
                "cond_exit", coord, direction,
                ctx.inventory.keys,
                len(state.monsters),
                tuple(sorted(state.tiles_of(schema.TILE_BUTTON_PRESSED))),
            )
            if signature not in self.tried_conditional and self._cooled(ctx, signature):
                self.tried_conditional.add(signature)
                return Goal(signature, "use_exit", {"direction": direction})
        return None

    def _best_reachable_chest(
        self,
        ctx: Ctx,
        here: tuple[int, int],
        *,
        max_rank: int | None = None,
    ):
        state = ctx.state
        best, best_score = None, None
        for chest in state.closed_chests():
            key = ("chest", ctx.memory.current_coord, chest)
            if not self._cooled(ctx, key):
                continue
            rank = self._chest_value_rank(ctx, state.tile(*chest))
            if max_rank is not None and rank > max_rank:
                continue
            goals = {t for t in _adjacent(chest) if walkable(ctx, t)}
            path = bfs_path(ctx, here, goals, avoid_monsters=False)
            if path is None:
                continue
            score = 10 * rank + len(path)
            if best_score is None or score < best_score:
                best, best_score = chest, score
        return best

    def _chest_value_rank(self, ctx: Ctx, cls: str) -> int:
        if cls == schema.TILE_CHEST_KEY:
            return 0
        if cls == schema.TILE_CHEST_ITEM:
            return 1
        if cls == schema.TILE_CHEST_HEAL:
            return 1 if self._completion_pressure(ctx) else 3
        if cls == schema.TILE_CHEST_UNKNOWN:
            return 2
        if cls == schema.TILE_CHEST_GOLD:
            return 5 if self._completion_pressure(ctx) else 4
        return 6

    def _pending_in_room(self, ctx: Ctx, coord: Coord) -> bool:
        room = ctx.memory.rooms.get(coord)
        if room is None or room.state is None:
            return True   # unknown rooms are always worth a look
        if coord in self.stale_rooms:
            return True
        state = room.state
        if state.closed_chests():
            return True
        if state.tiles_of(schema.TILE_BUTTON):
            return True
        for direction, exit_state in state.exits.items():
            if exit_state == "locked" and ctx.inventory.keys > 0:
                return True
            if direction not in room.visited_exits and exit_state != "-":
                target = _shift(coord, direction)
                if target not in ctx.memory.rooms:
                    return True
        return False

    @staticmethod
    def _has_probe_candidates(room) -> bool:
        """Unprobed boundary directions that may hide painted-over doors
        (weak pending) — walls are definitive, anything else deserves one
        probe eventually."""
        state = room.state
        for direction, tiles in EXIT_TILES.items():
            if state.exits.get(direction, "-") != "-":
                continue
            if direction in room.visited_exits or direction in room.probed_dirs:
                continue
            if any(state.tile(*t) == schema.TILE_WALL for t in tiles):
                continue
            return True
        return False

    def _should_engage(self, ctx: Ctx, here: tuple[int, int]) -> bool:
        # Engage only truly imminent threats: chasers close the gap on their
        # own, and patrollers/ambushers that keep their distance are cheaper
        # to walk away from than to hunt (the task_5 HP drain prices time).
        px, py = ctx.tracker.player_px
        close_threshold = (0.75 if self._task5(ctx) else 1.9) * TILE_SIZE
        if ctx.tracker.monster_clearance_px(px, py) < close_threshold:
            return True
        if self._task5(ctx) and ctx.memory.hp_estimate <= 2:
            return False
        # A far-away monster (patroller) still must die if it blocks work:
        # any closed chest whose approach passes through its territory.
        state = ctx.state
        for chest in state.closed_chests():
            goals = {t for t in _adjacent(chest) if walkable(ctx, t)}
            if goals and bfs_path(ctx, here, goals) is None \
                    and bfs_path(ctx, here, goals, avoid_monsters=False) is not None:
                return True
        for direction, exit_state in state.exits.items():
            if exit_state == "-":
                continue
            if exit_state == "locked" and ctx.inventory.keys <= 0:
                continue
            target = _shift(ctx.memory.current_coord, direction)
            if target in ctx.memory.rooms and not self._pending_in_room(ctx, target):
                continue
            goals = {t for t in EXIT_TILES[direction] if walkable(ctx, t)}
            if goals and bfs_path(ctx, here, goals) is None \
                    and bfs_path(ctx, here, goals, avoid_monsters=False) is not None:
                return True
        return False

    def _switch_known(self, ctx: Ctx) -> bool:
        return any(
            room.state is not None
            and room.state.tiles_of(schema.TILE_SWITCH, schema.TILE_SWITCH_ACTIVE)
            for room in ctx.memory.rooms.values()
        )

    def _toggle_goal(self, ctx: Ctx, here: tuple[int, int]) -> Goal | None:
        """Persistent lever intent: flip a switch in this room, or route
        toward the nearest room known to contain one."""
        state = ctx.state
        coord = ctx.memory.current_coord
        reach = reachable_tiles(ctx, here)

        switches = state.tiles_of(schema.TILE_SWITCH, schema.TILE_SWITCH_ACTIVE)
        reachable_switch = next(
            (s for s in switches if any(t in reach for t in _adjacent(s))), None
        )
        if reachable_switch is not None:
            key = ("toggle", coord, reachable_switch, self.toggles_done)
            return Goal(key, "toggle_switch", {"target": reachable_switch})

        candidates = [
            other_coord
            for other_coord, room in ctx.memory.rooms.items()
            if other_coord != coord and room.state is not None
            and room.state.tiles_of(schema.TILE_SWITCH, schema.TILE_SWITCH_ACTIVE)
        ]
        for other_coord in sorted(
            candidates, key=lambda c: abs(c[0] - coord[0]) + abs(c[1] - coord[1])
        ):
            hop = self._first_hop(ctx, other_coord)
            if hop is not None:
                key = ("route_switch", coord, other_coord, hop, self.toggles_done)
                return Goal(key, "use_exit", {"direction": hop})
        return None

    def _unblock_goal(self, ctx: Ctx, here: tuple[int, int]) -> Goal | None:
        """Proactive variant of the lever intent: some *pending* target in
        this room is unreachable although we have not tried it yet."""
        if self.pending_toggle or self.toggles_done >= MAX_TOGGLES:
            return None
        state = ctx.state
        coord = ctx.memory.current_coord
        reach = reachable_tiles(ctx, here)

        def exit_pending(direction: str, exit_state: str) -> bool:
            if exit_state == "-":
                return False
            target = _shift(coord, direction)
            if target not in ctx.memory.rooms or target in self.stale_rooms:
                return True
            if exit_state == "locked" and ctx.inventory.keys > 0:
                return True
            return self._pending_in_room(ctx, target)

        blocked = any(
            not any(t in reach for t in _adjacent(chest))
            for chest in state.closed_chests()
        ) or any(
            exit_pending(direction, exit_state)
            and not any(t in reach for t in EXIT_TILES[direction])
            for direction, exit_state in state.exits.items()
        )
        if not blocked or not self._switch_known(ctx):
            return None
        goal = self._toggle_goal(ctx, here)
        if goal is not None:
            self.pending_toggle = True   # persist the intent across rooms
        return goal

    def _route_goal(self, ctx: Ctx, here: tuple[int, int]) -> Goal | None:
        coord = ctx.memory.current_coord
        room = ctx.memory.room
        state = ctx.state

        # Frontier exits from the current room first.  Task 5 scores exits by
        # expected task value so low-value exploration does not outrank known
        # completion work.
        frontier_goals: list[tuple[int, Goal]] = []
        for direction in self._route_dir_order(ctx, coord):
            exit_state = state.exits.get(direction, "-")
            if exit_state == "-":
                continue
            target = _shift(coord, direction)
            unexplored = target not in ctx.memory.rooms
            stale = target in self.stale_rooms
            if not (unexplored or stale):
                continue
            if exit_state == "locked" and ctx.inventory.keys == 0:
                continue
            key = ("frontier", coord, direction, ctx.inventory.keys)
            if self._cooled(ctx, key):
                goal = Goal(key, "use_exit", {"direction": direction})
                if self._task5(ctx):
                    frontier_goals.append((self._local_exit_score(ctx, coord, direction), goal))
                else:
                    return goal
        if frontier_goals:
            return min(frontier_goals, key=lambda item: item[0])[1]

        # Otherwise route toward the nearest known room with pending work.
        pending_rooms = [
            c for c in ctx.memory.rooms
            if c != coord and self._pending_in_room(ctx, c)
        ]
        for target_coord in sorted(pending_rooms, key=lambda c: self._room_work_score(ctx, c)):
            hop = self._first_hop(ctx, target_coord)
            if hop is not None:
                key = ("route", coord, target_coord, hop, ctx.inventory.keys)
                if self._cooled(ctx, key):
                    return Goal(key, "use_exit", {"direction": hop})

        # Re-traverse visited exits if some room beyond might have work.
        for direction in self._dir_order():
            if direction in room.visited_exits:
                target = _shift(coord, direction)
                if self._pending_in_room(ctx, target):
                    key = ("revisit", coord, direction, ctx.memory.step_count // 200)
                    if self._cooled(ctx, key):
                        return Goal(key, "use_exit", {"direction": direction})
        return None

    def _route_dir_order(self, ctx: Ctx, coord: Coord) -> tuple[str, ...]:
        return tuple(sorted(
            EXIT_DELTA,
            key=lambda direction: (
                self._local_exit_score(ctx, coord, direction),
                DEFAULT_DIR_ORDER.index(direction),
            ),
        ))

    def _local_exit_score(self, ctx: Ctx, coord: Coord, direction: str) -> int:
        room = ctx.memory.rooms.get(coord)
        state = room.state if room is not None else ctx.state
        if state is None:
            return 1000
        exit_state = state.exits.get(direction, "-")
        if exit_state == "-":
            return 1000
        if exit_state == "locked":
            return -100 if ctx.inventory.keys > 0 else 950

        target = _shift(coord, direction)
        target_room = ctx.memory.rooms.get(target)
        if target_room is not None and target_room.state is not None:
            if self._pending_in_room(ctx, target):
                return self._room_work_score(ctx, target)
            if target in self.stale_rooms:
                return 70 + self._room_distance(ctx, target)
            return 100 + self._room_distance(ctx, target)

        if exit_state == "conditional":
            return -20
        if exit_state == "open":
            return 5
        return 10

    def _room_work_score(self, ctx: Ctx, coord: Coord) -> int:
        room = ctx.memory.rooms.get(coord)
        distance = self._room_distance(ctx, coord)
        if room is None or room.state is None:
            return 40 + distance
        state = room.state
        score = 80
        if coord in self.stale_rooms:
            score = min(score, 15)
        if ctx.inventory.keys > 0 and "locked" in state.exits.values():
            score = min(score, 0)
        for chest in state.closed_chests():
            score = min(score, 10 + 10 * self._chest_value_rank(ctx, state.tile(*chest)))
        if state.tiles_of(schema.TILE_BUTTON):
            score = min(score, 20)
        for direction, exit_state in state.exits.items():
            target = _shift(coord, direction)
            if exit_state != "-" and target not in ctx.memory.rooms:
                score = min(score, 35)
        return score + distance

    def _first_hop(self, ctx: Ctx, target: Coord) -> str | None:
        """BFS over the known room graph; returns the first exit direction."""
        from collections import deque

        start = ctx.memory.current_coord
        queue = deque([start])
        parent: dict[Coord, tuple[Coord, str] | None] = {start: None}
        while queue:
            coord = queue.popleft()
            if coord == target:
                hop = None
                while parent[coord] is not None:
                    coord, hop = parent[coord]
                return hop
            room = ctx.memory.rooms.get(coord)
            if room is None or room.state is None:
                continue
            for direction, exit_state in room.state.exits.items():
                if exit_state == "-":
                    continue
                if exit_state == "locked" and direction not in room.visited_exits \
                        and ctx.inventory.keys == 0:
                    continue
                nxt = _shift(coord, direction)
                if nxt in parent:
                    continue
                parent[nxt] = (coord, direction)
                queue.append(nxt)
        return None

    def _dir_order(self) -> tuple[str, ...]:
        hints = TASK_DIR_HINTS.get(self.task_id or "", ())
        rest = tuple(d for d in DEFAULT_DIR_ORDER if d not in hints)
        return hints + rest


def _is_reachability_failure(diagnosis: Any) -> bool:
    flat = repr(diagnosis)
    return "no_path" in flat or "unreachable" in flat


def _adjacent(tile: tuple[int, int]):
    x, y = tile
    return [
        t for t in ((x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y))
        if 0 <= t[0] < GRID_W and 0 <= t[1] < GRID_H
    ]


def _shift(coord: Coord, direction: str) -> Coord:
    dx, dy = EXIT_DELTA[direction]
    return (coord[0] + dx, coord[1] + dy)


def load_planner(task_id: str | None, *, prefer_induced: bool = True):
    """Return the global program: induced DSL artifact if available, else the
    hand-written fallback. Import is deferred so inference has no hard
    dependency on the induction package."""
    if prefer_induced:
        try:
            from .induction.dsl import load_artifact_planner

            planner = load_artifact_planner(task_id)
            if planner is not None:
                return planner
        except Exception:
            pass
    planner = FallbackPlanner()
    planner.reset(task_id)
    return planner

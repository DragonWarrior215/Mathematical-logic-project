"""Textual DSL for NSI skill programs (GPT-4o readable/writable).

A program is JSON:

    {
      "name": "task_1",
      "entry": "need_key",
      "reactive": [                      # guards checked every step, in order
        {"pred": "threatened() and inv.has_sword", "skill": "kill_monster",
         "args": {}}
      ],
      "nodes": [
        {"name": "need_key", "kind": "check", "pred": "inv.keys == 0",
         "on_true": "find_chest", "on_false": "go_exit"},
        {"name": "find_chest", "kind": "data",
         "bind": {"chest": "nearest(closed_chests())"}, "next": "open_it"},
        {"name": "open_it", "kind": "skill", "skill": "open_chest",
         "args": {"target": "var.chest"},
         "on_success": "need_key", "on_fail": "fail"},
        {"name": "go_exit", "kind": "skill", "skill": "use_exit",
         "args": {"direction": "'north'"},
         "on_success": "done", "on_fail": "fail"},
        {"name": "done", "kind": "terminal", "success": true},
        {"name": "fail", "kind": "terminal", "success": false}
      ]
    }

Node kinds: ``data`` (bind scope variables), ``check`` (branch on a
predicate; loops are checks with back edges), ``skill`` (invoke a primitive
skill until it returns), ``terminal``. Expressions are a restricted,
side-effect-free Python subset evaluated against the symbolic state — the
whole layer is deterministic and small enough to formalize in Lean.

Program complexity |pi| (the MDL term) = node count + expression sizes.
"""

from __future__ import annotations

import ast
import json
from pathlib import Path
from typing import Any

from ..constants import GRID_H, GRID_W, TILE_SIZE
from ..graph import (
    CheckOp,
    Ctx,
    DataOp,
    Interpreter,
    SkillOp,
    SkillProgram,
    TerminalOp,
)
from ..grounding import schema
from ..skills import SKILL_REGISTRY, bfs_path, walkable

ARTIFACT_DIR = Path(__file__).resolve().parent / "artifacts"

NODE_KINDS = ("data", "check", "skill", "terminal")

# JSON schema handed to GPT-4o structured outputs.
PROGRAM_JSON_SCHEMA: dict = {
    "type": "object",
    "properties": {
        "name": {"type": "string"},
        "entry": {"type": "string"},
        "reactive": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "pred": {"type": "string"},
                    "skill": {"type": "string"},
                    "args": {
                        "type": "object",
                        "properties": {
                            "target": {"type": ["string", "null"]},
                            "direction": {"type": ["string", "null"]},
                        },
                        "required": ["target", "direction"],
                        "additionalProperties": False,
                    },
                },
                "required": ["pred", "skill", "args"],
                "additionalProperties": False,
            },
        },
        "nodes": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "name": {"type": "string"},
                    "kind": {"type": "string", "enum": list(NODE_KINDS)},
                    "pred": {"type": ["string", "null"]},
                    "bind_name": {"type": ["string", "null"]},
                    "bind_expr": {"type": ["string", "null"]},
                    "skill": {"type": ["string", "null"]},
                    "args": {
                        "type": ["object", "null"],
                        "properties": {
                            "target": {"type": ["string", "null"]},
                            "direction": {"type": ["string", "null"]},
                        },
                        "required": ["target", "direction"],
                        "additionalProperties": False,
                    },
                    "next": {"type": ["string", "null"]},
                    "on_true": {"type": ["string", "null"]},
                    "on_false": {"type": ["string", "null"]},
                    "on_success": {"type": ["string", "null"]},
                    "on_fail": {"type": ["string", "null"]},
                    "success": {"type": ["boolean", "null"]},
                },
                "required": [
                    "name", "kind", "pred", "bind_name", "bind_expr", "skill",
                    "args", "next", "on_true", "on_false", "on_success",
                    "on_fail", "success",
                ],
                "additionalProperties": False,
            },
        },
    },
    "required": ["name", "entry", "reactive", "nodes"],
    "additionalProperties": False,
}


# ---------------------------------------------------------------------------
# Safe expression evaluation
# ---------------------------------------------------------------------------

_ALLOWED_NODES = (
    ast.Expression, ast.BoolOp, ast.And, ast.Or, ast.UnaryOp, ast.Not,
    ast.USub, ast.Compare, ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt,
    ast.GtE, ast.In, ast.NotIn, ast.Is, ast.IsNot, ast.BinOp, ast.Add,
    ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Call, ast.Name,
    ast.Load, ast.Constant, ast.Tuple, ast.List, ast.Subscript,
    ast.Attribute, ast.IfExp, ast.Slice,
)

_ATTR_ROOTS = {"inv", "var"}
_INV_FIELDS = {"keys", "gold", "has_sword", "has_shield", "items", "tools"}


class ExprError(ValueError):
    pass


def _validate(tree: ast.AST) -> None:
    for node in ast.walk(tree):
        if not isinstance(node, _ALLOWED_NODES):
            raise ExprError(f"disallowed syntax: {type(node).__name__}")
        if isinstance(node, ast.Attribute):
            if not isinstance(node.value, ast.Name) or node.value.id not in _ATTR_ROOTS:
                raise ExprError("attribute access only on inv./var.")
            if isinstance(node.value, ast.Name) and node.value.id == "inv" \
                    and node.attr not in _INV_FIELDS:
                raise ExprError(f"unknown inventory field: {node.attr}")
        if isinstance(node, ast.Call):
            if not isinstance(node.func, ast.Name):
                raise ExprError("only plain function calls allowed")


class _VarView:
    def __init__(self, scope: dict[str, Any]) -> None:
        self._scope = scope

    def __getattr__(self, name: str) -> Any:
        try:
            return self._scope[name]
        except KeyError as exc:
            raise ExprError(f"unbound variable: var.{name}") from exc


class _InvView:
    def __init__(self, inventory) -> None:
        self._inv = inventory

    def __getattr__(self, name: str) -> Any:
        if name not in _INV_FIELDS:
            raise ExprError(f"unknown inventory field: {name}")
        return getattr(self._inv, name)


def build_env(ctx: Ctx) -> dict[str, Any]:
    """The query namespace exposed to DSL expressions (pure functions of Z)."""
    state = ctx.state
    tracker = ctx.tracker
    memory = ctx.memory

    def closed_chests():
        return state.closed_chests() if state else []

    def chests(kind: str):
        mapping = {"key": schema.TILE_CHEST_KEY, "gold": schema.TILE_CHEST_GOLD,
                   "heal": schema.TILE_CHEST_HEAL, "item": schema.TILE_CHEST_ITEM}
        return state.tiles_of(mapping[kind]) if state else []

    def monster_count():
        return len(tracker.monsters)

    def nearest(tiles):
        here = tracker.player_tile()
        best, best_len = None, None
        for tile in tiles or []:
            tile = (int(tile[0]), int(tile[1]))
            goals = {tile} if walkable(ctx, tile) else {
                t for t in _adj(tile) if walkable(ctx, t)
            }
            path = bfs_path(ctx, here, goals, avoid_monsters=False)
            if path is not None and (best_len is None or len(path) < best_len):
                best, best_len = tile, len(path)
        return best

    def reachable(tile):
        if tile is None:
            return False
        tile = (int(tile[0]), int(tile[1]))
        here = tracker.player_tile()
        goals = {tile} if walkable(ctx, tile) else {
            t for t in _adj(tile) if walkable(ctx, t)
        }
        return bfs_path(ctx, here, goals, avoid_monsters=False) is not None

    def exit_state(direction: str) -> str:
        return state.exit_state(direction) if state else "-"

    def visited(direction: str) -> bool:
        return direction in memory.room.visited_exits

    def threatened() -> bool:
        px, py = tracker.player_px
        return tracker.monster_clearance_px(px, py) < 1.9 * TILE_SIZE

    def buttons(pressed: bool = False):
        cls = schema.TILE_BUTTON_PRESSED if pressed else schema.TILE_BUTTON
        return state.tiles_of(cls) if state else []

    def switches():
        return state.tiles_of(schema.TILE_SWITCH, schema.TILE_SWITCH_ACTIVE) \
            if state else []

    def room_known(direction: str) -> bool:
        from ..constants import EXIT_DELTA

        dx, dy = EXIT_DELTA[direction]
        cx, cy = memory.current_coord
        return (cx + dx, cy + dy) in memory.rooms

    def hop_toward(kind: str):
        """First-hop exit direction toward the nearest known room satisfying
        ``kind`` ('locked_exit'|'chest'|'switch'|'unexplored'). Returns None
        when the current room already satisfies it or nothing is known."""
        from collections import deque

        from ..constants import EXIT_DELTA

        def satisfies(coord) -> bool:
            room = memory.rooms.get(coord)
            if room is None or room.state is None:
                return False
            room_state = room.state
            if kind == "locked_exit":
                return "locked" in room_state.exits.values()
            if kind == "chest":
                return bool(room_state.closed_chests())
            if kind == "switch":
                return bool(room_state.tiles_of(
                    schema.TILE_SWITCH, schema.TILE_SWITCH_ACTIVE))
            if kind == "unexplored":
                return any(
                    exit_st != "-" and
                    (coord[0] + EXIT_DELTA[d][0], coord[1] + EXIT_DELTA[d][1])
                    not in memory.rooms
                    for d, exit_st in room_state.exits.items()
                )
            return False

        start = memory.current_coord
        if satisfies(start):
            return None
        queue = deque([start])
        parent: dict = {start: None}
        while queue:
            coord = queue.popleft()
            if coord != start and satisfies(coord):
                hop = None
                while parent[coord] is not None:
                    coord, hop = parent[coord]
                return hop
            room = memory.rooms.get(coord)
            if room is None or room.state is None:
                continue
            for direction, exit_st in room.state.exits.items():
                if exit_st == "-":
                    continue
                if exit_st == "locked" and direction not in room.visited_exits \
                        and ctx.inventory.keys == 0:
                    continue
                dx, dy = EXIT_DELTA[direction]
                nxt = (coord[0] + dx, coord[1] + dy)
                if nxt in parent:
                    continue
                parent[nxt] = (coord, direction)
                queue.append(nxt)
                # Unexplored neighbors count as candidate targets themselves.
                if kind == "unexplored" and nxt not in memory.rooms:
                    coord2, hop = nxt, None
                    while parent[coord2] is not None:
                        coord2, hop = parent[coord2]
                    return hop
        return None

    return {
        "closed_chests": closed_chests,
        "chests": chests,
        "monster_count": monster_count,
        "nearest": nearest,
        "reachable": reachable,
        "exit_state": exit_state,
        "visited": visited,
        "threatened": threatened,
        "buttons": buttons,
        "switches": switches,
        "room_known": room_known,
        "hop_toward": hop_toward,
        "player_tile": tracker.player_tile,
        "room_coord": lambda: memory.current_coord,
        "step_count": lambda: memory.step_count,
        "len": len,
        "abs": abs,
        "min": min,
        "max": max,
    }


def _adj(tile):
    x, y = tile
    return [
        t for t in ((x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y))
        if 0 <= t[0] < GRID_W and 0 <= t[1] < GRID_H
    ]


def compile_expr(source: str):
    tree = ast.parse(source, mode="eval")
    _validate(tree)
    code = compile(tree, "<dsl>", "eval")

    def run(ctx: Ctx) -> Any:
        env = build_env(ctx)
        # Bare names resolve to scope variables (LLMs often drop the "var."
        # prefix); core queries take precedence over scope on collision.
        env = {**ctx.scope, **env}
        env["inv"] = _InvView(ctx.inventory)
        env["var"] = _VarView(ctx.scope)
        return eval(code, {"__builtins__": {}}, env)  # noqa: S307 - sandboxed

    run.source = source  # type: ignore[attr-defined]
    return run


# ---------------------------------------------------------------------------
# Program compilation
# ---------------------------------------------------------------------------


def _clean_args(raw: dict | None) -> dict[str, str]:
    return {k: v for k, v in (raw or {}).items() if v is not None}


def _first(*values):
    return next((v for v in values if v), None)


def normalize_spec(spec: dict) -> dict:
    """Tolerant normalization of LLM-written specs: edge-field aliases,
    dangling edge targets (auto-terminals), and entry repair. The empirical
    consistency checker is the real gatekeeper — compilation should accept
    every structurally salvageable program."""
    spec = json.loads(json.dumps(spec))   # deep copy
    nodes = spec.get("nodes", [])
    names = {raw.get("name") for raw in nodes}

    referenced: set[str] = set()
    for raw in nodes:
        kind = raw.get("kind")
        if kind == "check":
            raw["on_true"] = _first(raw.get("on_true"), raw.get("on_success"),
                                    raw.get("next"))
            raw["on_false"] = _first(raw.get("on_false"), raw.get("on_fail"))
        elif kind == "skill":
            raw["on_success"] = _first(raw.get("on_success"), raw.get("on_true"),
                                       raw.get("next"))
            raw["on_fail"] = _first(raw.get("on_fail"), raw.get("on_false"))
        elif kind == "data":
            raw["next"] = _first(raw.get("next"), raw.get("on_success"),
                                 raw.get("on_true"))
        for field_name in ("next", "on_true", "on_false", "on_success", "on_fail"):
            target = raw.get(field_name)
            if kind == "terminal":
                continue
            if _edge_used(kind, field_name):
                if not target:
                    target = "auto_fail"
                    raw[field_name] = target
                referenced.add(target)

    for target in sorted(referenced - names):
        success = any(token in target.lower() for token in ("done", "success", "ok"))
        nodes.append({"name": target, "kind": "terminal", "success": success})
        names.add(target)

    if spec.get("entry") not in names and nodes:
        spec["entry"] = nodes[0]["name"]
    return spec


def _edge_used(kind: str | None, field_name: str) -> bool:
    return (
        (kind == "data" and field_name == "next")
        or (kind == "check" and field_name in ("on_true", "on_false"))
        or (kind == "skill" and field_name in ("on_success", "on_fail"))
    )


def compile_program(spec: dict) -> tuple[SkillProgram, list[tuple[Any, str, dict]]]:
    """Compile a DSL JSON spec into an executable SkillProgram plus the
    compiled reactive guard list [(pred_fn, skill, args_exprs)]."""
    spec = normalize_spec(spec)
    nodes: dict[str, Any] = {}
    for raw in spec["nodes"]:
        name, kind = raw["name"], raw["kind"]
        if kind == "data":
            bind_name = raw.get("bind_name")
            expr = compile_expr(raw["bind_expr"])

            def fn(ctx: Ctx, _name=bind_name, _expr=expr) -> None:
                ctx.scope[_name] = _expr(ctx)

            nodes[name] = DataOp(name, fn, raw["next"])
        elif kind == "check":
            nodes[name] = CheckOp(
                name, compile_expr(raw["pred"]), raw["on_true"], raw["on_false"]
            )
        elif kind == "skill":
            if raw["skill"] not in SKILL_REGISTRY:
                raise ValueError(f"unknown skill: {raw['skill']}")
            arg_exprs = {
                key: compile_expr(value)
                for key, value in _clean_args(raw.get("args")).items()
            }

            def args_fn(ctx: Ctx, _exprs=arg_exprs) -> dict[str, Any]:
                return {key: expr(ctx) for key, expr in _exprs.items()}

            nodes[name] = SkillOp(
                name, raw["skill"], args_fn, raw["on_success"], raw["on_fail"]
            )
        elif kind == "terminal":
            nodes[name] = TerminalOp(
                name, bool(raw.get("success")),
                lambda ctx: tuple(ctx.scope.get("last_diagnosis", ()) or ()),
            )
        else:
            raise ValueError(f"unknown node kind: {kind}")

    program = SkillProgram(spec["name"], nodes, spec["entry"])
    guards = [
        (compile_expr(g["pred"]), g["skill"], {
            key: compile_expr(value)
            for key, value in _clean_args(g.get("args")).items()
        })
        for g in spec.get("reactive", [])
    ]
    return program, guards


def complexity(spec: dict) -> int:
    """MDL |pi|: nodes + guards + a token-ish cost for every expression."""
    cost = 2 * len(spec.get("nodes", ())) + 2 * len(spec.get("reactive", ()))
    for raw in spec.get("nodes", ()):
        for field in ("pred", "bind_expr"):
            if raw.get(field):
                cost += len(raw[field].split())
        for value in _clean_args(raw.get("args")).values():
            cost += len(str(value).split())
    for guard in spec.get("reactive", ()):
        cost += len(guard.get("pred", "").split())
    return cost


# ---------------------------------------------------------------------------
# Runtime planner for DSL programs
# ---------------------------------------------------------------------------


class DSLPlanner:
    """Planner protocol implementation executing a DSL artifact.

    Includes a runtime reflective-recovery layer: when the program livelocks
    (no world progress for LIVELOCK_STEPS) or keeps terminating without
    finishing the episode, control temporarily falls back to the corrective
    planner until progress resumes — the online analogue of the paper's
    failure -> recovery -> graft loop (the offline graft is reflect.py).
    """

    RESTART_COOLDOWN = 40
    LIVELOCK_STEPS = 150
    RECOVERY_MAX_STEPS = 500
    MAX_RECOVERIES = 1   # then the corrective planner keeps control

    def __init__(self, spec: dict) -> None:
        self.spec = spec
        self.program, self.guards = compile_program(spec)
        self.interp = Interpreter(self.program)
        self.override: Any = None
        self.override_guard: int | None = None
        self.diagnoses: list[Any] = []
        self._restart_at: int | None = None
        self.goal_log: list = []   # debug parity with FallbackPlanner
        self._task_id: str | None = None
        self._recovery: Any = None
        self._recovery_until: int = 0
        self._marker: tuple | None = None
        self._marker_step: int = 0
        self.recoveries: int = 0

    def reset(self, task_id: str | None) -> None:
        self.interp.reset()
        self.override = None
        self.override_guard = None
        self.diagnoses.clear()
        self._restart_at = None
        self._task_id = task_id
        self._recovery = None
        self._recovery_until = 0
        self._marker = None
        self._marker_step = 0
        self.recoveries = 0

    def _progress_marker(self, ctx: Ctx) -> tuple:
        """Monotone progress counters only — room oscillation must NOT reset
        the livelock clock, and genuine advances always change one of these."""
        from ..grounding import schema

        chests_left = 0
        monsters_left = 0
        buttons_pressed = 0
        for room in ctx.memory.rooms.values():
            if room.state is None:
                continue
            chests_left += len(room.state.closed_chests())
            monsters_left += len(room.state.monsters)
            buttons_pressed += len(
                room.state.tiles_of(schema.TILE_BUTTON_PRESSED)
            )
        return (
            ctx.inventory.keys,
            ctx.inventory.gold,
            tuple(sorted(ctx.inventory.tools)),
            len(ctx.memory.rooms),
            chests_left,
            monsters_left,
            buttons_pressed,
        )

    def _start_recovery(self, ctx: Ctx, reason: str) -> int:
        from ..planner import FallbackPlanner

        self.recoveries += 1
        self.diagnoses.append(("livelock", reason))
        self.goal_log.append((ctx.memory.step_count, "recovery_start", reason))
        self._recovery = FallbackPlanner()
        self._recovery.reset(self._task_id)
        self._recovery_until = ctx.memory.step_count + self.RECOVERY_MAX_STEPS
        return self._recovery.step(ctx)

    def _check_livelock(self, ctx: Ctx) -> bool:
        marker = self._progress_marker(ctx)
        if marker != self._marker:
            self._marker = marker
            self._marker_step = ctx.memory.step_count
            return False
        # Under HP pressure (e.g. task_5's periodic drain) stalling is fatal
        # much sooner — hand over aggressively.
        limit = self.LIVELOCK_STEPS if ctx.memory.hp_estimate > 3 else 80
        return ctx.memory.step_count - self._marker_step >= limit

    def step(self, ctx: Ctx) -> int:
        from ..constants import ACTION_NOOP

        # Reflective recovery: hand control to the corrective planner while
        # the program is livelocked; return to the program on progress.
        if self._recovery is not None:
            permanent = self.recoveries >= self.MAX_RECOVERIES
            done = (
                self._marker != self._progress_marker(ctx)
                or ctx.memory.step_count >= self._recovery_until
            )
            if done and not permanent:
                self.goal_log.append(
                    (ctx.memory.step_count, "recovery_end", "")
                )
                self._recovery = None
                self._marker = self._progress_marker(ctx)
                self._marker_step = ctx.memory.step_count
                self.interp.reset()
                self._restart_at = None
                self._last_pc = None
            else:
                return self._recovery.step(ctx)
        elif self._check_livelock(ctx):
            return self._start_recovery(ctx, self.interp.pc)

        # Reactive guards (part of the induced artifact) preempt the graph.
        if self.override is None:
            for index, (pred, skill, arg_exprs) in enumerate(self.guards):
                try:
                    fired = bool(pred(ctx))
                except ExprError:
                    fired = False
                if fired:
                    self.override = ctx.make_skill(skill)
                    self.override.reset(
                        ctx, **{k: e(ctx) for k, e in arg_exprs.items()}
                    )
                    self.override_guard = index
                    break
        if self.override is not None:
            kind, payload = self.override.step(ctx)
            if kind == "act":
                return int(payload)
            self.goal_log.append((ctx.memory.step_count, f"guard:{kind}", payload))
            self.override = None
            self.override_guard = None

        if self.interp.finished is not None:
            if self.interp.finished.success:
                # The program believes it is done but the episode continues:
                # that is a coverage gap, not a reason to idle — hand over to
                # the corrective planner immediately.
                return self._start_recovery(ctx, "terminal_success")
            if self._restart_at is None:
                self._restart_at = ctx.memory.step_count + self.RESTART_COOLDOWN
            if ctx.memory.step_count >= self._restart_at:
                self.interp.reset()
                self._restart_at = None
                self._last_pc = None
                self.goal_log.append((ctx.memory.step_count, "restart", ""))
            else:
                return ACTION_NOOP

        try:
            kind, payload = self.interp.step(ctx)
        except Exception as exc:   # noqa: BLE001 - a bad expression must not
            # crash a live episode; surface it as a program failure.
            from ..graph import Outcome

            self.interp.finished = Outcome(False, ("runtime_error", str(exc)))
            self.diagnoses.append(("program", self.interp.finished.diagnosis))
            return ACTION_NOOP
        if kind == "act":
            if self.interp.pc != getattr(self, "_last_pc", None):
                self.goal_log.append((ctx.memory.step_count, "node", self.interp.pc))
                self._last_pc = self.interp.pc
            return int(payload)
        if not payload.success:
            self.diagnoses.append(("program", payload.diagnosis))
            self.goal_log.append(
                (ctx.memory.step_count, "terminal_fail", payload.diagnosis)
            )
        return ACTION_NOOP


# ---------------------------------------------------------------------------
# Artifact IO
# ---------------------------------------------------------------------------


def artifact_path(task_id: str | None) -> Path:
    if task_id:
        candidate = ARTIFACT_DIR / f"{task_id.replace('/', '_')}.json"
        if candidate.exists():
            return candidate
    return ARTIFACT_DIR / "global_program.json"


def load_artifact_planner(task_id: str | None) -> DSLPlanner | None:
    """Load the induced program for a task, honoring the live-validation
    selection (selection.json) when present. Returning None means "use the
    hand-written corrective planner"."""
    selection_path = ARTIFACT_DIR / "selection.json"
    path: Path | None = None
    if task_id and selection_path.exists():
        selection = json.loads(selection_path.read_text("utf-8"))
        entry = selection.get(task_id)
        if entry is not None:
            if entry.get("planner") == "fallback" or not entry.get("artifact"):
                return None
            path = ARTIFACT_DIR / entry["artifact"]
    if path is None:
        path = artifact_path(task_id)
    if not path.exists():
        return None
    spec = json.loads(path.read_text("utf-8"))
    planner = DSLPlanner(spec)
    planner.reset(task_id)
    return planner


def save_artifact(spec: dict, name: str) -> Path:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    path = ARTIFACT_DIR / f"{name}.json"
    path.write_text(json.dumps(spec, indent=1, ensure_ascii=False), "utf-8")
    return path

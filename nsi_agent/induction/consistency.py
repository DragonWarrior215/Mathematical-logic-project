"""Empirical programmatic consistency (deterministic, no LLM).

Replays a candidate DSL program against recorded traces: at every step the
program receives the recorded symbolic state and must emit the expert's
action. Coverage |R| counts matched steps; after a divergence the program is
re-aligned (fresh instance) so later segments still earn credit — this
approximates the paper's consistency-region size. The induction objective is

    max  sum_traces |R|  -  lambda * |pi|
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from ..constants import ACTION_NOOP, EXIT_DELTA
from ..graph import Ctx
from ..grounding.schema import SymbolicState
from ..memory import InventoryView, Memory
from ..skills import SKILL_REGISTRY
from ..tracker import TrackedMonster, Tracker
from .dsl import DSLPlanner, complexity

LAMBDA = 0.5
MAX_PROGRAM_STALL = 6


@dataclass
class Divergence:
    step: int
    expected: int
    got: int
    coord: tuple[int, int]
    state_text: str
    inv: dict
    node: str | None


@dataclass
class TraceResult:
    trace_name: str
    total: int
    matched: int
    divergences: list[Divergence] = field(default_factory=list)

    @property
    def coverage(self) -> float:
        return self.matched / max(1, self.total)


class ReplayHarness:
    """Feeds recorded observations into a fresh Memory/Tracker pair."""

    def __init__(self, task_id: str | None) -> None:
        self.memory = Memory()
        self.memory.reset(task_id)
        self.tracker = Tracker(self.memory)
        self.tracker.reset()
        self.ctx = Ctx(memory=self.memory, tracker=self.tracker,
                       skills=dict(SKILL_REGISTRY))
        self._coord: tuple[int, int] | None = None

    def observe(self, coord: tuple[int, int], state: SymbolicState,
                inv: dict) -> None:
        if self._coord is not None and coord != self._coord:
            delta = (coord[0] - self._coord[0], coord[1] - self._coord[1])
            direction = next(
                (d for d, v in EXIT_DELTA.items() if v == delta), None
            )
            if direction is not None:
                self.memory.transition(direction)
            else:
                self.memory.current_coord = coord
        self._coord = coord
        self.memory.current_coord = coord
        self.memory.integrate_keyframe(state)
        self.memory.inventory = InventoryView(
            keys=int(inv.get("keys", 0)),
            gold=int(inv.get("gold", 0)),
            items=tuple(inv.get("items", ())),
            tools=tuple(inv.get("tools", ())),
            equipped=dict(inv.get("equipped", {})),
        )
        self.memory.step_count += 1
        self.tracker.player_px = (float(state.player_px[0]), float(state.player_px[1]))
        self.tracker.facing = state.facing
        self.tracker.monsters = [TrackedMonster(m) for m in state.monsters]
        self.tracker.steps_since_sync = 0
        self.tracker.perceive_requested = False
        self.tracker.expect_transition = None
        self.tracker.last_transition_result = None


def replay(spec: dict, trace: dict, *, max_divergences: int = 5) -> TraceResult:
    steps = trace["steps"]
    result = TraceResult(trace_name=trace.get("task_id", "?"), total=len(steps),
                         matched=0)
    harness = ReplayHarness(trace.get("task_id"))
    planner = DSLPlanner(spec)
    planner.reset(trace.get("task_id"))
    stall = 0

    index = 0
    while index < len(steps):
        step = steps[index]
        state = SymbolicState.from_text(step["state"])
        harness.observe(tuple(step["coord"]), state, step["inv"])

        # Room transitions in the recording show up as expect_transition
        # successes for the program's use_exit skill.
        if index + 1 < len(steps) and steps[index + 1]["coord"] != step["coord"]:
            harness.tracker.last_transition_result = "moved"

        error: str | None = None
        try:
            action = planner.step(harness.ctx)
        except Exception as exc:   # noqa: BLE001 - surfaced in the divergence
            action = ACTION_NOOP
            error = f"{type(exc).__name__}: {exc}"
        expected = step["action"]

        if action == expected:
            result.matched += 1
            stall = 0
        elif action == ACTION_NOOP and expected != ACTION_NOOP:
            stall += 1
            if stall > MAX_PROGRAM_STALL:
                _record_divergence(result, planner, step, index, expected,
                                   action, error, max_divergences)
                planner = DSLPlanner(spec)
                planner.reset(trace.get("task_id"))
                stall = 0
        elif expected == ACTION_NOOP:
            pass   # expert idled; neutral
        else:
            _record_divergence(result, planner, step, index, expected,
                               action, error, max_divergences)
            planner = DSLPlanner(spec)
            planner.reset(trace.get("task_id"))
            stall = 0
        index += 1

    return result


def _record_divergence(result: TraceResult, planner: DSLPlanner, step: dict,
                       index: int, expected: int, got: int,
                       error: str | None, max_divergences: int) -> None:
    # Replay continues past the cap (coverage must reflect the whole trace);
    # only the recorded counterexamples are limited.
    if len(result.divergences) >= max_divergences:
        return
    node = planner.interp.pc if planner.interp.finished is None else "finished"
    if error:
        node = f"{node} [{error}]"
    result.divergences.append(Divergence(
        step=index,
        expected=expected,
        got=got,
        coord=tuple(step["coord"]),
        state_text=step["state"],
        inv=step["inv"],
        node=node,
    ))


def score(spec: dict, traces: list[dict]) -> tuple[float, list[TraceResult]]:
    results = [replay(spec, trace) for trace in traces]
    total_matched = sum(r.matched for r in results)
    return total_matched - LAMBDA * complexity(spec), results


def load_traces(root: Path) -> list[dict]:
    return [
        json.loads(path.read_text("utf-8"))
        for path in sorted(root.glob("*.json"))
    ]

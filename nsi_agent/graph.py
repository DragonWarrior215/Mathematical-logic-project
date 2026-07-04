"""NSI-style symbolic execution graphs (the G in a skill triple).

A skill/program is a graph of typed nodes over a shared scope C (variables)
and the symbolic state Z (memory + tracker). Node kinds follow the paper:

- DataOp:      bind/update scope variables from the symbolic state
- CheckOp:     evaluate a predicate, branch (loops = CheckOp with a back edge)
- PrimitiveOp: emit one environment action
- SkillOp:     invoke a sub-skill (temporally extended; runs until it returns)
- TerminalOp:  finish with success/failure plus a symbolic diagnosis term

The interpreter is resumable: each ``step`` advances the graph until exactly
one environment action is produced, or the program terminates. It is fully
deterministic given (program, scope, state) — this is the layer a Lean
formalization can model as a small-step transition semantics.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Protocol

Diagnosis = tuple[Any, ...]


@dataclass(frozen=True)
class Outcome:
    success: bool
    diagnosis: Diagnosis = ()

    def __bool__(self) -> bool:
        return self.success


class Skill(Protocol):
    """Native primitive skill protocol (temporally extended actions)."""

    def reset(self, ctx: "Ctx", **kwargs: Any) -> None: ...

    def step(self, ctx: "Ctx") -> "StepResult": ...


# A skill step yields ("act", action:int) | ("ok", detail) | ("fail", diagnosis)
StepResult = tuple[str, Any]


@dataclass
class Ctx:
    """Execution context shared by all nodes: Z (memory+tracker) and C (scope)."""

    memory: Any
    tracker: Any
    skills: dict[str, Callable[[], Skill]]
    scope: dict[str, Any] = field(default_factory=dict)

    @property
    def state(self):
        return self.memory.state

    @property
    def inventory(self):
        return self.memory.inventory

    def make_skill(self, name: str) -> Skill:
        return self.skills[name]()


# ---------------------------------------------------------------------------
# Node types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DataOp:
    name: str
    fn: Callable[[Ctx], None]
    next: str


@dataclass(frozen=True)
class CheckOp:
    name: str
    pred: Callable[[Ctx], bool]
    on_true: str
    on_false: str


@dataclass(frozen=True)
class PrimitiveOp:
    name: str
    fn: Callable[[Ctx], int]     # returns an env action id
    next: str


@dataclass(frozen=True)
class SkillOp:
    name: str
    skill: str                                  # registered skill name
    args: Callable[[Ctx], dict[str, Any]]       # invocation parameters theta
    on_success: str
    on_fail: str


@dataclass(frozen=True)
class TerminalOp:
    name: str
    success: bool
    diagnosis: Callable[[Ctx], Diagnosis] = lambda ctx: ()


Node = DataOp | CheckOp | PrimitiveOp | SkillOp | TerminalOp


@dataclass(frozen=True)
class SkillProgram:
    name: str
    nodes: dict[str, Node]
    entry: str

    def __post_init__(self) -> None:
        targets = {self.entry}
        for node in self.nodes.values():
            if isinstance(node, DataOp | PrimitiveOp):
                targets.add(node.next)
            elif isinstance(node, CheckOp):
                targets.update((node.on_true, node.on_false))
            elif isinstance(node, SkillOp):
                targets.update((node.on_success, node.on_fail))
        missing = targets - set(self.nodes)
        if missing:
            raise ValueError(f"program '{self.name}' references unknown nodes: {missing}")

    def complexity(self) -> int:
        """MDL-style program size |pi| used by the induction objective."""
        return len(self.nodes)


# Guard against non-productive cycles (a graph that never emits an action).
MAX_TRANSITIONS_PER_STEP = 256


class Interpreter:
    """Resumable executor: one env action per ``step`` call."""

    def __init__(self, program: SkillProgram) -> None:
        self.program = program
        self.pc: str = program.entry
        self.active_skill: Skill | None = None
        self.finished: Outcome | None = None

    def step(self, ctx: Ctx) -> tuple[str, Any]:
        """Returns ("act", action) or ("done", Outcome)."""
        if self.finished is not None:
            return ("done", self.finished)

        for _ in range(MAX_TRANSITIONS_PER_STEP):
            node = self.program.nodes[self.pc]

            if isinstance(node, DataOp):
                node.fn(ctx)
                self.pc = node.next
                continue

            if isinstance(node, CheckOp):
                self.pc = node.on_true if node.pred(ctx) else node.on_false
                continue

            if isinstance(node, PrimitiveOp):
                action = int(node.fn(ctx))
                self.pc = node.next
                return ("act", action)

            if isinstance(node, SkillOp):
                if self.active_skill is None:
                    self.active_skill = ctx.make_skill(node.skill)
                    self.active_skill.reset(ctx, **node.args(ctx))
                kind, payload = self.active_skill.step(ctx)
                if kind == "act":
                    return ("act", int(payload))
                self.active_skill = None
                ctx.scope["last_outcome"] = payload
                if kind == "ok":
                    self.pc = node.on_success
                else:
                    ctx.scope["last_diagnosis"] = payload
                    self.pc = node.on_fail
                continue

            if isinstance(node, TerminalOp):
                self.finished = Outcome(node.success, node.diagnosis(ctx))
                return ("done", self.finished)

            raise TypeError(f"unknown node type at '{self.pc}': {node!r}")

        self.finished = Outcome(False, ("nonproductive_loop", self.pc))
        return ("done", self.finished)

    def reset(self) -> None:
        self.pc = self.program.entry
        self.active_skill = None
        self.finished = None

"""Policy entry point (Perceive -> Think -> Act).

Inference-time inputs, per assignment rules:
- ``obs``  — the pixel frame (sole source of world predicates, via the VLM)
- ``info["inventory"]`` — explicitly provided by the evaluation interface
- ``task_id`` — passed by the evaluator to ``reset``; used only as a hint
  for exploration ordering

Nothing else in ``info`` is read on the inference path. The Oracle backend
(which reads engine internals) exists strictly for training-time debugging
and is refused unless explicitly enabled.

Evaluator usage:
    python utils/evaluate_policy.py --policy nsi_agent.agent:make_policy ...
"""

from __future__ import annotations

import os
from typing import Any, Protocol

import numpy as np

from .graph import Ctx
from .grounding.schema import SymbolicState
from .memory import Memory
from .planner import load_planner
from .skills import SKILL_REGISTRY
from .tracker import Tracker


class GroundingBackend(Protocol):
    def ground(self, obs: np.ndarray) -> SymbolicState: ...


class VLMGrounding:
    """Qwen2.5-VL grounding; heavy imports deferred until first use."""

    def __init__(self) -> None:
        self._model = None

    def ground(self, obs: np.ndarray) -> SymbolicState:
        if self._model is None:
            from .grounding.vlm import VLMGroundingModel

            self._model = VLMGroundingModel.load_default()
        return self._model.ground(obs)


class OracleGrounding:
    """DEBUG/TRAINING ONLY: perfect grounding from engine internals."""

    def __init__(self, env: Any) -> None:
        self.env = env

    def ground(self, obs: np.ndarray) -> SymbolicState:
        from .grounding.oracle import oracle_state

        return oracle_state(self.env)


class Policy:
    def __init__(
        self,
        backend: GroundingBackend | None = None,
        *,
        prefer_induced: bool = True,
    ) -> None:
        self.backend: GroundingBackend = backend or VLMGrounding()
        self.prefer_induced = prefer_induced
        self.memory = Memory()
        self.tracker = Tracker(self.memory)
        self._ground_backoff = 0
        self.planner = load_planner(None, prefer_induced=prefer_induced)
        self.ctx = Ctx(
            memory=self.memory,
            tracker=self.tracker,
            skills=dict(SKILL_REGISTRY),
        )

    def reset(self, seed: int | None = None, task_id: str | None = None) -> None:
        del seed  # the policy is deterministic
        self.memory.reset(task_id)
        self.tracker.reset()
        self._ground_backoff = 0
        self.planner = load_planner(task_id, prefer_induced=self.prefer_induced)
        self.ctx.scope.clear()

    def act(self, obs: np.ndarray, info: dict[str, Any]) -> int:
        self.memory.on_step(info)                 # inventory view only
        if self._blocked_by_reward(info):         # reward-as-feedback (allowed)
            self.tracker.note_blocked_feedback()

        if self.tracker.should_perceive() and self._ground_backoff <= 0:
            state = None
            try:
                state = self.backend.ground(obs)  # phi: pixels -> predicates
            except Exception:                     # noqa: BLE001 - a grounding
                # hiccup must never crash the episode: keep dead-reckoning
                # and retry after a short backoff (the frame will have
                # changed by then, which usually resolves the failure).
                self._ground_backoff = 3
            if state is not None:
                self.tracker.sync(state)          # reconcile with prediction
        elif self._ground_backoff > 0:
            self._ground_backoff -= 1

        try:
            action = self.planner.step(self.ctx)  # G: symbolic execution
        except Exception:                         # noqa: BLE001 - last-resort
            action = 0                            # guard for the evaluator
        self.tracker.apply_action(action)         # formal transition model
        return int(action)

    @staticmethod
    def _blocked_by_reward(info: dict[str, Any]) -> bool:
        """Detect a wall bump from the last step's reward value alone.

        The assignment allows the env reward as a historical feedback signal.
        A blocked move earns the invalid-action penalty on top of the step
        penalty, which is distinguishable from a normal step's reward.
        """
        reward = info.get("reward", {}) if isinstance(info, dict) else {}
        signals = reward.get("reward_signals") or {}
        weights = reward.get("reward_weights") or {}
        if not signals or "invalid_action" not in weights:
            return False
        scalar = 0.0
        for name, value in signals.items():
            if isinstance(value, (int, float)) and isinstance(
                weights.get(name, 0.0), (int, float)
            ):
                scalar += float(weights.get(name, 0.0)) * float(value)
        expected_blocked = float(weights.get("step", 0.0)) + float(
            weights.get("invalid_action", 0.0)
        )
        return abs(scalar - expected_blocked) < 1e-6


def make_policy() -> Policy:
    if os.environ.get("NSI_BACKEND", "vlm") == "oracle":
        raise RuntimeError(
            "OracleGrounding needs an env handle and is debug-only; "
            "use nsi_agent.debug_run for oracle rollouts."
        )
    return Policy()

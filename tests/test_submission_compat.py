from types import SimpleNamespace

import numpy as np

import nsi_agent.agent as agent_module
from nsi_agent.agent import Policy


class _Memory:
    task_id = None

    def reset(self, task_id=None):
        self.task_id = task_id

    def on_step(self, info):
        self.last_info = info


class _Tracker:
    def reset(self):
        self.reset_called = True

    def should_perceive(self):
        return False

    def apply_action(self, action):
        self.last_action = action

    def note_blocked_feedback(self):
        self.blocked = True


class _Planner:
    def step(self, ctx):
        return 0


def test_policy_binds_task_from_official_safe_info(monkeypatch):
    policy = object.__new__(Policy)
    policy.memory = _Memory()
    policy.tracker = _Tracker()
    policy.ctx = SimpleNamespace(scope={"stale": True})
    policy.planner = _Planner()
    policy.prefer_induced = True
    policy._ground_backoff = 1

    loaded = []

    def fake_load_planner(task_id, *, prefer_induced):
        loaded.append((task_id, prefer_induced))
        return _Planner()

    monkeypatch.setattr(agent_module, "load_planner", fake_load_planner)

    action = policy.act(
        np.zeros((128, 160, 3), dtype=np.uint8),
        {
            "task_id": "mathematical_logic/task_5",
            "last_reward": 0.0,
            "inventory": {},
        },
    )

    assert action == 0
    assert policy.memory.task_id == "mathematical_logic/task_5"
    assert loaded == [("mathematical_logic/task_5", True)]
    assert policy.ctx.scope == {}


def test_blocked_move_uses_official_scalar_reward():
    assert Policy._blocked_by_reward({"last_reward": -0.06})
    assert not Policy._blocked_by_reward({"last_reward": -0.01})
    assert not Policy._blocked_by_reward({"last_reward": -2.01})

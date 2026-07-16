"""Evaluation entry point.

    python utils/evaluate_policy.py --policy submission_agent.py --tasks ...

Inference inputs: pixel frames (obs), the scalar ``last_reward``, the inventory
provided by the evaluation interface, and ``task_id`` supplied by an explicit
``--task-policy`` binding. No other ``info`` fields are read on the inference
path.
"""

from nsi_agent.agent import Policy, make_policy  # noqa: F401

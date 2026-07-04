"""Evaluation entry point.

    python utils/evaluate_policy.py --policy submission_agent.py --tasks ...

Inference inputs: pixel frames (obs), the env reward as historical feedback,
the inventory provided by the evaluation interface, and the task_id passed to
``reset``. No other ``info`` fields are read on the inference path.
"""

from nsi_agent.agent import Policy, make_policy  # noqa: F401

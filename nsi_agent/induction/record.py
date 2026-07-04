"""Record demonstration traces from the fallback planner (training time).

Each trace step stores the full symbolic observation (oracle, per-step), the
inventory view, the executed action, and the active goal annotation — enough
for the deterministic replay in ``consistency.py`` and for building compact
trace summaries for GPT-4o.

    python -m nsi_agent.induction.record --out nsi_agent/induction/traces
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from nesylink.env import make_env

from ..agent import OracleGrounding, Policy

TASKS = tuple(f"mathematical_logic/task_{i}" for i in range(1, 6))


def record_episode(task_id: str, seed: int) -> dict:
    env = make_env(task_id=task_id, observation_mode="pixels")
    policy = Policy(backend=OracleGrounding(env), prefer_induced=False)
    policy.reset(seed=seed, task_id=task_id)

    obs, info = env.reset(seed=seed)
    steps = []
    terminated = truncated = False
    try:
        while not (terminated or truncated):
            # Capture the exact pre-action state externally, WITHOUT touching
            # the policy's own keyframe schedule (recording must not perturb
            # the demonstrated behavior).
            from ..grounding.oracle import oracle_state

            pre_state = oracle_state(env)
            action = policy.act(obs, info)
            goal = policy.planner.current
            obs, _, terminated, truncated, info = env.step(action)
            events = [
                record.get("name")
                for record in info.get("events", {}).get("records", [])
                if record.get("name")
            ]
            inv = info.get("inventory", {})
            steps.append({
                "coord": list(policy.memory.current_coord),
                "state": pre_state.to_text(),
                "inv": {
                    "keys": int(inv.get("keys", 0)),
                    "gold": int(inv.get("gold", 0)),
                    "items": list(inv.get("items", [])),
                    "tools": list(inv.get("tools", [])),
                    "equipped": dict(inv.get("equipped", {})),
                },
                "action": int(action),
                "goal": [goal.skill, _plain(goal.args)] if goal else None,
                "events": events,
            })
    finally:
        env.close()

    success = bool(
        info.get("game", {}).get("world_completed")
        or info.get("terminal_reason") == "world_completed"
    )
    return {"task_id": task_id, "seed": seed, "success": success, "steps": steps}


def _plain(args: dict) -> dict:
    return {
        key: list(value) if isinstance(value, tuple) else value
        for key, value in args.items()
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parent / "traces")
    parser.add_argument("--tasks", nargs="+", default=list(TASKS))
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)
    for task_id in args.tasks:
        trace = record_episode(task_id, args.seed)
        name = task_id.replace("/", "_") + ".json"
        (args.out / name).write_text(json.dumps(trace), "utf-8")
        print(f"{task_id}: success={trace['success']} steps={len(trace['steps'])}"
              f" -> {args.out / name}")


if __name__ == "__main__":
    main()

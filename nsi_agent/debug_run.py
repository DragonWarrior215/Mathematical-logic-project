"""Oracle-backend rollouts for symbolic-layer debugging (training-time only).

    .venv/bin/python -m nsi_agent.debug_run --tasks mathematical_logic/task_1 \
        --episodes 3 [--fallback] [--trace]
"""

from __future__ import annotations

import argparse
import json
from collections import Counter

from nesylink.env import make_env

from .agent import OracleGrounding, Policy


def run_episode(task_id: str, seed: int, *, prefer_induced: bool, trace: bool,
                backend: str = "oracle") -> dict:
    env = make_env(task_id=task_id, observation_mode="pixels")
    if backend == "oracle":
        grounding = OracleGrounding(env)
    else:
        from .agent import VLMGrounding

        grounding = VLMGrounding()
    policy = Policy(backend=grounding, prefer_induced=prefer_induced)
    policy.reset(seed=seed, task_id=task_id)

    obs, info = env.reset(seed=seed)
    events: Counter[str] = Counter()
    total_reward = 0.0
    steps = 0
    terminated = truncated = False
    try:
        while not (terminated or truncated):
            action = policy.act(obs, info)
            obs, reward, terminated, truncated, info = env.step(action)
            steps += 1
            total_reward += float(reward)
            for record in info.get("events", {}).get("records", []):
                name = record.get("name")
                if name:
                    events[name] += 1
            if trace and steps % 100 == 0:
                print(
                    f"  step={steps} tile={info['agent']['tile']} "
                    f"room={info['env']['room_id']} hp={info['agent']['hp']} "
                    f"keys={info['inventory']['keys']} goal={getattr(policy.planner, 'current', None)}"
                )
    finally:
        env.close()

    success = bool(
        info.get("game", {}).get("world_completed")
        or info.get("terminal_reason") == "world_completed"
    )
    return {
        "task_id": task_id,
        "seed": seed,
        "steps": steps,
        "reward": round(total_reward, 3),
        "success": success,
        "terminal_reason": info.get("terminal_reason"),
        "events": dict(sorted(events.items())),
        "diagnoses": [
            (list(k), repr(d)) for k, d in getattr(policy.planner, "diagnoses", [])
        ][-8:],
        "goal_log": [
            (step, kind, repr(key))
            for step, kind, key in getattr(policy.planner, "goal_log", [])
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tasks", nargs="+", default=[
        f"mathematical_logic/task_{i}" for i in range(1, 6)
    ])
    parser.add_argument("--episodes", type=int, default=1)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--fallback", action="store_true",
                        help="force the hand-written planner (skip induced artifacts)")
    parser.add_argument("--backend", choices=["oracle", "vlm"], default="oracle")
    parser.add_argument("--trace", action="store_true")
    args = parser.parse_args()

    summary = {}
    for task_id in args.tasks:
        results = []
        for episode in range(args.episodes):
            result = run_episode(
                task_id,
                args.seed + episode,
                prefer_induced=not args.fallback,
                trace=args.trace,
                backend=args.backend,
            )
            results.append(result)
            print(json.dumps({k: v for k, v in result.items() if k not in ("events", "goal_log")},
                             ensure_ascii=False))
            if not result["success"]:
                print("  events:", result["events"])
                for entry in result.get("goal_log", [])[-40:]:
                    print("   ", entry)
        summary[task_id] = sum(r["success"] for r in results) / len(results)
    print("\nsuccess rates:", json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

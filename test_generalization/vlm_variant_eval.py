"""Pixel-level generalization diagnostics (VLM grounding, GPU required).

Runs the same map variants as ``test_script.py`` but with the real
submission-form perception stack (Qwen2.5-VL grounding) instead of the
oracle. Comparing the two reports separates planner robustness failures
from visual grounding failures.

    NSI_VLM_MODEL=/root/autodl-tmp/models/grounding_merged_v3b \
        python test_generalization/vlm_variant_eval.py --out outputs/generalization_vlm
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import asdict
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
for entry in (str(PROJECT_ROOT), str(PROJECT_ROOT / "test_generalization")):
    if entry not in sys.path:
        sys.path.insert(0, entry)

from nesylink.env import make_env

from nsi_agent.agent import Policy

from test_script import EvalResult, event_names, variant_specs, write_json


def run_variant_vlm(policy: Policy, spec, map_path: Path, seed: int,
                    max_steps: int | None) -> EvalResult:
    env = make_env(
        task_id=spec.task_id,
        map_path=map_path,
        observation_mode="pixels",
        max_steps=max_steps,
    )
    policy.reset(seed=seed, task_id=spec.task_id)
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
            events.update(event_names(info))
    finally:
        env.close()

    success = bool(
        info.get("game", {}).get("world_completed")
        or info.get("terminal_reason") == "world_completed"
    )
    return EvalResult(
        variant=spec.name,
        task_id=spec.task_id,
        category=spec.category,
        description=spec.description,
        planner="vlm",
        seed=seed,
        success=success,
        steps=steps,
        reward=round(total_reward, 3),
        terminal_reason=info.get("terminal_reason"),
        event_counts=dict(sorted(events.items())),
        diagnoses=[
            (list(key), repr(detail))
            for key, detail in getattr(policy.planner, "diagnoses", [])
        ][-8:],
        map_path=str(map_path),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path,
                        default=PROJECT_ROOT / "outputs" / "generalization_vlm")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-steps", type=int, default=None)
    parser.add_argument("--variant-prefix", default=None,
                        help="Only run variants whose names start with this prefix.")
    args = parser.parse_args()

    variants_dir = args.out / "variant_maps"
    variants_dir.mkdir(parents=True, exist_ok=True)

    specs = variant_specs()
    if args.variant_prefix:
        specs = [spec for spec in specs if spec.name.startswith(args.variant_prefix)]
        if not specs:
            raise SystemExit(f"no variants matched prefix: {args.variant_prefix}")

    policy = Policy()  # VLM backend: the model is loaded once and reused.
    results: list[EvalResult] = []
    for spec in specs:
        map_path = spec.builder(variants_dir)
        result = run_variant_vlm(policy, spec, map_path, args.seed, args.max_steps)
        results.append(result)
        print(json.dumps(asdict(result), ensure_ascii=False), flush=True)

    episodes = len(results)
    successes = sum(row.success for row in results)
    summary = {
        "episodes": episodes,
        "success_rate": successes / episodes if episodes else 0.0,
        "avg_steps": sum(row.steps for row in results) / episodes if episodes else 0.0,
        "failures": [row.variant for row in results if not row.success],
    }
    write_json(args.out / "vlm_generalization_results.json", {
        "summary": summary,
        "results": [asdict(row) for row in results],
    })
    print(json.dumps(summary, ensure_ascii=False))
    print(f"wrote {args.out / 'vlm_generalization_results.json'}")


if __name__ == "__main__":
    main()

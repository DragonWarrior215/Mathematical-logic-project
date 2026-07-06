"""Reflective planning (development-time online evolution).

Runs the induced program in the real environment; when an episode fails, the
terminal diagnosis plus the trailing decision context are handed to GPT-4o,
which grafts a recovery branch onto the artifact. The patch is kept only if
(a) consistency coverage on the demonstration traces does not drop and
(b) the previously failing task now succeeds in a live oracle-backend run.

    python -m nsi_agent.induction.reflect --task mathematical_logic/task_4
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from nesylink.env import make_env

from ..agent import OracleGrounding, Policy
from .consistency import load_traces, score
from .dsl import (
    PROGRAM_JSON_SCHEMA,
    artifact_path,
    compile_program,
    save_artifact,
)
from .llm import structured_completion
from .synthesize import DSL_GUIDE

REFLECT_PROMPT = """The program below failed a live episode. Graft a recovery
branch onto it (keep working parts intact; extend failure edges / add guards
or checks). The failure diagnosis and recent decisions are given.

# Program
{program}

# Live failure
task: {task_id}
terminal_reason: {terminal_reason} (None = ran out of steps / too slow)
program diagnoses: {diagnoses}
last events: {events}
recent decisions (watch for loops!):
{decision_log}

Output the full corrected program.
"""


def run_live(task_id: str, spec: dict | None, seed: int = 0,
             map_path: Path | None = None) -> dict:
    env = make_env(task_id=task_id, observation_mode="pixels", map_path=map_path)
    policy = Policy(backend=OracleGrounding(env), prefer_induced=False)
    policy.reset(seed=seed, task_id=task_id)
    if spec is not None:
        from .dsl import DSLPlanner

        policy.planner = DSLPlanner(spec)
        policy.planner.reset(task_id)
    obs, info = env.reset(seed=seed)
    terminated = truncated = False
    events: list[str] = []
    try:
        while not (terminated or truncated):
            action = policy.act(obs, info)
            obs, _, terminated, truncated, info = env.step(action)
            for record in info.get("events", {}).get("records", []):
                name = record.get("name")
                if name and not name.startswith("move_") and name != "noop":
                    events.append(name)
    finally:
        env.close()
    return {
        "success": bool(info.get("game", {}).get("world_completed")
                        or info.get("terminal_reason") == "world_completed"),
        "terminal_reason": info.get("terminal_reason"),
        "events": events[-25:],
        "diagnoses": [repr(d) for d in getattr(policy.planner, "diagnoses", [])][-6:],
        "decision_log": [
            f"step {step}: {kind} {payload}"
            for step, kind, payload in getattr(policy.planner, "goal_log", [])[-30:]
        ],
    }


def reflect_once(task_id: str, traces_dir: Path, *, seed: int = 0,
                 map_path: Path | None = None) -> bool:
    path = artifact_path(task_id)
    spec = json.loads(path.read_text("utf-8"))
    outcome = run_live(task_id, spec, seed=seed, map_path=map_path)
    print(f"live run on {task_id}: {outcome['success']} "
          f"({outcome['terminal_reason']})")
    if outcome["success"]:
        return True

    traces = load_traces(traces_dir)
    baseline, _ = score(spec, traces)
    prompt = REFLECT_PROMPT.format(
        program=json.dumps(spec, ensure_ascii=False),
        task_id=task_id,
        terminal_reason=outcome["terminal_reason"],
        diagnoses=outcome["diagnoses"],
        events=outcome["events"],
        decision_log="\n".join(outcome["decision_log"]),
    )
    for attempt in range(3):
        candidate = structured_completion(DSL_GUIDE, prompt, PROGRAM_JSON_SCHEMA,
                                          temperature=0.2 * attempt)
        try:
            compile_program(candidate)
        except Exception as exc:   # noqa: BLE001
            prompt += f"\n\nThat failed to compile: {exc}"
            continue
        value, _ = score(candidate, traces)
        if value < baseline - 25:
            prompt += "\n\nRejected: the patch broke demonstration consistency."
            continue
        retry = run_live(task_id, candidate, seed=seed, map_path=map_path)
        print(f"  patched attempt {attempt}: live={retry['success']} "
              f"consistency {value:.1f} (baseline {baseline:.1f})")
        if retry["success"]:
            if map_path is not None:
                # Variant-driven evolution must not regress the canonical
                # task: re-validate the patch on the base map too.
                base = run_live(task_id, candidate, seed=seed)
                if not base["success"]:
                    prompt += (
                        "\n\nRejected: the patch passed the variant but broke "
                        f"the base task ({base['terminal_reason']})."
                    )
                    continue
            save_artifact(candidate, path.stem)
            print(f"  grafted recovery branch into {path}")
            return True
        prompt += (
            f"\n\nThe patch still failed live: {retry['terminal_reason']}, "
            f"diagnoses {retry['diagnoses']}. Try a different recovery."
        )
    return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--task", required=True)
    parser.add_argument("--traces", type=Path,
                        default=Path(__file__).resolve().parent / "traces")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--map-path", type=Path, default=None,
                        help="Optional variant map: evolve against this map "
                             "while keeping base-task and trace consistency.")
    args = parser.parse_args()
    reflect_once(args.task, args.traces, seed=args.seed, map_path=args.map_path)


if __name__ == "__main__":
    main()

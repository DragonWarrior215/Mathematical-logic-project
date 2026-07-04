"""Per-task artifact selection by live validation (training time).

Runs each candidate global program — per-task local expert, consolidated
global program, hand-written corrective planner — live on every task and
records the winner in ``artifacts/selection.json``. The runtime loader obeys
this file, so the shipped configuration is exactly what validation approved.

    python -m nsi_agent.induction.select
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .dsl import ARTIFACT_DIR
from .reflect import run_live

TASKS = tuple(f"mathematical_logic/task_{i}" for i in range(1, 6))


def candidates_for(task_id: str) -> list[tuple[str, Path | None]]:
    per_task = ARTIFACT_DIR / f"{task_id.replace('/', '_')}.json"
    global_path = ARTIFACT_DIR / "global_program.json"
    out: list[tuple[str, Path | None]] = []
    if per_task.exists():
        out.append(("local", per_task))
    if global_path.exists():
        out.append(("global", global_path))
    out.append(("fallback", None))
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    selection: dict[str, dict] = {}
    for task_id in TASKS:
        chosen = None
        for name, path in candidates_for(task_id):
            spec = json.loads(path.read_text("utf-8")) if path else None
            outcome = run_live(task_id, spec, seed=args.seed)
            print(f"{task_id} [{name}]: success={outcome['success']} "
                  f"({outcome['terminal_reason']})")
            if outcome["success"]:
                chosen = {"planner": name,
                          "artifact": path.name if path else None}
                break
        if chosen is None:
            chosen = {"planner": "fallback", "artifact": None}
            print(f"{task_id}: NO candidate succeeded; defaulting to fallback")
        selection[task_id] = chosen

    out_path = ARTIFACT_DIR / "selection.json"
    out_path.write_text(json.dumps(selection, indent=1), "utf-8")
    print(f"\nwrote {out_path}:")
    print(json.dumps(selection, indent=1))


if __name__ == "__main__":
    main()

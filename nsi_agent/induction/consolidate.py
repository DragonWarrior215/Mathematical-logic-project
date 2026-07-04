"""Stage 2: inter-trajectory skill consolidation.

Greedily merges local expert programs into one global skill. Each round
GPT-4o consolidates the current global program with the *hardest* local
expert (lowest coverage) using the paper's operators — conditional
branching, modular crossover, variable lifting, loop folding. A candidate is
accepted only if total consistency coverage strictly increases without
regressing any already-covered trace.

    python -m nsi_agent.induction.consolidate --traces nsi_agent/induction/traces
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .consistency import load_traces, score
from .dsl import (
    ARTIFACT_DIR,
    PROGRAM_JSON_SCHEMA,
    compile_program,
    complexity,
    save_artifact,
)
from .llm import structured_completion
from .synthesize import DSL_GUIDE, divergence_feedback, summarize_trace

CONSOLIDATION_PROMPT = """Merge two agent programs into ONE general program.

Apply these operators where useful:
- Conditional branching: introduce discriminative predicates so divergent
  behaviors coexist (e.g. branch on exit_state(...), inv.keys, chests('key')).
- Modular crossover: transfer useful subgraphs from the specialist, rebinding
  arguments through data nodes / state queries.
- Variable lifting: replace instance-specific constants with state queries
  (nearest(closed_chests()), exit directions chosen by exit_state checks).
- Loop folding: collapse repeated patterns into check-loop structures.

The merged program must reproduce BOTH demonstrated behaviors, decided by
observable state predicates, not by task names or step counts.

# Current global program
{global_program}

# Specialist program for the trace it fails on
{local_program}

# Trace the global program currently fails
{trace_summary}

# Where the global program diverges
{divergences}

Output the full merged program.
"""


def consolidate(traces_dir: Path, *, rounds_per_merge: int = 3) -> None:
    traces = load_traces(traces_dir)
    locals_: dict[str, dict] = {}
    for trace in traces:
        name = "local_" + trace["task_id"].replace("/", "_")
        path = ARTIFACT_DIR / f"{name}.json"
        if path.exists():
            locals_[trace["task_id"]] = json.loads(path.read_text("utf-8"))
    if not locals_:
        raise SystemExit("no local expert artifacts found — run synthesize first")

    # Initialize with the local expert that covers the most steps overall.
    best_task, best_spec, best_score, best_results = None, None, None, None
    for task_id, spec in locals_.items():
        value, results = score(spec, traces)
        print(f"local {task_id}: objective {value:.1f} "
              f"({[f'{r.coverage:.2f}' for r in results]})")
        if best_score is None or value > best_score:
            best_task, best_spec, best_score, best_results = (
                task_id, spec, value, results
            )
    print(f"\nglobal init from {best_task} (objective {best_score:.1f})")

    improved = True
    while improved:
        improved = False
        hardest = min(best_results, key=lambda r: r.coverage)
        if hardest.coverage > 0.97:
            break
        hard_trace = next(t for t in traces if t["task_id"] == hardest.trace_name)
        local_spec = locals_.get(hardest.trace_name)
        if local_spec is None:
            break
        print(f"\nmerging against hardest trace {hardest.trace_name} "
              f"(coverage {hardest.coverage:.2f})")

        prompt = CONSOLIDATION_PROMPT.format(
            global_program=json.dumps(best_spec, ensure_ascii=False),
            local_program=json.dumps(local_spec, ensure_ascii=False),
            trace_summary=summarize_trace(hard_trace, max_segments=40),
            divergences=divergence_feedback(hardest),
        )
        feedback = ""
        for round_index in range(rounds_per_merge):
            spec = structured_completion(
                DSL_GUIDE, prompt + feedback, PROGRAM_JSON_SCHEMA,
                temperature=0.0 if round_index == 0 else 0.3,
            )
            try:
                compile_program(spec)
            except Exception as exc:   # noqa: BLE001
                feedback = f"\n\nYour last merge failed to compile: {exc}. Fix it."
                continue
            value, results = score(spec, traces)
            regression = any(
                new.matched < old.matched - 10
                for new, old in zip(results, best_results)
            )
            print(f"  candidate round {round_index}: objective {value:.1f} "
                  f"({[f'{r.coverage:.2f}' for r in results]}) "
                  f"|pi|={complexity(spec)} regression={regression}")
            if value > best_score and not regression:
                best_spec, best_score, best_results = spec, value, results
                improved = True
                break
            feedback = (
                "\n\nThe merge was rejected: it must strictly increase total "
                "coverage without regressing other traces.\n"
                + "\n".join(divergence_feedback(r) for r in results
                            if r.divergences)[:3000]
            )

    path = save_artifact(best_spec, "global_program")
    print(f"\nsaved global program to {path} (objective {best_score:.1f})")
    for result in best_results:
        print(f"  {result.trace_name}: coverage {result.coverage:.3f}")
        # Tasks the global program does not fully cover keep their specialist.
        if result.coverage < 0.9 and result.trace_name in locals_:
            save_artifact(locals_[result.trace_name],
                          result.trace_name.replace("/", "_"))
            print(f"    kept specialist artifact for {result.trace_name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--traces", type=Path,
                        default=Path(__file__).resolve().parent / "traces")
    parser.add_argument("--rounds-per-merge", type=int, default=3)
    args = parser.parse_args()
    consolidate(args.traces, rounds_per_merge=args.rounds_per_merge)


if __name__ == "__main__":
    main()

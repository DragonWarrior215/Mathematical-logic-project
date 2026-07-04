"""Stage 1: intra-trajectory logic consolidation.

For each demonstration trace, GPT-4o synthesizes a local expert DSL program;
the deterministic consistency checker finds the first uncovered state
(divergence), which is fed back for iterative refinement — the paper's
"scan for uncovered states -> introduce conditional branches" loop.

    python -m nsi_agent.induction.synthesize \
        --traces nsi_agent/induction/traces --rounds 4
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from ..constants import ACTION_NAMES
from .consistency import TraceResult, load_traces, replay
from .dsl import PROGRAM_JSON_SCHEMA, compile_program, complexity, save_artifact
from .llm import structured_completion

DSL_GUIDE = """You write control programs for a dungeon-game agent in a JSON DSL.

# Program = {"name", "entry", "reactive": [...], "nodes": [...]}
Node kinds (every node object must include ALL fields; set unused ones null):
- data:    {"name","kind":"data","bind_name":"x","bind_expr":<expr>,"next":<node>}
- check:   {"name","kind":"check","pred":<expr>,"on_true":<node>,"on_false":<node>}
- skill:   {"name","kind":"skill","skill":<skill>,"args":{"target":<expr|null>,"direction":<expr|null>},"on_success":<node>,"on_fail":<node>}
- terminal:{"name","kind":"terminal","success":true|false}
Loops are check nodes with back edges. "reactive" guards
[{"pred":<expr>,"skill":...,"args":{...}}] preempt the graph every step while
true (use for combat interrupts).

# Skills (temporally extended; they navigate + act until done)
- open_chest {target: (x,y) chest tile}    - press_button {target: (x,y)}
- toggle_switch {target: (x,y) lever}      - use_exit {direction: 'north'|'south'|'west'|'east'}
- kill_monster {}  (fights the nearest monster; needs sword)
- goto {target: (x,y)}                     - wait {}

# Expressions: a restricted Python subset. Namespace:
inv.keys inv.gold inv.has_sword inv.has_shield     (inventory)
closed_chests() -> [(x,y)]     chests('key'|'gold'|'heal'|'item') -> [(x,y)]
monster_count()                threatened() -> bool (monster within 1.9 tiles)
nearest(tiles) -> (x,y)|None   reachable(tile) -> bool
exit_state('north'|...) -> '-'|'normal'|'locked'|'conditional'|'open'
visited('north'|...) -> bool   room_known('north'|...) -> bool
hop_toward('locked_exit'|'chest'|'switch'|'unexplored') -> direction|None
  (first exit direction on the known-room-graph path toward the nearest room
   with a locked exit / a closed chest / a lever / an unexplored neighbor;
   None if the CURRENT room already qualifies or nothing is known. THE tool
   for multi-room tasks: e.g. carry a key back with
   use_exit(hop_toward('locked_exit')), explore with hop_toward('unexplored'))
buttons() -> unpressed [(x,y)] buttons(True) -> pressed    switches() -> [(x,y)]
player_tile() room_coord() step_count() len() abs() min() max() var.<name>
String literals need quotes inside the expression: "'north'".

# Rules
- Edge fields by kind: check uses on_true/on_false; skill uses
  on_success/on_fail; data uses next. "entry" must name an existing node.
- Generalize: branch on state predicates (inv.keys == 0, monster_count() > 0,
  exit_state('east') == 'locked', reachable(...)), never on step counts.
- Prefer state queries (nearest(closed_chests())) over coordinate literals.
- The program is re-entered after skill failures via on_fail edges: route
  them to recovery logic (e.g. toggle a switch, then retry) or a terminal.
- Keep it small: at most ~18 nodes; fewest that reproduce the decisions.
- A "finished" program stops acting — make sure loops route back (e.g. after
  opening a chest, re-check what is still needed) instead of terminating
  while the task is unfinished.
"""


def summarize_trace(trace: dict, *, max_segments: int = 60) -> str:
    """Compress a trace into goal segments for the prompt."""
    steps = trace["steps"]
    segments = []
    current = None
    for index, step in enumerate(steps):
        goal = tuple(step["goal"][0:1]) + (json.dumps(step["goal"][1]),) \
            if step.get("goal") else ("idle", "{}")
        if current is None or goal != current["goal"]:
            if current is not None:
                segments.append(current)
            current = {"goal": goal, "start": index, "coord": step["coord"],
                       "inv": step["inv"], "events": []}
        for event in step.get("events", []):
            if event not in ("noop",) and not event.startswith("move_"):
                current["events"].append(event)
    if current is not None:
        segments.append(current)

    lines = [
        f"task: {trace['task_id']}   success: {trace['success']}   "
        f"steps: {len(steps)}",
        f"initial room state:\n{steps[0]['state']}",
        "",
        "decision segments (skill invocations by the expert):",
    ]
    for seg in segments[:max_segments]:
        skill, args = seg["goal"]
        inv = seg["inv"]
        events = ",".join(sorted(set(seg["events"]))) or "-"
        lines.append(
            f"- step {seg['start']:4d} room{tuple(seg['coord'])} "
            f"keys={inv['keys']} sword={'sword' in json.dumps(inv)} "
            f"-> {skill} {args} | events: {events}"
        )
    return "\n".join(lines)


def divergence_feedback(result: TraceResult) -> str:
    lines = [
        f"Consistency on {result.trace_name}: matched {result.matched}/"
        f"{result.total} expert steps.",
        "Divergences (fix these with better conditions, keep what works):",
    ]
    for div in result.divergences[:3]:
        node_hint = div.node
        if node_hint.startswith("finished"):
            node_hint += " (the program TERMINATED while the expert kept acting" \
                         " — add a loop back / more branches)"
        lines.append(
            f"- step {div.step} room{div.coord} keys={div.inv['keys']}: expert "
            f"did {ACTION_NAMES.get(div.expected)} but the program (at node "
            f"'{node_hint}') chose {ACTION_NAMES.get(div.got)}.\n  state:\n"
            + "\n".join("  " + ln for ln in div.state_text.splitlines())
        )
    return "\n".join(lines)


def synthesize_local(trace: dict, *, rounds: int = 4) -> tuple[dict, TraceResult]:
    """Iteratively synthesize a local expert program for one trace."""
    summary = summarize_trace(trace)
    user = (
        "Synthesize a DSL program that reproduces this expert demonstration "
        "and generalizes its decision logic.\n\n" + summary
    )
    best_spec, best_result = None, None
    feedback = ""
    for round_index in range(rounds):
        prompt = user if not feedback else user + "\n\n" + feedback
        try:
            spec = structured_completion(
                DSL_GUIDE, prompt, PROGRAM_JSON_SCHEMA,
                temperature=0.0 if round_index == 0 else 0.3,
            )
        except RuntimeError as exc:
            print(f"  round {round_index}: API failure ({exc}); continuing")
            continue
        try:
            compile_program(spec)
        except Exception as exc:   # noqa: BLE001 - feed compile errors back
            feedback = f"Your last program failed to compile: {exc}. Fix it."
            continue
        result = replay(spec, trace)
        print(f"  round {round_index}: matched {result.matched}/{result.total} "
              f"|pi|={complexity(spec)}")
        if best_result is None or result.matched > best_result.matched:
            best_spec, best_result = spec, result
        if not result.divergences and result.matched >= result.total * 0.98:
            break
        feedback = divergence_feedback(result) + \
            "\nRevise the program. Output the full corrected program."
    if best_spec is None:
        raise RuntimeError("no valid program synthesized")
    return best_spec, best_result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--traces", type=Path,
                        default=Path(__file__).resolve().parent / "traces")
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--only", nargs="*", default=None)
    args = parser.parse_args()

    for trace in load_traces(args.traces):
        task_id = trace["task_id"]
        if args.only and not any(o in task_id for o in args.only):
            continue
        print(f"synthesizing local expert for {task_id} ...")
        try:
            spec, result = synthesize_local(trace, rounds=args.rounds)
        except RuntimeError as exc:
            print(f"  FAILED for {task_id}: {exc}")
            continue
        name = "local_" + task_id.replace("/", "_")
        path = save_artifact(spec, name)
        print(f"  saved {path} (coverage {result.coverage:.3f})")


if __name__ == "__main__":
    main()

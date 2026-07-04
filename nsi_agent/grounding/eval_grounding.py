"""Per-field accuracy evaluation of the VLM grounding on held-out maps.

    python -m nsi_agent.grounding.eval_grounding \
        --data /root/autodl-tmp/data/grounding --split heldout \
        --model /root/autodl-tmp/models/Qwen2.5-VL-3B-Instruct \
        [--adapter /root/autodl-tmp/ckpt/grounding_lora/final] [--limit 200]
"""

from __future__ import annotations

import argparse
import json
import time
from collections import Counter
from pathlib import Path

import numpy as np
from PIL import Image

from .schema import SymbolicState
from .vlm import VLMGroundingModel

PX_TOLERANCE = 2


def compare(truth: SymbolicState, pred: SymbolicState) -> dict:
    grid_total = 80
    grid_wrong = sum(
        1
        for y in range(8)
        for x in range(10)
        if truth.grid[y][x] != pred.grid[y][x]
    )
    player_ok = (
        abs(truth.player_px[0] - pred.player_px[0]) <= PX_TOLERANCE
        and abs(truth.player_px[1] - pred.player_px[1]) <= PX_TOLERANCE
    )
    tile_ok = truth.player_tile == pred.player_tile

    def monster_key(monsters):
        return sorted((m.kind, m.px[0] // 8, m.px[1] // 8) for m in monsters)

    monsters_count_ok = len(truth.monsters) == len(pred.monsters)
    monsters_ok = monsters_count_ok and all(
        t[0] == p[0]
        and abs(t[1] - p[1]) <= 1
        and abs(t[2] - p[2]) <= 1
        for t, p in zip(monster_key(truth.monsters), monster_key(pred.monsters))
    )
    exits_ok = all(
        truth.exit_state(d) == pred.exit_state(d)
        for d in ("north", "south", "west", "east")
    )
    return {
        "grid_tile_acc": (grid_total - grid_wrong) / grid_total,
        "grid_exact": grid_wrong == 0,
        "player_px_ok": player_ok,
        "player_tile_ok": tile_ok,
        "facing_ok": truth.facing == pred.facing,
        "monsters_ok": monsters_ok,
        "monsters_count_ok": monsters_count_ok,
        "exits_ok": exits_ok,
        "all_ok": grid_wrong == 0 and player_ok and monsters_ok and exits_ok
        and truth.facing == pred.facing,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--split", default="heldout")
    parser.add_argument("--model", type=str, required=True)
    parser.add_argument("--adapter", type=str, default=None)
    parser.add_argument("--limit", type=int, default=300)
    parser.add_argument("--dump-errors", type=Path, default=None)
    args = parser.parse_args()

    rows = [
        json.loads(line)
        for line in (args.data / f"{args.split}.jsonl").read_text("utf-8").splitlines()
        if line.strip()
    ][: args.limit]
    print(f"evaluating {len(rows)} samples from {args.split}")

    model = VLMGroundingModel.load(
        model_dir=args.model, adapter_dir=args.adapter, four_bit=True
    )

    totals: Counter = Counter()
    grid_acc_sum = 0.0
    parse_failures = 0
    errors = []
    started = time.time()
    for index, row in enumerate(rows):
        frame = np.asarray(Image.open(args.data / row["image"]).convert("RGB"))
        truth = SymbolicState.from_text(row["label"])
        try:
            pred = model.ground(frame)
        except ValueError:
            parse_failures += 1
            errors.append({"image": row["image"], "raw": model.last_raw})
            continue
        result = compare(truth, pred)
        grid_acc_sum += result.pop("grid_tile_acc")
        for key, ok in result.items():
            totals[key] += bool(ok)
        if not result["all_ok"] and len(errors) < 40:
            errors.append({"image": row["image"], "truth": truth.to_text(),
                           "pred": pred.to_text()})
        if (index + 1) % 25 == 0:
            elapsed = time.time() - started
            print(f"  {index+1}/{len(rows)}  ({elapsed/(index+1):.2f}s/sample)")

    n = len(rows) - parse_failures
    print(f"\nparse failures: {parse_failures}/{len(rows)}")
    if n:
        print(f"grid tile accuracy: {grid_acc_sum / n:.4f}")
        for key in ("grid_exact", "player_px_ok", "player_tile_ok", "facing_ok",
                    "monsters_ok", "monsters_count_ok", "exits_ok", "all_ok"):
            print(f"{key}: {totals[key] / n:.4f}")
    if args.dump_errors and errors:
        args.dump_errors.write_text(json.dumps(errors, indent=1, ensure_ascii=False))
        print(f"wrote {len(errors)} error cases to {args.dump_errors}")


if __name__ == "__main__":
    main()

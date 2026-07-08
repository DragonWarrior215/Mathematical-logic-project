"""Extra task_5 generalization probes.

These variants are intentionally separate from test_script.py so the original
15+ benchmark set stays unchanged.  They use oracle grounding and evaluate the
current agent code as-is.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path

from test_script import (
    DEFAULT_OUT,
    EvalResult,
    VariantSpec,
    copy_dungeon,
    dungeon_room_path,
    object_by_id,
    read_json,
    run_variant,
    save_room_from_path,
    summarize,
    write_json,
    markdown_report,
)


DEFAULT_EXTRA_OUT = DEFAULT_OUT.parent / "task5_extra_eval"


def _rooms(dungeon: Path):
    center_path = dungeon_room_path(dungeon, "room_0_0.json")
    west_path = dungeon_room_path(dungeon, "room_-1_0.json")
    south_path = dungeon_room_path(dungeon, "room_0_1.json")
    east_path = dungeon_room_path(dungeon, "room_1_0.json")
    return (
        center_path, read_json(center_path),
        west_path, read_json(west_path),
        south_path, read_json(south_path),
        east_path, read_json(east_path),
    )


def _save(paths_and_rooms) -> None:
    for path, room in paths_and_rooms:
        save_room_from_path(path, room)


def build_t5_extra_button_near_locked(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_button_near_locked")
    c_path, center, s_path, south, *_ = _rooms(dungeon)
    object_by_id(center, "button_1")["pos"] = [8, 1]
    object_by_id(center, "chest_1")["pos"] = [2, 5]
    object_by_id(south, "chest_1")["pos"] = [7, 1]
    _save([(c_path, center), (s_path, south)])
    return dungeon


def build_t5_extra_center_maze(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_center_maze")
    c_path, center, *_ = _rooms(dungeon)
    center["layout"] = [
        "..........",
        "..#..#....",
        "..#..#....",
        "...#......",
        "......#...",
        "..#...#...",
        "..........",
        "..........",
    ]
    _save([(c_path, center)])
    return dungeon


def build_t5_extra_south_key_far(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_south_key_far")
    _, _, _, _, s_path, south, *_ = _rooms(dungeon)
    object_by_id(south, "chest_1")["pos"] = [1, 6]
    object_by_id(south, "monster_1")["pos"] = [7, 5]
    object_by_id(south, "trap_1")["pos"] = [3, 5]
    _save([(s_path, south)])
    return dungeon


def build_t5_extra_west_key_far(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_west_key_far")
    _, _, w_path, west, s_path, south, *_ = _rooms(dungeon)
    object_by_id(west, "chest_1")["loot"] = {"kind": "key", "key_id": "prototype_key"}
    object_by_id(west, "chest_1")["pos"] = [1, 1]
    object_by_id(south, "chest_1")["loot"] = {"kind": "gold", "amount": 5}
    _save([(w_path, west), (s_path, south)])
    return dungeon


def build_t5_extra_west_key_east_heal_far(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_west_key_east_heal_far")
    _, _, w_path, west, s_path, south, e_path, east = _rooms(dungeon)
    object_by_id(west, "chest_1")["loot"] = {"kind": "key", "key_id": "prototype_key"}
    object_by_id(west, "chest_1")["pos"] = [1, 1]
    object_by_id(south, "chest_1")["loot"] = {"kind": "gold", "amount": 5}
    east["layout"] = [
        "..........",
        ".######...",
        "......#...",
        "..###.#...",
        "....#.#...",
        "....#.....",
        "....###...",
        "..........",
    ]
    object_by_id(east, "chest_1")["pos"] = [8, 6]
    object_by_id(east, "monster_1")["pos"] = [6, 5]
    _save([(w_path, west), (s_path, south), (e_path, east)])
    return dungeon


def build_t5_extra_center_gold_far(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_center_gold_far")
    c_path, center, *_ = _rooms(dungeon)
    object_by_id(center, "chest_1")["pos"] = [8, 1]
    object_by_id(center, "button_1")["pos"] = [2, 6]
    _save([(c_path, center)])
    return dungeon


def build_t5_extra_west_monster_pressure(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_west_monster_pressure")
    _, _, w_path, west, *_ = _rooms(dungeon)
    object_by_id(west, "monster_1")["pos"] = [4, 4]
    object_by_id(west, "monster_2")["pos"] = [7, 2]
    object_by_id(west, "chest_1")["pos"] = [2, 6]
    _save([(w_path, west)])
    return dungeon


def build_t5_extra_south_layout_detour(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_south_layout_detour")
    _, _, _, _, s_path, south, *_ = _rooms(dungeon)
    south["layout"] = [
        "..........",
        "..........",
        "..####....",
        ".....#....",
        ".#...#....",
        "..........",
        ".#..#.....",
        "..........",
    ]
    object_by_id(south, "chest_1")["pos"] = [8, 5]
    _save([(s_path, south)])
    return dungeon


def build_t5_extra_heal_near_monster(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_heal_near_monster")
    *_, e_path, east = _rooms(dungeon)
    object_by_id(east, "chest_1")["pos"] = [7, 6]
    object_by_id(east, "monster_1")["pos"] = [6, 5]
    _save([(e_path, east)])
    return dungeon


def build_t5_extra_all_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_extra_all_shift")
    c_path, center, w_path, west, s_path, south, e_path, east = _rooms(dungeon)
    center["layout"] = [
        "..........",
        "..#.......",
        "..#..#....",
        "...#......",
        "..........",
        "......#...",
        "....#.....",
        "..........",
    ]
    object_by_id(center, "button_1")["pos"] = [7, 1]
    object_by_id(center, "chest_1")["pos"] = [2, 5]
    object_by_id(west, "monster_1")["pos"] = [4, 4]
    object_by_id(south, "chest_1")["pos"] = [7, 1]
    object_by_id(east, "chest_1")["pos"] = [8, 6]
    _save([(c_path, center), (w_path, west), (s_path, south), (e_path, east)])
    return dungeon


def variant_specs() -> list[VariantSpec]:
    task = "mathematical_logic/task_5"
    return [
        VariantSpec("task5_extra_button_near_locked", task, "object_shift",
                    "Move the button toward the locked side and shift the center/south chests.",
                    build_t5_extra_button_near_locked),
        VariantSpec("task5_extra_center_maze", task, "layout_shift",
                    "Add a denser center-room wall detour while preserving exits.",
                    build_t5_extra_center_maze),
        VariantSpec("task5_extra_south_key_far", task, "health_pressure_shift",
                    "Keep the key in the south room but move it behind a longer route and trap.",
                    build_t5_extra_south_key_far),
        VariantSpec("task5_extra_west_key_far", task, "topology_shift",
                    "Move the key to a far west chest and turn the south chest into gold.",
                    build_t5_extra_west_key_far),
        VariantSpec("task5_extra_west_key_east_heal_far", task, "combined_shift",
                    "Move the key west and also make the east heal room longer.",
                    build_t5_extra_west_key_east_heal_far),
        VariantSpec("task5_extra_center_gold_far", task, "goal_priority_shift",
                    "Move the optional center gold chest farther from the main route.",
                    build_t5_extra_center_gold_far),
        VariantSpec("task5_extra_west_monster_pressure", task, "combat_pressure_shift",
                    "Move west-room monsters to pressure chest navigation.",
                    build_t5_extra_west_monster_pressure),
        VariantSpec("task5_extra_south_layout_detour", task, "layout_shift",
                    "Add a south-room detour around the key chest.",
                    build_t5_extra_south_layout_detour),
        VariantSpec("task5_extra_heal_near_monster", task, "health_pressure_shift",
                    "Move the heal chest closer to the east ambusher.",
                    build_t5_extra_heal_near_monster),
        VariantSpec("task5_extra_all_shift", task, "combined_shift",
                    "Combine center layout, object, west monster, and heal-position shifts.",
                    build_t5_extra_all_shift),
    ]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_EXTRA_OUT)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-steps", type=int, default=None)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    variants_dir = args.out / "variant_maps"
    variants_dir.mkdir(parents=True, exist_ok=True)
    specs = variant_specs()
    map_paths = {spec.name: spec.builder(variants_dir) for spec in specs}
    results: list[EvalResult] = []
    for spec in specs:
        result = run_variant(
            spec,
            map_paths[spec.name],
            args.seed,
            prefer_induced=True,
            max_steps=args.max_steps,
        )
        results.append(result)
        print(json.dumps(asdict(result), ensure_ascii=False))
    summary = summarize(results)
    write_json(args.out / "generalization_results.json", {
        "summary": summary,
        "results": [asdict(result) for result in results],
    })
    (args.out / "generalization_report.md").write_text(
        markdown_report(results, summary),
        encoding="utf-8",
    )
    print(f"wrote {args.out / 'generalization_results.json'}")
    print(f"wrote {args.out / 'generalization_report.md'}")


if __name__ == "__main__":
    main()

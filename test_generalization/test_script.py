"""Generalization diagnostics for the mathematical-logic agent.

This script intentionally does not modify the agent.  It creates temporary
map variants, evaluates the existing policy with oracle grounding, and writes
JSON/Markdown diagnostics.  The goal is to find planner/skill robustness
problems before spending GPU time on VLM pixel tests.
"""

from __future__ import annotations

import argparse
import copy
import json
import shutil
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable


PROJECT_ROOT = Path(__file__).resolve().parent.parent
MAP_ROOT = PROJECT_ROOT / "nesylink" / "map_data" / "mathematical_logic"
DEFAULT_OUT = PROJECT_ROOT.parents[2] / "outputs" / "generalization_eval"

if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from nesylink.env import make_env

from nsi_agent.agent import OracleGrounding, Policy

TASKS = tuple(f"mathematical_logic/task_{i}" for i in range(1, 6))


@dataclass(frozen=True)
class VariantSpec:
    name: str
    task_id: str
    category: str
    description: str
    builder: Callable[[Path], Path]


@dataclass
class EvalResult:
    variant: str
    task_id: str
    category: str
    description: str
    planner: str
    seed: int
    success: bool
    steps: int
    reward: float
    terminal_reason: str | None
    event_counts: dict[str, int]
    diagnoses: list[Any]
    map_path: str


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")


def copy_single_room(task_name: str, out_dir: Path, variant_name: str) -> Path:
    src = MAP_ROOT / task_name / "room_001.json"
    dst_dir = out_dir / variant_name
    dst_dir.mkdir(parents=True, exist_ok=True)
    dst = dst_dir / "room_001.json"
    shutil.copy2(src, dst)
    return dst


def copy_dungeon(task_name: str, out_dir: Path, variant_name: str) -> Path:
    src_dir = MAP_ROOT / task_name
    dst_dir = out_dir / variant_name
    shutil.copytree(src_dir, dst_dir, dirs_exist_ok=True)
    return dst_dir / "dungeon.json"


def object_by_id(room: dict, object_id: str) -> dict:
    for obj in room.get("objects", []):
        if obj.get("id") == object_id:
            return obj
    raise KeyError(object_id)


def exit_by_id(room: dict, exit_id: str) -> dict:
    for ex in room.get("exits", []):
        if ex.get("id") == exit_id:
            return ex
    raise KeyError(exit_id)


def save_room_from_path(path: Path, room: dict) -> None:
    write_json(path, room)


def dungeon_room_path(dungeon_path: Path, room_file: str) -> Path:
    return dungeon_path.parent / "rooms" / room_file


# ---------------------------------------------------------------------------
# Variant builders
# ---------------------------------------------------------------------------


def build_t1_key_east(out_dir: Path) -> Path:
    path = copy_single_room("task_1", out_dir, "task1_key_east")
    room = read_json(path)
    object_by_id(room, "chest_key")["pos"] = [8, 6]
    room["spawns"]["default"] = [2, 6]
    save_room_from_path(path, room)
    return path


def build_t1_south_exit(out_dir: Path) -> Path:
    path = copy_single_room("task_1", out_dir, "task1_south_exit")
    room = read_json(path)
    ex = exit_by_id(room, "north_exit")
    ex["id"] = "south_exit"
    ex["direction"] = "south"
    ex["target_entry"] = "from_north"
    room["spawns"]["from_north"] = [4, 1]
    save_room_from_path(path, room)
    return path


def build_t1_mirrored_room(out_dir: Path) -> Path:
    path = copy_single_room("task_1", out_dir, "task1_mirrored_room")
    room = read_json(path)
    room["layout"] = [row[::-1] for row in room["layout"]]
    for spawn_name, pos in list(room["spawns"].items()):
        room["spawns"][spawn_name] = [9 - pos[0], pos[1]]
    object_by_id(room, "chest_key")["pos"] = [9, 3]
    save_room_from_path(path, room)
    return path


def build_t2_monster_far(out_dir: Path) -> Path:
    path = copy_single_room("task_2", out_dir, "task2_monster_far")
    room = read_json(path)
    object_by_id(room, "chest_key")["pos"] = [8, 3]
    object_by_id(room, "monster_chaser_left")["pos"] = [6, 5]
    room["spawns"]["default"] = [7, 2]
    save_room_from_path(path, room)
    return path


def build_t2_east_exit(out_dir: Path) -> Path:
    path = copy_single_room("task_2", out_dir, "task2_east_exit")
    room = read_json(path)
    ex = exit_by_id(room, "west_exit")
    ex["id"] = "east_exit"
    ex["direction"] = "east"
    ex["target_entry"] = "from_west"
    room["spawns"]["from_west"] = [1, 4]
    object_by_id(room, "chest_key")["pos"] = [7, 3]
    object_by_id(room, "monster_chaser_left")["pos"] = [4, 3]
    save_room_from_path(path, room)
    return path


def build_t2_wall_detour(out_dir: Path) -> Path:
    path = copy_single_room("task_2", out_dir, "task2_wall_detour")
    room = read_json(path)
    room["layout"] = [
        "..........",
        "..........",
        "...###....",
        "..........",
        "....###...",
        "..........",
        "..........",
        "..........",
    ]
    object_by_id(room, "chest_key")["pos"] = [1, 5]
    object_by_id(room, "monster_chaser_left")["pos"] = [6, 2]
    save_room_from_path(path, room)
    return path


def build_t3_key_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_3", out_dir, "task3_key_shift")
    key_path = dungeon_room_path(dungeon, "key_room.json")
    key_room = read_json(key_path)
    object_by_id(key_room, "return_key_chest")["pos"] = [2, 5]
    save_room_from_path(key_path, key_room)
    hall_path = dungeon_room_path(dungeon, "monster_hall.json")
    hall = read_json(hall_path)
    object_by_id(hall, "hall_chaser")["pos"] = [3, 2]
    save_room_from_path(hall_path, hall)
    return dungeon


def build_t3_hall_detour(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_3", out_dir, "task3_hall_detour")
    hall_path = dungeon_room_path(dungeon, "monster_hall.json")
    hall = read_json(hall_path)
    hall["layout"] = [
        "..........",
        "..###.....",
        ".....#....",
        ".....#....",
        ".....#....",
        ".....###..",
        "..........",
        "..........",
    ]
    object_by_id(hall, "hall_chaser")["pos"] = [3, 5]
    save_room_from_path(hall_path, hall)
    return dungeon


def build_t3_east_key_chain(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_3", out_dir, "task3_east_key_chain")
    start_path = dungeon_room_path(dungeon, "start_room.json")
    hall_path = dungeon_room_path(dungeon, "monster_hall.json")
    key_path = dungeon_room_path(dungeon, "key_room.json")
    start = read_json(start_path)
    hall = read_json(hall_path)
    key = read_json(key_path)

    start["coord"] = [0, 0]
    hall["coord"] = [1, 0]
    key["coord"] = [2, 0]
    start["spawns"] = {"default": [4, 4], "from_east": [8, 4], "from_west": [1, 4]}
    start["exits"] = [
        {
            "id": "east_exit",
            "direction": "east",
            "target_room": "monster_hall",
            "target_entry": "from_west",
            "type": "normal",
            "success_message": "MONSTER HALL",
        },
        {
            "id": "locked_left_exit",
            "direction": "west",
            "target_room": "start_room",
            "target_entry": "from_west",
            "type": "locked_key",
            "requires": {"key_count": 1, "consume_key": True},
            "blocked_message": "NEED KEY FROM EAST",
            "success_message": "TASK CLEARED!",
            "complete_task": True,
        },
    ]
    hall["spawns"] = {"default": [1, 4], "from_west": [1, 4], "from_east": [8, 4]}
    hall["exits"] = [
        {
            "id": "west_exit",
            "direction": "west",
            "target_room": "start_room",
            "target_entry": "from_east",
            "type": "normal",
            "success_message": "START ROOM",
        },
        {
            "id": "east_exit",
            "direction": "east",
            "target_room": "key_room",
            "target_entry": "from_west",
            "type": "normal",
            "success_message": "KEY ROOM",
        },
    ]
    key["spawns"] = {"default": [1, 4], "from_west": [1, 4]}
    key["exits"] = [
        {
            "id": "west_exit",
            "direction": "west",
            "target_room": "monster_hall",
            "target_entry": "from_east",
            "type": "normal",
            "success_message": "MONSTER HALL",
        }
    ]
    save_room_from_path(start_path, start)
    save_room_from_path(hall_path, hall)
    save_room_from_path(key_path, key)
    return dungeon


def build_t4_object_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_4", out_dir, "task4_object_shift")
    north_path = dungeon_room_path(dungeon, "north.json")
    east_path = dungeon_room_path(dungeon, "east.json")
    south_path = dungeon_room_path(dungeon, "south.json")
    north = read_json(north_path)
    east = read_json(east_path)
    south = read_json(south_path)
    object_by_id(north, "key_chest")["pos"] = [6, 2]
    object_by_id(east, "sword_chest")["pos"] = [3, 3]
    object_by_id(south, "guardian")["pos"] = [5, 5]
    save_room_from_path(north_path, north)
    save_room_from_path(east_path, east)
    save_room_from_path(south_path, south)
    return dungeon


def build_t4_switch_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_4", out_dir, "task4_switch_shift")
    west_path = dungeon_room_path(dungeon, "west.json")
    west = read_json(west_path)
    object_by_id(west, "bridge_switch")["pos"] = [6, 2]
    west["layout"] = [
        "##########",
        "#........#",
        "#........#",
        "..........",
        "..........",
        "#..##....#",
        "#........#",
        "##########",
    ]
    save_room_from_path(west_path, west)
    return dungeon


def build_t4_final_chest_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_4", out_dir, "task4_final_chest_shift")
    center_path = dungeon_room_path(dungeon, "center.json")
    center = read_json(center_path)
    object_by_id(center, "final_chest")["pos"] = [5, 4]
    save_room_from_path(center_path, center)
    return dungeon


def build_t5_object_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_object_shift")
    center_path = dungeon_room_path(dungeon, "room_0_0.json")
    south_path = dungeon_room_path(dungeon, "room_0_1.json")
    center = read_json(center_path)
    south = read_json(south_path)
    object_by_id(center, "button_1")["pos"] = [7, 1]
    object_by_id(center, "chest_1")["pos"] = [2, 5]
    object_by_id(south, "chest_1")["pos"] = [7, 1]
    save_room_from_path(center_path, center)
    save_room_from_path(south_path, south)
    return dungeon


def build_t5_layout_shift(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_layout_shift")
    center_path = dungeon_room_path(dungeon, "room_0_0.json")
    center = read_json(center_path)
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
    save_room_from_path(center_path, center)
    return dungeon


def build_t5_key_in_west(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_key_in_west")
    west_path = dungeon_room_path(dungeon, "room_-1_0.json")
    south_path = dungeon_room_path(dungeon, "room_0_1.json")
    west = read_json(west_path)
    south = read_json(south_path)
    object_by_id(west, "chest_1")["loot"] = {"kind": "key", "key_id": "prototype_key"}
    object_by_id(south, "chest_1")["loot"] = {"kind": "gold", "amount": 5}
    save_room_from_path(west_path, west)
    save_room_from_path(south_path, south)
    return dungeon


def build_t5_key_west_center_detour(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_key_west_center_detour")
    center_path = dungeon_room_path(dungeon, "room_0_0.json")
    west_path = dungeon_room_path(dungeon, "room_-1_0.json")
    south_path = dungeon_room_path(dungeon, "room_0_1.json")
    center = read_json(center_path)
    west = read_json(west_path)
    south = read_json(south_path)
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
    object_by_id(west, "chest_1")["loot"] = {"kind": "key", "key_id": "prototype_key"}
    object_by_id(south, "chest_1")["loot"] = {"kind": "gold", "amount": 5}
    save_room_from_path(center_path, center)
    save_room_from_path(west_path, west)
    save_room_from_path(south_path, south)
    return dungeon


def build_t5_west_key_decoy_chests(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_west_key_decoy_chests")
    center_path = dungeon_room_path(dungeon, "room_0_0.json")
    east_path = dungeon_room_path(dungeon, "room_1_0.json")
    west_path = dungeon_room_path(dungeon, "room_-1_0.json")
    south_path = dungeon_room_path(dungeon, "room_0_1.json")
    center = read_json(center_path)
    east = read_json(east_path)
    west = read_json(west_path)
    south = read_json(south_path)
    object_by_id(west, "chest_1")["loot"] = {"kind": "key", "key_id": "prototype_key"}
    object_by_id(west, "chest_1")["pos"] = [1, 1]
    object_by_id(south, "chest_1")["loot"] = {"kind": "gold", "amount": 5}
    object_by_id(center, "chest_1")["pos"] = [6, 1]
    object_by_id(east, "chest_1")["pos"] = [8, 6]
    save_room_from_path(center_path, center)
    save_room_from_path(east_path, east)
    save_room_from_path(west_path, west)
    save_room_from_path(south_path, south)
    return dungeon


def build_t5_east_heal_far(out_dir: Path) -> Path:
    dungeon = copy_dungeon("task_5", out_dir, "task5_east_heal_far")
    east_path = dungeon_room_path(dungeon, "room_1_0.json")
    east = read_json(east_path)
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
    save_room_from_path(east_path, east)
    return dungeon


def variant_specs() -> list[VariantSpec]:
    return [
        VariantSpec("task1_key_east", "mathematical_logic/task_1", "object_shift",
                    "Move the key chest from the west side to the east side.", build_t1_key_east),
        VariantSpec("task1_south_exit", "mathematical_logic/task_1", "topology_shift",
                    "Move the locked completion exit from north to south.", build_t1_south_exit),
        VariantSpec("task1_mirrored_room", "mathematical_logic/task_1", "layout_shift",
                    "Mirror the room horizontally, including spawn and key chest.", build_t1_mirrored_room),
        VariantSpec("task2_monster_far", "mathematical_logic/task_2", "object_shift",
                    "Move the key chest and monster to new positions.", build_t2_monster_far),
        VariantSpec("task2_east_exit", "mathematical_logic/task_2", "topology_shift",
                    "Move the conditional completion exit from west to east.", build_t2_east_exit),
        VariantSpec("task2_wall_detour", "mathematical_logic/task_2", "layout_shift",
                    "Add interior wall detours while keeping the kill-and-key objective.", build_t2_wall_detour),
        VariantSpec("task3_key_shift", "mathematical_logic/task_3", "object_shift",
                    "Move the key chest and chaser within the existing west chain.", build_t3_key_shift),
        VariantSpec("task3_hall_detour", "mathematical_logic/task_3", "layout_shift",
                    "Add a wall detour in the monster hall.", build_t3_hall_detour),
        VariantSpec("task3_east_key_chain", "mathematical_logic/task_3", "topology_shift",
                    "Mirror the key-fetch chain to the east and put the locked exit west.", build_t3_east_key_chain),
        VariantSpec("task4_object_shift", "mathematical_logic/task_4", "object_shift",
                    "Move key chest, sword chest, and guardian positions.", build_t4_object_shift),
        VariantSpec("task4_switch_shift", "mathematical_logic/task_4", "layout_shift",
                    "Move the bridge switch and add small obstacles in the west room.", build_t4_switch_shift),
        VariantSpec("task4_final_chest_shift", "mathematical_logic/task_4", "object_shift",
                    "Move the hidden final chest inside the center room.", build_t4_final_chest_shift),
        VariantSpec("task5_object_shift", "mathematical_logic/task_5", "object_shift",
                    "Move the center button/chest and south key chest.", build_t5_object_shift),
        VariantSpec("task5_layout_shift", "mathematical_logic/task_5", "layout_shift",
                    "Alter the center-room wall pattern while preserving exits.", build_t5_layout_shift),
        VariantSpec("task5_key_in_west", "mathematical_logic/task_5", "topology_shift",
                    "Move the key reward from the south room chest to the west room chest.", build_t5_key_in_west),
        VariantSpec("task5_key_west_center_detour", "mathematical_logic/task_5", "combined_shift",
                    "Move the key to the west room and alter the center-room wall pattern.", build_t5_key_west_center_detour),
        VariantSpec("task5_west_key_decoy_chests", "mathematical_logic/task_5", "goal_priority_shift",
                    "Move the key to a west chest while keeping nearby non-key chest decoys.", build_t5_west_key_decoy_chests),
        VariantSpec("task5_east_heal_far", "mathematical_logic/task_5", "health_pressure_shift",
                    "Move the post-lock heal chest farther behind a detour in the east room.", build_t5_east_heal_far),
    ]


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------


def event_names(info: dict[str, Any]) -> list[str]:
    names = [
        str(record.get("name"))
        for record in info.get("events", {}).get("records", [])
        if isinstance(record, dict) and record.get("name") is not None
    ]
    game = info.get("game", {})
    if game.get("world_completed", False) or info.get("terminal_reason") == "world_completed":
        names.append("world_completed")
    if game.get("dead", False) or info.get("terminal_reason") == "agent_dead":
        names.append("agent_dead")
    return names


def run_variant(spec: VariantSpec, map_path: Path, seed: int, *, prefer_induced: bool,
                max_steps: int | None) -> EvalResult:
    env = make_env(
        task_id=spec.task_id,
        map_path=map_path,
        observation_mode="pixels",
        max_steps=max_steps,
    )
    policy = Policy(backend=OracleGrounding(env), prefer_induced=prefer_induced)
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
        planner="selected" if prefer_induced else "fallback",
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


def summarize(results: list[EvalResult]) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for group_name, key_fn in (
        ("by_planner", lambda r: r.planner),
        ("by_task", lambda r: f"{r.planner}:{r.task_id}"),
        ("by_category", lambda r: f"{r.planner}:{r.category}"),
    ):
        grouped: dict[str, list[EvalResult]] = defaultdict(list)
        for result in results:
            grouped[key_fn(result)].append(result)
        summary[group_name] = {}
        for key, rows in sorted(grouped.items()):
            episodes = len(rows)
            successes = sum(row.success for row in rows)
            event_totals: Counter[str] = Counter()
            for row in rows:
                event_totals.update(row.event_counts)
            summary[group_name][key] = {
                "episodes": episodes,
                "success_rate": successes / episodes,
                "avg_steps": sum(row.steps for row in rows) / episodes,
                "avg_reward": sum(row.reward for row in rows) / episodes,
                "event_totals": dict(sorted(event_totals.items())),
            }
    return summary


def markdown_report(results: list[EvalResult], summary: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Generalization Evaluation Report")
    lines.append("")
    lines.append("This report evaluates the current agent without modifying its code.")
    lines.append("All runs use oracle grounding, so the measured layer is symbolic planning, memory, and skills rather than VLM perception.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append("| Planner | Episodes | Success rate | Avg steps | Avg reward |")
    lines.append("|---|---:|---:|---:|---:|")
    for planner, stats in summary["by_planner"].items():
        lines.append(
            f"| {planner} | {stats['episodes']} | {stats['success_rate']:.3f} | "
            f"{stats['avg_steps']:.1f} | {stats['avg_reward']:.3f} |"
        )
    lines.append("")
    lines.append("## Results By Variant")
    lines.append("")
    lines.append("| Variant | Task | Category | Planner | Success | Steps | Reward | Terminal | Key events |")
    lines.append("|---|---|---|---|---:|---:|---:|---|---|")
    for row in sorted(results, key=lambda r: (r.planner, r.task_id, r.variant)):
        event_bits = ", ".join(
            f"{name}:{count}"
            for name, count in row.event_counts.items()
            if name in {
                "world_completed", "environment_completed", "agent_dead",
                "action_blocked", "trap_triggered", "monster_killed",
                "chest_opened", "key_collected", "door_opened", "room_changed",
            }
        )
        lines.append(
            f"| {row.variant} | {row.task_id} | {row.category} | {row.planner} | "
            f"{'yes' if row.success else 'no'} | {row.steps} | {row.reward:.3f} | "
            f"{row.terminal_reason or '-'} | {event_bits or '-'} |"
        )
    lines.append("")
    lines.append("## Results By Category")
    lines.append("")
    lines.append("| Planner/category | Episodes | Success rate | Avg steps | Avg reward |")
    lines.append("|---|---:|---:|---:|---:|")
    for key, stats in summary["by_category"].items():
        lines.append(
            f"| {key} | {stats['episodes']} | {stats['success_rate']:.3f} | "
            f"{stats['avg_steps']:.1f} | {stats['avg_reward']:.3f} |"
        )
    lines.append("")
    lines.append("## Results By Task")
    lines.append("")
    lines.append("| Planner/task | Episodes | Success rate | Avg steps | Avg reward |")
    lines.append("|---|---:|---:|---:|---:|")
    for key, stats in summary["by_task"].items():
        lines.append(
            f"| {key} | {stats['episodes']} | {stats['success_rate']:.3f} | "
            f"{stats['avg_steps']:.1f} | {stats['avg_reward']:.3f} |"
        )
    lines.append("")
    lines.append("## Variant Descriptions")
    lines.append("")
    for row in sorted({r.variant: r for r in results}.values(), key=lambda r: r.variant):
        lines.append(f"- `{row.variant}` ({row.category}, {row.task_id}): {row.description}")
    lines.append("")
    failures = [row for row in results if row.planner == "selected" and not row.success]
    lines.append("## Primary Failure Signals")
    lines.append("")
    if not failures:
        lines.append("No selected-planner failures were observed in this batch.")
    else:
        for row in failures:
            lines.append(
                f"- `{row.variant}` failed after {row.steps} steps, terminal={row.terminal_reason}, "
                f"diagnoses={row.diagnoses or '[]'}, events={row.event_counts}"
            )
    lines.append("")
    lines.append("## Notes")
    lines.append("")
    lines.append("- Color/palette changes are not included here because this machine has no CUDA-capable GPU and VLM pixel inference is not practical locally.")
    lines.append("- These tests intentionally keep task cores intact: task_1 remains key-door, task_2 remains kill+key, task_3 remains key-fetch-return, task_4 remains bridge/key/sword/monster/final chest, and task_5 remains a mixed multi-room objective.")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-steps", type=int, default=None)
    parser.add_argument("--fallback-too", action="store_true")
    parser.add_argument("--variant-prefix", default=None,
                        help="Only run variants whose names start with this prefix.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    variants_dir = args.out / "variant_maps"
    variants_dir.mkdir(parents=True, exist_ok=True)

    specs = variant_specs()
    if args.variant_prefix:
        specs = [spec for spec in specs if spec.name.startswith(args.variant_prefix)]
        if not specs:
            raise SystemExit(f"no variants matched prefix: {args.variant_prefix}")
    map_paths = {spec.name: spec.builder(variants_dir) for spec in specs}

    results: list[EvalResult] = []
    for prefer_induced in ([True, False] if args.fallback_too else [True]):
        for spec in specs:
            result = run_variant(
                spec,
                map_paths[spec.name],
                args.seed,
                prefer_induced=prefer_induced,
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

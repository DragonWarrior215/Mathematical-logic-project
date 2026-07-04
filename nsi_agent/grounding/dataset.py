"""Training-time dataset generation for the VLM grounding module.

Produces (frame PNG, symbolic-state text) pairs from:
1. Fallback-policy episodes on the five course tasks (on-policy states,
   including opened doors, rotated bridges, combat poses);
2. Biased random walks on the course maps and on procedurally generated
   *variant* single-room maps (novel wall layouts / object placements —
   the generalization axis the final evaluation will probe).

Uses ``info``/engine internals for labels, which the assignment explicitly
allows at training time. Held-out split is BY MAP so grounding accuracy is
measured on layouts never seen in training.

    python -m nsi_agent.grounding.dataset --out data/grounding \
        --task-episodes 3 --variant-maps 60 --walk-steps 700
"""

from __future__ import annotations

import argparse
import json
import random
from collections import deque
from pathlib import Path

import numpy as np
from PIL import Image

from nesylink.env import make_env

from ..constants import ACTION_A, ACTION_B, MOVE_ACTIONS
from .oracle import oracle_state

TASKS = tuple(f"mathematical_logic/task_{i}" for i in range(1, 6))

LOOTS = (
    {"kind": "key", "key_id": "vk"},
    {"kind": "gold", "amount": 2},
    {"kind": "heal", "amount": 1},
    {"kind": "item", "item_id": "sword", "tool": "sword", "equip_slot": "A"},
)
MONSTER_TYPES = ("chaser", "patroller", "ambusher")
EXIT_TYPES = ("normal", "locked_key", "conditional")


# ---------------------------------------------------------------------------
# Variant map generation
# ---------------------------------------------------------------------------


def make_variant_room(rng: random.Random) -> dict:
    """Random single-room map exercising every renderable object class."""
    while True:
        walls: set[tuple[int, int]] = set()
        # Wall segments + scattered blocks in the interior.
        for _ in range(rng.randint(2, 4)):
            x0, y0 = rng.randint(1, 8), rng.randint(1, 6)
            horizontal = rng.random() < 0.5
            for k in range(rng.randint(2, 5)):
                x, y = (x0 + k, y0) if horizontal else (x0, y0 + k)
                if 1 <= x <= 8 and 1 <= y <= 6:
                    walls.add((x, y))
        for _ in range(rng.randint(0, 4)):
            walls.add((rng.randint(1, 8), rng.randint(1, 6)))
        # Keep exit boundary tiles clear.
        for tile in ((4, 0), (5, 0), (4, 7), (5, 7), (0, 3), (0, 4), (9, 3), (9, 4)):
            walls.discard(tile)

        free = [
            (x, y) for x in range(10) for y in range(8) if (x, y) not in walls
        ]
        rng.shuffle(free)
        take = iter(free)

        objects = []
        blockers: set[tuple[int, int]] = set(walls)

        dynamic_objects = []
        if rng.random() < 0.35:
            # A bridge strip over gap tiles (decorative but pixel-accurate).
            y = rng.randint(1, 6)
            xs = list(range(rng.randint(1, 3), rng.randint(6, 9)))
            tiles = [[x, y] for x in xs if (x, y) not in blockers]
            if len(tiles) >= 2:
                split = max(1, len(tiles) // 2)
                dynamic_objects.append({
                    "id": "deco_bridge", "kind": "rotating_bridge",
                    "initial_state": "a",
                    "background_tile": "gap", "active_tile": "bridge",
                    "states": {"a": {"tiles": tiles[:split]},
                               "b": {"tiles": tiles[split:]}},
                })
                for tile in tiles:
                    blockers.add(tuple(tile))   # keep objects off the strip

        def place() -> tuple[int, int]:
            for tile in take:
                if tile not in blockers:
                    return tile
            raise StopIteration

        try:
            for i in range(rng.randint(1, 3)):
                pos = place()
                blockers.add(pos)
                chest = {
                    "id": f"chest_{i}", "kind": "chest", "pos": list(pos),
                    "loot": dict(rng.choice(LOOTS)),
                }
                objects.append(chest)
            for i in range(rng.randint(0, 2)):
                pos = place()
                objects.append({
                    "id": f"trap_{i}", "kind": "trap", "pos": list(pos),
                    "damage": 1,
                    **({"trap_type": "abyss", "respawn_delay_steps": 2}
                       if rng.random() < 0.4 else {}),
                })
            if rng.random() < 0.6:
                pos = place()
                objects.append({"id": "button_0", "kind": "button", "pos": list(pos)})
            if dynamic_objects and rng.random() < 0.8:
                pos = place()
                blockers.add(pos)
                objects.append({
                    "id": "switch_0", "kind": "switch", "pos": list(pos),
                    "activation": "interact", "message": "SWITCH",
                    "effect": {"type": "cycle_state", "target": "deco_bridge",
                               "order": ["a", "b"]},
                })
            if rng.random() < 0.5:
                pos = place()
                blockers.add(pos)
                objects.append({
                    "id": "npc_0", "kind": "npc", "pos": list(pos),
                    "text": "Hello adventurer.",
                })
            for i in range(rng.randint(0, 2)):
                pos = place()
                objects.append({
                    "id": f"monster_{i}", "kind": "monster", "pos": list(pos),
                    "monster_type": rng.choice(MONSTER_TYPES),
                    "hp": rng.randint(1, 3), "damage": 1,
                    **({"ambush_range": 2} if rng.random() < 0.3 else {}),
                })
            spawn = place()
        except StopIteration:
            continue

        exits = []
        for direction in ("north", "south", "west", "east"):
            if rng.random() < 0.55:
                exit_type = rng.choice(EXIT_TYPES)
                entry = {
                    "id": f"{direction}_exit", "direction": direction,
                    "target_room": "room_001", "target_entry": "default",
                    "type": exit_type,
                }
                if exit_type == "locked_key":
                    entry["requires"] = {"key_count": 1, "consume_key": False}
                elif exit_type == "conditional":
                    entry["requires"] = (
                        {"button_pressed": "button_0"}
                        if any(o["id"] == "button_0" for o in objects)
                        and rng.random() < 0.5
                        else {"all_monsters_defeated": True}
                    )
                exits.append(entry)

        # Connectivity: player must reach every non-blocking interactive tile.
        if not _connected(walls, spawn):
            continue

        layout = [
            "".join("#" if (x, y) in walls else "." for x in range(10))
            for y in range(8)
        ]
        return {
            "id": "room_001",
            "coord": [0, 0],
            "layout": layout,
            "spawns": {"default": list(spawn)},
            "default_spawn": "default",
            "objects": objects,
            "dynamic_objects": dynamic_objects,
            "exits": exits,
        }


def _connected(walls: set[tuple[int, int]], spawn: tuple[int, int]) -> bool:
    seen = {spawn}
    queue = deque([spawn])
    while queue:
        x, y = queue.popleft()
        for nx, ny in ((x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y)):
            if 0 <= nx < 10 and 0 <= ny < 8 and (nx, ny) not in walls \
                    and (nx, ny) not in seen:
                seen.add((nx, ny))
                queue.append((nx, ny))
    floor = 80 - len(walls)
    return len(seen) >= floor * 0.9


def write_variant_map(room: dict, root: Path, index: int) -> Path:
    map_dir = root / f"variant_{index:03d}"
    map_dir.mkdir(parents=True, exist_ok=True)
    (map_dir / "room_001.json").write_text(json.dumps(room, indent=1), "utf-8")
    return map_dir / "room_001.json"


# ---------------------------------------------------------------------------
# Sample collection
# ---------------------------------------------------------------------------


class Writer:
    def __init__(self, out: Path) -> None:
        self.out = out
        (out / "images").mkdir(parents=True, exist_ok=True)
        self.records: list[dict] = []
        self.seen_labels: dict[str, int] = {}

    def add(self, frame: np.ndarray, label: str, source: str) -> None:
        # Cap near-duplicate states (identical label text) per source.
        count = self.seen_labels.get(label, 0)
        if count >= 2:
            return
        self.seen_labels[label] = count + 1
        name = f"{source}_{len(self.records):06d}.png"
        Image.fromarray(frame).save(self.out / "images" / name)
        self.records.append({"image": f"images/{name}", "label": label, "source": source})

    def flush(self, heldout_sources: set[str]) -> None:
        train = [r for r in self.records if r["source"] not in heldout_sources]
        heldout = [r for r in self.records if r["source"] in heldout_sources]
        for filename, rows in (("train.jsonl", train), ("heldout.jsonl", heldout)):
            with (self.out / filename).open("w", encoding="utf-8") as fh:
                for row in rows:
                    fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        print(f"wrote {len(train)} train / {len(heldout)} heldout samples to {self.out}")


def random_walk(env, writer: Writer, source: str, steps: int,
                rng: random.Random, sample_every: int = 11) -> None:
    env.reset(seed=rng.randint(0, 10**6))
    direction = rng.choice(MOVE_ACTIONS)
    for step in range(steps):
        roll = rng.random()
        if roll < 0.06:
            action = ACTION_A
        elif roll < 0.09:
            action = ACTION_B
        else:
            if roll > 0.9 or step % rng.randint(9, 25) == 0:
                direction = rng.choice(MOVE_ACTIONS)
            action = direction
        obs, _, terminated, truncated, _ = env.step(action)
        if step % sample_every == 0:
            writer.add(obs, oracle_state(env).to_text(), source)
        if terminated or truncated:
            env.reset(seed=rng.randint(0, 10**6))


def policy_episode(env, writer: Writer, source: str, task_id: str,
                   seed: int, sample_every: int = 7) -> None:
    from ..agent import OracleGrounding, Policy

    policy = Policy(backend=OracleGrounding(env), prefer_induced=False)
    policy.reset(seed=seed, task_id=task_id)
    obs, info = env.reset(seed=seed)
    terminated = truncated = False
    step = 0
    while not (terminated or truncated):
        action = policy.act(obs, info)
        obs, _, terminated, truncated, info = env.step(action)
        step += 1
        if step % sample_every == 0:
            writer.add(obs, oracle_state(env).to_text(), source)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=Path("data/grounding"))
    parser.add_argument("--task-episodes", type=int, default=3)
    parser.add_argument("--variant-maps", type=int, default=60)
    parser.add_argument("--walk-steps", type=int, default=700)
    parser.add_argument("--unique-maps", type=int, default=0,
                        help="additionally: N single-use layouts with ~3 "
                             "samples each — forces true visual reading of "
                             "the grid instead of layout memorization")
    parser.add_argument("--seed", type=int, default=7)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    writer = Writer(args.out)
    heldout_sources: set[str] = set()

    for task_id in TASKS:
        short = task_id.rsplit("_", 1)[-1]
        for episode in range(args.task_episodes):
            env = make_env(task_id=task_id, observation_mode="pixels")
            try:
                policy_episode(env, writer, f"task{short}", task_id, seed=episode)
            finally:
                env.close()
        env = make_env(task_id=task_id, observation_mode="pixels")
        try:
            random_walk(env, writer, f"task{short}walk", args.walk_steps, rng)
        finally:
            env.close()
        print(f"{task_id}: {len(writer.records)} samples so far")

    maps_root = args.out / "variant_maps"
    for index in range(args.variant_maps):
        room = make_variant_room(rng)
        map_path = write_variant_map(room, maps_root, index)
        source = f"variant{index:03d}"
        if index % 5 == 0:
            heldout_sources.add(source)   # unseen layouts for eval
        env = make_env(
            map_path=map_path,
            reward_id="mathematical_logic/task_1",
            observation_mode="pixels",
            max_steps=10**6,
        )
        try:
            random_walk(env, writer, source, args.walk_steps, rng)
        finally:
            env.close()
        if index % 10 == 0:
            print(f"variant {index}: {len(writer.records)} samples so far")

    for index in range(args.unique_maps):
        room = make_variant_room(rng)
        map_path = write_variant_map(room, maps_root / "unique", index)
        source = f"u{index:04d}"
        if index % 20 == 0:
            heldout_sources.add(source)
        env = make_env(
            map_path=map_path,
            reward_id="mathematical_logic/task_1",
            observation_mode="pixels",
            max_steps=10**6,
        )
        try:
            random_walk(env, writer, source, steps=37, rng=rng, sample_every=12)
        finally:
            env.close()
        if index % 250 == 0:
            print(f"unique {index}: {len(writer.records)} samples so far")

    writer.flush(heldout_sources)


if __name__ == "__main__":
    main()

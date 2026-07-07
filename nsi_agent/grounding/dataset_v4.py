"""v4 grounding dataset: state-flip supplements + label hygiene.

v3b's persistent misperceptions traced to two data defects:

- the 1503-sample abyss supplement (and ~10% of v3 rows) predate the
  oracle visibility fix, so pixel-invisible doors (both boundary tiles
  under active abyss) carry exit labels — training the model to *guess*
  doors it cannot see (phantom exits, south-door noise);
- opened locked_key doors are barely represented, so the model keeps
  reporting "locked"/"conditional" after the engine opened them
  (task_4 lever ping-pong).

This module fixes both:

1. ``--relabel``      textual cleanup of old jsonl rows: any exit whose
                      two door tiles both read 'A' in the GRID is
                      relabeled "-" (exactly the current oracle rule);
2. flip-variant rooms unique layouts with locked_key doors captured
                      before/after ``ExitRuntimeState.opened`` flips;
3. abyss-door matrix  ab2-style abyss rooms regenerated under the
                      visibility-aligned oracle, plus opened-lock and
                      partial-coverage (one-tile-visible) combos;
4. course-map sweeps  oracle-policy episodes on the five task maps that
                      pause to mutate exits/chests/buttons/levers/bridge
                      states in place (with exact restore + oracle-text
                      assertion), so mid-episode room states the agent
                      actually encounters are densely represented.

    python -m nsi_agent.grounding.dataset_v4 --out data/grounding_v4 \
        --flip-rooms 700 --abyss-rooms 400
    python -m nsi_agent.grounding.dataset_v4 --relabel-in old.jsonl \
        --relabel-out new.jsonl --image-prefix /root/autodl-tmp/data/grounding_v3
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

from nesylink.env import make_env

from ..constants import MOVE_ACTIONS
from .dataset import TASKS, Writer, make_variant_room, random_walk, write_variant_map
from .oracle import oracle_state
from .schema import FACINGS

TILE = 16
DOOR_TILES = {
    "north": ((4, 0), (5, 0)),
    "south": ((4, 7), (5, 7)),
    "west": ((0, 3), (0, 4)),
    "east": ((9, 3), (9, 4)),
}
_SHORT = {"N": "north", "S": "south", "W": "west", "E": "east"}


# ---------------------------------------------------------------------------
# Label hygiene: fix pre-visibility-fix exit labels textually
# ---------------------------------------------------------------------------


def relabel_text(label: str) -> str:
    """Blank exit directions whose both door tiles show active abyss.

    Grid 'A' is painted exactly when an active, un-bridged abyss trap sits
    on the tile — the same predicate the current oracle uses to drop
    pixel-invisible exits — so this text rule reproduces its output.
    """
    lines = label.splitlines()
    grid = lines[1:9]
    if len(lines) < 10 or lines[0] != "GRID" or not lines[-1].startswith("EXITS"):
        return label
    tokens = []
    for token in lines[-1].split()[1:]:
        short, state = token.split(":", 1)
        direction = _SHORT.get(short.upper())
        if direction and state != "-":
            if all(grid[y][x] == "A" for x, y in DOOR_TILES[direction]):
                state = "-"
        tokens.append(f"{short}:{state}")
    lines[-1] = "EXITS " + " ".join(tokens)
    return "\n".join(lines)


def relabel_jsonl(src: Path, dst: Path, image_prefix: str | None) -> None:
    changed = total = 0
    with dst.open("w", encoding="utf-8") as out:
        for line in src.read_text("utf-8").splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            total += 1
            fixed = relabel_text(row["label"])
            if fixed != row["label"]:
                changed += 1
                row["label"] = fixed
            if image_prefix and not row["image"].startswith("/"):
                row["image"] = f"{image_prefix}/{row['image']}"
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
    print(f"{src} -> {dst}: relabeled {changed}/{total} rows")


# ---------------------------------------------------------------------------
# Shared capture helpers (no env.step — rendering is pure in runtime state)
# ---------------------------------------------------------------------------


def capture(env, writer: Writer, source: str) -> None:
    writer.add(env.unwrapped._get_obs(), oracle_state(env).to_text(), source)


def free_tiles(room) -> list[tuple[int, int]]:
    """Teleport candidates: walkable, hazard-free, off door tiles (a player
    sprite parked on a boundary door tile would occlude the door state we
    are trying to supervise)."""
    blocked = room.runtime_blocking_tiles()
    door_tiles = {tile for c in room.exits for tile in c.tiles}
    tiles = [
        (x, y)
        for x in range(room.width)
        for y in range(room.height)
        if (x, y) not in blocked and room.trap_at((x, y)) is None
    ]
    clear = [t for t in tiles if t not in door_tiles]
    return clear or tiles


def teleport(env, tile: tuple[int, int], facing: str) -> None:
    player = env.unwrapped.engine.runtime.player
    player.position_px = (tile[0] * float(TILE), tile[1] * float(TILE))
    player.facing = facing


def open_exit(room, exit_config) -> None:
    state = room.exit_state(exit_config)
    state.unlocked = True
    state.opened = True


# ---------------------------------------------------------------------------
# 2. Flip-variant rooms: locked_key doors before/after opening
# ---------------------------------------------------------------------------


def make_locked_room(rng: random.Random) -> dict:
    room = make_variant_room(rng)
    directions = ["north", "south", "west", "east"]
    rng.shuffle(directions)
    exits = []
    for index, direction in enumerate(directions[: rng.randint(2, 4)]):
        if index == 0 or rng.random() < 0.5:
            exit_type = "locked_key"
        else:
            exit_type = rng.choice(("normal", "conditional"))
        entry = {
            "id": f"{direction}_exit", "direction": direction,
            "target_room": "room_001", "target_entry": "default",
            "type": exit_type,
        }
        if exit_type == "locked_key":
            entry["requires"] = {"key_count": 1, "consume_key": False}
        elif exit_type == "conditional":
            entry["requires"] = {"all_monsters_defeated": True}
        exits.append(entry)
    room["exits"] = exits
    return room


def gen_flip_variants(writer: Writer, maps_root: Path, count: int,
                      rng: random.Random, heldout: set[str]) -> None:
    for index in range(count):
        room_dict = make_locked_room(rng)
        map_path = write_variant_map(room_dict, maps_root, index)
        source = f"flip{index:04d}"
        if index % 20 == 0:
            heldout.add(source)
        env = make_env(
            map_path=map_path,
            reward_id="mathematical_logic/task_1",
            observation_mode="pixels",
            max_steps=10**6,
        )
        try:
            env.reset(seed=rng.randint(0, 10**6))
            for _ in range(rng.randint(2, 7)):
                env.step(rng.choice(MOVE_ACTIONS))
            room = env.unwrapped.engine.runtime.room
            locked = [c for c in room.exits if c.exit_type == "locked_key"]
            floors = free_tiles(room)
            capture(env, writer, source)                       # all locked
            rng.shuffle(locked)
            for exit_config in locked:                         # open one by one
                open_exit(room, exit_config)
                near = min(
                    floors,
                    key=lambda t: min(
                        abs(t[0] - dx) + abs(t[1] - dy)
                        for dx, dy in exit_config.tiles
                    ),
                )
                teleport(env, near, rng.choice(FACINGS))
                capture(env, writer, source)
            teleport(env, rng.choice(floors), rng.choice(FACINGS))
            capture(env, writer, source)                       # all open, afar
        finally:
            env.close()
        if index % 100 == 0:
            print(f"flip {index}: {len(writer.records)} samples")


# ---------------------------------------------------------------------------
# 3. Abyss-door matrix: doors over abyss / bridge / partial coverage
# ---------------------------------------------------------------------------

_ARMS = {
    "north": [(x, y) for y in range(0, 3) for x in (4, 5)],
    "south": [(x, y) for y in range(5, 8) for x in (4, 5)],
    "east": [(x, y) for x in range(6, 10) for y in (3, 4)],
}


def make_abyss_room_v4(rng: random.Random) -> dict:
    horiz = [(x, y) for y in (3, 4) for x in range(0, rng.randint(6, 10))]
    arms = [d for d in _ARMS if rng.random() < 0.4]
    bridge_tiles = list(dict.fromkeys(
        horiz + [t for d in arms for t in _ARMS[d]]
    ))

    # Abyss everywhere except an optional clear patch that leaves one door
    # half- or fully visible without any bridge (partial-coverage case).
    abyss = {(x, y) for x in range(10) for y in range(8)}
    patch_dir = rng.choice((None, None, "north", "south", "west", "east"))
    if patch_dir:
        door = DOOR_TILES[patch_dir]
        keep = door if rng.random() < 0.5 else door[:1]
        for tile in keep:
            abyss.discard(tile)

    spawn = rng.choice(bridge_tiles)
    objects = [{
        "id": "abyss_all", "kind": "trap", "trap_type": "abyss", "damage": 1,
        "respawn_delay_steps": 2,
        "tiles": [list(t) for t in sorted(abyss)],
    }]
    if rng.random() < 0.3:
        chest_tile = rng.choice(bridge_tiles)
        if chest_tile != spawn:
            objects.append({
                "id": "c0", "kind": "chest", "pos": list(chest_tile),
                "loot": {"kind": rng.choice(["gold", "key", "heal"])},
            })
    exits = []
    for direction in ("north", "south", "west", "east"):
        if rng.random() < 0.8:
            exit_type = rng.choice(("normal", "locked_key", "conditional"))
            entry = {
                "id": f"{direction}_e", "direction": direction,
                "target_room": "room_001", "target_entry": "default",
                "type": exit_type,
            }
            if exit_type == "locked_key":
                entry["requires"] = {"key_count": 1, "consume_key": False}
            elif exit_type == "conditional":
                entry["requires"] = {"all_monsters_defeated": True}
            exits.append(entry)
    return {
        "id": "room_001", "coord": [0, 0], "layout": ["." * 10] * 8,
        "spawns": {"default": list(spawn)}, "default_spawn": "default",
        "objects": objects,
        "dynamic_objects": [{
            "id": "bridge", "kind": "rotating_bridge",
            "initial_state": "a", "background_tile": "none",
            "active_tile": "bridge",
            "states": {"a": {"tiles": [list(t) for t in bridge_tiles]}},
        }],
        "exits": exits,
    }


def gen_abyss_matrix(writer: Writer, maps_root: Path, count: int,
                     rng: random.Random, heldout: set[str]) -> None:
    for index in range(count):
        room_dict = make_abyss_room_v4(rng)
        map_path = write_variant_map(room_dict, maps_root, index)
        source = f"abx{index:04d}"
        if index % 20 == 0:
            heldout.add(source)
        env = make_env(
            map_path=map_path,
            reward_id="mathematical_logic/task_1",
            observation_mode="pixels",
            max_steps=10**6,
        )
        try:
            env.reset(seed=rng.randint(0, 10**6))
            room = env.unwrapped.engine.runtime.room
            floors = free_tiles(room)   # bridge + clear-patch tiles
            capture(env, writer, source)
            for _ in range(2):
                teleport(env, rng.choice(floors), rng.choice(FACINGS))
                capture(env, writer, source)
            locked = [c for c in room.exits if c.exit_type == "locked_key"]
            if locked and rng.random() < 0.6:
                for exit_config in locked:
                    open_exit(room, exit_config)
                teleport(env, rng.choice(floors), rng.choice(FACINGS))
                capture(env, writer, source)                   # open over abyss
        finally:
            env.close()
        if index % 100 == 0:
            print(f"abx {index}: {len(writer.records)} samples")


# ---------------------------------------------------------------------------
# 4. Course-map sweeps: mutate real task rooms in place, capture, restore
# ---------------------------------------------------------------------------


def sweep_room(env, writer: Writer, source: str, rng: random.Random) -> None:
    runtime = env.unwrapped.engine.runtime
    room, player = runtime.room, runtime.player
    before = oracle_state(env).to_text()

    saved_exits = {
        c.exit_id: (room.exit_state(c).unlocked, room.exit_state(c).opened)
        for c in room.exits
    }
    saved_chests = {cid: c.is_open for cid, c in room.chests.items()}
    saved_buttons = {bid: b.is_pressed for bid, b in room.buttons.items()}
    saved_switches = {sid: s.is_pressed for sid, s in room.switches.items()}
    saved_dynamic = dict(room.dynamic_states)
    saved_player = (player.position_px, player.facing)

    floors = free_tiles(room)

    def snap() -> None:
        capture(env, writer, source)

    # a) open each closed locked door, player teleported next to it
    closed = [
        c for c in room.exits
        if c.exit_type == "locked_key" and not room.exit_state(c).opened
    ]
    for exit_config in closed:
        open_exit(room, exit_config)
        if floors:
            near = min(
                floors,
                key=lambda t: min(
                    abs(t[0] - dx) + abs(t[1] - dy)
                    for dx, dy in exit_config.tiles
                ),
            )
            teleport(env, near, rng.choice(FACINGS))
        snap()

    # b) bridge states x (locked doors already opened above)
    for target, dynamic_object in room.dynamic_objects.items():
        states = list(dynamic_object.states)
        current = room.dynamic_states.get(target, dynamic_object.initial_state)
        for state_name in states:
            if state_name == current:
                continue
            room.set_dynamic_state(target, state_name)
            if floors:
                teleport(env, rng.choice(floors), rng.choice(FACINGS))
            snap()

    # c) open closed chests + press buttons/levers (late-game look)
    mutated = False
    for chest in room.chests.values():
        if chest.is_visible and not chest.is_open:
            chest.is_open = True
            mutated = True
    for button in room.buttons.values():
        button.is_pressed = not button.is_pressed
        mutated = True
    for switch in room.switches.values():
        switch.is_pressed = not switch.is_pressed
        mutated = True
    if mutated:
        snap()

    # restore exactly
    for exit_config in room.exits:
        state = room.exit_state(exit_config)
        state.unlocked, state.opened = saved_exits[exit_config.exit_id]
    for cid, was_open in saved_chests.items():
        room.chests[cid].is_open = was_open
    for bid, pressed in saved_buttons.items():
        room.buttons[bid].is_pressed = pressed
    for sid, pressed in saved_switches.items():
        room.switches[sid].is_pressed = pressed
    for target, state_name in saved_dynamic.items():
        if room.dynamic_states.get(target) != state_name:
            room.set_dynamic_state(target, state_name)
    player.position_px, player.facing = saved_player

    after = oracle_state(env).to_text()
    if after != before:
        raise RuntimeError(
            f"sweep restore mismatch in {room.room_id}:\n{before}\n---\n{after}"
        )


def gen_task_sweeps(writer: Writer, rng: random.Random,
                    sweep_every: int = 50) -> None:
    from ..agent import OracleGrounding, Policy

    plans = [(task_id, 0, sweep_every) for task_id in TASKS]
    plans.append(("mathematical_logic/task_4", 1, 30))   # densest on task_4
    for task_id, seed, every in plans:
        short = task_id.rsplit("_", 1)[-1]
        source = f"sweep{short}s{seed}"
        env = make_env(task_id=task_id, observation_mode="pixels")
        try:
            policy = Policy(backend=OracleGrounding(env), prefer_induced=False)
            policy.reset(seed=seed, task_id=task_id)
            obs, info = env.reset(seed=seed)
            terminated = truncated = False
            step = 0
            last_room = None
            while not (terminated or truncated):
                runtime = env.unwrapped.engine.runtime
                room_id = runtime.room.room_id
                if room_id != last_room or step % every == 0:
                    sweep_room(env, writer, source, rng)
                    last_room = room_id
                action = policy.act(obs, info)
                obs, _, terminated, truncated, info = env.step(action)
                step += 1
        finally:
            env.close()
        print(f"{source}: {len(writer.records)} samples")


# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=Path("data/grounding_v4"))
    parser.add_argument("--flip-rooms", type=int, default=700)
    parser.add_argument("--abyss-rooms", type=int, default=400)
    parser.add_argument("--sweep-every", type=int, default=50)
    parser.add_argument("--seed", type=int, default=41)
    parser.add_argument("--relabel-in", type=Path, default=None)
    parser.add_argument("--relabel-out", type=Path, default=None)
    parser.add_argument("--image-prefix", type=str, default=None)
    args = parser.parse_args()

    if args.relabel_in:
        relabel_jsonl(args.relabel_in, args.relabel_out, args.image_prefix)
        return

    rng = random.Random(args.seed)
    writer = Writer(args.out)
    heldout: set[str] = set()
    gen_task_sweeps(writer, rng, args.sweep_every)
    gen_flip_variants(writer, args.out / "flip_maps", args.flip_rooms, rng, heldout)
    gen_abyss_matrix(writer, args.out / "abyss_maps", args.abyss_rooms, rng, heldout)
    writer.flush(heldout)


if __name__ == "__main__":
    main()

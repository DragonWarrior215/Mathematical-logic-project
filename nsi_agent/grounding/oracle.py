"""Oracle grounding: build a SymbolicState from engine internals.

DEBUG / TRAINING ONLY. This module reads environment internals and therefore
must never sit on the inference path of a submitted policy. It exists to:

- generate (frame, label) pairs for VLM fine-tuning (``dataset.py``),
- record demonstration traces for the NSI induction pipeline,
- debug the symbolic layer independently of VLM accuracy.

It emits exactly what a perfect grounding module would perceive from pixels:
hidden chests are excluded, conditional doors stay "conditional" (their
satisfaction is not observable), and coordinates are pixel-precise.
"""

from __future__ import annotations

from . import schema
from .schema import Monster, SymbolicState


def oracle_state(env) -> SymbolicState:
    """Extract the symbolic state of the current room from a gym env."""
    runtime = env.unwrapped.engine.runtime
    return state_from_runtime(runtime.room, runtime.player)


def state_from_runtime(room, player) -> SymbolicState:
    grid = [[schema.TILE_FLOOR] * room.width for _ in range(room.height)]

    def put(pos, cls) -> None:
        x, y = pos
        if 0 <= x < room.width and 0 <= y < room.height:
            grid[y][x] = cls

    for pos in room.walls:
        put(pos, schema.TILE_WALL)

    for pos, kind in room.dynamic_tiles.items():
        put(pos, schema.TILE_BRIDGE if kind == "bridge" else schema.TILE_GAP)

    for trap in room.traps.values():
        if not trap.is_active or room.dynamic_tiles.get(trap.pos) == "bridge":
            continue
        put(trap.pos, schema.TILE_ABYSS if trap.trap_type == "abyss" else schema.TILE_TRAP)

    for button in room.buttons.values():
        put(button.pos, schema.TILE_BUTTON_PRESSED if button.is_pressed else schema.TILE_BUTTON)

    for switch in room.switches.values():
        put(switch.pos, schema.TILE_SWITCH_ACTIVE if switch.is_pressed else schema.TILE_SWITCH)

    for npc in room.npcs.values():
        put(npc.pos, schema.TILE_NPC)

    loot_class = {
        "key": schema.TILE_CHEST_KEY,
        "gold": schema.TILE_CHEST_GOLD,
        "coin": schema.TILE_CHEST_GOLD,
        "heal": schema.TILE_CHEST_HEAL,
        "potion": schema.TILE_CHEST_HEAL,
        "heart": schema.TILE_CHEST_HEAL,
        "item": schema.TILE_CHEST_ITEM,
    }
    for chest in room.chests.values():
        if not chest.is_visible:
            continue
        if chest.is_open:
            put(chest.pos, schema.TILE_CHEST_OPEN)
        else:
            kind = str(chest.loot.get("kind", ""))
            put(chest.pos, loot_class.get(kind, schema.TILE_CHEST_UNKNOWN))

    exits: dict[str, str] = {}
    for exit_config in room.exits:
        # The renderer paints active abyss AFTER exits, so a door whose tiles
        # are covered by un-bridged abyss is pixel-invisible. The oracle must
        # label what a perfect *visual* grounder could see — the blind-probe
        # planner rule handles discovering such doors behaviorally.
        covered = all(
            room.trap_at(tile) is not None
            and room.trap_at(tile).trap_type == "abyss"
            for tile in exit_config.tiles
        )
        if covered:
            continue
        if exit_config.exit_type == "locked_key":
            opened = room.exit_state(exit_config).opened
            exits[exit_config.direction] = "open" if opened else "locked"
        elif exit_config.exit_type == "conditional":
            exits[exit_config.direction] = "conditional"
        else:
            exits[exit_config.direction] = "normal"

    monsters = tuple(
        Monster(
            kind=monster.monster_type,
            px=(int(round(monster.position_px[0])), int(round(monster.position_px[1]))),
        )
        for monster in room.monsters.values()
    )

    facing = getattr(player, "action_facing", None) or player.facing
    if facing not in schema.FACINGS:
        facing = "down"

    return SymbolicState(
        grid=tuple("".join(row) for row in grid),
        player_px=(int(round(player.position_px[0])), int(round(player.position_px[1]))),
        facing=facing,
        monsters=monsters,
        exits=exits,
    )

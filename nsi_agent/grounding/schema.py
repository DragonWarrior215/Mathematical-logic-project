"""Symbolic-state schema shared by the VLM grounding, oracle, tracker and DSL.

The state is intentionally compact so a 3B VLM can emit it in ~150 tokens:

    GRID
    ##########
    ..........   (8 rows of 10 chars, row 0 = top)
    PLAYER 64,96 up
    MONSTERS chaser:32,32 patroller:96,80
    EXITS N:- S:normal W:locked E:-

Tile classes (one char per tile, static/interactive world only — the player
and monsters are pixel-precise fields, not grid cells):

    .  floor                          T  spike trap
    #  wall                           A  abyss
    K  closed chest (key loot)        _  gap
    G  closed chest (gold loot)       =  bridge
    H  closed chest (heal loot)       b  button (not pressed)
    S  closed chest (item/sword)      B  button (pressed)
    C  closed chest (unknown loot)    L  switch / lever (idle)
    O  opened chest                   l  switch / lever (activated)
    N  npc

Exit states: ``-`` no exit, ``normal`` open passage, ``locked`` key door,
``conditional`` conditional door, ``open`` a previously locked/conditional
door now open.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field, replace

from ..constants import GRID_H, GRID_W, MAP_H_PX, MAP_W_PX, TILE_SIZE

TILE_FLOOR = "."
TILE_WALL = "#"
TILE_CHEST_KEY = "K"
TILE_CHEST_GOLD = "G"
TILE_CHEST_HEAL = "H"
TILE_CHEST_ITEM = "S"
TILE_CHEST_UNKNOWN = "C"
TILE_CHEST_OPEN = "O"
TILE_TRAP = "T"
TILE_ABYSS = "A"
TILE_GAP = "_"
TILE_BRIDGE = "="
TILE_BUTTON = "b"
TILE_BUTTON_PRESSED = "B"
TILE_SWITCH = "L"
TILE_SWITCH_ACTIVE = "l"
TILE_NPC = "N"

TILE_CLASSES = (
    TILE_FLOOR, TILE_WALL,
    TILE_CHEST_KEY, TILE_CHEST_GOLD, TILE_CHEST_HEAL, TILE_CHEST_ITEM,
    TILE_CHEST_UNKNOWN, TILE_CHEST_OPEN,
    TILE_TRAP, TILE_ABYSS, TILE_GAP, TILE_BRIDGE,
    TILE_BUTTON, TILE_BUTTON_PRESSED,
    TILE_SWITCH, TILE_SWITCH_ACTIVE,
    TILE_NPC,
)

CLOSED_CHEST_TILES = frozenset({
    TILE_CHEST_KEY, TILE_CHEST_GOLD, TILE_CHEST_HEAL,
    TILE_CHEST_ITEM, TILE_CHEST_UNKNOWN,
})
CHEST_TILES = CLOSED_CHEST_TILES | {TILE_CHEST_OPEN}

# Tiles the engine treats as hard collision blockers for movement.
BLOCKING_TILES = frozenset({TILE_WALL, TILE_NPC, TILE_GAP}) | CHEST_TILES

# Walkable but damaging — the planner must avoid them.
HAZARD_TILES = frozenset({TILE_TRAP, TILE_ABYSS})

EXIT_STATES = ("-", "normal", "locked", "conditional", "open")
EXIT_DIRS = ("north", "south", "west", "east")
_EXIT_SHORT = {"north": "N", "south": "S", "west": "W", "east": "E"}

MONSTER_TYPES = ("chaser", "patroller", "ambusher")

FACINGS = ("up", "down", "left", "right")


@dataclass(frozen=True)
class Monster:
    kind: str                 # one of MONSTER_TYPES
    px: tuple[int, int]       # top-left pixel position

    @property
    def tile(self) -> tuple[int, int]:
        return ((self.px[0] + TILE_SIZE // 2) // TILE_SIZE,
                (self.px[1] + TILE_SIZE // 2) // TILE_SIZE)


@dataclass(frozen=True)
class SymbolicState:
    """One room's symbolic snapshot — the output of the grounding module."""

    grid: tuple[str, ...]                     # GRID_H strings of GRID_W chars
    player_px: tuple[int, int]                # top-left pixel position
    facing: str                               # one of FACINGS
    monsters: tuple[Monster, ...] = ()
    exits: dict[str, str] = field(default_factory=dict)  # dir -> exit state

    # -- derived helpers -------------------------------------------------

    @property
    def player_tile(self) -> tuple[int, int]:
        return ((self.player_px[0] + TILE_SIZE // 2) // TILE_SIZE,
                (self.player_px[1] + TILE_SIZE // 2) // TILE_SIZE)

    def tile(self, x: int, y: int) -> str:
        if 0 <= x < GRID_W and 0 <= y < GRID_H:
            return self.grid[y][x]
        return TILE_WALL

    def tiles_of(self, *classes: str) -> list[tuple[int, int]]:
        wanted = set(classes)
        return [
            (x, y)
            for y in range(GRID_H)
            for x in range(GRID_W)
            if self.grid[y][x] in wanted
        ]

    def closed_chests(self) -> list[tuple[int, int]]:
        return self.tiles_of(*CLOSED_CHEST_TILES)

    def is_blocking(self, x: int, y: int) -> bool:
        return self.tile(x, y) in BLOCKING_TILES

    def is_hazard(self, x: int, y: int) -> bool:
        return self.tile(x, y) in HAZARD_TILES

    def exit_state(self, direction: str) -> str:
        return self.exits.get(direction, "-")

    def with_tile(self, x: int, y: int, cls: str) -> "SymbolicState":
        rows = list(self.grid)
        rows[y] = rows[y][:x] + cls + rows[y][x + 1:]
        return replace(self, grid=tuple(rows))

    # -- serialization ---------------------------------------------------

    def to_text(self) -> str:
        monsters = " ".join(f"{m.kind}:{m.px[0]},{m.px[1]}" for m in self.monsters)
        exits = " ".join(
            f"{_EXIT_SHORT[d]}:{self.exits.get(d, '-')}" for d in EXIT_DIRS
        )
        return (
            "GRID\n"
            + "\n".join(self.grid)
            + f"\nPLAYER {self.player_px[0]},{self.player_px[1]} {self.facing}"
            + f"\nMONSTERS {monsters}".rstrip()
            + f"\nEXITS {exits}"
        )

    @classmethod
    def from_text(cls, text: str) -> "SymbolicState":
        """Parse the compact format, tolerating minor VLM formatting noise."""
        lines = [ln.strip() for ln in text.strip().splitlines() if ln.strip()]
        grid: list[str] = []
        player_px = (0, 0)
        facing = "down"
        monsters: list[Monster] = []
        exits: dict[str, str] = {}

        for ln in lines:
            upper = ln.upper()
            if upper == "GRID":
                continue
            if upper.startswith("PLAYER"):
                match = re.search(r"(-?\d+)\s*,\s*(-?\d+)\s*(\w+)?", ln)
                if match:
                    player_px = (
                        _clamp(int(match.group(1)), 0, MAP_W_PX - TILE_SIZE),
                        _clamp(int(match.group(2)), 0, MAP_H_PX - TILE_SIZE),
                    )
                    raw_facing = (match.group(3) or "down").lower()
                    facing = raw_facing if raw_facing in FACINGS else "down"
                continue
            if upper.startswith("MONSTERS"):
                for kind, mx, my in re.findall(r"(\w+)\s*:\s*(-?\d+)\s*,\s*(-?\d+)", ln):
                    kind = kind.lower()
                    if kind in MONSTER_TYPES:
                        monsters.append(Monster(
                            kind,
                            (
                                _clamp(int(mx), 0, MAP_W_PX - TILE_SIZE),
                                _clamp(int(my), 0, MAP_H_PX - TILE_SIZE),
                            ),
                        ))
                continue
            if upper.startswith("EXITS"):
                for short, state in re.findall(r"([NSWE])\s*:\s*([\w-]+)", ln):
                    direction = {v: k for k, v in _EXIT_SHORT.items()}[short.upper()]
                    state = state.lower()
                    exits[direction] = state if state in EXIT_STATES else "-"
                continue
            # Otherwise: candidate grid row. Tolerate length drift in VLM
            # output: pad/trim to GRID_W. Uniform rows (e.g. an all-bridge
            # "======" the LM abbreviated) are padded with their own char.
            row = "".join(ch for ch in ln if ch in TILE_CLASSES)
            if 4 <= len(row) <= GRID_W + 6 and len(grid) < GRID_H:
                pad = row[-1] if len(set(row)) == 1 else TILE_FLOOR
                row = row[:GRID_W].ljust(GRID_W, pad)
                grid.append(row)

        if len(grid) != GRID_H:
            raise ValueError(
                f"grid has {len(grid)} valid rows, expected {GRID_H}:\n{text}"
            )
        return cls(
            grid=tuple(grid),
            player_px=player_px,
            facing=facing,
            monsters=tuple(monsters),
            exits=exits,
        )


def _clamp(value: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, value))

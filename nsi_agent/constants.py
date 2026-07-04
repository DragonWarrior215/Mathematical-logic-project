"""Self-contained constants for the NSI agent.

Deliberately duplicated from ``nesylink.core.constants`` so the inference-time
agent never imports environment internals. Values describe the *public* game
interface (action ids, geometry) documented in the assignment handout.
"""

from __future__ import annotations

ACTION_NOOP = 0
ACTION_UP = 1
ACTION_DOWN = 2
ACTION_LEFT = 3
ACTION_RIGHT = 4
ACTION_A = 5
ACTION_B = 6

MOVE_ACTIONS = (ACTION_UP, ACTION_DOWN, ACTION_LEFT, ACTION_RIGHT)

ACTION_NAMES = {
    ACTION_NOOP: "WAIT",
    ACTION_UP: "UP",
    ACTION_DOWN: "DOWN",
    ACTION_LEFT: "LEFT",
    ACTION_RIGHT: "RIGHT",
    ACTION_A: "BUTTON_A",
    ACTION_B: "BUTTON_B",
}

TILE_SIZE = 16
GRID_W = 10
GRID_H = 8
MAP_W_PX = GRID_W * TILE_SIZE   # 160
MAP_H_PX = GRID_H * TILE_SIZE   # 128

PLAYER_SPEED_PX = 1.0
MONSTER_SPEED_PX = 0.5
MONSTER_STUN_TICKS = 60
SWORD_SWING_TICKS = 6
PLAYER_MAX_HP = 5

DIRECTIONS = ("up", "down", "left", "right")

DIR_VECTORS = {
    "up": (0, -1),
    "down": (0, 1),
    "left": (-1, 0),
    "right": (1, 0),
}

MOVE_ACTION_TO_DIR = {
    ACTION_UP: "up",
    ACTION_DOWN: "down",
    ACTION_LEFT: "left",
    ACTION_RIGHT: "right",
}

DIR_TO_MOVE_ACTION = {v: k for k, v in MOVE_ACTION_TO_DIR.items()}

# Exit tiles are fixed per direction by the engine's room schema.
EXIT_TILES = {
    "north": ((4, 0), (5, 0)),
    "south": ((4, 7), (5, 7)),
    "west": ((0, 3), (0, 4)),
    "east": ((9, 3), (9, 4)),
}

OPPOSITE_DIR = {"north": "south", "south": "north", "west": "east", "east": "west"}

# Room-coordinate delta when passing through an exit in a given direction.
EXIT_DELTA = {"north": (0, -1), "south": (0, 1), "west": (-1, 0), "east": (1, 0)}

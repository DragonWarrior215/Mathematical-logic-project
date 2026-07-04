"""Shared prompt/format definitions for the VLM grounding model."""

from __future__ import annotations

# Frames are upscaled with nearest-neighbor. Scale 3.5 maps the 160x128 frame
# to 560x448, so Qwen2.5-VL's 28px merged patches align EXACTLY with the 16px
# game tiles (each tile = 2x2 vision tokens) — a strong inductive bias for
# per-tile classification.
IMAGE_SCALE = 3.5

SYSTEM_PROMPT = (
    "You are the perception module of a game agent. The image is one room of "
    "a Zelda-like dungeon, a 10x8 grid of square tiles. Report the symbolic "
    "state EXACTLY in this format:\n"
    "GRID\n"
    "<8 rows of 10 characters, row 0 = top; per tile: . floor, # wall, "
    "K closed chest with key, G closed chest with gold, H closed chest with "
    "heal, S closed chest with item, C closed chest unknown, O opened chest, "
    "T spike trap, A abyss, _ gap, = bridge, b button up, B button pressed, "
    "L lever idle, l lever activated, N npc>\n"
    "PLAYER <x>,<y> <facing: up|down|left|right>\n"
    "MONSTERS <type>:<x>,<y> ... (chaser|patroller|ambusher; omit line content "
    "if none)\n"
    "EXITS N:<state> S:<state> W:<state> E:<state> (state: -, normal, locked, "
    "conditional, open)\n"
    "Coordinates are top-left pixels of the 16x16 sprite in the ORIGINAL "
    "160x128 frame (each tile is 16x16 there). The player and monsters are "
    "NOT part of the grid. Exit doors sit on boundary tiles N:(4,0),(5,0) "
    "S:(4,7),(5,7) W:(0,3),(0,4) E:(9,3),(9,4); report the underlying tile "
    "as floor. Output nothing else."
)

USER_PROMPT = "State?"

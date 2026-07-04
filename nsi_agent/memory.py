"""Cross-step / cross-room symbolic memory (the persistent part of Z).

Rooms are identified by odometry coordinates: the start room is (0, 0) and
passing through an exit in direction d shifts the coordinate by EXIT_DELTA[d].
This requires no map ground truth — only the agent's own transition history.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .constants import EXIT_DELTA, GRID_H, GRID_W, PLAYER_MAX_HP
from .grounding import schema
from .grounding.schema import SymbolicState

Coord = tuple[int, int]
Tile = tuple[int, int]


LEARNED_BLOCK_TTL = 300   # steps before a collision-inferred wall expires


@dataclass
class RoomMemory:
    coord: Coord
    state: SymbolicState | None = None          # last grounded snapshot
    learned_blocked: dict[Tile, int] = field(default_factory=dict)  # tile -> expiry step
    visited_exits: set[str] = field(default_factory=set)   # directions we used
    probed_dirs: set[str] = field(default_factory=set)     # blind probes tried
    failed_exits: dict[str, int] = field(default_factory=dict)  # dir -> fail count
    opened_chests: set[Tile] = field(default_factory=set)
    talked_npcs: set[Tile] = field(default_factory=set)
    switch_toggles: int = 0

    def known_exits(self) -> dict[str, str]:
        return dict(self.state.exits) if self.state else {}


@dataclass
class InventoryView:
    """The explicitly-allowed inventory information from the eval interface."""

    keys: int = 0
    gold: int = 0
    items: tuple[str, ...] = ()
    tools: tuple[str, ...] = ()
    equipped: dict[str, str] = field(default_factory=dict)

    @classmethod
    def from_info(cls, info: dict[str, Any]) -> "InventoryView":
        inv = info.get("inventory", {}) if isinstance(info, dict) else {}
        return cls(
            keys=int(inv.get("keys", 0)),
            gold=int(inv.get("gold", 0)),
            items=tuple(str(item) for item in inv.get("items", ())),
            tools=tuple(str(tool) for tool in inv.get("tools", ())),
            equipped={str(k): str(v) for k, v in dict(inv.get("equipped", {})).items()},
        )

    @property
    def has_sword(self) -> bool:
        return self.equipped.get("A") == "sword" or "sword" in self.tools

    @property
    def has_shield(self) -> bool:
        return self.equipped.get("B") == "shield" or "shield" in self.tools


class Memory:
    """Room graph + inventory + coarse HP estimate."""

    def __init__(self) -> None:
        self.rooms: dict[Coord, RoomMemory] = {}
        self.current_coord: Coord = (0, 0)
        self.inventory = InventoryView()
        self.hp_estimate: float = PLAYER_MAX_HP
        self.step_count: int = 0
        self.task_id: str | None = None

    # -- room bookkeeping ------------------------------------------------

    @property
    def room(self) -> RoomMemory:
        return self.rooms.setdefault(
            self.current_coord, RoomMemory(coord=self.current_coord)
        )

    @property
    def state(self) -> SymbolicState | None:
        return self.room.state

    def integrate_keyframe(self, state: SymbolicState) -> None:
        """Merge a fresh grounding snapshot into the current room's memory."""
        room = self.room
        room.state = state
        # Perception supersedes collision guesses for tiles it can classify;
        # keep only unexpired learned blocks that perception still calls floor
        # (these flag grounding mistakes discovered the hard way).
        room.learned_blocked = {
            tile: expiry
            for tile, expiry in room.learned_blocked.items()
            if state.tile(*tile) == schema.TILE_FLOOR and expiry > self.step_count
        }
        for tile in state.tiles_of(schema.TILE_CHEST_OPEN):
            room.opened_chests.add(tile)

    def transition(self, direction: str, new_state: SymbolicState | None = None) -> None:
        self.room.visited_exits.add(direction)
        dx, dy = EXIT_DELTA[direction]
        cx, cy = self.current_coord
        self.current_coord = (cx + dx, cy + dy)
        if new_state is not None:
            self.integrate_keyframe(new_state)

    def mark_blocked(self, tile: Tile) -> None:
        if 0 <= tile[0] < GRID_W and 0 <= tile[1] < GRID_H:
            self.room.learned_blocked[tile] = self.step_count + LEARNED_BLOCK_TTL

    # -- blocking / walkability queries used by the planner ---------------

    def is_blocking(self, x: int, y: int) -> bool:
        expiry = self.room.learned_blocked.get((x, y))
        if expiry is not None and expiry > self.step_count:
            return True
        state = self.state
        return state.is_blocking(x, y) if state else False

    def is_hazard(self, x: int, y: int) -> bool:
        state = self.state
        return state.is_hazard(x, y) if state else False

    # -- episode-level updates --------------------------------------------

    def on_step(self, info: dict[str, Any]) -> None:
        self.step_count += 1
        self.inventory = InventoryView.from_info(info)
        if self.task_id == "mathematical_logic/task_5" and self.step_count % 200 == 0:
            self.hp_estimate -= 1.0  # hidden periodic drain observed in training

    def note_damage(self, amount: float = 1.0) -> None:
        self.hp_estimate = max(0.0, self.hp_estimate - amount)

    def note_heal(self, amount: float = 1.0) -> None:
        self.hp_estimate = min(float(PLAYER_MAX_HP), self.hp_estimate + amount)

    def reset(self, task_id: str | None = None) -> None:
        self.rooms.clear()
        self.current_coord = (0, 0)
        self.inventory = InventoryView()
        self.hp_estimate = PLAYER_MAX_HP
        self.step_count = 0
        self.task_id = task_id

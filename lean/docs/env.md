# Lean Environment Formalization

## Purpose

This directory contains the Module 1 environment formalization for the
mathematical logic project. The goal of the Lean file is:

1. to abstract the Python game environment into explicit symbolic data types,
2. to define state transition functions that match the important environment
   rules as closely as possible,
3. to prove basic safety and consistency properties required by the assignment.

The main file is [EnvFormalization.lean](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/lean/EnvFormalization.lean:1).

## What Is Formalized

The current formalization covers the environment layer, not the policy layer.

### State space

- grid positions, directions, and the 7 environment actions
- loot, chests, traps, buttons, switches, NPCs, monsters, exits
- dynamic bridge objects with multiple states
- room state and multi-room world state
- player inventory, tools, equipped slot A / slot B
- task completion state through `environmentCompleted`

### Transition semantics

- tile-level movement and facing updates
- blocking by walls, visible chests, NPCs, and bridge gaps
- chest / NPC / switch interaction priority for `BUTTON_A`
- sword attack only when slot `A` is equipped with `sword`
- shield raise only when slot `B` is equipped with `shield`
- action duration, active shield state, and sword / shield action startup
- spike trap and abyss trap damage plus respawn behavior
- abyss control lock, delayed respawn, and respawn-tile selection priority
- button activation on stepping onto a tile
- dynamic bridge switching
- exit condition checking and room transitions
- step ordering aligned with the Python engine: action, transition, tile effects, monster update, monster contact
- symbolic monster AI for chaser / patroller / ambusher
- monster contact stun timing, defeat reward, monster-gated exit unlock, hidden chest reveal
- world completion by `complete_task` exit or by "all chests opened"

## Python Correspondence

The Lean model is matched against these Python modules:

- [constants.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/constants.py:1)
- [state.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/state.py:1)
- [schema.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/world/schema.py:1)
- [movement.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/mechanics/movement.py:1)
- [interactions.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/mechanics/interactions.py:1)
- [combat.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/mechanics/combat.py:1)
- [progress.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/mechanics/progress.py:1)
- [weapons.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/equipment/weapons.py:1)
- [defense.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/equipment/defense.py:1)
- [service.py](C:/Users/zhangw17/Documents/GitHub/Mathematical-logic-project/nesylink/core/equipment/service.py:1)

Key Lean definitions and their Python counterparts:

| Lean | Python |
|---|---|
| `Direction`, `Action` | action ids and move directions in `constants.py` |
| `RoomState`, `WorldState` | runtime state split across `state.py`, `schema.py`, engine runtime |
| `dynamicTileAt`, `trapAt?`, `isBlocking`, `canOccupy` | `schema.py` runtime blocking tiles and trap masking by bridge |
| `applyLoot` | `interactions.py: apply_loot` |
| `resolveSpikeTrap` | `interactions.py: resolve_spike_trap` |
| `resolveAbyssTrap` | `interactions.py: resolve_abyss_trap`, `find_abyss_respawn_tile` |
| `exitConditionSatisfied`, `applyExit`, `entrySpawnPos` | `movement.py: can_use_exit`, `apply_exit`, `entry_spawn_tile` |
| `applySwitchToggle` | `interactions.py: activate_switch` |
| `onMonsterKilled` | `combat.py: remove_defeated_monster` |
| `resolveMonsterContact` | `combat.py: resolve_monster_contact` |
| `allChestsOpened`, `goalReached` | `progress.py: all_chests_opened`, `engine.py` termination logic |

## Important Design Choices

The file aims to stay close to Python semantics while keeping the symbolic model
manageable for Module 1. The remaining abstractions are explicit.

1. Pixel movement is abstracted to tile movement.
   Python moves in pixels inside each 16x16 tile. Lean models one symbolic move
   as one tile transition.

2. Monster behavior is modeled symbolically at tile granularity.
   The Lean file now includes chaser / patroller / ambusher updates, stun
   timing, contact damage, sword damage, defeat reward, exit unlocking, and
   hidden-chest reveal. What is still abstracted away is pixel-level hitbox
   geometry, continuous collision response, and knockback.

3. Exit runtime state is folded into `Exit.unlocked`.
   This keeps the symbolic state compact while preserving the key door-opening
   behavior used by the Python environment.

4. Monster move periods are not modeled.
   Python throttles certain monster types (e.g. patrollers move every 2 steps
   via `monster_move_periods`). Lean lets all monsters move every step. This is
   a conservative over-approximation: any safety property proven in Lean holds
   a fortiori in Python where monsters are slower.

Because the assignment explicitly allows justified simplification as long as it
is documented, these abstractions should be stated honestly in the final report
instead of being described as literal byte-for-byte equivalence.

## Properties Already Proved

The file proves several basic environment properties required by Module 1:

- `inBounds_of_canOccupy`
  successful occupancy implies the tile is inside the legal map bounds

- `blocked_basicMove_keeps_player`
  if a target tile is illegal, the move does not change player position

- `free_basicMove_moves_player`
  if a target tile is legal, movement reaches exactly the facing tile

- `free_basicMove_stays_in_bounds`
  a successful move never leaves the grid

- `heal_loot_preserves_max_health`
  healing cannot exceed max health

- `spike_trap_never_increases_health`
  spike traps never increase health

- `abyss_trap_never_increases_health`
  abyss traps never increase health

- `bridge_hides_trap`
  when a bridge covers a tile, the abyss/trap below is not active there

- `sword_loot_equips_slotA`
  sword loot with an equip instruction correctly equips slot `A`

- `locked_exit_without_keys_denied`
  a locked-key exit cannot be used when the player has too few keys

- `goalReached_of_allChestsOpened`
  chest-completion worlds satisfy the goal predicate once all visible chests are open

- `applyExit_completeTask_sets_goalReached`
  traversing a `complete_task` exit marks the environment as completed

- `shieldB_without_shield_does_not_raise`
  pressing `BUTTON_B` without an equipped shield does not start the shield branch

These theorems are intentionally focused on the environment layer rather than on
planner completeness or policy optimality.

## Task Witnesses Included

The Lean file includes small concrete witnesses derived from real project tasks:

- `task1Init`
  key chest plus locked-key `complete_task` exit

- `task4Room`
  center room of task 4 with rotating bridge, center abyss, and hidden final chest

- `task4Init`
  task 4 style initial equipment configuration: `A = none`, `B = shield`

Two `example` proofs check the bridge tile semantics for different dynamic
states.

## Audit Conclusion

Compared with the earlier draft, the current version now explicitly models:

- task completion as a persistent world-state fact instead of only checking the
  current exit tile
- slot-based equipment semantics for sword and shield
- action durations and shield activity via `actionItem` plus `actionTicksRemaining`
- abyss control lock, delayed respawn, and safe respawn-tile selection
- correct locked-key consumption behavior for one-time unlocking
- hidden chest reveal conditions with optional trigger room restriction
- engine step ordering that matches the Python environment more closely
- current-room monster stun timing rather than globally ticking every room
- symbolic chaser / patroller / ambusher movement instead of static monsters

This is strong enough to present as a serious Module 1 environment
formalization, and it is much closer to the Python implementation than the
earlier draft. The honest claim is:

- the Lean file matches the key environment semantics for tasks 1-5 at symbolic tile level
- it is suitable for the assignment when the documented abstractions are stated
- it should not be described as full bit-level equivalence with the Python engine

## How to Check

The repository includes a [lean-toolchain](../lean-toolchain) pin (Lean 4.29.0). Build the whole formalization with Lake:

```bash
cd lean && lake build
```

The current file compiles successfully under Lean 4.29.0 and uses no `sorry`,
`admit`, or custom axioms.

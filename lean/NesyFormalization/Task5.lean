import NesyFormalization.Skills
import NesyFormalization.Task2

namespace NesyFormalization

/-!
  `mathematical_logic/task_5` 的关卡结构与关键可行性证明。

  任务目标：探索多房间地牢并打开所有宝箱。这里显式建模四个房间的墙体、关键
  宝箱、按钮、怪物和出口条件，并证明关键门禁和最终目标。
-/

inductive Task5RoomId where
  | start
  | west
  | south
  | east
  deriving DecidableEq, Repr

structure Task5RoomInfo where
  id : Task5RoomId
  walls : List Position := []
  traps : List Position := []
  buttons : List Position := []
  chests : List Chest := []
  npcs : List Position := []
  monsters : List Monster := []
  exits : List Exit := []
  spawns : List Position := []
  deriving Repr

def task5StartChest : Chest :=
  { pos := (4, 2), loot := { kind := .gold, amount := 2 }, opened := false }

def task5WestChest : Chest :=
  { pos := (2, 6), loot := { kind := .gold, amount := 5 }, opened := false }

def task5SouthKeyChest : Chest :=
  { pos := (8, 5), loot := { kind := .key, amount := 1 }, opened := false }

def task5EastHealChest : Chest :=
  { pos := (7, 1), loot := { kind := .heal, amount := 1 }, opened := false }

def task5SouthExit : Exit :=
  {
    dir := .down
    state := .conditional
    requirement := { needPressedButton := true }
  }

def task5EastExit : Exit :=
  {
    dir := .right
    state := .locked
    requirement := {
      requiredKeys := 1
      consumeKey := true
    }
  }

def task5WestExit : Exit :=
  { dir := .left, state := .normal }

def task5NorthExit : Exit :=
  { dir := .up, state := .normal }

def task5ReturnWestExit : Exit :=
  { dir := .left, state := .normal }

def task5StartWalls : List Position :=
  [(5, 1), (5, 2), (3, 3), (4, 3), (6, 5)]

def task5WestWalls : List Position :=
  [(1, 2), (2, 2), (5, 5), (4, 6), (5, 6)]

def task5SouthWalls : List Position :=
  [(2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (7, 2), (4, 6)]

def task5EastWalls : List Position :=
  [(2, 2), (2, 3), (2, 4), (5, 4), (6, 4)]

def task5StartMonster : Monster :=
  { pos := (7, 4), kind := .chaser, hp := 2, damage := 1 }

def task5WestMonster1 : Monster :=
  { pos := (2, 4), kind := .chaser, hp := 2, damage := 1 }

def task5WestMonster2 : Monster :=
  { pos := (6, 3), kind := .ambusher, hp := 2, damage := 1 }

def task5SouthMonster : Monster :=
  { pos := (6, 6), kind := .patroller, hp := 3, damage := 1 }

def task5EastMonster : Monster :=
  { pos := (7, 5), kind := .ambusher, hp := 2, damage := 1 }

def task5StartInfo : Task5RoomInfo :=
  {
    id := .start
    walls := task5StartWalls
    buttons := [(2, 6)]
    chests := [task5StartChest]
    npcs := [(7, 6)]
    monsters := [task5StartMonster]
    exits := [task5EastExit, task5WestExit, task5SouthExit]
    spawns := [(1, 1), (1, 4), (4, 1), (8, 4)]
  }

def task5WestInfo : Task5RoomInfo :=
  {
    id := .west
    walls := task5WestWalls
    chests := [task5WestChest]
    npcs := [(7, 6)]
    monsters := [task5WestMonster1, task5WestMonster2]
    exits := [{ dir := .right, state := .normal }]
    spawns := [(8, 4)]
  }

def task5SouthInfo : Task5RoomInfo :=
  {
    id := .south
    walls := task5SouthWalls
    traps := [(1, 5)]
    chests := [task5SouthKeyChest]
    npcs := [(2, 1)]
    monsters := [task5SouthMonster]
    exits := [task5NorthExit]
    spawns := [(4, 1)]
  }

def task5EastInfo : Task5RoomInfo :=
  {
    id := .east
    walls := task5EastWalls
    chests := [task5EastHealChest]
    npcs := [(7, 6)]
    monsters := [task5EastMonster]
    exits := [task5ReturnWestExit]
    spawns := [(1, 4)]
  }

def task5ExpectedRoute : List Task5RoomId :=
  [.start, .west, .start, .south, .start, .east]

theorem task5_route_visits_all_objective_rooms :
    .west ∈ task5ExpectedRoute ∧
    .south ∈ task5ExpectedRoute ∧
    .east ∈ task5ExpectedRoute := by
  simp [task5ExpectedRoute]

def task5StartRoom : SymbolicState :=
  {
    player := (1, 1)
    facing := .down
    hp := maxPlayerHp
    inventory := defaultCombatInventory
    walls := task5StartInfo.walls
    buttonsUp := task5StartInfo.buttons
    chests := task5StartInfo.chests
    npcs := task5StartInfo.npcs
    monsters := task5StartInfo.monsters
    exits := task5StartInfo.exits
  }

def task5Goal (s : SymbolicState) : Prop :=
  { task5StartChest with opened := true } ∈ s.chests ∧
  { task5WestChest with opened := true } ∈ s.chests ∧
  { task5SouthKeyChest with opened := true } ∈ s.chests ∧
  { task5EastHealChest with opened := true } ∈ s.chests

theorem task5_can_press_south_button :
    PressButtonOk task5StartRoom
      { task5StartRoom with
        buttonsUp := task5StartRoom.buttonsUp.erase (2, 6)
        buttonsPressed := (2, 6) :: task5StartRoom.buttonsPressed }
      (2, 6) := by
  exact pressButton_ok_of_buttonUp (by simp [task5StartRoom, task5StartInfo])

theorem task5_south_exit_traversable_after_button :
    canTraverseExit
      { task5StartRoom with
          player := (4, 7)
          buttonsUp := []
          buttonsPressed := [(2, 6)] }
      .down := by
  simp [canTraverseExit, exitTiles, exitAt?, exitRequirementMet,
    task5StartRoom, task5StartInfo, task5EastExit, task5WestExit, task5SouthExit,
    inventoryHas]

theorem task5_east_exit_traversable_with_key :
    canTraverseExit
      { task5StartRoom with
          player := (9, 3)
          inventory := { defaultCombatInventory with keys := 1 } }
      .right := by
  simp [canTraverseExit, exitTiles, exitAt?, exitRequirementMet,
    task5StartRoom, task5StartInfo, task5EastExit, task5WestExit, task5SouthExit,
    defaultCombatInventory, inventoryHas]

def task5AllOpenedState : SymbolicState :=
  {
    player := (7, 1)
    facing := .down
    hp := maxPlayerHp
    inventory := { defaultCombatInventory with keys := 0, gold := 7 }
    chests := [
      { task5StartChest with opened := true },
      { task5WestChest with opened := true },
      { task5SouthKeyChest with opened := true },
      { task5EastHealChest with opened := true }
    ]
    monsters := []
  }

/-- 当四个 objective chests 都处于 opened 状态时，task 5 的目标谓词成立。 -/
theorem task5_all_chests_opened_completes :
    task5Goal task5AllOpenedState := by
  simp [task5Goal, task5AllOpenedState, task5StartChest, task5WestChest,
    task5SouthKeyChest, task5EastHealChest]

/-- 南房钥匙宝箱打开后会提供东门所需钥匙。 -/
theorem task5_south_key_chest_gives_key :
    ({ task5StartRoom with
        inventory := applyLootToInventory defaultCombatInventory task5SouthKeyChest.loot }).inventory.keys
      = 1 := by
  simp [task5SouthKeyChest, applyLootToInventory, defaultCombatInventory]

end NesyFormalization

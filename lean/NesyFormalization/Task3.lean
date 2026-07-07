import NesyFormalization.Skills
import NesyFormalization.Task2

namespace NesyFormalization

/-!
  `mathematical_logic/task_3` 的关卡结构与关键可行性证明。

  任务目标：向西穿过怪物房，到钥匙房拿钥匙，返回起点并打开东侧锁门。这里显式
  建模三个房间、怪物房、钥匙房和起点房的关键出口。
-/

inductive Task3RoomId where
  | start
  | monsterHall
  | keyRoom
  deriving DecidableEq, Repr

structure Task3RoomInfo where
  id : Task3RoomId
  npcs : List Position := []
  chests : List Chest := []
  monsters : List Monster := []
  exits : List Exit := []
  spawns : List Position := []
  deriving Repr

def task3ReturnKeyChest : Chest :=
  {
    pos := (5, 4)
    loot := { kind := .key, amount := 1 }
    opened := false
  }

def task3EastExit : Exit :=
  {
    dir := .right
    state := .locked
    requirement := {
      requiredKeys := 1
      consumeKey := true
    }
    completeTask := true
  }

def task3WestNormalExit : Exit :=
  { dir := .left, state := .normal }

def task3HallEastExit : Exit :=
  { dir := .right, state := .normal }

def task3HallWestExit : Exit :=
  { dir := .left, state := .normal }

def task3KeyRoomEastExit : Exit :=
  { dir := .right, state := .normal }

def task3HallMonster : Monster :=
  { pos := (5, 3), kind := .chaser, hp := 2, damage := 1 }

def task3StartInfo : Task3RoomInfo :=
  {
    id := .start
    npcs := [(4, 1)]
    exits := [task3WestNormalExit, task3EastExit]
    spawns := [(4, 4), (1, 4), (8, 4)]
  }

def task3MonsterHallInfo : Task3RoomInfo :=
  {
    id := .monsterHall
    monsters := [task3HallMonster]
    exits := [task3HallEastExit, task3HallWestExit]
    spawns := [(8, 4), (1, 4)]
  }

def task3KeyRoomInfo : Task3RoomInfo :=
  {
    id := .keyRoom
    chests := [task3ReturnKeyChest]
    exits := [task3KeyRoomEastExit]
    spawns := [(8, 4)]
  }

def task3ExpectedRoute : List Task3RoomId :=
  [.start, .monsterHall, .keyRoom, .monsterHall, .start]

theorem task3_route_visits_key_room_and_returns :
    .keyRoom ∈ task3ExpectedRoute ∧
    .start ∈ task3ExpectedRoute := by
  simp [task3ExpectedRoute]

def task3StartRoom : SymbolicState :=
  {
    player := (4, 4)
    facing := .down
    hp := maxPlayerHp
    inventory := defaultCombatInventory
    npcs := task3StartInfo.npcs
    exits := task3StartInfo.exits
  }

def task3KeyRoom : SymbolicState :=
  {
    player := (8, 4)
    facing := .left
    hp := maxPlayerHp
    inventory := defaultCombatInventory
    chests := task3KeyRoomInfo.chests
    exits := task3KeyRoomInfo.exits
  }

def task3Goal (s : SymbolicState) : Prop :=
  s.worldComplete = true

/-- 钥匙房中，站在宝箱旁边交互可以获得返程钥匙。 -/
theorem task3_can_collect_return_key :
    Step { task3KeyRoom with player := (6, 4) } .interact
      { task3KeyRoom with
          player := (6, 4)
          inventory := applyLootToInventory defaultCombatInventory task3ReturnKeyChest.loot
          chests := openChestList [task3ReturnKeyChest] task3ReturnKeyChest } := by
  have hopen : canOpenChest { task3KeyRoom with player := (6, 4) } task3ReturnKeyChest := by
    simp [canOpenChest, adjacent, task3KeyRoom, task3KeyRoomInfo, task3ReturnKeyChest]
  simpa [task3KeyRoom, task3KeyRoomInfo, task3ReturnKeyChest, applyLootToHp] using
    (Step.interactOpenChest hopen)

/-- 回到起点房并持有钥匙时，东侧锁门可通过。 -/
theorem task3_east_exit_traversable :
    canTraverseExit
      { task3StartRoom with
          player := (9, 3)
          inventory := { defaultCombatInventory with keys := 1 } }
      .right := by
  simp [canTraverseExit, exitTiles, exitAt?, exitRequirementMet,
    task3StartRoom, task3StartInfo, task3WestNormalExit, task3EastExit,
    defaultCombatInventory, inventoryHas]

/-- 通过 task 3 的东侧锁门会完成任务。 -/
theorem task3_exit_completes :
    task3Goal
      ({ { task3StartRoom with
            player := (9, 3)
            inventory := { defaultCombatInventory with keys := 1 } } with
          facing := .right
          inventory := consumeKeysForExit
            ({ defaultCombatInventory with keys := 1 })
            task3EastExit.requirement
          exits := openExitList task3StartInfo.exits task3EastExit
          roomChanged := true
          worldComplete := false || task3EastExit.completeTask }) := by
  simp [task3Goal, task3EastExit]

end NesyFormalization

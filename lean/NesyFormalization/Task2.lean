import NesyFormalization.Skills

namespace NesyFormalization

/-!
  `mathematical_logic/task_2` 的关卡结构与关键可行性证明。

  任务目标：击败怪物、拿钥匙、从西侧条件门离开。task 2 是单房间任务，因此这里
  显式建模 room_001 的陷阱、宝箱、怪物和条件出口。
-/

inductive Task2RoomId where
  | room001
  deriving DecidableEq, Repr

structure Task2RoomInfo where
  id : Task2RoomId
  traps : List Position := []
  chests : List Chest := []
  monsters : List Monster := []
  exits : List Exit := []
  spawns : List Position := []
  deriving Repr

def defaultCombatInventory : Inventory :=
  {
    items := ["sword", "shield"]
    tools := ["sword", "shield"]
    equippedA := some "sword"
    equippedB := some "shield"
  }

def task2Traps : List Position :=
  [(1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0),
   (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7), (7, 7), (8, 7)]

def task2Monster : Monster :=
  { pos := (2, 2), kind := .chaser, hp := 1, damage := 1 }

def task2KeyChest : Chest :=
  {
    pos := (1, 3)
    loot := { kind := .key, amount := 1 }
    opened := false
  }

def task2WestExit : Exit :=
  {
    dir := .left
    state := .conditional
    requirement := {
      requiredKeys := 1
      needAllMonstersDefeated := true
    }
    completeTask := true
  }

def task2RoomInfo : Task2RoomInfo :=
  {
    id := .room001
    traps := task2Traps
    chests := [task2KeyChest]
    monsters := [task2Monster]
    exits := [task2WestExit]
    spawns := [(7, 3), (8, 4)]
  }

def task2ExpectedRoute : List Task2RoomId :=
  [.room001]

theorem task2_route_stays_in_single_room :
    .room001 ∈ task2ExpectedRoute := by
  simp [task2ExpectedRoute]

def task2Initial : SymbolicState :=
  {
    player := (7, 3)
    facing := .down
    hp := maxPlayerHp
    inventory := defaultCombatInventory
    traps := task2RoomInfo.traps
    chests := task2RoomInfo.chests
    monsters := task2RoomInfo.monsters
    exits := task2RoomInfo.exits
  }

def task2Goal (s : SymbolicState) : Prop :=
  s.worldComplete = true

/-- 默认装备包含剑能力，因此 task 2 可以攻击怪物。 -/
theorem task2_has_sword : hasSword task2Initial := by
  simp [hasSword, inventoryHas, task2Initial, defaultCombatInventory]

/-- 在怪物旁边挥剑可以清空 task 2 的唯一怪物。 -/
theorem task2_can_defeat_monster :
    Step { task2Initial with player := (2, 3) } .interact
      { task2Initial with player := (2, 3), monsters := [] } := by
  have hattack : canAttackMonster { task2Initial with player := (2, 3) } task2Monster := by
    simp [canAttackMonster, hasSword, inventoryHas, adjacent,
      task2Initial, task2RoomInfo, task2Monster, defaultCombatInventory]
  simpa [damageMonsterList, task2Initial, task2Monster] using
    (Step.interactAttackMonster hattack)

/-- 击败怪物后，站在钥匙宝箱旁边交互可以拿到钥匙。 -/
theorem task2_can_collect_key :
    Step { task2Initial with player := (2, 3), monsters := [] } .interact
      { task2Initial with
          player := (2, 3)
          monsters := []
          inventory := applyLootToInventory defaultCombatInventory task2KeyChest.loot
          chests := openChestList [task2KeyChest] task2KeyChest } := by
  have hopen : canOpenChest
      { task2Initial with player := (2, 3), monsters := [] } task2KeyChest := by
    simp [canOpenChest, adjacent, task2Initial, task2RoomInfo, task2KeyChest]
  simpa [task2Initial, task2KeyChest, applyLootToHp] using
    (Step.interactOpenChest hopen)

/-- 满足“怪物清空 + 持有钥匙”后，西侧条件门可通过。 -/
theorem task2_west_exit_traversable :
    canTraverseExit
      { task2Initial with
          player := (0, 3)
          monsters := []
          inventory := { defaultCombatInventory with keys := 1 } }
      .left := by
  simp [canTraverseExit, exitTiles, exitAt?, exitRequirementMet,
    task2Initial, task2RoomInfo, task2WestExit, defaultCombatInventory, inventoryHas]

/-- 通过 task 2 的西侧终点门会完成任务。 -/
theorem task2_exit_completes :
    task2Goal
      ({ { task2Initial with
            player := (0, 3)
            monsters := []
            inventory := { defaultCombatInventory with keys := 1 } } with
          facing := .left
          inventory := consumeKeysForExit
            ({ defaultCombatInventory with keys := 1 })
            task2WestExit.requirement
          exits := openExitList [task2WestExit] task2WestExit
          roomChanged := true
          worldComplete := false || task2WestExit.completeTask }) := by
  simp [task2Goal, task2WestExit]

end NesyFormalization

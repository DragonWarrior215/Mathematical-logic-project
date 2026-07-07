import NesyFormalization.Core

namespace NesyFormalization

/-!
  `mathematical_logic/task_1` 的具体关卡建模。

  这里我们只负责给出 task 1 的墙体、宝箱、出口和初始状态。核心环境语义已经在
  `Core.lean` 里统一定义，因此后续其他关卡文件也可以沿用同样的结构。
-/

inductive Task1RoomId where
  | room001
  deriving DecidableEq, Repr

structure Task1RoomInfo where
  id : Task1RoomId
  walls : List Position := []
  chests : List Chest := []
  exits : List Exit := []
  deriving Repr

/-- 由 task 1 JSON 房间布局抄出的墙体集合。 -/
def task1Walls : List Position :=
  [
    (0, 2), (1, 2),
    (4, 2), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2),
    (0, 5), (1, 5), (2, 5), (3, 5), (4, 5), (5, 5), (6, 5)
  ]

/-- task 1 中唯一的钥匙宝箱。 -/
def task1Chest : Chest :=
  {
    pos := (0, 3)
    loot := {
      kind := .key
      amount := 1
    }
    opened := false
  }

/-- task 1 北侧锁门出口。 -/
def task1NorthExit : Exit :=
  {
    dir := .up
    state := .locked
    requirement := {
      requiredKeys := 1
      consumeKey := true
    }
    completeTask := true
  }

def task1RoomInfo : Task1RoomInfo :=
  {
    id := .room001
    walls := task1Walls
    chests := [task1Chest]
    exits := [task1NorthExit]
  }

/-- task 1 的初始符号状态。 -/
def task1Initial : SymbolicState :=
  {
    player := (4, 6)
    facing := .down
    hp := maxPlayerHp
    inventory := {}
    walls := task1RoomInfo.walls
    traps := []
    abysses := []
    gaps := []
    bridges := []
    buttonsUp := []
    buttonsPressed := []
    switchesIdle := []
    switchesActive := []
    npcs := []
    chests := task1RoomInfo.chests
    monsters := []
    exits := task1RoomInfo.exits
    roomChanged := false
    worldComplete := false
  }

/-- 完成 task 1 的标志是任务完成位被置真。 -/
def task1Goal (s : SymbolicState) : Prop :=
  s.worldComplete = true

/-- task 1 的中间目标是拿到钥匙。 -/
def task1IntermediateGoal (s : SymbolicState) : Prop :=
  s.inventory.keys > 0

/-- 初始位置 `(4, 6)` 确实在地图边界内。 -/
theorem task1_start_inBounds : inBounds task1Initial.player := by
  simp [task1Initial, inBounds, gridWidth, gridHeight]

/-- 初始玩家位置既不在墙上，也不在危险 tile 上。 -/
theorem task1_start_safe : SafeState task1Initial := by
  unfold SafeState task1Initial
  simp [inBounds, gridWidth, gridHeight, isBlockingTile, isHazardTile,
    isChestTile, isMonsterTile, task1RoomInfo, task1Walls, task1Chest]

/-- 关闭状态的宝箱会阻挡移动。 -/
theorem task1_chest_is_blocking : isBlockingTile task1Initial task1Chest.pos := by
  unfold isBlockingTile isChestTile task1Initial
  simp [task1RoomInfo, task1Chest]

/-- 没拿到钥匙之前，北侧锁门还不能通过。 -/
theorem task1_cannot_exit_without_key : ¬ canTraverseExit task1Initial .up := by
  unfold canTraverseExit exitAt? exitRequirementMet task1Initial
  simp [exitTiles, task1RoomInfo, task1NorthExit, inventoryHas]

/-- 参考路径的第一步 `(4, 6) -> (5, 6)` 是合法可走的。 -/
theorem task1_first_right_is_walkable :
    walkable task1Initial (advance task1Initial.player .right) := by
  unfold walkable inBounds isBlockingTile isHazardTile task1Initial advance
  simp [gridWidth, gridHeight, isChestTile, isMonsterTile, task1RoomInfo, task1Walls, task1Chest]

/--
  如果玩家站在钥匙宝箱旁边并执行 `interact`，那么这一步一定会把钥匙数加到 1。
-/
theorem task1_opening_chest_yields_key
    {t : SymbolicState}
    (hstep : Step
      { task1Initial with player := (1, 3) }
      .interact t) :
    t.inventory.keys = 1 := by
  have hopen : canOpenChest { task1Initial with player := (1, 3) } task1Chest := by
    simp [canOpenChest, task1Initial, task1RoomInfo, task1Chest, adjacent]
  cases hstep with
  | interactOpenChest =>
      rename_i chest h
      have hEq : chest = task1Chest := by
        simpa [canOpenChest, task1Initial, task1RoomInfo, task1Chest] using h.1
      subst hEq
      simp [task1Initial, task1Chest, applyLootToInventory]
  | interactAttackMonster =>
      rename_i monster hattack
      exact False.elim (by
        rcases hattack with ⟨hm, _, _⟩
        cases hm)
  | interactToggleSwitch =>
      rename_i pos htoggle
      exact False.elim (by cases htoggle <;> simp [task1Initial] at *)
  | interactTalkNpc =>
      rename_i pos htalk
      exact False.elim (by
        rcases htalk with ⟨hnpc, _⟩
        simp [task1Initial] at hnpc)
  | interactNoEffect hnoneChest hnoneMonster hnoneSwitch hnoneNpc =>
      exact False.elim (hnoneChest task1Chest hopen)

end NesyFormalization

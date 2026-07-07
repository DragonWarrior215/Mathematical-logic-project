import NesyFormalization.Skills
import NesyFormalization.Task2

namespace NesyFormalization

/-!
  `mathematical_logic/task_4` 的关卡结构与关键可行性证明。

  这里的证明粒度仍然是“符号层 milestone”，不是像素级完整轨迹证明；但本文件
  现在显式建模了 task 4 的五个房间、墙体、中心旋转桥三种状态、关键出口、关键
  宝箱与怪物。后续若要继续加强，可以在这些定义上补充具体路径 `ValidPath` 证明。
-/

inductive Task4RoomId where
  | west
  | center
  | north
  | east
  | south
  deriving DecidableEq, Repr

structure Task4RoomInfo where
  id : Task4RoomId
  walls : List Position := []
  bridges : List Position := []
  abysses : List Position := []
  switches : List Position := []
  chests : List Chest := []
  monsters : List Monster := []
  exits : List Exit := []
  deriving Repr

def task4ShieldInventory : Inventory :=
  {
    items := ["shield"]
    tools := ["shield"]
    equippedB := some "shield"
  }

def task4ArmedInventory : Inventory :=
  {
    keys := 1
    items := ["sword", "shield"]
    tools := ["sword", "shield"]
    equippedA := some "sword"
    equippedB := some "shield"
  }

def task4SwitchPos : Position := (4, 4)

def task4KeyChest : Chest :=
  {
    pos := (4, 3)
    loot := { kind := .key, amount := 1 }
    opened := false
  }

def task4SwordChest : Chest :=
  {
    pos := (5, 4)
    loot := {
      kind := .item
      itemId := some "sword"
      tool := some "sword"
      equipSlot := some "A"
    }
    opened := false
  }

def task4Guardian : Monster :=
  { pos := (4, 4), kind := .chaser, hp := 1, damage := 1 }

def task4FinalChest : Chest :=
  {
    pos := (4, 4)
    loot := { kind := .gold, amount := 1 }
    opened := false
  }

def task4WestExit : Exit := { dir := .left, state := .normal }
def task4NorthExit : Exit := { dir := .up, state := .normal }
def task4SouthExit : Exit := { dir := .down, state := .normal }

def task4EastExit : Exit :=
  {
    dir := .right
    state := .locked
    requirement := {
      requiredKeys := 1
      consumeKey := false
    }
  }

/-- Walls copied from task 4 west/east room layout. -/
def task4SideRoomWalls : List Position :=
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0),
   (0, 1), (9, 1), (0, 2), (9, 2),
   (0, 5), (9, 5), (0, 6), (9, 6),
   (0, 7), (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7), (7, 7), (8, 7), (9, 7)]

def task4NorthRoomWalls : List Position :=
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0),
   (0, 1), (9, 1), (0, 2), (9, 2), (0, 3), (9, 3),
   (0, 4), (9, 4), (0, 5), (9, 5), (0, 6), (9, 6),
   (0, 7), (1, 7), (2, 7), (3, 7), (6, 7), (7, 7), (8, 7), (9, 7)]

def task4SouthRoomWalls : List Position :=
  [(0, 0), (1, 0), (2, 0), (3, 0), (6, 0), (7, 0), (8, 0), (9, 0),
   (0, 1), (9, 1), (0, 2), (9, 2), (0, 3), (9, 3),
   (0, 4), (9, 4), (0, 5), (9, 5), (0, 6), (9, 6),
   (0, 7), (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7), (7, 7), (8, 7), (9, 7)]

def task4RowTiles (y : Nat) : List Position :=
  (List.range gridWidth).map (fun x => (x, y))

def task4RowsToTiles : List Nat → List Position
  | [] => []
  | y :: ys => task4RowTiles y ++ task4RowsToTiles ys

def task4AllTiles : List Position :=
  task4RowsToTiles (List.range gridHeight)

def task4BridgeWestToNorth : List Position :=
  [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
   (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4),
   (4, 0), (5, 0), (4, 1), (5, 1), (4, 2), (5, 2)]

def task4BridgeWestToEast : List Position :=
  [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (7, 3), (8, 3), (9, 3),
   (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4), (6, 4), (7, 4), (8, 4), (9, 4)]

def task4BridgeWestToSouth : List Position :=
  [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
   (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4),
   (4, 5), (5, 5), (4, 6), (5, 6), (4, 7), (5, 7)]

/-- Center room is an abyss rectangle except for the active bridge tiles. -/
def task4CenterAbysses (bridge : List Position) : List Position :=
  task4AllTiles.filter (fun p => !bridge.contains p)

def task4WestInfo : Task4RoomInfo :=
  {
    id := .west
    walls := task4SideRoomWalls
    switches := [task4SwitchPos]
    exits := [{ dir := .right, state := .normal }]
  }

def task4CenterInfo (bridge : List Position) : Task4RoomInfo :=
  {
    id := .center
    bridges := bridge
    abysses := task4CenterAbysses bridge
    chests := [task4FinalChest]
    exits := [task4EastExit, task4WestExit, task4NorthExit, task4SouthExit]
  }

def task4NorthInfo : Task4RoomInfo :=
  {
    id := .north
    walls := task4NorthRoomWalls
    chests := [task4KeyChest]
    exits := [{ dir := .down, state := .normal }]
  }

def task4EastInfo : Task4RoomInfo :=
  {
    id := .east
    walls := task4SideRoomWalls
    chests := [task4SwordChest]
    exits := [{ dir := .left, state := .normal }]
  }

def task4SouthInfo : Task4RoomInfo :=
  {
    id := .south
    walls := task4SouthRoomWalls
    monsters := [task4Guardian]
    exits := [{ dir := .up, state := .normal }]
  }

def task4ExpectedRoute : List Task4RoomId :=
  [.west, .center, .north, .center, .east, .center, .south, .center]

theorem task4_route_visits_all_required_rooms :
    .north ∈ task4ExpectedRoute ∧
    .east ∈ task4ExpectedRoute ∧
    .south ∈ task4ExpectedRoute := by
  simp [task4ExpectedRoute]

theorem task4_bridge_states_expose_required_directions :
    (4, 0) ∈ task4BridgeWestToNorth ∧
    (9, 3) ∈ task4BridgeWestToEast ∧
    (4, 7) ∈ task4BridgeWestToSouth := by
  simp [task4BridgeWestToNorth, task4BridgeWestToEast, task4BridgeWestToSouth]

def task4WestRoom : SymbolicState :=
  {
    player := (8, 4)
    facing := .left
    hp := maxPlayerHp
    inventory := task4ShieldInventory
    walls := task4WestInfo.walls
    switchesIdle := task4WestInfo.switches
    exits := task4WestInfo.exits
  }

def task4NorthRoom : SymbolicState :=
  {
    player := (4, 6)
    facing := .up
    hp := maxPlayerHp
    inventory := task4ShieldInventory
    walls := task4NorthInfo.walls
    chests := task4NorthInfo.chests
    exits := task4NorthInfo.exits
  }

def task4CenterWithKey : SymbolicState :=
  {
    player := (9, 3)
    facing := .right
    hp := maxPlayerHp
    inventory := { task4ShieldInventory with keys := 1 }
    bridges := task4BridgeWestToEast
    abysses := task4CenterAbysses task4BridgeWestToEast
    exits := (task4CenterInfo task4BridgeWestToEast).exits
  }

def task4EastRoom : SymbolicState :=
  {
    player := (1, 4)
    facing := .right
    hp := maxPlayerHp
    inventory := { task4ShieldInventory with keys := 1 }
    walls := task4EastInfo.walls
    chests := task4EastInfo.chests
    exits := task4EastInfo.exits
  }

def task4SouthRoomArmed : SymbolicState :=
  {
    player := (4, 5)
    facing := .up
    hp := maxPlayerHp
    inventory := task4ArmedInventory
    walls := task4SouthInfo.walls
    monsters := task4SouthInfo.monsters
    exits := task4SouthInfo.exits
  }

def task4CenterFinal : SymbolicState :=
  {
    player := (5, 4)
    facing := .left
    hp := maxPlayerHp
    inventory := task4ArmedInventory
    bridges := task4BridgeWestToSouth
    abysses := task4CenterAbysses task4BridgeWestToSouth
    chests := [task4FinalChest]
    monsters := []
    exits := (task4CenterInfo task4BridgeWestToSouth).exits
  }

def task4Goal (s : SymbolicState) : Prop :=
  { task4FinalChest with opened := true } ∈ s.chests

theorem task4_can_toggle_bridge_switch :
    ToggleSwitchOk task4WestRoom
      { task4WestRoom with
          switchesIdle := task4WestRoom.switchesIdle.erase task4SwitchPos
          switchesActive := task4SwitchPos :: task4WestRoom.switchesActive }
      task4SwitchPos := by
  exact toggleSwitch_ok_of_canToggle (by simp [canToggleSwitch, task4WestRoom,
    task4WestInfo, task4SwitchPos])

theorem task4_can_collect_key :
    Step { task4NorthRoom with player := (5, 3) } .interact
      { task4NorthRoom with
          player := (5, 3)
          inventory := applyLootToInventory task4ShieldInventory task4KeyChest.loot
          chests := openChestList [task4KeyChest] task4KeyChest } := by
  have hopen : canOpenChest { task4NorthRoom with player := (5, 3) } task4KeyChest := by
    simp [canOpenChest, adjacent, task4NorthRoom, task4NorthInfo, task4KeyChest]
  simpa [task4NorthRoom, task4NorthInfo, task4KeyChest, applyLootToHp] using
    (Step.interactOpenChest hopen)

theorem task4_east_exit_traversable :
    canTraverseExit task4CenterWithKey .right := by
  simp [canTraverseExit, exitTiles, exitAt?, exitRequirementMet,
    task4CenterWithKey, task4CenterInfo, task4EastExit, task4ShieldInventory, inventoryHas]

theorem task4_can_collect_sword :
    OpenChestOk { task4EastRoom with player := (4, 4) }
      { task4EastRoom with
          player := (4, 4)
          hp := applyLootToHp task4EastRoom.hp task4SwordChest.loot
          inventory := applyLootToInventory task4EastRoom.inventory task4SwordChest.loot
          chests := openChestList [task4SwordChest] task4SwordChest }
      task4SwordChest := by
  exact openChest_ok_of_canOpenChest (by
    simp [canOpenChest, adjacent, task4EastRoom, task4EastInfo, task4SwordChest])

theorem task4_sword_chest_equips_sword :
    (applyLootToInventory task4EastRoom.inventory task4SwordChest.loot).equippedA = some "sword" := by
  simp [applyLootToInventory, task4SwordChest]

theorem task4_can_defeat_guardian :
    Step task4SouthRoomArmed .interact
      { task4SouthRoomArmed with monsters := [] } := by
  have hattack : canAttackMonster task4SouthRoomArmed task4Guardian := by
    simp [canAttackMonster, hasSword, inventoryHas, adjacent,
      task4SouthRoomArmed, task4SouthInfo, task4Guardian, task4ArmedInventory]
  simpa [damageMonsterList, task4SouthRoomArmed, task4SouthInfo, task4Guardian] using
    (Step.interactAttackMonster hattack)

theorem task4_can_open_final_chest :
    task4Goal
      { task4CenterFinal with
          hp := applyLootToHp task4CenterFinal.hp task4FinalChest.loot
          inventory := applyLootToInventory task4CenterFinal.inventory task4FinalChest.loot
          chests := openChestList [task4FinalChest] task4FinalChest } := by
  simp [task4Goal, openChestList, task4FinalChest]

end NesyFormalization

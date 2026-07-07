import Std

/-!
模块 1：NesyLink 数理逻辑任务的环境形式化。

本文件刻意在格子（tile）粒度上建模符号游戏层，并尽量与以下 Python 实现保持对应：

- `nesylink/core/constants.py`
- `nesylink/core/state.py`
- `nesylink/core/world/schema.py`
- `nesylink/core/mechanics/movement.py`
- `nesylink/core/mechanics/interactions.py`
- `nesylink/core/mechanics/combat.py`
- `nesylink/core/mechanics/progress.py`
- `nesylink/core/equipment/weapons.py`
- `nesylink/core/equipment/defense.py`

仍作为环境抽象记录下来的简化如下：

1. 像素级移动被抽象为格子移动。
2. 怪物 AI 在格子粒度上符号化建模，但像素级碰撞盒、连续碰撞响应和击退仍被抽象掉。
3. 深渊控制锁、延迟重生和重生格子优先级都在格子粒度上符号化建模。
4. 出口运行时状态被折叠进 `Exit.unlocked` 字段。
5. 怪物移动周期未建模；例如 Python 中巡逻怪每 2 步移动一次，而这里所有怪物每步移动。
   这是保守的过近似：若某个安全性质在 Lean 中成立，那么在怪物更慢的 Python 环境中也成立。

未使用 `sorry`、`admit` 或自定义公理。
-/

namespace EnvFormalization

abbrev Position := Nat × Nat

inductive Direction where
  | up
  | down
  | left
  | right
  deriving Repr, DecidableEq, Inhabited, BEq

inductive Action where
  | wait
  | up
  | down
  | left
  | right
  | interactA
  | shieldB
  deriving Repr, DecidableEq, Inhabited, BEq

inductive LootKind where
  | key
  | gold
  | heal
  | item
  deriving Repr, DecidableEq, Inhabited, BEq

inductive TrapType where
  | spike
  | abyss
  deriving Repr, DecidableEq, Inhabited, BEq

inductive MonsterType where
  | chaser
  | patroller
  | ambusher
  deriving Repr, DecidableEq, Inhabited, BEq

inductive ExitType where
  | normal
  | lockedKey
  | conditional
  deriving Repr, DecidableEq, Inhabited, BEq

inductive DynamicTileKind where
  | none
  | gap
  | bridge
  deriving Repr, DecidableEq, Inhabited, BEq

inductive EquipSlot where
  | A
  | B
  deriving Repr, DecidableEq, Inhabited, BEq

structure Loot where
  kind : LootKind
  amount : Nat := 1
  itemName : Option String := none
  toolName : Option String := none
  equipSlot : Option EquipSlot := none
  deriving Repr, DecidableEq, Inhabited, BEq

structure Chest where
  chestId : String
  pos : Position
  loot : Loot
  isOpen : Bool := false
  isVisible : Bool := true
  revealOnAllMonstersDefeated : Bool := false
  revealTriggerRoomId : Option String := none
  deriving Repr, DecidableEq, Inhabited, BEq

structure Trap where
  trapId : String
  pos : Position
  trapType : TrapType := .spike
  damage : Nat := 1
  respawnTo : String := "default"
  respawnDelaySteps : Nat := 0
  singleUse : Bool := false
  isActive : Bool := true
  deriving Repr, DecidableEq, Inhabited, BEq

structure Button where
  buttonId : String
  pos : Position
  isPressed : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

structure Switch where
  switchId : String
  pos : Position
  isPressed : Bool := false
  targetObjectId : String
  order : List String
  deriving Repr, DecidableEq, Inhabited, BEq

structure NPC where
  npcId : String
  pos : Position
  text : String
  deriving Repr, DecidableEq, Inhabited, BEq

structure Monster where
  monsterId : String
  pos : Position
  spawnPos : Position := (0, 0)
  monsterType : MonsterType
  hp : Nat := 3
  damage : Nat := 1
  ambushRangeTiles : Nat := 2
  patrolSpanTiles : Nat := 1
  patrolIndex : Nat := 0
  activated : Bool := false
  stunTicksRemaining : Nat := 0
  deriving Repr, DecidableEq, Inhabited, BEq

structure Exit where
  exitId : String
  direction : Direction
  tiles : List Position
  exitType : ExitType := .normal
  requiresKeyCount : Nat := 0
  consumeKey : Bool := false
  requiresButtonId : Option String := none
  requiresItem : Option String := none
  requiresAllMonstersDefeated : Bool := false
  unlocked : Bool := true
  completeTask : Bool := false
  targetRoomId : String := ""
  targetEntry : String := "default"
  deriving Repr, DecidableEq, Inhabited, BEq

structure DynamicObjectState where
  stateId : String
  tiles : List Position
  deriving Repr, DecidableEq, Inhabited, BEq

structure DynamicObject where
  objectId : String
  kind : String := "rotating_bridge"
  initialState : String
  states : List DynamicObjectState
  backgroundTile : DynamicTileKind := .gap
  activeTile : DynamicTileKind := .bridge
  currentState : String
  deriving Repr, DecidableEq, Inhabited, BEq

structure RoomState where
  roomId : String
  walls : List Position
  chests : List Chest
  traps : List Trap
  buttons : List Button
  switches : List Switch
  npcs : List NPC
  monsters : List Monster
  exits : List Exit
  dynamicObjects : List DynamicObject
  spawns : List (String × Position)
  defaultSpawn : Position
  deriving Repr, DecidableEq, Inhabited, BEq

structure WorldState where
  player : Position
  facing : Direction
  health : Nat := 5
  maxHealth : Nat := 5
  keys : Nat := 0
  gold : Nat := 0
  items : List String := []
  tools : List String := []
  equippedA : String := "none"
  equippedB : String := "none"
  actionItem : Option String := none
  actionFacing : Option Direction := none
  actionTicksRemaining : Nat := 0
  controlLockStepsRemaining : Nat := 0
  pendingRespawn : Option Position := none
  environmentCompleted : Bool := false
  rooms : List RoomState
  currentRoomIdx : Nat := 0
  worldCompletionViaExit : Bool := true
  deriving Repr, DecidableEq, Inhabited, BEq

def containsPos (ps : List Position) (p : Position) : Bool :=
  ps.any (fun q => q == p)

def containsString (xs : List String) (x : String) : Bool :=
  xs.any (fun y => y == x)

def lookupAssoc? : List (String × Position) → String → Option Position
  | [], _ => none
  | (name, pos) :: rest, key =>
      if name == key then some pos else lookupAssoc? rest key

def getAt? : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt? xs n

def replaceAt : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, value => value :: xs
  | x :: xs, n + 1, value => x :: replaceAt xs n value

def roomByIdIdx? : List RoomState → String → Option Nat
  | [], _ => none
  | room :: rest, roomId =>
      if room.roomId == roomId then
        some 0
      else
        match roomByIdIdx? rest roomId with
        | some n => some (n + 1)
        | none => none

def indexOfString? : List String → String → Option Nat
  | [], _ => none
  | x :: xs, target =>
      if x == target then
        some 0
      else
        match indexOfString? xs target with
        | some n => some (n + 1)
        | none => none

def currentRoom (w : WorldState) : RoomState :=
  match getAt? w.rooms w.currentRoomIdx with
  | some room => room
  | none => default

def setCurrentRoom (w : WorldState) (room : RoomState) : WorldState :=
  { w with rooms := replaceAt w.rooms w.currentRoomIdx room }

def InBounds (p : Position) : Prop :=
  p.1 < 10 ∧ p.2 < 8

def inBounds (p : Position) : Bool :=
  decide (p.1 < 10) && decide (p.2 < 8)

def manhattan (a b : Position) : Nat :=
  let dx := if a.1 ≤ b.1 then b.1 - a.1 else a.1 - b.1
  let dy := if a.2 ≤ b.2 then b.2 - a.2 else a.2 - b.2
  dx + dy

def Adjacent (a b : Position) : Prop :=
  manhattan a b ≤ 1

def adjacent (a b : Position) : Bool :=
  decide (manhattan a b ≤ 1)

def facingTile (p : Position) (d : Direction) : Position :=
  match d with
  | .up => (p.1, p.2 - 1)
  | .down => (p.1, p.2 + 1)
  | .left => (p.1 - 1, p.2)
  | .right => (p.1 + 1, p.2)

def actionDirection? : Action → Option Direction
  | .up => some .up
  | .down => some .down
  | .left => some .left
  | .right => some .right
  | _ => none

def entryDirection? (entry : String) : Option Direction :=
  let normalized := entry.trimAscii.toString.toLower
  if normalized == "north" || normalized == "from_north" || normalized == "north_entry" then
    some .up
  else if normalized == "south" || normalized == "from_south" || normalized == "south_entry" then
    some .down
  else if normalized == "west" || normalized == "from_west" || normalized == "west_entry" then
    some .left
  else if normalized == "east" || normalized == "from_east" || normalized == "east_entry" then
    some .right
  else
    none

def entrySpawnCandidates (d : Direction) : List Position :=
  match d with
  | .up => [(4, 1), (5, 1)]
  | .down => [(4, 6), (5, 6)]
  | .left => [(1, 3), (1, 4)]
  | .right => [(8, 3), (8, 4)]

def firstOpenEntrySpawn? (r : RoomState) (d : Direction) : Option Position :=
  (entrySpawnCandidates d).find? (fun p => !(containsPos r.walls p))

def stateContains (st : DynamicObjectState) (p : Position) : Bool :=
  containsPos st.tiles p

def dynamicTileAt (r : RoomState) (p : Position) : DynamicTileKind :=
  match r.dynamicObjects.find? (fun obj =>
      obj.states.any (fun st => st.stateId == obj.currentState && stateContains st p)) with
  | some obj => obj.activeTile
  | none =>
      match r.dynamicObjects.find? (fun obj =>
          obj.states.any (fun st => stateContains st p)) with
      | some obj => obj.backgroundTile
      | none => .none

def trapAt? (r : RoomState) (p : Position) : Option Trap :=
  if dynamicTileAt r p == .bridge then
    none
  else
    r.traps.find? (fun t => t.isActive && t.pos == p)

def buttonAt? (r : RoomState) (p : Position) : Option Button :=
  r.buttons.find? (fun b => b.pos == p)

def exitAt? (r : RoomState) (p : Position) (d : Direction) : Option Exit :=
  r.exits.find? (fun e => e.direction == d && containsPos e.tiles p)

def isBlocking (r : RoomState) (p : Position) : Bool :=
  containsPos r.walls p ||
    r.chests.any (fun c => c.isVisible && c.pos == p) ||
    r.npcs.any (fun n => n.pos == p) ||
    dynamicTileAt r p == .gap

def canOccupy (r : RoomState) (p : Position) : Bool :=
  inBounds p && !(isBlocking r p)

def hasActiveTrapAt (r : RoomState) (p : Position) : Bool :=
  r.traps.any (fun t => t.isActive && t.pos == p)

def safeRespawnTile (r : RoomState) (p : Position) : Bool :=
  inBounds p && !(isBlocking r p) && !hasActiveTrapAt r p

def respawnPos (r : RoomState) (spawnName : String) : Position :=
  match lookupAssoc? r.spawns spawnName with
  | some pos => pos
  | none => r.defaultSpawn

def abyssRespawnPos (r : RoomState) (previous abyss : Position) : Position :=
  if previous != abyss && safeRespawnTile r previous then
    previous
  else
    match [(abyss.1 - 1, abyss.2), (abyss.1 + 1, abyss.2), (abyss.1, abyss.2 - 1), (abyss.1, abyss.2 + 1)].find? (safeRespawnTile r) with
    | some pos => pos
    | none => r.defaultSpawn

def allMonstersDefeated (r : RoomState) : Bool :=
  r.monsters.isEmpty

def chestReady (c : Chest) : Bool :=
  c.isVisible && c.isOpen

def allChestsOpenedRooms : List RoomState → Bool
  | [] => true
  | room :: rest =>
      room.chests.all chestReady && allChestsOpenedRooms rest

def chestCount : List RoomState → Nat
  | [] => 0
  | room :: rest => room.chests.length + chestCount rest

def allChestsOpened (w : WorldState) : Bool :=
  decide (0 < chestCount w.rooms) && allChestsOpenedRooms w.rooms

def exitConditionSatisfied (w : WorldState) (e : Exit) : Bool :=
  match e.exitType with
  | .normal => true
  | .lockedKey =>
      if e.unlocked then
        true
      else
        decide (e.requiresKeyCount ≤ w.keys)
  | .conditional =>
      let buttonOk :=
        match e.requiresButtonId with
        | none => true
        | some buttonId =>
            (currentRoom w).buttons.any (fun b => b.buttonId == buttonId && b.isPressed)
      let itemOk :=
        match e.requiresItem with
        | none => true
        | some itemName => containsString w.items itemName
      let monsterOk :=
        if e.requiresAllMonstersDefeated then
          allMonstersDefeated (currentRoom w)
        else
          true
      let keyOk := decide (e.requiresKeyCount ≤ w.keys)
      buttonOk && itemOk && monsterOk && keyOk

def goalReached (w : WorldState) : Bool :=
  w.environmentCompleted || (!w.worldCompletionViaExit && allChestsOpened w)

def roomWellFormed (r : RoomState) : Prop :=
  (∀ p ∈ r.walls, InBounds p) ∧
  (∀ spawn ∈ r.spawns, InBounds spawn.2 ∧ !containsPos r.walls spawn.2) ∧
  (∀ chest ∈ r.chests, InBounds chest.pos ∧ !containsPos r.walls chest.pos) ∧
  (∀ trap ∈ r.traps, InBounds trap.pos ∧ !containsPos r.walls trap.pos) ∧
  (∀ button ∈ r.buttons, InBounds button.pos ∧ !containsPos r.walls button.pos) ∧
  (∀ sw ∈ r.switches, InBounds sw.pos ∧ !containsPos r.walls sw.pos) ∧
  (∀ npc ∈ r.npcs, InBounds npc.pos ∧ !containsPos r.walls npc.pos) ∧
  (∀ monster ∈ r.monsters, InBounds monster.pos ∧ !containsPos r.walls monster.pos) ∧
  (∀ exitCfg ∈ r.exits, ∀ tile ∈ exitCfg.tiles, InBounds tile ∧ !containsPos r.walls tile) ∧
  (∀ obj ∈ r.dynamicObjects, ∀ st ∈ obj.states, ∀ tile ∈ st.tiles, InBounds tile ∧ !containsPos r.walls tile) ∧
  InBounds r.defaultSpawn ∧ !containsPos r.walls r.defaultSpawn

def WellFormed (w : WorldState) : Prop :=
  w.currentRoomIdx < w.rooms.length ∧
  InBounds w.player ∧
  !containsPos (currentRoom w).walls w.player ∧
  ∀ room ∈ w.rooms, roomWellFormed room

def addItem (items : List String) (itemName : String) : List String :=
  if containsString items itemName then items else itemName :: items

def setEquippedSlot (w : WorldState) (slot : EquipSlot) (toolName : String) : WorldState :=
  match slot with
  | .A => { w with equippedA := toolName }
  | .B => { w with equippedB := toolName }

def hasEquippedSword (w : WorldState) : Bool :=
  w.equippedA == "sword"

def hasEquippedShield (w : WorldState) : Bool :=
  w.equippedB == "shield"

def actionActive (w : WorldState) (itemName : String) : Bool :=
  w.actionItem == some itemName && decide (0 < w.actionTicksRemaining)

def shieldActive (w : WorldState) : Bool :=
  actionActive w "shield"

def startAction (w : WorldState) (itemName : String) (facing : Direction) (ticks : Nat) : WorldState :=
  { w with actionItem := some itemName, actionFacing := some facing, actionTicksRemaining := ticks }

def clearAction (w : WorldState) : WorldState :=
  { w with actionItem := none, actionFacing := none, actionTicksRemaining := 0 }

def advancePlayerActionState (w : WorldState) : WorldState :=
  if 1 < w.actionTicksRemaining then
    { w with actionTicksRemaining := w.actionTicksRemaining - 1 }
  else
    w

def finalizePlayerActionState (w : WorldState) (actionStartedThisStep : Bool) : WorldState :=
  if actionStartedThisStep then
    w
  else
    match w.actionItem with
    | none => w
    | some _ =>
        if w.actionTicksRemaining ≤ 1 then
          clearAction w
        else
          w

def applyLoot (w : WorldState) (loot : Loot) : WorldState :=
  match loot.kind with
  | .key =>
      { w with keys := w.keys + max 1 loot.amount }
  | .gold =>
      { w with gold := w.gold + max 1 loot.amount }
  | .heal =>
      { w with health := min w.maxHealth (w.health + max 1 loot.amount) }
  | .item =>
      let itemName := loot.itemName.getD "item"
      let w1 := { w with items := addItem w.items itemName }
      let w2 :=
        match loot.toolName with
        | some toolName => { w1 with tools := addItem w1.tools toolName }
        | none => w1
      match loot.toolName, loot.equipSlot with
      | some toolName, some slot => setEquippedSlot w2 slot toolName
      | _, _ => w2

def openChestById (chests : List Chest) (chestId : String) : List Chest :=
  chests.map (fun c => if c.chestId == chestId then { c with isOpen := true } else c)

def pressButtonById (buttons : List Button) (buttonId : String) : List Button :=
  buttons.map (fun b => if b.buttonId == buttonId then { b with isPressed := true } else b)

def pressSwitchById (switches : List Switch) (switchId : String) : List Switch :=
  switches.map (fun s => if s.switchId == switchId then { s with isPressed := true } else s)

def deactivateTrapById (traps : List Trap) (trapId : String) : List Trap :=
  traps.map (fun t => if t.trapId == trapId then { t with isActive := false } else t)

def reduceMonsterHpById (monsters : List Monster) (monsterId : String) : List Monster :=
  monsters.map (fun m => if m.monsterId == monsterId then { m with hp := m.hp - 1 } else m)

def setMonsterStunById (monsters : List Monster) (monsterId : String) (ticks : Nat) : List Monster :=
  monsters.map (fun m => if m.monsterId == monsterId then { m with stunTicksRemaining := ticks } else m)

def removeMonsterById (monsters : List Monster) (monsterId : String) : List Monster :=
  monsters.filter (fun m => m.monsterId != monsterId)

def unlockExitById (exits : List Exit) (exitId : String) : List Exit :=
  exits.map (fun e => if e.exitId == exitId then { e with unlocked := true } else e)

def unlockMonsterGatedExits (exits : List Exit) : List Exit :=
  exits.map (fun e =>
    if e.requiresAllMonstersDefeated then { e with unlocked := true } else e)

def revealMonsterTriggeredChests (rooms : List RoomState) (triggerRoomId : String) : List RoomState :=
  rooms.map (fun room =>
    { room with
        chests := room.chests.map (fun chest =>
          if chest.revealOnAllMonstersDefeated &&
              match chest.revealTriggerRoomId with
              | none => true
              | some roomId => roomId == triggerRoomId
          then
            { chest with isVisible := true }
          else
            chest) })

def dynamicObjectById? : List RoomState → String → Option DynamicObject
  | [], _ => none
  | room :: rest, objectId =>
      match room.dynamicObjects.find? (fun obj => obj.objectId == objectId) with
      | some obj => some obj
      | none => dynamicObjectById? rest objectId

def setDynamicObjectState (rooms : List RoomState) (objectId nextState : String) : List RoomState :=
  rooms.map (fun room =>
    { room with
        dynamicObjects := room.dynamicObjects.map (fun obj =>
          if obj.objectId == objectId then
            { obj with currentState := nextState }
          else
            obj) })

def nextStateInOrder? (order : List String) (current : String) : Option String :=
  match indexOfString? order current with
  | some idx =>
      let nextIdx := (idx + 1) % order.length
      getAt? order nextIdx
  | none => none

def entrySpawnPos (r : RoomState) (targetEntry : String) : Position :=
  match entryDirection? targetEntry with
  | some dir =>
      match firstOpenEntrySpawn? r dir with
      | some pos => pos
      | none => respawnPos r targetEntry
  | none => respawnPos r targetEntry

def eraseFirstPos : List Position → Position → List Position
  | [], _ => []
  | p :: ps, target =>
      if p == target then
        ps
      else
        p :: eraseFirstPos ps target

def monsterCanOccupy (r : RoomState) (occupied : List Position) (p : Position) : Bool :=
  canOccupy r p && !containsPos occupied p

def preferredDirectionsToward (src target : Position) : List Direction :=
  let dx := if src.1 ≤ target.1 then target.1 - src.1 else src.1 - target.1
  let dy := if src.2 ≤ target.2 then target.2 - src.2 else src.2 - target.2
  let horiz :=
    if src.1 ≤ target.1 then
      [.right, .left]
    else
      [.left, .right]
  let vert :=
    if src.2 ≤ target.2 then
      [.down, .up]
    else
      [.up, .down]
  if dy ≤ dx then
    horiz ++ vert
  else
    vert ++ horiz

def firstValidMonsterStep? (r : RoomState) (occupied : List Position)
    (current target : Position) : Option Position :=
  (preferredDirectionsToward current target).findSome? (fun d =>
    let nextPos := facingTile current d
    if manhattan nextPos target < manhattan current target && monsterCanOccupy r occupied nextPos then
      some nextPos
    else
      none)

def moveMonsterToward (r : RoomState) (occupied : List Position)
    (current target : Position) : Position :=
  match firstValidMonsterStep? r occupied current target with
  | some nextPos => nextPos
  | none => current

def withinAmbushRange (monster player : Position) (radius : Nat) : Bool :=
  let dx := if monster.1 ≤ player.1 then player.1 - monster.1 else monster.1 - player.1
  let dy := if monster.2 ≤ player.2 then player.2 - monster.2 else monster.2 - player.2
  dx ≤ radius && dy ≤ radius

def monsterPatrolPoints (m : Monster) : List Position :=
  let x0 := m.spawnPos.1
  let y0 := m.spawnPos.2
  let x1 := min 9 (x0 + m.patrolSpanTiles)
  let y1 := min 7 (y0 + m.patrolSpanTiles)
  [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]

def monsterPatrolTarget? (m : Monster) : Option Position :=
  getAt? (monsterPatrolPoints m) (m.patrolIndex % (monsterPatrolPoints m).length)

def updatePatroller (r : RoomState) (occupied : List Position) (m : Monster) : Monster :=
  let route := monsterPatrolPoints m
  if route.isEmpty then
    m
  else
    let target := (getAt? route (m.patrolIndex % route.length)).getD m.pos
    let advancedIndex :=
      if m.pos == target then
        (m.patrolIndex + 1) % route.length
      else
        m.patrolIndex % route.length
    let nextTarget := (getAt? route advancedIndex).getD m.pos
    { m with
        patrolIndex := advancedIndex
        pos := moveMonsterToward r occupied m.pos nextTarget }

def updateChaserLikeMonster (r : RoomState) (occupied : List Position)
    (m : Monster) (target : Position) : Monster :=
  { m with pos := moveMonsterToward r occupied m.pos target }

def updateMonster (r : RoomState) (playerPos : Position) (occupied : List Position) (m : Monster) : Monster :=
  if 0 < m.stunTicksRemaining then
    { m with stunTicksRemaining := m.stunTicksRemaining - 1 }
  else
    match m.monsterType with
    | .chaser => updateChaserLikeMonster r occupied m playerPos
    | .patroller => updatePatroller r occupied m
    | .ambusher =>
        let activatedNow := m.activated || withinAmbushRange m.pos playerPos m.ambushRangeTiles
        let m1 := { m with activated := activatedNow }
        if activatedNow then
          updateChaserLikeMonster r occupied m1 playerPos
        else
          m1

def updateMonstersList (r : RoomState) (playerPos : Position)
    (occupied : List Position) : List Monster → List Monster
  | [] => []
  | monster :: rest =>
      let occupiedWithoutSelf := eraseFirstPos occupied monster.pos
      let updated := updateMonster r playerPos occupiedWithoutSelf monster
      let occupiedNext := updated.pos :: occupiedWithoutSelf
      updated :: updateMonstersList r playerPos occupiedNext rest

def updateMonstersCurrentRoom (w : WorldState) : WorldState :=
  let room := currentRoom w
  let updatedMonsters := updateMonstersList room w.player (room.monsters.map Monster.pos) room.monsters
  setCurrentRoom w { room with monsters := updatedMonsters }

def advanceControlLock (w : WorldState) : WorldState :=
  if w.controlLockStepsRemaining = 0 then
    w
  else
    let remaining := w.controlLockStepsRemaining - 1
    if remaining > 0 then
      { w with controlLockStepsRemaining := remaining }
    else
      match w.pendingRespawn with
      | some respawnPos =>
          { w with
              controlLockStepsRemaining := 0
              pendingRespawn := none
              player := respawnPos }
      | none =>
          { w with controlLockStepsRemaining := 0 }

def resolveSpikeTrap (w : WorldState) (trap : Trap) : WorldState :=
  let room := currentRoom w
  let updatedRoom :=
    if trap.singleUse then
      { room with traps := deactivateTrapById room.traps trap.trapId }
    else
      room
  let newHealth := w.health - trap.damage
  let newPlayer :=
    if newHealth = 0 then
      w.player
    else
      respawnPos updatedRoom trap.respawnTo
  let w1 := setCurrentRoom w updatedRoom
  { w1 with health := newHealth, player := newPlayer }

def resolveAbyssTrap (w : WorldState) (trap : Trap) (previous : Position) : WorldState :=
  let room := currentRoom w
  let updatedRoom :=
    if trap.singleUse then
      { room with traps := deactivateTrapById room.traps trap.trapId }
    else
      room
  let newHealth := w.health - trap.damage
  let newPlayer :=
    if newHealth = 0 then
      w.player
    else
      abyssRespawnPos updatedRoom previous trap.pos
  let lockSteps := max 1 (if trap.respawnDelaySteps = 0 then 2 else trap.respawnDelaySteps)
  let w1 := setCurrentRoom w updatedRoom
  if newHealth = 0 then
    { w1 with health := newHealth }
  else
    { w1 with
        health := newHealth
        controlLockStepsRemaining := lockSteps
        pendingRespawn := some newPlayer }

def applyExit (w : WorldState) (e : Exit) : WorldState :=
  let sourceRoom := currentRoom w
  let consumeNow := e.exitType == .lockedKey && !e.unlocked && e.consumeKey
  let updatedSourceRoom :=
    if e.exitType == .lockedKey && !e.unlocked then
      { sourceRoom with exits := unlockExitById sourceRoom.exits e.exitId }
    else
      sourceRoom
  let w1 := setCurrentRoom w updatedSourceRoom
  let newKeys :=
    if consumeNow then
      w1.keys - e.requiresKeyCount
    else
      w1.keys
  let completed := w1.environmentCompleted || e.completeTask
  match roomByIdIdx? w1.rooms e.targetRoomId with
  | some idx =>
      let targetRoom := (getAt? w1.rooms idx).getD default
      { w1 with
          currentRoomIdx := idx
          player := entrySpawnPos targetRoom e.targetEntry
          keys := newKeys
          environmentCompleted := completed
          controlLockStepsRemaining := 0
          pendingRespawn := none }
  | none =>
      { w1 with
          keys := newKeys
          environmentCompleted := completed
          controlLockStepsRemaining := 0
          pendingRespawn := none }

def onMonsterKilled (w : WorldState) (monster : Monster) : WorldState :=
  let room := currentRoom w
  let remaining := removeMonsterById room.monsters monster.monsterId
  let updatedRoom :=
    { room with
        monsters := remaining
        exits :=
          if remaining.isEmpty then
            unlockMonsterGatedExits room.exits
          else
            room.exits }
  let w1 := { (setCurrentRoom w updatedRoom) with gold := w.gold + 2 }
  if remaining.isEmpty then
    { w1 with rooms := revealMonsterTriggeredChests w1.rooms room.roomId }
  else
    w1

def applySwitchToggle (w : WorldState) (sw : Switch) : WorldState :=
  let room := currentRoom w
  let w1 := setCurrentRoom w { room with switches := pressSwitchById room.switches sw.switchId }
  match dynamicObjectById? w1.rooms sw.targetObjectId with
  | some obj =>
      match nextStateInOrder? sw.order obj.currentState with
      | some nextState => { w1 with rooms := setDynamicObjectState w1.rooms sw.targetObjectId nextState }
      | none => w1
  | none => w1

def resolveMonsterContact (w : WorldState) : WorldState :=
  match (currentRoom w).monsters.find? (fun m => m.pos == w.player && m.stunTicksRemaining = 0) with
  | some monster =>
      let room := currentRoom w
      let updatedRoom := { room with monsters := setMonsterStunById room.monsters monster.monsterId 60 }
      let w1 := setCurrentRoom w updatedRoom
      if shieldActive w then
        w1
      else
        { w1 with health := w1.health - monster.damage }
  | none => w

def applyTileEffects (w previous : WorldState) : WorldState :=
  let room := currentRoom w
  let afterButton :=
    match buttonAt? room w.player with
    | some button =>
      if button.isPressed then
          w
        else
          setCurrentRoom w { room with buttons := pressButtonById room.buttons button.buttonId }
    | none => w
  let roomAfterButton := currentRoom afterButton
  let afterTrap :=
    match trapAt? roomAfterButton afterButton.player with
    | some trap =>
        match trap.trapType with
        | .spike => resolveSpikeTrap afterButton trap
        | .abyss => resolveAbyssTrap afterButton trap previous.player
    | none => afterButton
  afterTrap

def basicMove (w : WorldState) (d : Direction) : WorldState :=
  let target := facingTile w.player d
  let turned := { w with facing := d }
  if canOccupy (currentRoom w) target then
    { turned with player := target }
  else
    turned

def moveStep (w : WorldState) (d : Direction) : WorldState :=
  let moved := basicMove w d
  match exitAt? (currentRoom moved) moved.player d with
  | some e =>
      if exitConditionSatisfied moved e then
        applyExit moved e
      else
        moved
  | none => moved

def interactStep (w : WorldState) : WorldState × Bool :=
  let room := currentRoom w
  match room.chests.find? (fun c => c.isVisible && !c.isOpen && adjacent w.player c.pos) with
  | some chest =>
      let w1 := setCurrentRoom w { room with chests := openChestById room.chests chest.chestId }
      (applyLoot w1 chest.loot, false)
  | none =>
      match room.npcs.find? (fun n => adjacent w.player n.pos) with
      | some _ => (w, false)
      | none =>
          match room.switches.find? (fun sw => adjacent w.player sw.pos) with
          | some sw => (applySwitchToggle w sw, false)
          | none =>
              if !hasEquippedSword w then
                (w, false)
              else
                match room.monsters.find? (fun m => adjacent w.player m.pos && facingTile w.player w.facing == m.pos) with
                | some monster =>
                    let acting := startAction w "sword" w.facing 6
                    if monster.hp ≤ 1 then
                      (onMonsterKilled acting monster, true)
                    else
                      let updatedRoom := {
                        room with monsters := setMonsterStunById (reduceMonsterHpById room.monsters monster.monsterId) monster.monsterId 60
                      }
                      (setCurrentRoom acting updatedRoom, true)
                | none => (startAction w "sword" w.facing 6, true)

def actionStep (w : WorldState) (a : Action) : WorldState × Bool :=
  match a with
  | .wait => (w, false)
  | .up => (moveStep w .up, false)
  | .down => (moveStep w .down, false)
  | .left => (moveStep w .left, false)
  | .right => (moveStep w .right, false)
  | .interactA => interactStep w
  | .shieldB =>
      if hasEquippedShield w then
        (startAction w "shield" w.facing 6, true)
      else
        (w, false)

def postActionResolve (before after : WorldState) (_a : Action) : WorldState :=
  let afterTiles :=
    if after.health = 0 then
      after
    else
      applyTileEffects after before
  if afterTiles.health = 0 then
    afterTiles
  else
    resolveMonsterContact (updateMonstersCurrentRoom afterTiles)

def step (w : WorldState) (a : Action) : WorldState :=
  if w.controlLockStepsRemaining > 0 then
    advanceControlLock w
  else if w.health = 0 then
    w
  else
    let w0 := advancePlayerActionState w
    let (acted, actionStarted) := actionStep w0 a
    let settled := postActionResolve w0 acted a
    finalizePlayerActionState settled actionStarted

theorem inBounds_of_canOccupy {r : RoomState} {p : Position}
    (h : canOccupy r p = true) : InBounds p := by
  have hb : inBounds p = true := by
    simp [canOccupy] at h
    exact h.1
  unfold inBounds at hb
  simp at hb
  exact hb

theorem blocked_basicMove_keeps_player {w : WorldState} {d : Direction}
    (h : canOccupy (currentRoom w) (facingTile w.player d) = false) :
    (basicMove w d).player = w.player := by
  simp [basicMove, h]

theorem free_basicMove_moves_player {w : WorldState} {d : Direction}
    (h : canOccupy (currentRoom w) (facingTile w.player d) = true) :
    (basicMove w d).player = facingTile w.player d := by
  simp [basicMove, h]

theorem free_basicMove_stays_in_bounds {w : WorldState} {d : Direction}
    (h : canOccupy (currentRoom w) (facingTile w.player d) = true) :
    InBounds (basicMove w d).player := by
  rw [free_basicMove_moves_player h]
  exact inBounds_of_canOccupy h

theorem heal_loot_preserves_max_health (w : WorldState) (n : Nat) :
    (applyLoot w { kind := .heal, amount := n }).health ≤ w.maxHealth := by
  simp [applyLoot]
  exact Nat.min_le_left _ _

theorem spike_trap_never_increases_health (w : WorldState) (trap : Trap) :
    (resolveSpikeTrap w trap).health ≤ w.health := by
  simp [resolveSpikeTrap]

theorem abyss_trap_never_increases_health (w : WorldState) (trap : Trap) (previous : Position) :
    (resolveAbyssTrap w trap previous).health ≤ w.health := by
  by_cases hs : trap.singleUse
  · by_cases hh : w.health - trap.damage = 0
    · simp [resolveAbyssTrap, hs, hh]
    · simp [resolveAbyssTrap, hs, hh]
  · by_cases hh : w.health - trap.damage = 0
    · simp [resolveAbyssTrap, hs, hh]
    · simp [resolveAbyssTrap, hs, hh]

theorem bridge_hides_trap {r : RoomState} {p : Position}
    (h : dynamicTileAt r p = .bridge) :
    trapAt? r p = none := by
  have hb : (dynamicTileAt r p == .bridge) = true := by
    rw [h]
    rfl
  unfold trapAt?
  rw [if_pos hb]

theorem sword_loot_equips_slotA (w : WorldState) :
    (applyLoot w
      { kind := .item
        itemName := some "sword"
        toolName := some "sword"
        equipSlot := some .A }).equippedA = "sword" := by
  simp [applyLoot, setEquippedSlot, addItem, containsString]

theorem locked_exit_without_keys_denied (w : WorldState) (required : Nat)
    (h : w.keys < required) :
    exitConditionSatisfied w
      { (default : Exit) with
          exitType := .lockedKey
          unlocked := false
          requiresKeyCount := required } = false := by
  simp [exitConditionSatisfied, Nat.not_le_of_gt h]

theorem goalReached_of_allChestsOpened {w : WorldState}
    (hExit : w.worldCompletionViaExit = false)
    (hChests : allChestsOpened w = true) :
    goalReached w = true := by
  simp [goalReached, hExit, hChests]

theorem applyExit_completeTask_sets_goalReached (w : WorldState) (e : Exit) :
    e.completeTask = true →
    goalReached (applyExit w e) = true := by
  intro h
  simp [goalReached, applyExit]
  split <;> simp [h]

theorem shieldB_without_shield_does_not_raise (w : WorldState)
    (h : hasEquippedShield w = false) :
    actionStep w .shieldB = (w, false) := by
  simp [actionStep, h]

def task1GoalRoom : RoomState :=
  { roomId := "task1_goal"
    walls := []
    chests := []
    traps := []
    buttons := []
    switches := []
    npcs := []
    monsters := []
    exits := []
    dynamicObjects := []
    spawns := [("west", (1, 3)), ("default", (1, 3))]
    defaultSpawn := (1, 3) }

def task1Room : RoomState :=
  { roomId := "task1_start"
    walls := [(3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7)]
    chests := [{
      chestId := "key_chest"
      pos := (1, 3)
      loot := { kind := .key, amount := 1 }
    }]
    traps := []
    buttons := []
    switches := []
    npcs := []
    monsters := []
    exits := [{
      exitId := "task1_exit"
      direction := .right
      tiles := [(9, 3), (9, 4)]
      exitType := .lockedKey
      requiresKeyCount := 1
      consumeKey := true
      unlocked := false
      completeTask := true
      targetRoomId := "task1_goal"
      targetEntry := "west"
    }]
    dynamicObjects := []
    spawns := [("default", (7, 3))]
    defaultSpawn := (7, 3) }

def task1Init : WorldState :=
  { player := (7, 3)
    facing := .left
    health := 5
    maxHealth := 5
    keys := 0
    gold := 0
    items := []
    tools := []
    equippedA := "none"
    equippedB := "none"
    actionItem := none
    actionFacing := none
    actionTicksRemaining := 0
    controlLockStepsRemaining := 0
    pendingRespawn := none
    environmentCompleted := false
    rooms := [task1Room, task1GoalRoom]
    currentRoomIdx := 0
    worldCompletionViaExit := true }

def task4Bridge : DynamicObject :=
  { objectId := "center_bridge"
    initialState := "west_to_north"
    states := [
      { stateId := "west_to_north"
        tiles := [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
                  (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4),
                  (4, 0), (5, 0), (4, 1), (5, 1), (4, 2), (5, 2)] },
      { stateId := "west_to_east"
        tiles := [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (7, 3), (8, 3), (9, 3),
                  (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4), (6, 4), (7, 4), (8, 4), (9, 4)] },
      { stateId := "west_to_south"
        tiles := [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
                  (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4),
                  (4, 5), (5, 5), (4, 6), (5, 6), (4, 7), (5, 7)] }
    ]
    backgroundTile := .none
    activeTile := .bridge
    currentState := "west_to_north" }

def task4Room : RoomState :=
  { roomId := "task4_center"
    walls := []
    chests := [{
      chestId := "final_chest"
      pos := (4, 4)
      loot := { kind := .gold, amount := 1 }
      isVisible := false
      revealOnAllMonstersDefeated := true
      revealTriggerRoomId := some "south"
    }]
    traps := [{
      trapId := "center_abyss"
      pos := (4, 4)
      trapType := .abyss
      damage := 1
      respawnTo := "default"
      respawnDelaySteps := 2
    }]
    buttons := []
    switches := [{
      switchId := "switch_1"
      pos := (2, 2)
      targetObjectId := "center_bridge"
      order := ["west_to_north", "west_to_east", "west_to_south"]
    }]
    npcs := []
    monsters := []
    exits := []
    dynamicObjects := [task4Bridge]
    spawns := [("default", (1, 4)), ("west_door", (1, 4)), ("east_door", (8, 4)),
               ("from_north", (4, 1)), ("from_south", (4, 6))]
    defaultSpawn := (1, 4) }

def task4Init : WorldState :=
  { player := (1, 4)
    facing := .right
    health := 5
    maxHealth := 5
    keys := 0
    gold := 0
    items := ["shield"]
    tools := ["shield"]
    equippedA := "none"
    equippedB := "shield"
    actionItem := none
    actionFacing := none
    actionTicksRemaining := 0
    controlLockStepsRemaining := 0
    pendingRespawn := none
    environmentCompleted := false
    rooms := [task4Room]
    currentRoomIdx := 0
    worldCompletionViaExit := true }

example : dynamicTileAt task4Room (8, 4) = .none := by
  native_decide

example : dynamicTileAt
    ({ task4Room with
        dynamicObjects := [{ task4Bridge with currentState := "west_to_east" }] }) (8, 4) = .bridge := by
  native_decide

end EnvFormalization

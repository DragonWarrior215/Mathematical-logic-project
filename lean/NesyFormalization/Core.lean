namespace NesyFormalization

/-!
  NesyLink 数理逻辑任务的基础符号环境模型。

  这个文件的目标不是刻画某一个具体关卡，而是抽出能被多个关卡复用的公共语义：
  玩家、怪物、宝箱、按钮、开关、出口、物品栏，以及与它们相关的一步转移规则。

  这里刻画的是 `nsi_agent` 依赖的“符号层”，而不是完整的像素渲染或真实引擎的每个
  细节。这样做的好处是：后续每个关卡文件只需要给出自己的初始地图、对象摆放和目
  标谓词，就能复用这里的定义和证明框架。
-/

/-- 10 x 8 可玩网格上的 tile 坐标 `(x, y)`。 -/
abbrev Position := Nat × Nat

/-- 来自 `nsi_agent/constants.py` 的公开房间尺寸。 -/
def gridWidth : Nat := 10
def gridHeight : Nat := 8

/-- 默认最大生命值，用于回血类 loot 的裁剪。 -/
def maxPlayerHp : Nat := 5

/-- 方向同时用于移动、朝向和出口朝向。 -/
inductive Facing where
  | up
  | down
  | left
  | right
  deriving DecidableEq, Repr

/--
  抽象动作，对应环境里的 WAIT、四个移动动作以及 A/B 两个槽位。

  这里保留 `interact` / `defend` 命名，是为了让第一层形式化更容易读；语义上
  可以分别理解为“触发 A 槽动作”和“触发 B 槽动作”。
-/
inductive Action where
  | wait
  | move (dir : Facing)
  | interact
  | defend
  deriving DecidableEq, Repr

/-- 出口状态与 `grounding/schema.py` 对齐。 -/
inductive ExitState where
  | none
  | normal
  | locked
  | conditional
  | open
  deriving DecidableEq, Repr

/-- 怪物类型与环境里的三种内置 monster 对齐。 -/
inductive MonsterKind where
  | chaser
  | patroller
  | ambusher
  deriving DecidableEq, Repr

/-- 宝箱内 loot 的大类。 -/
inductive LootKind where
  | key
  | gold
  | heal
  | item
  deriving DecidableEq, Repr

/--
  第一层证明里会用到的物品栏视图。

  这里把 `nsi_agent` 和环境接口里会出现的关键字段都纳入进来：钥匙、金币、道具、
  工具，以及 A/B 槽当前装备了什么。
-/
structure Inventory where
  keys : Nat := 0
  gold : Nat := 0
  items : List String := []
  tools : List String := []
  equippedA : Option String := none
  equippedB : Option String := none
  deriving DecidableEq, Repr

/-- 宝箱 loot 的抽象表示。 -/
structure ChestLoot where
  kind : LootKind
  amount : Nat := 1
  itemId : Option String := none
  tool : Option String := none
  equipSlot : Option String := none
  deriving DecidableEq, Repr

/-- 符号层中的宝箱对象。 -/
structure Chest where
  pos : Position
  loot : ChestLoot
  opened : Bool := false
  deriving DecidableEq, Repr

/-- 符号层中的怪物对象。 -/
structure Monster where
  pos : Position
  kind : MonsterKind
  hp : Nat
  damage : Nat := 1
  deriving DecidableEq, Repr

/--
  出口的门禁条件。

  这层抽象覆盖了课程环境里几种关键约束：钥匙数量、是否消耗钥匙、是否要求清空怪
  物、是否要求至少有一个按钮被按下，以及是否要求持有某个物品。
-/
structure ExitRequirement where
  requiredKeys : Nat := 0
  consumeKey : Bool := false
  needAllMonstersDefeated : Bool := false
  needPressedButton : Bool := false
  requiredItem : Option String := none
  deriving DecidableEq, Repr

/-- 带有方向、状态和过门条件的出口描述。 -/
structure Exit where
  dir : Facing
  state : ExitState
  requirement : ExitRequirement := {}
  completeTask : Bool := false
  deriving DecidableEq, Repr

/--
  一个可跨关卡复用的紧凑符号状态。

  这里依旧使用 `List` 而不是有限集合，避免引入 Mathlib 依赖；在这里我们只关注
  成员关系，因此重复元素不会影响安全性和可达性证明。
-/
structure SymbolicState where
  player : Position
  facing : Facing := .down
  hp : Nat := maxPlayerHp
  inventory : Inventory := {}
  walls : List Position := []
  traps : List Position := []
  abysses : List Position := []
  gaps : List Position := []
  bridges : List Position := []
  buttonsUp : List Position := []
  buttonsPressed : List Position := []
  switchesIdle : List Position := []
  switchesActive : List Position := []
  npcs : List Position := []
  chests : List Chest := []
  monsters : List Monster := []
  exits : List Exit := []
  roomChanged : Bool := false
  worldComplete : Bool := false
  deriving Repr

/-- 一个 tile 位于 10 x 8 的可玩房间内部。 -/
def inBounds (p : Position) : Prop :=
  p.1 < gridWidth ∧ p.2 < gridHeight

/-- `Nat` 上的绝对差，用来定义网格距离。 -/
def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- 两个 tile 的曼哈顿距离。 -/
def manhattan (p q : Position) : Nat :=
  absDiff p.1 q.1 + absDiff p.2 q.2

/--
  沿某个方向前进一个 tile。

  由于坐标类型是 `Nat`，从 `x = 0` 向左移动或从 `y = 0` 向上移动时会饱和在
  0；随后再由 `walkable` 或出口语义判断这一步是否合法。
-/
def advance (p : Position) : Facing → Position
  | .up => (p.1, p.2 - 1)
  | .down => (p.1, p.2 + 1)
  | .left => (p.1 - 1, p.2)
  | .right => (p.1 + 1, p.2)

/--
  正交相邻的 tile 邻接关系。

  这里不用 `advance` 来定义邻接，因为 `Nat` 的减法在边界会饱和；例如从
  `(0, 0)` 向左“前进”仍会得到 `(0, 0)`。显式写出四邻接等式，可以避免边界处
  出现“自己邻接自己”的退化情形，也方便 task 文件中的 `simp [adjacent]` 自动化。
-/
def adjacent (p q : Position) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

/-- 引擎视为出口的边界 tile。 -/
def exitTiles : Facing → List Position
  | .up => [(4, 0), (5, 0)]
  | .down => [(4, 7), (5, 7)]
  | .left => [(0, 3), (0, 4)]
  | .right => [(9, 3), (9, 4)]

/-- 物品栏是否包含指定物品或工具。 -/
def inventoryHas (inv : Inventory) (name : String) : Prop :=
  name ∈ inv.items ∨
  name ∈ inv.tools ∨
  inv.equippedA = some name ∨
  inv.equippedB = some name

/-- 玩家当前是否具备剑能力。 -/
def hasSword (s : SymbolicState) : Prop :=
  inventoryHas s.inventory "sword"

/-- 查询某个方向的出口描述。 -/
def exitAt? (s : SymbolicState) (dir : Facing) : Option Exit :=
  s.exits.find? (fun e => e.dir = dir)

/-- 查询某个方向的出口状态；若查不到则表示没有出口。 -/
def exitState (s : SymbolicState) (dir : Facing) : ExitState :=
  match exitAt? s dir with
  | some e => e.state
  | none => .none

/-- 查询某个位置上的宝箱。 -/
def chestAt? (s : SymbolicState) (pos : Position) : Option Chest :=
  s.chests.find? (fun c => c.pos = pos)

/-- 查询某个位置上的怪物。 -/
def monsterAt? (s : SymbolicState) (pos : Position) : Option Monster :=
  s.monsters.find? (fun m => m.pos = pos)

/-- 所有尚未打开的宝箱。 -/
def closedChests (s : SymbolicState) : List Chest :=
  s.chests.filter (fun c => !c.opened)

/-- 所有已经打开的宝箱。 -/
def openedChests (s : SymbolicState) : List Chest :=
  s.chests.filter (fun c => c.opened)

/-- 任何状态的宝箱在环境里都阻挡移动。 -/
def isChestTile (s : SymbolicState) (p : Position) : Prop :=
  ∃ c, c ∈ s.chests ∧ c.pos = p

/-- 怪物所在 tile。 -/
def isMonsterTile (s : SymbolicState) (p : Position) : Prop :=
  ∃ m, m ∈ s.monsters ∧ m.pos = p

/-- 由于会阻挡移动，规划器不应进入这些 tile。 -/
def isBlockingTile (s : SymbolicState) (p : Position) : Prop :=
  p ∈ s.walls ∨ p ∈ s.npcs ∨ p ∈ s.gaps ∨ isChestTile s p

/-- 规划器视为有伤害或不安全的 tile。 -/
def isHazardTile (s : SymbolicState) (p : Position) : Prop :=
  p ∈ s.traps ∨ p ∈ s.abysses ∨ isMonsterTile s p

/--
  带 `allowHazard` 开关的可行走谓词。

  `allowHazard = true` 时只放宽陷阱/深渊/怪物这类风险约束；边界和硬阻塞仍然必须
  满足。这对应 Python 里 `walkable(..., allow_hazard=True)` 的语义。
-/
def walkableWithHazard (s : SymbolicState) (p : Position) (allowHazard : Bool) : Prop :=
  inBounds p ∧ ¬ isBlockingTile s p ∧ (allowHazard = false → ¬ isHazardTile s p)

/-- 一个严格可行走 tile 必须在边界内、不可阻挡且不危险。 -/
def walkable (s : SymbolicState) (p : Position) : Prop :=
  inBounds p ∧ ¬ isBlockingTile s p ∧ ¬ isHazardTile s p

/-- 当宝箱处于关闭状态且与玩家正交相邻时，玩家可以开启它。 -/
def canOpenChest (s : SymbolicState) (chest : Chest) : Prop :=
  chest ∈ s.chests ∧ chest.opened = false ∧ adjacent s.player chest.pos

/-- 玩家是否可以攻击某个怪物。 -/
def canAttackMonster (s : SymbolicState) (monster : Monster) : Prop :=
  monster ∈ s.monsters ∧ hasSword s ∧ adjacent s.player monster.pos

/-- 玩家是否可以切换某个开关。 -/
def canToggleSwitch (s : SymbolicState) (pos : Position) : Prop :=
  pos ∈ s.switchesIdle ∨ pos ∈ s.switchesActive

/-- 玩家是否可以与某个 NPC 对话。 -/
def canTalkNpc (s : SymbolicState) (pos : Position) : Prop :=
  pos ∈ s.npcs ∧ adjacent s.player pos

/-- 出口条件是否满足。 -/
def exitRequirementMet (s : SymbolicState) (req : ExitRequirement) : Prop :=
  req.requiredKeys ≤ s.inventory.keys ∧
  (req.needAllMonstersDefeated → s.monsters = []) ∧
  (req.needPressedButton → s.buttonsPressed ≠ []) ∧
  match req.requiredItem with
  | some name => inventoryHas s.inventory name
  | none => True

/--
  一个可穿越的出口，指的是：玩家站在所选方向的出口 tile 上，并且该出口条件成立。
-/
def canTraverseExit (s : SymbolicState) (dir : Facing) : Prop :=
  s.player ∈ exitTiles dir ∧
  ∃ e, exitAt? s dir = some e ∧
    match e.state with
    | .normal => True
    | .open => True
    | .locked => exitRequirementMet s e.requirement
    | .conditional => exitRequirementMet s e.requirement
    | .none => False

/-- 穿越某个出口时对物品栏的影响。 -/
def consumeKeysForExit (inv : Inventory) (req : ExitRequirement) : Inventory :=
  if req.consumeKey then
    { inv with keys := inv.keys - req.requiredKeys }
  else
    inv

/-- 宝箱 loot 对物品栏的影响。 -/
def applyLootToInventory (inv : Inventory) (loot : ChestLoot) : Inventory :=
  match loot.kind with
  | .key =>
      { inv with keys := inv.keys + loot.amount }
  | .gold =>
      { inv with gold := inv.gold + loot.amount }
  | .heal =>
      inv
  | .item =>
      let inv1 := match loot.itemId with
        | some itemId => { inv with items := itemId :: inv.items }
        | none => inv
      let inv2 := match loot.tool with
        | some tool => { inv1 with tools := tool :: inv1.tools }
        | none => inv1
      match loot.equipSlot, loot.tool with
      | some "A", some tool => { inv2 with equippedA := some tool }
      | some "B", some tool => { inv2 with equippedB := some tool }
      | _, _ => inv2

/-- 宝箱 loot 对生命值的影响。 -/
def applyLootToHp (hp : Nat) (loot : ChestLoot) : Nat :=
  match loot.kind with
  | .heal => Nat.min maxPlayerHp (hp + loot.amount)
  | _ => hp

/-- 将某个宝箱标记为已打开。 -/
def openChestList (chests : List Chest) (chest : Chest) : List Chest :=
  { chest with opened := true } :: chests.erase chest

/-- 将某个怪物受到一次攻击后的列表更新。 -/
def damageMonsterList (monsters : List Monster) (monster : Monster) : List Monster :=
  if monster.hp ≤ 1 then
    monsters.erase monster
  else
    { monster with hp := monster.hp - 1 } :: monsters.erase monster

/-- 将某个出口更新为开放状态。 -/
def openExitList (exits : List Exit) (exit : Exit) : List Exit :=
  { exit with state := .open } :: exits.erase exit

/--
  一步符号转移。

  这里把“普通行走”和“穿越出口”分成两个不同的移动分支；同时对 A 槽动作给出
  了几类环境里常见的效果：开箱、攻击怪物、切换开关、与 NPC 交互，以及无效果。
-/
inductive Step : SymbolicState → Action → SymbolicState → Prop where
  | moveWalk
      {s : SymbolicState} {dir : Facing} :
      walkable s (advance s.player dir) →
      ¬ canTraverseExit s dir →
      Step s (.move dir) { s with player := advance s.player dir, facing := dir }
  | moveBlocked
      {s : SymbolicState} {dir : Facing} :
      ¬ walkable s (advance s.player dir) →
      ¬ canTraverseExit s dir →
      Step s (.move dir) { s with facing := dir }
  | moveExit
      {s : SymbolicState} {dir : Facing} {e : Exit} :
      exitAt? s dir = some e →
      canTraverseExit s dir →
      Step s (.move dir)
        { s with
            facing := dir
            inventory := consumeKeysForExit s.inventory e.requirement
            exits := openExitList s.exits e
            roomChanged := true
            worldComplete := s.worldComplete || e.completeTask }
  | interactOpenChest
      {s : SymbolicState} {chest : Chest} :
      canOpenChest s chest →
      Step s .interact
        { s with
            hp := applyLootToHp s.hp chest.loot
            inventory := applyLootToInventory s.inventory chest.loot
            chests := openChestList s.chests chest }
  | interactAttackMonster
      {s : SymbolicState} {monster : Monster} :
      canAttackMonster s monster →
      Step s .interact
        { s with monsters := damageMonsterList s.monsters monster }
  | interactToggleSwitch
      {s : SymbolicState} {pos : Position} :
      canToggleSwitch s pos →
      Step s .interact
        { s with
            switchesIdle := s.switchesIdle.erase pos
            switchesActive := pos :: s.switchesActive }
  | interactTalkNpc
      {s : SymbolicState} {pos : Position} :
      canTalkNpc s pos →
      Step s .interact s
  | interactNoEffect
      {s : SymbolicState} :
      (∀ chest, ¬ canOpenChest s chest) →
      (∀ monster, ¬ canAttackMonster s monster) →
      (∀ pos, ¬ canToggleSwitch s pos) →
      (∀ pos, ¬ canTalkNpc s pos) →
      Step s .interact s
  | wait
      {s : SymbolicState} :
      Step s .wait s
  | defend
      {s : SymbolicState} :
      Step s .defend s

/-- 后续移动与规划证明会复用的基本玩家安全不变式。 -/
def SafeState (s : SymbolicState) : Prop :=
  inBounds s.player ∧ ¬ isBlockingTile s s.player ∧ ¬ isHazardTile s s.player

/-- 绝对差是对称的。 -/
theorem absDiff_comm (a b : Nat) : absDiff a b = absDiff b a := by
  unfold absDiff
  split <;> split <;> omega

/-- 自己到自己的绝对差为 0。 -/
theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  unfold absDiff
  simp

/-- 相等的两个自然数绝对差为 0。 -/
theorem absDiff_eq_zero_of_eq {a b : Nat} (h : a = b) : absDiff a b = 0 := by
  subst b
  exact absDiff_self a

/-- 若 `a + 1 = b`，则二者绝对差为 1。 -/
theorem absDiff_eq_one_of_add_one_left {a b : Nat} (h : a + 1 = b) :
    absDiff a b = 1 := by
  unfold absDiff
  split <;> omega

/-- 若 `b + 1 = a`，则二者绝对差为 1。 -/
theorem absDiff_eq_one_of_add_one_right {a b : Nat} (h : b + 1 = a) :
    absDiff a b = 1 := by
  rw [absDiff_comm]
  exact absDiff_eq_one_of_add_one_left h

/-- 曼哈顿距离是对称的。 -/
theorem manhattan_comm (p q : Position) : manhattan p q = manhattan q p := by
  unfold manhattan
  rw [absDiff_comm p.1 q.1, absDiff_comm p.2 q.2]

/-- 自己到自己的曼哈顿距离为 0。 -/
theorem manhattan_self (p : Position) : manhattan p p = 0 := by
  unfold manhattan
  simp [absDiff_self]

/-- 邻接关系是对称的。 -/
theorem neighbor_symm {p q : Position} (h : adjacent p q) : adjacent q p := by
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · left
    refine ⟨hx.symm, ?_⟩
    rcases hy with hy | hy
    · right
      exact hy
    · left
      exact hy
  · right
    refine ⟨hy.symm, ?_⟩
    rcases hx with hx | hx
    · right
      exact hx
    · left
      exact hx

/-- 任意两个邻接格子的曼哈顿距离为 1。 -/
theorem neighbor_manhattan {p q : Position} (h : adjacent p q) : manhattan p q = 1 := by
  unfold adjacent manhattan at *
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hy with hy | hy
    · rw [absDiff_eq_zero_of_eq hx, absDiff_eq_one_of_add_one_left hy]
    · rw [absDiff_eq_zero_of_eq hx, absDiff_eq_one_of_add_one_right hy]
  · rcases hx with hx | hx
    · rw [absDiff_eq_zero_of_eq hy, absDiff_eq_one_of_add_one_left hx]
    · rw [absDiff_eq_zero_of_eq hy, absDiff_eq_one_of_add_one_right hx]

/-- 一个格子不会与自己构成邻接关系。 -/
theorem neighbor_ne {p q : Position} (h : adjacent p q) : p ≠ q := by
  intro heq
  subst heq
  unfold adjacent at h
  omega

/-- 可行走性蕴含候选 tile 一定在房间内部。 -/
theorem walkable_inBounds {s : SymbolicState} {p : Position}
    (h : walkable s p) : inBounds p := by
  exact h.1

/-- 可行走格子一定不是阻塞格。 -/
theorem walkable_not_blocking {s : SymbolicState} {p : Position}
    (h : walkable s p) : ¬ isBlockingTile s p := by
  exact h.2.1

/-- 可行走格子一定不是危险格。 -/
theorem walkable_not_hazard {s : SymbolicState} {p : Position}
    (h : walkable s p) : ¬ isHazardTile s p := by
  exact h.2.2

/-- 允许危险格时，几何约束仍保证不越界且不进入硬阻塞。 -/
theorem walkable_allow_hazard_geometry {s : SymbolicState} {p : Position}
    (h : walkableWithHazard s p true) : inBounds p ∧ ¬ isBlockingTile s p := by
  exact ⟨h.1, h.2.1⟩

/-- 严格可行走蕴含宽松可行走。 -/
theorem walkable_mono {s : SymbolicState} {p : Position}
    (h : walkableWithHazard s p false) : walkableWithHazard s p true := by
  exact ⟨h.1, h.2.1, by intro hfalse; cases hfalse⟩

/-- 若一次普通移动是可行走的，且当前并非出口穿越，那么玩家会前进到目标位置。 -/
theorem moveWalk_player_eq
    {s t : SymbolicState} {dir : Facing}
    (h : Step s (.move dir) t)
    (hw : walkable s (advance s.player dir))
    (hnotExit : ¬ canTraverseExit s dir) :
    t.player = advance s.player dir := by
  cases h with
  | moveWalk _ _ =>
      rfl
  | moveBlocked hblocked hnoexit =>
      exact False.elim (hblocked hw)
  | moveExit hexit hexitOk =>
      exact False.elim (hnotExit hexitOk)

/-- 普通成功移动会保持局部安全不变式：目标位置在边界内、不可阻挡且不危险。 -/
theorem moveWalk_preservesSafe
    {s t : SymbolicState} {dir : Facing}
    (hs : Step s (.move dir) t)
    (hw : walkable s (advance s.player dir))
    (hnotExit : ¬ canTraverseExit s dir) :
    SafeState t := by
  cases hs with
  | moveWalk hw' _ =>
      unfold SafeState
      simpa [walkable] using hw'
  | moveBlocked hblocked hnoexit =>
      exact False.elim (hblocked hw)
  | moveExit hexit hexitOk =>
      exact False.elim (hnotExit hexitOk)

end NesyFormalization

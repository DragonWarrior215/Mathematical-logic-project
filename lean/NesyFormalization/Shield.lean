import NesyFormalization.Core

namespace NesyFormalization

set_option linter.unnecessarySimpa false

/-!
  Safety shield 的抽象形式化。

  Python 中的 `shielded` 使用像素坐标和 Chebyshev 距离保护玩家不进入怪物的
  uncertainty ball。这里先在 tile 层给出同构的抽象版本：怪物有位置和不确定半径，
  危险区随不确定半径扩大；若一个移动会进入危险区，shield 不能原样放行该移动。
-/

/-- tracker 中记录的怪物位置和不确定半径。 -/
structure TrackedMonster where
  pos : Position
  uncertainty : Nat := 0
  deriving DecidableEq, Repr

/-- tile 层 Chebyshev 距离，模拟 Python 中 `max(abs(dx), abs(dy))` 的保护逻辑。 -/
def chebyshev (p q : Position) : Nat :=
  Nat.max (absDiff p.1 q.1) (absDiff p.2 q.2)

/-- 怪物的危险半径。这里的 `+ 1` 抽象了怪物/玩家碰撞盒自身大小。 -/
def dangerRadius (m : TrackedMonster) : Nat :=
  m.uncertainty + 1

/-- 某位置是否落入单个怪物的不确定危险区。 -/
def inMonsterDanger (p : Position) (m : TrackedMonster) : Prop :=
  chebyshev p m.pos ≤ dangerRadius m

/-- 某位置是否落入任意已跟踪怪物的危险区。 -/
def inDangerRegion (monsters : List TrackedMonster) (p : Position) : Prop :=
  ∃ m, m ∈ monsters ∧ inMonsterDanger p m

/-- 带额外 margin 的怪物禁入格；边界条件直接放进谓词里，便于后续证明。 -/
def monsterBlockedTile (m : TrackedMonster) (margin : Nat) (p : Position) : Prop :=
  inBounds p ∧ chebyshev p m.pos ≤ dangerRadius m + margin

/-- 在当前 tracker 包络下，某位置是安全的。 -/
def positionSafe (monsters : List TrackedMonster) (p : Position) : Prop :=
  ¬ inDangerRegion monsters p

/-- 一步动作的安全性：移动动作要求下一 tile 安全，非移动动作不改变位置。 -/
def actionSafe
    (s : SymbolicState) (monsters : List TrackedMonster) : Action → Prop
  | .move dir => positionSafe monsters (advance s.player dir)
  | .wait => True
  | .interact => True
  | .defend => True

/-- tracker 未重新感知时，不确定半径会保守增长。 -/
def growUncertainty (delta : Nat) (m : TrackedMonster) : TrackedMonster :=
  { m with uncertainty := m.uncertainty + delta }

/-- danger region 对 uncertainty 单调：半径增长后，原本危险的位置仍然危险。 -/
theorem inMonsterDanger_grow
    {p : Position} {m : TrackedMonster} {delta : Nat}
    (h : inMonsterDanger p m) :
    inMonsterDanger p (growUncertainty delta m) := by
  unfold inMonsterDanger dangerRadius growUncertainty at *
  have hone : 1 ≤ delta + 1 := Nat.succ_le_succ (Nat.zero_le delta)
  have hrad : m.uncertainty + 1 ≤ m.uncertainty + (delta + 1) :=
    Nat.add_le_add_left hone m.uncertainty
  exact Nat.le_trans h (by simpa [Nat.add_assoc] using hrad)

/-- 对整组怪物同样成立：增长 uncertainty 不会缩小危险区。 -/
theorem inDangerRegion_grow_head
    {p : Position} {m : TrackedMonster} {ms : List TrackedMonster} {delta : Nat}
    (h : inDangerRegion (m :: ms) p) :
    inDangerRegion (growUncertainty delta m :: ms.map (growUncertainty delta)) p := by
  rcases h with ⟨m', hm', hdanger⟩
  cases hm' with
  | head =>
      exact ⟨growUncertainty delta m, by simp, inMonsterDanger_grow hdanger⟩
  | tail _ htail =>
      have hmem : growUncertainty delta m' ∈
          growUncertainty delta m :: ms.map (growUncertainty delta) := by
        simp only [List.mem_cons, List.mem_map]
        right
        exact ⟨m', htail, rfl⟩
      exact ⟨growUncertainty delta m', hmem, inMonsterDanger_grow hdanger⟩

/-- 怪物禁入格的定义已经包含地图边界条件。 -/
theorem monster_blocked_in_bounds
    {m : TrackedMonster} {margin : Nat} {p : Position}
    (h : monsterBlockedTile m margin p) : inBounds p := by
  exact h.1

/-- 格子中心落入估计半径内时，它属于 margin 为 0 的禁入区。 -/
theorem monster_uncertainty_covered
    {m : TrackedMonster} {p : Position}
    (hin : inBounds p)
    (hcover : chebyshev p m.pos ≤ dangerRadius m) :
    monsterBlockedTile m 0 p := by
  exact ⟨hin, by simpa using hcover⟩

/-- 增大 margin 不会缩小怪物禁入区。 -/
theorem monster_margin_monotone
    {m : TrackedMonster} {p : Position} {margin margin' : Nat}
    (hle : margin ≤ margin')
    (h : monsterBlockedTile m margin p) :
    monsterBlockedTile m margin' p := by
  exact ⟨h.1, Nat.le_trans h.2 (Nat.add_le_add_left hle (dangerRadius m))⟩

/--
  真实安全距离谓词。

  这一层不试图证明 VLM/tracker 自身永远正确，而是把“真实怪物被符号包络覆盖”作为
  `GroundingSound` 一类的接口假设传入。
-/
def RealMonsterSafe (realMonsters : List Position) (p : Position) : Prop :=
  ∀ real, real ∈ realMonsters → ¬ adjacent p real

/-- 符号安全性对真实世界安全性的接口假设。 -/
def MonsterRegionSound
    (tracked : List TrackedMonster) (realMonsters : List Position) : Prop :=
  ∀ p, positionSafe tracked p → RealMonsterSafe realMonsters p

/-- 若 tracker 的怪物包络是保守正确的，则符号安全位置在真实环境中也安全。 -/
theorem monster_region_real_sound
    {tracked : List TrackedMonster} {realMonsters : List Position} {p : Position}
    (hsound : MonsterRegionSound tracked realMonsters)
    (hsafe : positionSafe tracked p) :
    RealMonsterSafe realMonsters p := by
  exact hsound p hsafe

/--
  Shield relation：`Shielded s monsters fallback requested issued` 表示在状态 `s`
  中，shield 接收到 `requested` 后实际发出 `issued`。

  `fallback` 对应 Python 中不安全时返回的 `NOOP` 或 `ACTION_B`，在抽象层分别用
  `.wait` 或 `.defend` 表示。
-/
inductive Shielded
    (s : SymbolicState) (monsters : List TrackedMonster) (fallback : Action) :
    Action → Action → Prop where
  | passNonMove {a : Action} :
      (∀ dir, a ≠ .move dir) →
      Shielded s monsters fallback a a
  | allowMove {dir : Facing} :
      actionSafe s monsters (.move dir) →
      Shielded s monsters fallback (.move dir) (.move dir)
  | blockMove {dir : Facing} :
      ¬ actionSafe s monsters (.move dir) →
      (∀ dir', fallback ≠ .move dir') →
      Shielded s monsters fallback (.move dir) fallback

/-- 若 shield 原样放行某个移动动作，则该移动满足安全条件。 -/
theorem shield_allows_move_safe
    {s : SymbolicState} {monsters : List TrackedMonster} {fallback : Action}
    {dir : Facing}
    (h : Shielded s monsters fallback (.move dir) (.move dir)) :
    actionSafe s monsters (.move dir) := by
  cases h with
  | passNonMove hnot =>
      exact False.elim (hnot dir rfl)
  | allowMove hsafe =>
      exact hsafe
  | blockMove hunsafe hfallback =>
      exact False.elim (hfallback dir rfl)

/-- 若某个移动会进入危险区，则 shield 不会原样放行该移动。 -/
theorem shield_blocks_unsafe_move
    {s : SymbolicState} {monsters : List TrackedMonster} {fallback : Action}
    {dir : Facing} {issued : Action}
    (hunsafe : ¬ actionSafe s monsters (.move dir))
    (h : Shielded s monsters fallback (.move dir) issued) :
    issued ≠ .move dir := by
  intro hissued
  subst hissued
  exact hunsafe (shield_allows_move_safe h)

/--
  若 fallback 本身安全，则 shield 的输出总是安全的。

  这对应 Python 中“不安全移动被改成 `NOOP` 或盾牌动作”的安全 fallback 逻辑。
-/
theorem shield_output_safe
    {s : SymbolicState} {monsters : List TrackedMonster} {fallback requested issued : Action}
    (hfallback : actionSafe s monsters fallback)
    (h : Shielded s monsters fallback requested issued) :
    actionSafe s monsters issued := by
  cases h with
  | passNonMove hnot =>
      cases requested with
      | wait => trivial
      | interact => trivial
      | defend => trivial
      | move dir => exact False.elim (hnot dir rfl)
  | allowMove hsafe =>
      exact hsafe
  | blockMove _ _ =>
      exact hfallback

/-- `.wait` 总是安全 fallback。 -/
theorem wait_fallback_safe
    {s : SymbolicState} {monsters : List TrackedMonster} :
    actionSafe s monsters .wait := by
  trivial

/-- `.defend` 总是安全 fallback。 -/
theorem defend_fallback_safe
    {s : SymbolicState} {monsters : List TrackedMonster} :
    actionSafe s monsters .defend := by
  trivial

/-- 在包络 sound 的假设下，Shield 输出的安全动作也满足真实世界安全性。 -/
theorem shield_real_world_safe
    {s : SymbolicState} {tracked : List TrackedMonster} {realMonsters : List Position}
    {fallback requested issued : Action}
    (hregion : MonsterRegionSound tracked realMonsters)
    (hfallback : actionSafe s tracked fallback)
    (hshield : Shielded s tracked fallback requested issued) :
    match issued with
    | .move dir => RealMonsterSafe realMonsters (advance s.player dir)
    | .wait => True
    | .interact => True
    | .defend => True := by
  have hsafe : actionSafe s tracked issued := shield_output_safe hfallback hshield
  cases issued with
  | wait => trivial
  | interact => trivial
  | defend => trivial
  | move dir =>
      exact monster_region_real_sound hregion hsafe

end NesyFormalization

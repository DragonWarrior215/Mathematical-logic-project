import NesyFormalization.MapSemantics

namespace EnvFormalization

/-- 跟踪器抽象：怪物位置加上一个不确定性半径。 -/
structure TrackedMonster where
  pos : Position
  uncertainty : Nat := 0
  deriving Repr, DecidableEq

/-- 自然数坐标上的绝对差。 -/
def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- Chebyshev 距离，对应怪物周围的方形不确定区域。 -/
def chebyshev (p q : Position) : Nat :=
  Nat.max (absDiff p.1 q.1) (absDiff p.2 q.2)

/-- 已跟踪怪物的保守危险半径。 -/
def dangerRadius (m : TrackedMonster) : Nat :=
  m.uncertainty + 1

/-- 若格子在边界内且位于半径加安全边距的范围内，则它被怪物区域阻挡。 -/
def monsterBlockedTile (m : TrackedMonster) (margin : Nat) (p : Position) : Prop :=
  InBounds p ∧ chebyshev p m.pos ≤ dangerRadius m + margin

/-- 一个格子位于单个怪物的不确定危险区域内。 -/
def inMonsterDanger (p : Position) (m : TrackedMonster) : Prop :=
  chebyshev p m.pos ≤ dangerRadius m

/-- 一个格子位于至少一个已跟踪怪物的危险区域内。 -/
def inDangerRegion (monsters : List TrackedMonster) (p : Position) : Prop :=
  ∃ m, m ∈ monsters ∧ inMonsterDanger p m

/-- 符号安全表示不处于任何已跟踪怪物的危险区域中。 -/
def positionSafe (monsters : List TrackedMonster) (p : Position) : Prop :=
  ¬ inDangerRegion monsters p

/-- `monster_blocked_in_bounds`：每个被怪物阻挡的格子都显式位于边界内。 -/
theorem monster_blocked_in_bounds
    {m : TrackedMonster} {margin : Nat} {p : Position}
    (h : monsterBlockedTile m margin p) : InBounds p := by
  exact h.1

/-- `monster_uncertainty_covered`：被不确定性半径覆盖意味着在安全边距为 0 时被阻挡。 -/
theorem monster_uncertainty_covered
    {m : TrackedMonster} {p : Position}
    (hin : InBounds p)
    (hcover : chebyshev p m.pos ≤ dangerRadius m) :
    monsterBlockedTile m 0 p := by
  exact ⟨hin, by simpa using hcover⟩

/-- `monster_margin_monotone`：增大安全边距只会扩大阻挡区域。 -/
theorem monster_margin_monotone
    {m : TrackedMonster} {p : Position} {margin margin' : Nat}
    (hle : margin ≤ margin')
    (h : monsterBlockedTile m margin p) :
    monsterBlockedTile m margin' p := by
  exact ⟨h.1, Nat.le_trans h.2 (Nat.add_le_add_left hle (dangerRadius m))⟩

/-- 真实世界安全性：候选格子不与任何真实怪物严格相邻。 -/
def RealMonsterSafe (realMonsters : List Position) (p : Position) : Prop :=
  ∀ real, real ∈ realMonsters → ¬ Neighbor p real

/-- 将符号怪物区域与真实怪物位置连接起来的接口假设。 -/
def MonsterRegionSound
    (tracked : List TrackedMonster) (realMonsters : List Position) : Prop :=
  ∀ p, positionSafe tracked p → RealMonsterSafe realMonsters p

/-- `monster_region_real_sound`：在语义落地接口下，符号安全蕴含真实安全。 -/
theorem monster_region_real_sound
    {tracked : List TrackedMonster} {realMonsters : List Position} {p : Position}
    (hsound : MonsterRegionSound tracked realMonsters)
    (hsafe : positionSafe tracked p) :
    RealMonsterSafe realMonsters p := by
  exact hsound p hsafe

end EnvFormalization

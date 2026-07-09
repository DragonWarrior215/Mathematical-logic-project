import NesyFormalization.NsiAgentFormalization

namespace EnvFormalization

/-!
  怪物危险语义的证明层。

  `TrackedMonster`、`dangerRadius`、`monsterBlockedTile`、`positionSafe` 等运行定义
  位于 `NsiAgentFormalization.lean`；本文件只证明这些定义的基本性质。
-/

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

/--
`monster_region_real_sound`：在 tracker/grounding 覆盖条件成立时，
符号层判定安全的格子在真实怪物位置上也安全。

这里的 `MonsterRegionSound` 是连接符号怪物区域和真实怪物位置的接口条件：
它表达“真实怪物始终被 tracker 的不确定区域覆盖”。这个覆盖性本身应由
tracker/grounding 相关定理证明；本定理只负责把该条件用于怪物危险语义。
-/
theorem monster_region_real_sound
    {tracked : List TrackedMonster} {realMonsters : List Position} {p : Position}
    (hregion : MonsterRegionSound tracked realMonsters)
    (hsafe : positionSafe tracked p) :
    RealMonsterSafe realMonsters p := by
  exact hregion p hsafe

end EnvFormalization

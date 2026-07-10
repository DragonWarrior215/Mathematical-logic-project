import NesyFormalization.NsiAgentFormalization

namespace EnvFormalization

/-- 若动作存在目标格子，且该格子位于已跟踪怪物危险区域之外，则动作安全。 -/
def actionSafe (w : WorldState) (tracked : List TrackedMonster) (a : Action) : Prop :=
  match actionTarget? w a with
  | some p => positionSafe tracked p
  | none => True

/-- 可执行的单怪物危险判定与命题版定义等价。 -/
theorem inMonsterDangerBool_true_iff
    (p : Position) (m : TrackedMonster) :
    inMonsterDangerBool p m = true ↔ inMonsterDanger p m := by
  simp [inMonsterDangerBool, inMonsterDanger]

/-- Python/Lean agent 实际使用的布尔安全检查与 `positionSafe` 命题等价。 -/
theorem positionSafeBool_true_iff
    (tracked : List TrackedMonster) (p : Position) :
    positionSafeBool tracked p = true ↔ positionSafe tracked p := by
  simp [positionSafeBool, positionSafe, inDangerRegion,
    inMonsterDangerBool_true_iff]

/-- 描述安全屏蔽如何透传、允许或替换请求动作的关系。 -/
inductive Shielded (w : WorldState) (tracked : List TrackedMonster) (fallback : Action) :
    Action → Action → Prop where
  | passNonMove {a : Action} :
      actionTarget? w a = none →
      Shielded w tracked fallback a a
  | allowMove {a : Action} {p : Position} :
      actionTarget? w a = some p →
      positionSafe tracked p →
      Shielded w tracked fallback a a
  | blockMove {a : Action} {p : Position} :
      actionTarget? w a = some p →
      ¬ positionSafe tracked p →
      actionTarget? w fallback = none →
      Shielded w tracked fallback a fallback

/-- `shieldFallback` 总是非移动动作（等待或举盾）。 -/
theorem shieldFallback_nonmove (w : WorldState) :
    actionTarget? w (shieldFallback w) = none := by
  unfold shieldFallback
  by_cases hshield : hasEquippedShield w = true <;>
    simp [hshield, actionTarget?]

/--
可执行函数 `shieldAction` 确实满足抽象关系 `Shielded`：非移动透传，
安全移动放行，危险移动替换为非移动 fallback。
-/
theorem shieldAction_spec
    (w : WorldState) (tracked : List TrackedMonster) (requested : Action) :
    Shielded w tracked (shieldFallback w) requested
      (shieldAction w tracked requested) := by
  unfold shieldAction
  cases htarget : actionTarget? w requested with
  | none =>
      simp
      exact Shielded.passNonMove htarget
  | some p =>
      simp
      by_cases hsafe : positionSafeBool tracked p = true
      · simp [hsafe]
        exact Shielded.allowMove htarget
          ((positionSafeBool_true_iff tracked p).1 hsafe)
      · have hunsafe : ¬ positionSafe tracked p := by
          intro hp
          exact hsafe ((positionSafeBool_true_iff tracked p).2 hp)
        simp [hsafe]
        exact Shielded.blockMove htarget hunsafe (shieldFallback_nonmove w)

/-- `shield_real_world_safe`：在区域可靠性下，经安全屏蔽过滤的移动在真实世界中安全。 -/
theorem shield_real_world_safe
    {w : WorldState} {tracked : List TrackedMonster} {realMonsters : List Position}
    {fallback requested issued : Action}
    (hregion : MonsterRegionSound tracked realMonsters)
    (_hfallback : actionSafe w tracked fallback)
    (hshield : Shielded w tracked fallback requested issued) :
    match actionTarget? w issued with
    | some p => RealMonsterSafe realMonsters p
    | none => True := by
  cases hshield with
  | passNonMove hnone =>
      simp [hnone]
  | allowMove htarget hsafe =>
      simp [htarget]
      exact hregion _ hsafe
  | blockMove _ _ hfallbackNonMove =>
      simp [hfallbackNonMove]

/--
可执行的 `shieldAction` 的直接真实安全性结论：若 tracker 危险区对真实怪物
是保守可靠的，则实际函数输出的移动目标格对真实怪物安全。
-/
theorem shieldAction_real_world_safe
    {w : WorldState} {tracked : List TrackedMonster} {realMonsters : List Position}
    (hregion : MonsterRegionSound tracked realMonsters)
    (requested : Action) :
    match actionTarget? w (shieldAction w tracked requested) with
    | some p => RealMonsterSafe realMonsters p
    | none => True := by
  apply shield_real_world_safe
    (fallback := shieldFallback w) (requested := requested)
  · exact hregion
  · unfold actionSafe
    rw [shieldFallback_nonmove]
    trivial
  · exact shieldAction_spec w tracked requested

end EnvFormalization

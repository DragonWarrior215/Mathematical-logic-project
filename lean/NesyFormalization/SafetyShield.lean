import NesyFormalization.MonsterDanger

namespace EnvFormalization

/-- 移动动作的目标格子；对被动或非移动动作返回 `none`。 -/
def actionTarget? (w : WorldState) : Action → Option Position
  | .up => some (facingTile w.player .up)
  | .down => some (facingTile w.player .down)
  | .left => some (facingTile w.player .left)
  | .right => some (facingTile w.player .right)
  | .wait => none
  | .interactA => none
  | .shieldB => none

/-- 若动作存在目标格子，且该格子位于已跟踪怪物危险区域之外，则动作安全。 -/
def actionSafe (w : WorldState) (tracked : List TrackedMonster) (a : Action) : Prop :=
  match actionTarget? w a with
  | some p => positionSafe tracked p
  | none => True

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
      exact monster_region_real_sound hregion hsafe
  | blockMove _ _ hfallbackNonMove =>
      simp [hfallbackNonMove]

end EnvFormalization

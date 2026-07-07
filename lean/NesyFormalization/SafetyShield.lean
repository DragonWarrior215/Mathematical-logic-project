import NesyFormalization.MonsterDanger

namespace EnvFormalization

/-- The tile targeted by a movement action, or `none` for passive/non-movement actions. -/
def actionTarget? (w : WorldState) : Action → Option Position
  | .up => some (facingTile w.player .up)
  | .down => some (facingTile w.player .down)
  | .left => some (facingTile w.player .left)
  | .right => some (facingTile w.player .right)
  | .wait => none
  | .interactA => none
  | .shieldB => none

/-- An action is safe when its target tile, if any, is outside tracked monster danger regions. -/
def actionSafe (w : WorldState) (tracked : List TrackedMonster) (a : Action) : Prop :=
  match actionTarget? w a with
  | some p => positionSafe tracked p
  | none => True

/-- Relation describing how the shield either passes, allows, or replaces a requested action. -/
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

/-- `shield_real_world_safe`: shield-filtered movement is real-world safe under region soundness. -/
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

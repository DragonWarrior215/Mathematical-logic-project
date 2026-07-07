import NesyFormalization.MapSemantics

namespace EnvFormalization

/-- Tracker abstraction: a monster position plus an uncertainty radius. -/
structure TrackedMonster where
  pos : Position
  uncertainty : Nat := 0
  deriving Repr, DecidableEq

/-- Absolute difference on natural coordinates. -/
def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- Chebyshev distance, matching square uncertainty regions around monsters. -/
def chebyshev (p q : Position) : Nat :=
  Nat.max (absDiff p.1 q.1) (absDiff p.2 q.2)

/-- Conservative danger radius for a tracked monster. -/
def dangerRadius (m : TrackedMonster) : Nat :=
  m.uncertainty + 1

/-- A tile is blocked by a monster region when it is in bounds and within radius plus margin. -/
def monsterBlockedTile (m : TrackedMonster) (margin : Nat) (p : Position) : Prop :=
  InBounds p ∧ chebyshev p m.pos ≤ dangerRadius m + margin

/-- A tile lies inside a single monster's uncertainty danger region. -/
def inMonsterDanger (p : Position) (m : TrackedMonster) : Prop :=
  chebyshev p m.pos ≤ dangerRadius m

/-- A tile lies in the danger region of at least one tracked monster. -/
def inDangerRegion (monsters : List TrackedMonster) (p : Position) : Prop :=
  ∃ m, m ∈ monsters ∧ inMonsterDanger p m

/-- Symbolic safety means not being in any tracked monster danger region. -/
def positionSafe (monsters : List TrackedMonster) (p : Position) : Prop :=
  ¬ inDangerRegion monsters p

/-- `monster_blocked_in_bounds`: every monster-blocked tile is explicitly in bounds. -/
theorem monster_blocked_in_bounds
    {m : TrackedMonster} {margin : Nat} {p : Position}
    (h : monsterBlockedTile m margin p) : InBounds p := by
  exact h.1

/-- `monster_uncertainty_covered`: coverage by the uncertainty radius implies blocked-at-margin-zero. -/
theorem monster_uncertainty_covered
    {m : TrackedMonster} {p : Position}
    (hin : InBounds p)
    (hcover : chebyshev p m.pos ≤ dangerRadius m) :
    monsterBlockedTile m 0 p := by
  exact ⟨hin, by simpa using hcover⟩

/-- `monster_margin_monotone`: increasing the safety margin can only enlarge the blocked region. -/
theorem monster_margin_monotone
    {m : TrackedMonster} {p : Position} {margin margin' : Nat}
    (hle : margin ≤ margin')
    (h : monsterBlockedTile m margin p) :
    monsterBlockedTile m margin' p := by
  exact ⟨h.1, Nat.le_trans h.2 (Nat.add_le_add_left hle (dangerRadius m))⟩

/-- Real-world safety: the candidate tile is not strictly adjacent to any real monster. -/
def RealMonsterSafe (realMonsters : List Position) (p : Position) : Prop :=
  ∀ real, real ∈ realMonsters → ¬ Neighbor p real

/-- Interface assumption connecting symbolic monster regions to real monster positions. -/
def MonsterRegionSound
    (tracked : List TrackedMonster) (realMonsters : List Position) : Prop :=
  ∀ p, positionSafe tracked p → RealMonsterSafe realMonsters p

/-- `monster_region_real_sound`: symbolic safety implies real safety under the grounding interface. -/
theorem monster_region_real_sound
    {tracked : List TrackedMonster} {realMonsters : List Position} {p : Position}
    (hsound : MonsterRegionSound tracked realMonsters)
    (hsafe : positionSafe tracked p) :
    RealMonsterSafe realMonsters p := by
  exact hsound p hsafe

end EnvFormalization

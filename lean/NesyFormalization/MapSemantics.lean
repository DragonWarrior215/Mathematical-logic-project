import NesyFormalization.EnvFormalization

namespace EnvFormalization

/-!
  来自 `定理列表.xlsx` 的地图层语义，基于环境中的 `RoomState` 和 `Position` 类型。
-/

def Neighbor (p q : Position) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

def isMonsterTile (r : RoomState) (p : Position) : Bool :=
  r.monsters.any (fun m => m.pos == p)

def isHazardTile (r : RoomState) (p : Position) : Bool :=
  hasActiveTrapAt r p || isMonsterTile r p

def walkableWithHazard (r : RoomState) (p : Position) (allowHazard : Bool) : Prop :=
  InBounds p ∧ isBlocking r p = false ∧
    (allowHazard = false → isHazardTile r p = false)

def walkable (r : RoomState) (p : Position) : Prop :=
  walkableWithHazard r p false

theorem neighbor_symm {p q : Position} (h : Neighbor p q) : Neighbor q p := by
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

theorem neighbor_manhattan {p q : Position} (h : Neighbor p q) :
    manhattan p q = 1 := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  unfold Neighbor at h
  simp at h
  unfold manhattan
  simp
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hy with hy | hy
    · subst qx
      subst qy
      simp
    · subst qx
      subst py
      simp
  · rcases hx with hx | hx
    · subst qy
      subst qx
      simp
    · subst qy
      subst px
      simp

theorem neighbor_ne {p q : Position} (h : Neighbor p q) : p ≠ q := by
  intro heq
  subst q
  unfold Neighbor at h
  omega

theorem walkable_in_bounds {r : RoomState} {p : Position}
    (h : walkable r p) : InBounds p := by
  exact h.1

theorem walkable_not_blocking {r : RoomState} {p : Position}
    (h : walkable r p) : isBlocking r p = false := by
  exact h.2.1

theorem walkable_not_hazard {r : RoomState} {p : Position}
    (h : walkable r p) : isHazardTile r p = false := by
  exact h.2.2 rfl

theorem walkable_allow_hazard_geometry {r : RoomState} {p : Position}
    (h : walkableWithHazard r p true) :
    InBounds p ∧ isBlocking r p = false := by
  exact ⟨h.1, h.2.1⟩

theorem walkable_mono {r : RoomState} {p : Position}
    (h : walkable r p) : walkableWithHazard r p true := by
  exact ⟨h.1, h.2.1, by intro hfalse; cases hfalse⟩

end EnvFormalization

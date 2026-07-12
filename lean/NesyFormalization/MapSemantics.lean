import NesyFormalization.EnvFormalization

namespace EnvFormalization

/-!
  来自 `定理列表.xlsx` 的地图层语义，基于环境中的 `RoomState` 和 `Position` 类型。
-/

/-- 严格四邻接关系：上下左右相差一格，但不包含同格。 -/
def Neighbor (p q : Position) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

/-- 某格是否当前被怪物占据；这是地图层的离散怪物占据谓词。 -/
def isMonsterTile (r : RoomState) (p : Position) : Bool :=
  r.monsters.any (fun m => m.pos == p)

/-- 某格是否是危险格：激活陷阱或怪物所在格。 -/
def isHazardTile (r : RoomState) (p : Position) : Bool :=
  (trapAt? r p).isSome || isMonsterTile r p

/-- 可行走格的几何条件；当 `allowHazard = false` 时，还要求该格不是危险格。 -/
def walkableWithHazard (r : RoomState) (p : Position) (allowHazard : Bool) : Prop :=
  InBounds p ∧ isBlocking r p = false ∧
    (allowHazard = false → isHazardTile r p = false)

/-- 默认的严格可行走格：在界内、不阻挡、且不是危险格。 -/
def walkable (r : RoomState) (p : Position) : Prop :=
  walkableWithHazard r p false

/-- `Neighbor` 是对称的：若 `p` 是 `q` 的邻格，则 `q` 也是 `p` 的邻格。 -/
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

/-- 严格邻格的 Manhattan 距离恰好为 1。 -/
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

/-- 严格邻格不可能是同一个格子。 -/
theorem neighbor_ne {p q : Position} (h : Neighbor p q) : p ≠ q := by
  intro heq
  subst q
  unfold Neighbor at h
  omega

/-- 严格可行走格一定在地图边界内。 -/
theorem walkable_in_bounds {r : RoomState} {p : Position}
    (h : walkable r p) : InBounds p := by
  exact h.1

/-- 严格可行走格一定不是阻挡格。 -/
theorem walkable_not_blocking {r : RoomState} {p : Position}
    (h : walkable r p) : isBlocking r p = false := by
  exact h.2.1

/-- 严格可行走格一定不是危险格。 -/
theorem walkable_not_hazard {r : RoomState} {p : Position}
    (h : walkable r p) : isHazardTile r p = false := by
  exact h.2.2 rfl

/-- 若允许危险格，则 `walkableWithHazard` 只保留几何约束：在界内且不阻挡。 -/
theorem walkable_allow_hazard_geometry {r : RoomState} {p : Position}
    (h : walkableWithHazard r p true) :
    InBounds p ∧ isBlocking r p = false := by
  exact ⟨h.1, h.2.1⟩

/-- 严格可行走格在放宽危险限制后仍然可行走。 -/
theorem walkable_mono {r : RoomState} {p : Position}
    (h : walkable r p) : walkableWithHazard r p true := by
  exact ⟨h.1, h.2.1, by intro hfalse; cases hfalse⟩


end EnvFormalization

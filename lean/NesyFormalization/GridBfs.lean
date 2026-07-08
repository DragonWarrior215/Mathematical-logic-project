import NesyFormalization.NsiAgentFormalization

namespace EnvFormalization

/-- 布尔边界检查蕴含命题版边界检查。 -/
theorem inBoundsBool_sound {p : Position}
    (h : inBounds p = true) : InBounds p := by
  unfold inBounds at h
  unfold InBounds
  simp at h
  exact h

/-- 布尔 `walkable` 在默认不允许危险格时蕴含命题版 `walkable`。 -/
theorem walkableBool_sound {r : RoomState} {p : Position}
    (h : walkableBool r p false = true) :
    walkable r p := by
  unfold walkableBool at h
  simp at h
  exact ⟨inBoundsBool_sound h.1.1, h.1.2, by intro _; exact h.2⟩

/-- `gridNeighbors` 只产生严格四邻格。 -/
theorem gridNeighbors_neighbor {p q : Position}
    (h : q ∈ gridNeighbors p) : Neighbor p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold gridNeighbors at h
  by_cases hy : y = 0
  · by_cases hx : x = 0
    · simp [hy, hx] at h
      unfold Neighbor
      simp
      omega
    · simp [hy, hx] at h
      unfold Neighbor
      simp
      omega
  · by_cases hx : x = 0
    · simp [hy, hx] at h
      unfold Neighbor
      simp
      omega
    · simp [hy, hx] at h
      unfold Neighbor
      simp
      omega

/-- 若路径链已经到达 `current`，再接上严格邻格 `nxt` 后仍是路径链。 -/
theorem pathChain_append_neighbor
    {path : List Position} {current nxt : Position}
    (hlast : path.getLast? = some current)
    (hchain : PathChain path)
    (hneigh : Neighbor current nxt) :
    PathChain (path ++ [nxt]) := by
  induction path with
  | nil =>
      simp [PathChain]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp at hlast
          subst p
          simp [PathChain, hneigh]
      | cons q qs =>
          simp [PathChain] at hchain ⊢
          exact ⟨hchain.1, ih hlast hchain.2⟩

/--
路径扩展引理：如果 `path` 已经是从 `start` 到 `current` 的有效路径，
且 `nxt` 是可走的严格邻格，那么 `path ++ [nxt]` 是从 `start` 到 `nxt` 的有效路径。
-/
theorem validPath_extend
    {r : RoomState} {start current nxt : Position} {path : List Position}
    (hvalid : ValidPath r start current path)
    (hneigh : Neighbor current nxt)
    (hwalk : walkable r nxt) :
    ValidPath r start nxt (path ++ [nxt]) := by
  rcases hvalid with ⟨hend, hwalks, hchain⟩
  rcases hend with ⟨hhead, hlast⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · cases path with
      | nil =>
          simp at hhead
      | cons p ps =>
          simpa using hhead
    · simp
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hwalks p hp
    · simp at hp
      subst hp
      exact hwalk
  · exact pathChain_append_neighbor hlast hchain hneigh

/--
队列展开保持路径语义：从一个已经可靠的节点展开出的每个 child，
仍然携带一条从起点到 child 当前位置的有效路径。
-/
theorem expandNode_sound
    {r : RoomState} {start : Position} {seen avoid goals : List Position}
    {node child : BfsNode}
    (hnode : NodeSound r start node)
    (hmem : child ∈ expandNode r seen avoid goals false node) :
    NodeSound r start child := by
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt false && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      have hwalkBool : walkableBool r nxt false = true := by
        have hallowed' := hallowed
        simp at hallowed'
        exact hallowed'.1
      exact validPath_extend hnode (gridNeighbors_neighbor hnbr)
        (walkableBool_sound hwalkBool)
  · simp [hseen] at hcase

/-!
  下面这些是后续要证明的 BFS 性质目标/接口，不再提供“传入规格再返回规格”
  的投影定理。真正已经证明的内容目前是上面的局部构造引理，例如
  `gridNeighbors_neighbor` 和 `expandNode_sound`。
-/

/-- BFS 可靠性目标：任意返回路径都是房间中的有效路径。 -/
def BfsSound (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path, bfs r start goal = some path → ValidPath r start goal path

/-- BFS 无重复性质目标：任意返回路径都不包含重复格子。 -/
def BfsNoDup (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path, bfs r start goal = some path → path.Nodup

/-- BFS 避怪性质：返回路径上的格子对跟踪器状态是安全的。 -/
def BfsAvoidsMonsters
    (bfs : RoomState → Position → Position → Option (List Position))
    (trackedOf : RoomState → List TrackedMonster) : Prop :=
  ∀ r start goal path p,
    bfs r start goal = some path →
    p ∈ path →
    positionSafe (trackedOf r) p

/-- BFS 最短性目标：返回路径不长于任何其他有效路径。 -/
def BfsShortest (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path alt,
    bfs r start goal = some path →
    ValidPath r start goal alt →
    path.length ≤ alt.length

/-- BFS 完备性目标：只要目标可达，BFS 就能返回某条路径。 -/
def BfsComplete (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal, Reachable r start goal → ∃ path, bfs r start goal = some path

/-- `reachable_tiles` 的可靠性：每个报告出的格子都确实可达。 -/
def ReachableTilesSound (reachableTiles : RoomState → Position → List Position) : Prop :=
  ∀ r start p, p ∈ reachableTiles r start → Reachable r start p

/-- `reachable_tiles` 的完备性：每个确实可达的格子都会被报告。 -/
def ReachableTilesComplete (reachableTiles : RoomState → Position → List Position) : Prop :=
  ∀ r start p, Reachable r start p → p ∈ reachableTiles r start

end EnvFormalization

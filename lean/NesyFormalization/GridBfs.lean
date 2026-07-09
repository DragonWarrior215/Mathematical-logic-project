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

/-- 当前 BFS 模式下的可行走谓词，保留 `allowHazard` 参数。 -/
def walkableForMode (r : RoomState) (allowHazard : Bool) (p : Position) : Prop :=
  walkableWithHazard r p allowHazard

/-- 布尔 `walkableBool` 在任意 hazard 模式下蕴含命题版模式可走。 -/
theorem walkableBool_sound_mode {r : RoomState} {p : Position} {allowHazard : Bool}
    (h : walkableBool r p allowHazard = true) :
    walkableForMode r allowHazard p := by
  unfold walkableForMode walkableBool walkableWithHazard at *
  simp at h
  constructor
  · exact inBoundsBool_sound h.1.1
  constructor
  · exact h.1.2
  · intro hfalse
    subst allowHazard
    simpa using h.2

/-- 命题版模式可走性可以反映回可执行的 `walkableBool` 判断。 -/
theorem walkableBool_complete_mode {r : RoomState} {p : Position} {allowHazard : Bool}
    (h : walkableForMode r allowHazard p) :
    walkableBool r p allowHazard = true := by
  unfold walkableForMode walkableWithHazard at h
  unfold walkableBool inBounds
  rcases h with ⟨hin, hblock, hhazard⟩
  unfold InBounds at hin
  simp [hin.1, hin.2, hblock]
  cases allowHazard with
  | false =>
      simp [hhazard rfl]
  | true =>
      simp

/-- 路径中的每个格子都满足当前 BFS hazard 模式下的可行走性。 -/
def PathWalkableForMode (r : RoomState) (allowHazard : Bool) (path : List Position) : Prop :=
  ∀ p, p ∈ path → walkableForMode r allowHazard p

/-- 带 `allowHazard` 模式的有效路径。 -/
def ValidPathForMode
    (r : RoomState) (allowHazard : Bool) (start goal : Position) (path : List Position) :
    Prop :=
  PathEndpoints path start goal ∧ PathWalkableForMode r allowHazard path ∧ PathChain path

/-- 带 `allowHazard` 模式的 BFS 节点可靠性。 -/
def NodeSoundForMode
    (r : RoomState) (allowHazard : Bool) (start : Position) (node : BfsNode) : Prop :=
  ValidPathForMode r allowHazard start node.tile node.path

/-- 带 `allowHazard` 模式的 BFS 队列可靠性。 -/
def QueueSoundForMode
    (r : RoomState) (allowHazard : Bool) (start : Position) (queue : List BfsNode) : Prop :=
  ∀ node, node ∈ queue → NodeSoundForMode r allowHazard start node

/-- 一个格子被当前 BFS 状态覆盖：它要么在 `seen` 中，要么是队列里某个节点的 tile。 -/
def TileCovered (seen : List Position) (queue : List BfsNode) (p : Position) : Prop :=
  p ∈ seen ∨ ∃ node, node ∈ queue ∧ node.tile = p

/-- `containsPos` 与列表成员关系等价。 -/
theorem containsPos_true_iff (ps : List Position) (p : Position) :
    containsPos ps p = true ↔ p ∈ ps := by
  unfold containsPos
  simp [List.any_eq_true]

/-- 若 `containsPos` 返回 false，则该格子不在列表中。 -/
theorem containsPos_false_not_mem {ps : List Position} {p : Position}
    (h : containsPos ps p = false) : p ∉ ps := by
  intro hp
  have ht : containsPos ps p = true := (containsPos_true_iff ps p).2 hp
  rw [h] at ht
  contradiction

/-- 若格子是目标，或不在禁入集合中，则满足 BFS 的 `avoid` 过滤规则。 -/
theorem allowedByAvoid_of_goal_or_not_avoid
    {avoid goals : List Position} {p : Position}
    (h : p ∈ goals ∨ p ∉ avoid) :
    allowedByAvoid avoid goals p = true := by
  unfold allowedByAvoid
  rcases h with hgoal | havoid
  · have hgoalBool : containsPos goals p = true := (containsPos_true_iff goals p).2 hgoal
    simp [hgoalBool]
  · by_cases hav : containsPos avoid p = true
    · exfalso
      exact havoid ((containsPos_true_iff avoid p).1 hav)
    · cases hg : containsPos goals p
      · simp [hav]
      · simp

/-- 列表成员可以拆成“前缀 + 该元素 + 后缀”。 -/
theorem list_mem_split {α : Type} {x : α} {xs : List α}
    (h : x ∈ xs) : ∃ front suffix, xs = front ++ x :: suffix := by
  induction xs with
  | nil =>
      simp at h
  | cons y ys ih =>
      simp at h
      rcases h with hxy | hy
      · subst y
        exact ⟨[], ys, by simp⟩
      · rcases ih hy with ⟨front, suffix, hsplit⟩
        exact ⟨y :: front, suffix, by simp [hsplit]⟩

/-- 10×8 地图中的全部格子。 -/
def allPositions : List Position :=
  List.flatMap (fun x => (List.range 8).map (fun y => (x, y))) (List.range 10)

/-- 每个界内格子都出现在 `allPositions` 枚举中。 -/
theorem inBounds_mem_allPositions {p : Position}
    (h : InBounds p) : p ∈ allPositions := by
  rcases p with ⟨x, y⟩
  unfold InBounds at h
  unfold allPositions
  rw [List.mem_flatMap]
  refine ⟨x, ?_, ?_⟩
  · exact List.mem_range.mpr h.1
  · simp [List.mem_range]
    exact h.2

/-- `allPositions` 中的每个格子都在地图边界内。 -/
theorem allPositions_inBounds {p : Position}
    (hp : p ∈ allPositions) : InBounds p := by
  rcases p with ⟨x, y⟩
  unfold allPositions at hp
  rw [List.mem_flatMap] at hp
  rcases hp with ⟨x0, hx0, hp⟩
  simp [List.mem_range] at hp
  rcases hp with ⟨hy, hxy⟩
  subst x
  unfold InBounds
  exact ⟨by simpa [List.mem_range] using hx0, hy⟩

/-- `allPositions` 枚举了 10×8 地图的 80 个格子。 -/
theorem allPositions_length : allPositions.length = 80 := by
  native_decide

/-- `allPositions` 没有重复枚举格子。 -/
theorem allPositions_nodup : allPositions.Nodup := by
  native_decide

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

/-- 每个严格四邻格都会出现在 `gridNeighbors` 的枚举结果中。 -/
theorem neighbor_mem_gridNeighbors {p q : Position}
    (h : Neighbor p q) : q ∈ gridNeighbors p := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold Neighbor at h
  unfold gridNeighbors
  simp at h ⊢
  rcases h with h | h
  · rcases h with ⟨hx, hy⟩
    subst qx
    rcases hy with hy | hy
    · subst qy
      by_cases hy0 : y = 0 <;> simp [hy0]
    · have hy0 : y ≠ 0 := by omega
      have hqy : qy = y - 1 := by omega
      subst qy
      simp [hy0]
  · rcases h with ⟨hy, hx⟩
    subst qy
    rcases hx with hx | hx
    · subst qx
      by_cases hy0 : y = 0 <;> by_cases hx0 : x = 0 <;> simp [hy0, hx0]
    · have hx0 : x ≠ 0 := by omega
      have hqx : qx = x - 1 := by omega
      subst qx
      by_cases hy0 : y = 0 <;> simp [hy0, hx0]

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
模式化路径扩展引理：如果 `path` 在当前 hazard 模式下有效，
且 `nxt` 是可走的严格邻格，则扩展后的路径仍然在该模式下有效。
-/
theorem validPathForMode_extend
    {r : RoomState} {allowHazard : Bool} {start current nxt : Position} {path : List Position}
    (hvalid : ValidPathForMode r allowHazard start current path)
    (hneigh : Neighbor current nxt)
    (hwalk : walkableForMode r allowHazard nxt) :
    ValidPathForMode r allowHazard start nxt (path ++ [nxt]) := by
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

/--
模式化队列展开可靠性：从一个在当前 hazard 模式下可靠的节点展开出的 child，
仍然携带一条同模式下的有效路径。
-/
theorem expandNode_sound_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {node child : BfsNode}
    (hnode : NodeSoundForMode r allowHazard start node)
    (hmem : child ∈ expandNode r seen avoid goals allowHazard node) :
    NodeSoundForMode r allowHazard start child := by
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt allowHazard && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      have hwalkBool : walkableBool r nxt allowHazard = true := by
        have hallowedCopy := hallowed
        simp at hallowedCopy
        exact hallowedCopy.1
      exact validPathForMode_extend hnode (gridNeighbors_neighbor hnbr)
        (walkableBool_sound_mode hwalkBool)
  · simp [hseen] at hcase

/--
`expandNode` 的发现方向：一个未访问、当前模式下可走、且满足 `avoid` 规则的邻格，
一定会被加入当前节点的 child 列表。
-/
theorem expandNode_contains_allowed_neighbor
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position}
    {node : BfsNode} {nxt : Position}
    (hneigh : nxt ∈ gridNeighbors node.tile)
    (hseen : containsPos seen nxt = false)
    (hwalk : walkableBool r nxt allowHazard = true)
    (hallowed : allowedByAvoid avoid goals nxt = true) :
    { tile := nxt, path := node.path ++ [nxt] } ∈
      expandNode r seen avoid goals allowHazard node := by
  unfold expandNode
  simp only [List.mem_filterMap]
  refine ⟨nxt, hneigh, ?_⟩
  simp [hseen, hwalk, hallowed]

/--
一次展开的 frontier 覆盖：对当前弹出的 `node`，任意满足模式约束的邻居 `nxt`，
在展开后都会出现在新的 `seen` 中。若它不是旧 `seen` 中的格子，则它会作为 child
进入本轮扩展出的队列。
-/
theorem expandNode_frontier_covered
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position}
    {node : BfsNode} {nxt : Position}
    (hneigh : nxt ∈ gridNeighbors node.tile)
    (hwalk : walkableBool r nxt allowHazard = true)
    (hallowed : allowedByAvoid avoid goals nxt = true) :
    nxt ∈ seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node) ∧
      (nxt ∈ seen ∨
        ∃ child, child ∈ expandNode r seen avoid goals allowHazard node ∧ child.tile = nxt) := by
  by_cases hseenBool : containsPos seen nxt = true
  · have hseenMem : nxt ∈ seen := (containsPos_true_iff seen nxt).1 hseenBool
    constructor
    · rw [List.mem_append]
      exact Or.inl hseenMem
    · exact Or.inl hseenMem
  · have hseenFalse : containsPos seen nxt = false := by
      cases h : containsPos seen nxt
      · rfl
      · exact False.elim (hseenBool h)
    let child : BfsNode := { tile := nxt, path := node.path ++ [nxt] }
    have hchild :
        child ∈ expandNode r seen avoid goals allowHazard node :=
      expandNode_contains_allowed_neighbor
        (node := node) (nxt := nxt) hneigh hseenFalse hwalk hallowed
    have htile : child.tile = nxt := by
      simp [child]
    constructor
    · rw [List.mem_append]
      right
      unfold bfsNodeTiles
      exact List.mem_map.mpr ⟨child, hchild, htile⟩
    · exact Or.inr ⟨child, hchild, htile⟩

/--
一次 BFS 循环后的队列覆盖：当前节点的每个满足模式约束的邻居，在更新后的
`seen'` 中可见，并且若不是旧 `seen`，就已经进入 `queue ++ children`。
-/
theorem bfs_step_covers_frontier
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position}
    {queue : List BfsNode}
    {node : BfsNode} {nxt : Position}
    (hneigh : nxt ∈ gridNeighbors node.tile)
    (hwalk : walkableBool r nxt allowHazard = true)
    (hallowed : allowedByAvoid avoid goals nxt = true) :
    let children := expandNode r seen avoid goals allowHazard node
    nxt ∈ seen ++ bfsNodeTiles children ∧
      (nxt ∈ seen ∨
        ∃ child, child ∈ queue ++ children ∧ child.tile = nxt) := by
  intro children
  rcases expandNode_frontier_covered
      (r := r) (allowHazard := allowHazard) (seen := seen)
      (avoid := avoid) (goals := goals) (node := node) (nxt := nxt)
      hneigh hwalk hallowed with
    ⟨hseen, hqueue⟩
  constructor
  · exact hseen
  · rcases hqueue with hOld | hChild
    · exact Or.inl hOld
    · rcases hChild with ⟨child, hmem, htile⟩
      exact Or.inr ⟨child, by
        rw [List.mem_append]
        exact Or.inr hmem, htile⟩

/--
命题版的单步 frontier 覆盖：若 `nxt` 是当前节点的严格邻居，在当前模式下可走，
并且满足目标例外/避让规则，则处理当前节点后，`nxt` 被新的 `seen + queue`
覆盖。
-/
theorem bfs_step_covers_constrained_neighbor
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position}
    {queue : List BfsNode} {node : BfsNode} {nxt : Position}
    (hneighbor : Neighbor node.tile nxt)
    (hwalk : walkableForMode r allowHazard nxt)
    (hallowed : nxt ∈ goals ∨ nxt ∉ avoid) :
    let children := expandNode r seen avoid goals allowHazard node
    nxt ∈ seen ++ bfsNodeTiles children ∧
      (nxt ∈ seen ∨
        ∃ child, child ∈ queue ++ children ∧ child.tile = nxt) := by
  exact bfs_step_covers_frontier
    (r := r) (allowHazard := allowHazard) (seen := seen)
    (avoid := avoid) (goals := goals) (queue := queue) (node := node)
    (nxt := nxt)
    (neighbor_mem_gridNeighbors hneighbor)
    (walkableBool_complete_mode hwalk)
    (allowedByAvoid_of_goal_or_not_avoid hallowed)

/--
一步 BFS 递归不会丢失旧覆盖：若队首节点的 tile 已经在 `seen` 中，则弹出队首、
追加 children 之后，原先被 `seen + node :: queue` 覆盖的格子仍被
`seen' + queue ++ children` 覆盖。
-/
theorem tileCovered_preserved_after_step
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position}
    {queue : List BfsNode} {node : BfsNode} {p : Position}
    (hnodeSeen : node.tile ∈ seen)
    (hcover : TileCovered seen (node :: queue) p) :
    let children := expandNode r seen avoid goals allowHazard node
    TileCovered (seen ++ bfsNodeTiles children) (queue ++ children) p := by
  intro children
  unfold TileCovered at hcover ⊢
  rcases hcover with hseen | hqueued
  · left
    rw [List.mem_append]
    exact Or.inl hseen
  · rcases hqueued with ⟨coveredNode, hmem, htile⟩
    simp at hmem
    rcases hmem with hnodeEq | hqueueMem
    · subst coveredNode
      subst p
      left
      rw [List.mem_append]
      exact Or.inl hnodeSeen
    · right
      exact ⟨coveredNode, by
        rw [List.mem_append]
        exact Or.inl hqueueMem, htile⟩

/-- 队列中的每个节点都携带一条从 `start` 到自身位置的有效路径。 -/
def QueueSound (r : RoomState) (start : Position) (queue : List BfsNode) : Prop :=
  ∀ node, node ∈ queue → NodeSound r start node

/-- 单个 BFS 节点携带的路径不含重复格子。 -/
def NodeNoDup (node : BfsNode) : Prop :=
  node.path.Nodup

/-- 单个 BFS 节点携带的路径已经被当前 `seen` 集合发现。 -/
def NodePathInSeen (seen : List Position) (node : BfsNode) : Prop :=
  ∀ p, p ∈ node.path → p ∈ seen

/-- 队列中的每个 BFS 节点都携带无重复路径。 -/
def QueueNoDupPaths (queue : List BfsNode) : Prop :=
  ∀ node, node ∈ queue → NodeNoDup node

/-- 队列中每个节点路径上的格子都已经被当前 `seen` 集合发现。 -/
def QueuePathsInSeen (seen : List Position) (queue : List BfsNode) : Prop :=
  ∀ node, node ∈ queue → NodePathInSeen seen node

/-- BFS 搜索状态的核心不变量：队列节点语义可靠，且每个节点路径都包含在 `seen` 中。 -/
def BfsStateInvariant
    (r : RoomState) (allowHazard : Bool) (start : Position)
    (seen : List Position) (queue : List BfsNode) : Prop :=
  QueueSoundForMode r allowHazard start queue ∧ QueuePathsInSeen seen queue

/--
BFS 路径避开 `avoid` 的不变量。
起点可能已经在 `avoid` 中，目标格也允许作为例外；除此之外路径节点不能在 `avoid` 中。
-/
def NodeAvoidsExceptStartGoals
    (start : Position) (goals avoid : List Position) (node : BfsNode) : Prop :=
  ∀ p, p ∈ node.path → p ≠ start → p ∉ goals → p ∉ avoid

/-- 队列中每个节点都满足 `avoid` 例外不变量。 -/
def QueueAvoidsExceptStartGoals
    (start : Position) (goals avoid : List Position) (queue : List BfsNode) : Prop :=
  ∀ node, node ∈ queue → NodeAvoidsExceptStartGoals start goals avoid node

/-- 初始 BFS 节点是可靠的，前提是起点本身可走。 -/
theorem initialBfsNode_sound
    {r : RoomState} {start : Position}
    (hstart : walkable r start) :
    NodeSound r start (initialBfsNode start) := by
  unfold NodeSound initialBfsNode ValidPath PathEndpoints PathWalkable
  simp [PathChain, hstart]

/-- 初始 BFS 节点在任意 hazard 模式下都是可靠的，前提是起点在该模式下可走。 -/
theorem initialBfsNode_sound_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    (hstart : walkableForMode r allowHazard start) :
    NodeSoundForMode r allowHazard start (initialBfsNode start) := by
  unfold NodeSoundForMode initialBfsNode ValidPathForMode PathEndpoints PathWalkableForMode
  simp [PathChain, hstart]

/-- 初始 BFS 队列在当前模式下语义可靠。 -/
theorem initialQueue_sound_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    (hstart : walkableForMode r allowHazard start) :
    QueueSoundForMode r allowHazard start [initialBfsNode start] := by
  intro node hmem
  have hnode : node = initialBfsNode start := by
    simpa using hmem
  rw [hnode]
  exact initialBfsNode_sound_mode hstart

/-- 若一个节点可靠，则由它展开出的所有 child 节点都可靠。 -/
theorem expandNode_queue_sound
    {r : RoomState} {start : Position} {seen avoid goals : List Position}
    {node : BfsNode}
    (hnode : NodeSound r start node) :
    QueueSound r start (expandNode r seen avoid goals false node) := by
  intro child hmem
  exact expandNode_sound hnode hmem

/-- 若一个节点在当前 hazard 模式下可靠，则由它展开出的所有 child 节点都可靠。 -/
theorem expandNode_queue_sound_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {node : BfsNode}
    (hnode : NodeSoundForMode r allowHazard start node) :
    QueueSoundForMode r allowHazard start (expandNode r seen avoid goals allowHazard node) := by
  intro child hmem
  exact expandNode_sound_mode hnode hmem

/-- 初始 BFS 节点携带无重复路径。 -/
theorem initialBfsNode_nodup (start : Position) :
    NodeNoDup (initialBfsNode start) := by
  unfold NodeNoDup initialBfsNode
  simp

/-- 初始 BFS 节点的路径已经包含在初始 `seen = [start]` 中。 -/
theorem initialBfsNode_path_in_seen (start : Position) :
    NodePathInSeen [start] (initialBfsNode start) := by
  intro p hp
  unfold initialBfsNode at hp
  simpa using hp

/-- 初始 BFS 队列中的路径都已经包含在初始 `seen` 中。 -/
theorem initialQueue_paths_in_seen (start : Position) :
    QueuePathsInSeen [start] [initialBfsNode start] := by
  intro node hmem
  have hnode : node = initialBfsNode start := by
    simpa using hmem
  rw [hnode]
  exact initialBfsNode_path_in_seen start

/-- 初始 BFS 状态满足核心状态不变量。 -/
theorem initialBfsStateInvariant
    {r : RoomState} {allowHazard : Bool} {start : Position}
    (hstart : walkableForMode r allowHazard start) :
    BfsStateInvariant r allowHazard start [start] [initialBfsNode start] := by
  constructor
  · exact initialQueue_sound_mode hstart
  · exact initialQueue_paths_in_seen start

/-- 初始 BFS 状态覆盖起点。 -/
theorem initial_tileCovered_start (start : Position) :
    TileCovered [start] [initialBfsNode start] start := by
  unfold TileCovered
  left
  simp

/-- 可靠节点的 `tile` 是其携带路径的最后一个节点，因此出现在该路径中。 -/
theorem node_tile_mem_path_of_sound
    {r : RoomState} {start : Position} {node : BfsNode}
    (hnode : NodeSound r start node) :
    node.tile ∈ node.path := by
  rcases hnode with ⟨hend, _hwalk, _hchain⟩
  rcases hend with ⟨_hhead, hlast⟩
  by_cases hnil : node.path = []
  · rw [hnil] at hlast
    simp at hlast
  · rcases List.getLast?_eq_some_iff.mp hlast with ⟨ys, hpath⟩
    rw [hpath]
    simp

/-- 模式化可靠节点的 `tile` 出现在其携带路径中。 -/
theorem node_tile_mem_path_of_sound_mode
    {r : RoomState} {allowHazard : Bool} {start : Position} {node : BfsNode}
    (hnode : NodeSoundForMode r allowHazard start node) :
    node.tile ∈ node.path := by
  rcases hnode with ⟨hend, _hwalk, _hchain⟩
  rcases hend with ⟨_hhead, hlast⟩
  by_cases hnil : node.path = []
  · rw [hnil] at hlast
    simp at hlast
  · rcases List.getLast?_eq_some_iff.mp hlast with ⟨ys, hpath⟩
    rw [hpath]
    simp

/-- 若节点路径已经包含在 `seen`，且节点语义可靠，则节点 tile 也已经在 `seen` 中。 -/
theorem node_tile_in_seen_of_path_in_seen
    {r : RoomState} {start : Position} {seen : List Position} {node : BfsNode}
    (hnode : NodeSound r start node)
    (hinseen : NodePathInSeen seen node) :
    node.tile ∈ seen :=
  hinseen node.tile (node_tile_mem_path_of_sound hnode)

/-- 模式化版本：可靠节点路径包含于 `seen` 时，节点 tile 也在 `seen` 中。 -/
theorem node_tile_in_seen_of_path_in_seen_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen : List Position} {node : BfsNode}
    (hnode : NodeSoundForMode r allowHazard start node)
    (hinseen : NodePathInSeen seen node) :
    node.tile ∈ seen :=
  hinseen node.tile (node_tile_mem_path_of_sound_mode hnode)

/--
带 BFS 队列不变量的一步旧覆盖保持：如果队列节点都语义可靠且路径都在 `seen` 中，
那么弹出队首并追加 children 不会丢失任何旧的 `seen + queue` 覆盖。
-/
theorem tileCovered_preserved_after_step_of_invariants
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {queue : List BfsNode}
    {node : BfsNode} {p : Position}
    (hqueueSound : QueueSoundForMode r allowHazard start (node :: queue))
    (hpathsSeen : QueuePathsInSeen seen (node :: queue))
    (hcover : TileCovered seen (node :: queue) p) :
    let children := expandNode r seen avoid goals allowHazard node
    TileCovered (seen ++ bfsNodeTiles children) (queue ++ children) p := by
  have hnodeSeen : node.tile ∈ seen :=
    node_tile_in_seen_of_path_in_seen_mode
      (hqueueSound node (by simp))
      (hpathsSeen node (by simp))
  exact tileCovered_preserved_after_step
    (r := r) (allowHazard := allowHazard) (seen := seen)
    (avoid := avoid) (goals := goals) (queue := queue) (node := node)
    (p := p) hnodeSeen hcover

/--
一步 BFS 覆盖推进：处理队首节点后，旧的覆盖不会丢；同时该节点的任意合法邻居
也会被新的 `seen + queue` 覆盖。
-/
theorem tileCovered_step_progress
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {queue : List BfsNode}
    {node : BfsNode} {p : Position}
    (hqueueSound : QueueSoundForMode r allowHazard start (node :: queue))
    (hpathsSeen : QueuePathsInSeen seen (node :: queue))
    (hcoverOrFrontier :
      TileCovered seen (node :: queue) p ∨
        (Neighbor node.tile p ∧ walkableForMode r allowHazard p ∧
          (p ∈ goals ∨ p ∉ avoid))) :
    let children := expandNode r seen avoid goals allowHazard node
    TileCovered (seen ++ bfsNodeTiles children) (queue ++ children) p := by
  intro children
  rcases hcoverOrFrontier with hcover | hfrontier
  · exact tileCovered_preserved_after_step_of_invariants
      (r := r) (allowHazard := allowHazard) (start := start)
      (seen := seen) (avoid := avoid) (goals := goals)
      (queue := queue) (node := node) (p := p)
      hqueueSound hpathsSeen hcover
  · rcases hfrontier with ⟨hneighbor, hwalk, hallowed⟩
    rcases bfs_step_covers_constrained_neighbor
        (r := r) (allowHazard := allowHazard) (seen := seen)
        (avoid := avoid) (goals := goals) (queue := queue) (node := node)
        (nxt := p) hneighbor hwalk hallowed with
      ⟨hseen, hqueue⟩
    unfold TileCovered
    rcases hqueue with hOld | hQueued
    · left
      rw [List.mem_append]
      exact Or.inl hOld
    · right
      exact hQueued

/-- 初始路径只有起点，因此满足 `avoid` 例外不变量。 -/
theorem initialBfsNode_avoids_except_start_goals
    (start : Position) (goals avoid : List Position) :
    NodeAvoidsExceptStartGoals start goals avoid (initialBfsNode start) := by
  intro p hp hne _hnotGoal
  unfold initialBfsNode at hp
  simp at hp
  subst p
  exfalso
  exact hne rfl

/--
从一个无重复节点展开 child 时，若旧路径都在 `seen` 中，那么 child 的路径仍无重复。
-/
theorem expandNode_nodup
    {r : RoomState} {seen avoid goals : List Position} {node child : BfsNode}
    (hnodup : NodeNoDup node)
    (hinseen : NodePathInSeen seen node)
    (hmem : child ∈ expandNode r seen avoid goals false node) :
    NodeNoDup child := by
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, _hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt false && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      unfold NodeNoDup at hnodup ⊢
      rw [List.nodup_append]
      constructor
      · exact hnodup
      constructor
      · simp
      · intro a ha b hb _heq
        simp at hb
        subst b
        subst a
        exact containsPos_false_not_mem hseen (hinseen nxt ha)
  · simp [hseen] at hcase

/-- 若一个节点满足无重复不变量，则它展开出的所有 child 也满足。 -/
theorem expandNode_queue_nodup
    {r : RoomState} {seen avoid goals : List Position} {node : BfsNode}
    (hnodup : NodeNoDup node)
    (hinseen : NodePathInSeen seen node) :
    QueueNoDupPaths (expandNode r seen avoid goals false node) := by
  intro child hmem
  exact expandNode_nodup hnodup hinseen hmem

/-- `expandNode` 保持 `avoid` 例外不变量。 -/
theorem expandNode_avoids_except_start_goals
    {r : RoomState} {start : Position} {seen avoid goals : List Position}
    {node child : BfsNode}
    (hnode : NodeAvoidsExceptStartGoals start goals avoid node)
    (hmem : child ∈ expandNode r seen avoid goals false node) :
    NodeAvoidsExceptStartGoals start goals avoid child := by
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, _hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt false && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      intro p hp hne hnotGoal
      rw [List.mem_append] at hp
      rcases hp with hpOld | hpNew
      · exact hnode p hpOld hne hnotGoal
      · simp at hpNew
        subst p
        have hallowed' := hallowed
        unfold allowedByAvoid at hallowed'
        simp at hallowed'
        have hnotGoalBool : containsPos goals nxt = false := by
          cases hg : containsPos goals nxt
          · rfl
          · exfalso
            exact hnotGoal ((containsPos_true_iff goals nxt).1 hg)
        rw [hnotGoalBool] at hallowed'
        simp at hallowed'
        exact containsPos_false_not_mem hallowed'.2
  · simp [hseen] at hcase

/-- `expandNode` 产生的 child 队列满足 `avoid` 例外不变量。 -/
theorem expandNode_queue_avoids_except_start_goals
    {r : RoomState} {start : Position} {seen avoid goals : List Position}
    {node : BfsNode}
    (hnode : NodeAvoidsExceptStartGoals start goals avoid node) :
    QueueAvoidsExceptStartGoals start goals avoid
      (expandNode r seen avoid goals false node) := by
  intro child hmem
  exact expandNode_avoids_except_start_goals hnode hmem

/-- `expandNode` 在任意 hazard 模式下都保持 `avoid` 例外不变量。 -/
theorem expandNode_avoids_except_start_goals_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {node child : BfsNode}
    (hnode : NodeAvoidsExceptStartGoals start goals avoid node)
    (hmem : child ∈ expandNode r seen avoid goals allowHazard node) :
    NodeAvoidsExceptStartGoals start goals avoid child := by
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, _hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt allowHazard && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      intro p hp hne hnotGoal
      rw [List.mem_append] at hp
      rcases hp with hpOld | hpNew
      · exact hnode p hpOld hne hnotGoal
      · simp at hpNew
        subst p
        have hallowedCopy := hallowed
        unfold allowedByAvoid at hallowedCopy
        simp at hallowedCopy
        have hnotGoalBool : containsPos goals nxt = false := by
          cases hg : containsPos goals nxt
          · rfl
          · exfalso
            exact hnotGoal ((containsPos_true_iff goals nxt).1 hg)
        rw [hnotGoalBool] at hallowedCopy
        simp at hallowedCopy
        exact containsPos_false_not_mem hallowedCopy.2
  · simp [hseen] at hcase

/-- `expandNode` 在任意 hazard 模式下产生的 child 队列满足 `avoid` 例外不变量。 -/
theorem expandNode_queue_avoids_except_start_goals_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {node : BfsNode}
    (hnode : NodeAvoidsExceptStartGoals start goals avoid node) :
    QueueAvoidsExceptStartGoals start goals avoid
      (expandNode r seen avoid goals allowHazard node) := by
  intro child hmem
  exact expandNode_avoids_except_start_goals_mode hnode hmem

/-- 可靠队列追加可靠队列后仍可靠。 -/
theorem queueSound_append
    {r : RoomState} {start : Position} {xs ys : List BfsNode}
    (hxs : QueueSound r start xs)
    (hys : QueueSound r start ys) :
    QueueSound r start (xs ++ ys) := by
  intro node hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hx => exact hxs node hx
  | inr hy => exact hys node hy

/-- 模式化可靠队列追加可靠队列后仍可靠。 -/
theorem queueSoundForMode_append
    {r : RoomState} {allowHazard : Bool} {start : Position} {xs ys : List BfsNode}
    (hxs : QueueSoundForMode r allowHazard start xs)
    (hys : QueueSoundForMode r allowHazard start ys) :
    QueueSoundForMode r allowHazard start (xs ++ ys) := by
  intro node hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hx => exact hxs node hx
  | inr hy => exact hys node hy

/-- 无重复路径队列追加后仍满足无重复路径不变量。 -/
theorem queueNoDup_append
    {xs ys : List BfsNode}
    (hxs : QueueNoDupPaths xs)
    (hys : QueueNoDupPaths ys) :
    QueueNoDupPaths (xs ++ ys) := by
  intro node hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hx => exact hxs node hx
  | inr hy => exact hys node hy

/-- `avoid` 例外不变量在队列追加后保持。 -/
theorem queueAvoids_append
    {start : Position} {goals avoid : List Position} {xs ys : List BfsNode}
    (hxs : QueueAvoidsExceptStartGoals start goals avoid xs)
    (hys : QueueAvoidsExceptStartGoals start goals avoid ys) :
    QueueAvoidsExceptStartGoals start goals avoid (xs ++ ys) := by
  intro node hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hx => exact hxs node hx
  | inr hy => exact hys node hy

/-- 路径包含于 `seen` 的队列不变量在追加更多 seen 格子后仍成立。 -/
theorem queuePathsInSeen_extend
    {seen extra : List Position} {nodes : List BfsNode}
    (hqueue : QueuePathsInSeen seen nodes) :
    QueuePathsInSeen (seen ++ extra) nodes := by
  intro node hmem p hp
  rw [List.mem_append]
  left
  exact hqueue node hmem p hp

/-- 路径包含于 seen 的队列追加后仍满足该不变量。 -/
theorem queuePathsInSeen_append
    {seen : List Position} {xs ys : List BfsNode}
    (hxs : QueuePathsInSeen seen xs)
    (hys : QueuePathsInSeen seen ys) :
    QueuePathsInSeen seen (xs ++ ys) := by
  intro node hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hx => exact hxs node hx
  | inr hy => exact hys node hy

/-- 一步递归保持模式化队列可靠性。 -/
theorem queueSoundForMode_step
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {node : BfsNode} {queue : List BfsNode}
    (hqueue : QueueSoundForMode r allowHazard start (node :: queue)) :
    QueueSoundForMode r allowHazard start
      (queue ++ expandNode r seen avoid goals allowHazard node) := by
  have hrest : QueueSoundForMode r allowHazard start queue := by
    intro n hn
    exact hqueue n (by simp [hn])
  have hchildren :
      QueueSoundForMode r allowHazard start
        (expandNode r seen avoid goals allowHazard node) :=
    expandNode_queue_sound_mode (hqueue node (by simp))
  exact queueSoundForMode_append hrest hchildren

/-- `expandNode` 产生的 child 路径都包含在更新后的 `seen'` 中。 -/
theorem expandNode_path_in_next_seen
    {r : RoomState} {seen avoid goals : List Position} {node child : BfsNode}
    (hinseen : NodePathInSeen seen node)
    (hmem : child ∈ expandNode r seen avoid goals false node) :
    NodePathInSeen (seen ++ bfsNodeTiles (expandNode r seen avoid goals false node)) child := by
  have hchildMem := hmem
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, _hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt false && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      intro p hp
      rw [List.mem_append]
      rw [List.mem_append] at hp
      rcases hp with hpOld | hpNew
      · left
        exact hinseen p hpOld
      · simp at hpNew
        subst p
        right
        unfold bfsNodeTiles
        exact List.mem_map.mpr ⟨{ tile := nxt, path := node.path ++ [nxt] }, hchildMem, rfl⟩
  · simp [hseen] at hcase

/-- `expandNode` 产生的 child 队列在更新后的 `seen'` 下满足路径覆盖不变量。 -/
theorem expandNode_queue_paths_in_next_seen
    {r : RoomState} {seen avoid goals : List Position} {node : BfsNode}
    (hinseen : NodePathInSeen seen node) :
    QueuePathsInSeen
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals false node))
      (expandNode r seen avoid goals false node) := by
  intro child hmem
  exact expandNode_path_in_next_seen hinseen hmem

/-- 模式化版本：`expandNode` 产生的 child 路径都包含在更新后的 `seen'` 中。 -/
theorem expandNode_path_in_next_seen_mode
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position}
    {node child : BfsNode}
    (hinseen : NodePathInSeen seen node)
    (hmem : child ∈ expandNode r seen avoid goals allowHazard node) :
    NodePathInSeen
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node)) child := by
  have hchildMem := hmem
  unfold expandNode at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨nxt, _hnbr, hcase⟩
  cases hseen : containsPos seen nxt
  · cases hallowed : walkableBool r nxt allowHazard && allowedByAvoid avoid goals nxt
    · simp [hseen, hallowed] at hcase
    · simp [hseen, hallowed] at hcase
      subst child
      intro p hp
      rw [List.mem_append]
      rw [List.mem_append] at hp
      rcases hp with hpOld | hpNew
      · left
        exact hinseen p hpOld
      · simp at hpNew
        subst p
        right
        unfold bfsNodeTiles
        exact List.mem_map.mpr
          ⟨{ tile := nxt, path := node.path ++ [nxt] }, hchildMem, rfl⟩
  · simp [hseen] at hcase

/-- 模式化版本：`expandNode` 的 child 队列在更新后的 `seen'` 下满足路径覆盖不变量。 -/
theorem expandNode_queue_paths_in_next_seen_mode
    {r : RoomState} {allowHazard : Bool} {seen avoid goals : List Position} {node : BfsNode}
    (hinseen : NodePathInSeen seen node) :
    QueuePathsInSeen
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
      (expandNode r seen avoid goals allowHazard node) := by
  intro child hmem
  exact expandNode_path_in_next_seen_mode hinseen hmem

/-- 一步递归保持“队列路径包含于 seen”的不变量。 -/
theorem queuePathsInSeen_step_mode
    {r : RoomState} {allowHazard : Bool}
    {seen avoid goals : List Position} {node : BfsNode} {queue : List BfsNode}
    (hpaths : QueuePathsInSeen seen (node :: queue)) :
    QueuePathsInSeen
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
      (queue ++ expandNode r seen avoid goals allowHazard node) := by
  have hnodeInSeen : NodePathInSeen seen node := hpaths node (by simp)
  have hrestSeen :
      QueuePathsInSeen
        (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        queue :=
    queuePathsInSeen_extend
      (by
        intro n hn
        exact hpaths n (by simp [hn]))
  have hchildrenSeen :
      QueuePathsInSeen
        (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        (expandNode r seen avoid goals allowHazard node) :=
    expandNode_queue_paths_in_next_seen_mode hnodeInSeen
  exact queuePathsInSeen_append hrestSeen hchildrenSeen

/-- 一步递归保持 BFS 核心状态不变量。 -/
theorem bfsStateInvariant_step
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {seen avoid goals : List Position} {node : BfsNode} {queue : List BfsNode}
    (hinv : BfsStateInvariant r allowHazard start seen (node :: queue)) :
    BfsStateInvariant r allowHazard start
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
      (queue ++ expandNode r seen avoid goals allowHazard node) := by
  rcases hinv with ⟨hsound, hpaths⟩
  constructor
  · exact queueSoundForMode_step
      (r := r) (allowHazard := allowHazard) (start := start)
      (seen := seen) (avoid := avoid) (goals := goals)
      (node := node) (queue := queue) hsound
  · exact queuePathsInSeen_step_mode
      (r := r) (allowHazard := allowHazard)
      (seen := seen) (avoid := avoid) (goals := goals)
      (node := node) (queue := queue) hpaths

/--
证明用的 BFS 状态推进函数：与 `bfsSearch` 的队列/seen 更新一致，但不在 goal 处
提前返回路径，只返回推进后的 `(seen, queue)`。它用于表达多步 frontier 覆盖不变量。
-/
def bfsAdvance
    (r : RoomState) (goals avoid : List Position) (allowHazard : Bool) :
    Nat → List Position → List BfsNode → List Position × List BfsNode
  | 0, seen, queue => (seen, queue)
  | _ + 1, seen, [] => (seen, [])
  | fuel + 1, seen, node :: queue =>
      let children := expandNode r seen avoid goals allowHazard node
      let seen' := seen ++ bfsNodeTiles children
      bfsAdvance r goals avoid allowHazard fuel seen' (queue ++ children)

/-- 证明用的 BFS trace 状态：额外记录已经弹出并处理过的 tile。 -/
def bfsAdvanceTrace
    (r : RoomState) (goals avoid : List Position) (allowHazard : Bool) :
    Nat → List Position → List Position → List BfsNode →
      List Position × List Position × List BfsNode
  | 0, processed, seen, queue => (processed, seen, queue)
  | _ + 1, processed, seen, [] => (processed, seen, [])
  | fuel + 1, processed, seen, node :: queue =>
      let children := expandNode r seen avoid goals allowHazard node
      let processed' := processed ++ [node.tile]
      let seen' := seen ++ bfsNodeTiles children
      bfsAdvanceTrace r goals avoid allowHazard fuel processed' seen' (queue ++ children)

/-- 在 trace 语义下，一个格子已经被处理过，或仍作为队列节点等待处理。 -/
def TraceCovered (processed : List Position) (queue : List BfsNode) (p : Position) : Prop :=
  p ∈ processed ∨ ∃ node, node ∈ queue ∧ node.tile = p

/-- `seen` 中的每个格子都应当能在 processed 或 queue 中找到来源。 -/
def SeenTraceCovered
    (processed seen : List Position) (queue : List BfsNode) : Prop :=
  ∀ p, p ∈ seen → TraceCovered processed queue p

/-- 已处理节点的合法 frontier 已经被 processed/queue 覆盖。 -/
def ProcessedFrontierClosed
    (r : RoomState) (allowHazard : Bool) (goals avoid : List Position)
    (processed : List Position) (queue : List BfsNode) : Prop :=
  ∀ p nxt,
    p ∈ processed →
    Neighbor p nxt →
    walkableForMode r allowHazard nxt →
    (nxt ∈ goals ∨ nxt ∉ avoid) →
    TraceCovered processed queue nxt

/-- 从当前格子出发的一条满足 BFS 模式约束的路径后缀。 -/
inductive ConstrainedSuffix
    (r : RoomState) (allowHazard : Bool) (goals avoid : List Position) :
    Position → List Position → Prop where
  | single {p : Position}
      (hwalk : walkableForMode r allowHazard p) :
      ConstrainedSuffix r allowHazard goals avoid p [p]
  | cons {p q : Position} {rest : List Position}
      (hwalk : walkableForMode r allowHazard p)
      (hneigh : Neighbor p q)
      (hnext : q ∈ goals ∨ q ∉ avoid)
      (htail : ConstrainedSuffix r allowHazard goals avoid q (q :: rest)) :
      ConstrainedSuffix r allowHazard goals avoid p (p :: q :: rest)

/--
把普通路径结构转换为 `ConstrainedSuffix`。这里要求路径中每个点满足当前模式可走，
相邻链成立，并且每一步的下一个点要么是 goal，要么不在 avoid 中。
-/
theorem constrainedSuffix_of_chain
    {r : RoomState} {allowHazard : Bool} {goals avoid : List Position} :
    ∀ {path : List Position} {start : Position},
      path.head? = some start →
      path.Nodup →
      PathWalkableForMode r allowHazard path →
      PathChain path →
      (∀ p, p ∈ path → p ≠ start → p ∉ goals → p ∉ avoid) →
      ConstrainedSuffix r allowHazard goals avoid start path
  | [], start, hhead, _hnodup, _hwalks, _hchain, _havoid => by
      simp at hhead
  | [p], start, hhead, _hnodup, hwalks, _hchain, _havoid => by
      simp at hhead
      subst p
      exact ConstrainedSuffix.single (hwalks start (by simp))
  | p :: q :: rest, start, hhead, hnodup, hwalks, hchain, havoid => by
      simp at hhead
      subst p
      have hnodupSplit := hnodup
      simp at hnodupSplit
      have hnodupTail : (q :: rest).Nodup := by
        simp [hnodupSplit.2.1, hnodupSplit.2.2]
      have hstartNotTail : start ∉ q :: rest := by
        intro hs
        simp at hs
        rcases hs with hs | hs
        · exact hnodupSplit.1.1 hs
        · exact hnodupSplit.1.2 hs
      have htail :
          ConstrainedSuffix r allowHazard goals avoid q (q :: rest) :=
        constrainedSuffix_of_chain
          (path := q :: rest) (start := q)
          (by simp)
          hnodupTail
          (by
            intro x hx
            exact hwalks x (by simp [hx]))
          (by
            simpa [PathChain] using hchain.2)
          (by
            intro x hx hxq hxnotGoal
            by_cases hx_is_q : x = q
            · exact False.elim (hxq hx_is_q)
            exact havoid x (by simp [hx])
              (by
                intro hxstart
                exact hstartNotTail (by simpa [hxstart] using hx))
              hxnotGoal)
      have hnext : q ∈ goals ∨ q ∉ avoid := by
        by_cases hgoal : q ∈ goals
        · exact Or.inl hgoal
        · right
          exact havoid q (by simp)
            (by
              intro hqStart
              have hneighbor : Neighbor start q := by
                simpa [PathChain] using hchain.1
              exact neighbor_ne hneighbor hqStart.symm)
            hgoal
      exact ConstrainedSuffix.cons
        (hwalks start (by simp))
        (by simpa [PathChain] using hchain.1)
        hnext htail

/-- trace 层的核心覆盖不变量。 -/
def BfsTraceInvariant
    (r : RoomState) (allowHazard : Bool) (goals avoid : List Position)
    (processed seen : List Position) (queue : List BfsNode) : Prop :=
  SeenTraceCovered processed seen queue ∧
    ProcessedFrontierClosed r allowHazard goals avoid processed queue

/-- 初始 trace 状态满足覆盖不变量。 -/
theorem initialBfsTraceInvariant
    {r : RoomState} {allowHazard : Bool} {goals avoid : List Position} {start : Position} :
    BfsTraceInvariant r allowHazard goals avoid [] [start] [initialBfsNode start] := by
  constructor
  · intro p hp
    unfold TraceCovered
    right
    refine ⟨initialBfsNode start, by simp, ?_⟩
    simp [initialBfsNode] at hp ⊢
    exact hp.symm
  · intro p _nxt hp _hneigh _hwalk _hallowed
    simp at hp

/-- trace 覆盖在一步 BFS 处理后保持。 -/
theorem traceCovered_preserved_after_step
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {node : BfsNode} {queue : List BfsNode} {p : Position}
    (hcover : TraceCovered processed (node :: queue) p) :
    let children := expandNode r seen avoid goals allowHazard node
    TraceCovered (processed ++ [node.tile]) (queue ++ children) p := by
  intro children
  unfold TraceCovered at hcover ⊢
  rcases hcover with hproc | hqueue
  · left
    rw [List.mem_append]
    exact Or.inl hproc
  · rcases hqueue with ⟨coveredNode, hmem, htile⟩
    simp at hmem
    rcases hmem with hhead | hrest
    · subst coveredNode
      subst p
      left
      rw [List.mem_append]
      exact Or.inr (by simp)
    · right
      refine ⟨coveredNode, ?_, htile⟩
      rw [List.mem_append]
      exact Or.inl hrest

/-- 新加入的 child tile 在 trace 中由新队列覆盖。 -/
theorem child_tile_traceCovered_after_step
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {node child : BfsNode} {queue : List BfsNode}
    (hchild : child ∈ expandNode r seen avoid goals allowHazard node) :
    TraceCovered (processed ++ [node.tile])
      (queue ++ expandNode r seen avoid goals allowHazard node) child.tile := by
  unfold TraceCovered
  right
  refine ⟨child, ?_, rfl⟩
  rw [List.mem_append]
  exact Or.inr hchild

/-- `TileCovered` 可以借助 `SeenTraceCovered` 提升为 trace 覆盖。 -/
theorem tileCovered_to_traceCovered
    {processed seen : List Position} {queue : List BfsNode} {p : Position}
    (hseenTrace : SeenTraceCovered processed seen queue)
    (hcover : TileCovered seen queue p) :
    TraceCovered processed queue p := by
  unfold TileCovered at hcover
  rcases hcover with hseen | hqueue
  · exact hseenTrace p hseen
  · unfold TraceCovered
    exact Or.inr hqueue

/-- 一步处理后，新的 `seen` 仍然都能由 processed/queue 解释。 -/
theorem seenTraceCovered_step
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {node : BfsNode} {queue : List BfsNode}
    (hseenTrace : SeenTraceCovered processed seen (node :: queue)) :
    SeenTraceCovered (processed ++ [node.tile])
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
      (queue ++ expandNode r seen avoid goals allowHazard node) := by
  intro p hp
  rw [List.mem_append] at hp
  rcases hp with hpSeen | hpChildTile
  · exact traceCovered_preserved_after_step
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (processed := processed) (seen := seen) (node := node) (queue := queue)
      (p := p) (hseenTrace p hpSeen)
  · unfold bfsNodeTiles at hpChildTile
    rcases List.mem_map.mp hpChildTile with ⟨child, hchild, htile⟩
    subst p
    exact child_tile_traceCovered_after_step
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (processed := processed) (seen := seen) (node := node) (queue := queue)
      hchild

/-- 一步处理后，已处理节点的 frontier 闭包保持。 -/
theorem processedFrontierClosed_step
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {node : BfsNode} {queue : List BfsNode}
    (hseenTrace :
      SeenTraceCovered (processed ++ [node.tile])
        (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        (queue ++ expandNode r seen avoid goals allowHazard node))
    (hclosed : ProcessedFrontierClosed r allowHazard goals avoid processed (node :: queue)) :
    ProcessedFrontierClosed r allowHazard goals avoid
      (processed ++ [node.tile])
      (queue ++ expandNode r seen avoid goals allowHazard node) := by
  intro p nxt hp hneighbor hwalk hallowed
  rw [List.mem_append] at hp
  rcases hp with hpOld | hpNew
  · exact traceCovered_preserved_after_step
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (processed := processed) (seen := seen) (node := node) (queue := queue)
      (p := nxt)
      (hclosed p nxt hpOld hneighbor hwalk hallowed)
  · simp at hpNew
    subst p
    have htile :
        TileCovered
          (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
          (queue ++ expandNode r seen avoid goals allowHazard node)
          nxt := by
      rcases bfs_step_covers_constrained_neighbor
          (r := r) (allowHazard := allowHazard) (seen := seen)
          (avoid := avoid) (goals := goals) (queue := queue) (node := node)
          (nxt := nxt) hneighbor hwalk hallowed with
        ⟨hseen, hqueue⟩
      unfold TileCovered
      rcases hqueue with hOld | hQueued
      · left
        rw [List.mem_append]
        exact Or.inl hOld
      · right
        exact hQueued
    exact tileCovered_to_traceCovered hseenTrace htile

/-- 一步 BFS 处理保持 trace 覆盖不变量。 -/
theorem bfsTraceInvariant_step
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {node : BfsNode} {queue : List BfsNode}
    (hinv : BfsTraceInvariant r allowHazard goals avoid processed seen (node :: queue)) :
    BfsTraceInvariant r allowHazard goals avoid
      (processed ++ [node.tile])
      (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
      (queue ++ expandNode r seen avoid goals allowHazard node) := by
  rcases hinv with ⟨hseenTrace, hclosed⟩
  have hseenStep :
      SeenTraceCovered (processed ++ [node.tile])
        (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        (queue ++ expandNode r seen avoid goals allowHazard node) :=
    seenTraceCovered_step
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (processed := processed) (seen := seen) (node := node) (queue := queue)
      hseenTrace
  exact ⟨hseenStep,
    processedFrontierClosed_step
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (processed := processed) (seen := seen) (node := node) (queue := queue)
      hseenStep hclosed⟩

/-- `bfsAdvanceTrace` 推进任意多步都保持 trace 覆盖不变量。 -/
theorem bfsAdvanceTrace_preserves_invariant
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} {fuel : Nat}
    (hinv : BfsTraceInvariant r allowHazard goals avoid processed seen queue) :
    BfsTraceInvariant r allowHazard goals avoid
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).1
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.1
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.2 := by
  revert processed seen queue
  induction fuel with
  | zero =>
      intro processed seen queue hinv
      simpa [bfsAdvanceTrace] using hinv
  | succ fuel ih =>
      intro processed seen queue hinv
      cases queue with
      | nil =>
          simpa [bfsAdvanceTrace] using hinv
      | cons node rest =>
          simp [bfsAdvanceTrace]
          exact ih (bfsTraceInvariant_step
            (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
            (processed := processed) (seen := seen) (node := node) (queue := rest)
            hinv)

/-- `bfsAdvanceTrace` 只会向 `seen` 追加格子，不会删除旧的 seen。 -/
theorem bfsAdvanceTrace_seen_monotone
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} {fuel : Nat} {p : Position}
    (hp : p ∈ seen) :
    p ∈ (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.1 := by
  revert processed seen queue
  induction fuel with
  | zero =>
      intro processed seen queue hp
      simpa [bfsAdvanceTrace] using hp
  | succ fuel ih =>
      intro processed seen queue hp
      cases queue with
      | nil =>
          simpa [bfsAdvanceTrace] using hp
      | cons node rest =>
          simp [bfsAdvanceTrace]
          exact ih (by
            rw [List.mem_append]
            exact Or.inl hp)

/-- `seen` 中的任意格子在 trace 推进任意步后仍由 processed/queue 覆盖。 -/
theorem bfsAdvanceTrace_preserves_seen_traceCovered
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} {fuel : Nat} {p : Position}
    (hinv : BfsTraceInvariant r allowHazard goals avoid processed seen queue)
    (hp : p ∈ seen) :
    TraceCovered
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).1
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.2
      p := by
  have hinv' :=
    bfsAdvanceTrace_preserves_invariant
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (processed := processed) (seen := seen) (queue := queue) (fuel := fuel)
      hinv
  exact hinv'.1 p (bfsAdvanceTrace_seen_monotone
    (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
    (processed := processed) (seen := seen) (queue := queue) (fuel := fuel)
    hp)

/-- 已经 trace-covered 的格子在 trace 推进任意步后仍然 trace-covered。 -/
theorem bfsAdvanceTrace_preserves_traceCovered
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} {fuel : Nat} {p : Position}
    (hinv : BfsTraceInvariant r allowHazard goals avoid processed seen queue)
    (hcover : TraceCovered processed queue p) :
    TraceCovered
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).1
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.2
      p := by
  revert processed seen queue
  induction fuel with
  | zero =>
      intro processed seen queue hinv hcover
      simpa [bfsAdvanceTrace] using hcover
  | succ fuel ih =>
      intro processed seen queue hinv hcover
      cases queue with
      | nil =>
          simpa [bfsAdvanceTrace] using hcover
      | cons node rest =>
          simp [bfsAdvanceTrace]
          have hstepInv :
              BfsTraceInvariant r allowHazard goals avoid
                (processed ++ [node.tile])
                (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
                (rest ++ expandNode r seen avoid goals allowHazard node) :=
            bfsTraceInvariant_step
              (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
              (processed := processed) (seen := seen) (node := node) (queue := rest)
              hinv
          have hstepCover :
              TraceCovered (processed ++ [node.tile])
                (rest ++ expandNode r seen avoid goals allowHazard node) p :=
            traceCovered_preserved_after_step
              (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
              (processed := processed) (seen := seen) (node := node) (queue := rest)
              (p := p) hcover
          exact ih hstepInv hstepCover

/--
trace 版：若队列中某个节点 `node` 的合法邻居是 frontier，则处理到该节点并继续推进
任意多步后，该邻居被 processed/queue 覆盖。
-/
theorem bfsAdvanceTrace_covers_frontier_of_queued_node
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {front suffix : List BfsNode} {node : BfsNode} {fuel : Nat} {p : Position}
    (hinv : BfsTraceInvariant r allowHazard goals avoid processed seen (front ++ node :: suffix))
    (hfrontier :
      Neighbor node.tile p ∧ walkableForMode r allowHazard p ∧
        (p ∈ goals ∨ p ∉ avoid)) :
    TraceCovered
      (bfsAdvanceTrace r goals avoid allowHazard (front.length + 1 + fuel)
        processed seen (front ++ node :: suffix)).1
      (bfsAdvanceTrace r goals avoid allowHazard (front.length + 1 + fuel)
        processed seen (front ++ node :: suffix)).2.2
      p := by
  induction front generalizing processed seen suffix with
  | nil =>
      have hstepInv :
          BfsTraceInvariant r allowHazard goals avoid
            (processed ++ [node.tile])
            (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
            (suffix ++ expandNode r seen avoid goals allowHazard node) :=
        bfsTraceInvariant_step
          (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
          (processed := processed) (seen := seen) (node := node) (queue := suffix)
          hinv
      have hnow :
          TraceCovered (processed ++ [node.tile])
            (suffix ++ expandNode r seen avoid goals allowHazard node) p := by
        exact hstepInv.2 node.tile p (by
          rw [List.mem_append]
          exact Or.inr (by simp)) hfrontier.1 hfrontier.2.1 hfrontier.2.2
      simpa [bfsAdvanceTrace, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        bfsAdvanceTrace_preserves_traceCovered
        (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
        (processed := processed ++ [node.tile])
        (seen := seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        (queue := suffix ++ expandNode r seen avoid goals allowHazard node)
        (fuel := fuel) (p := p) hstepInv hnow
  | cons head rest ih =>
      have hstepInv :
          BfsTraceInvariant r allowHazard goals avoid
            (processed ++ [head.tile])
            (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
            (rest ++ node :: (suffix ++ expandNode r seen avoid goals allowHazard head)) := by
        have hraw :
            BfsTraceInvariant r allowHazard goals avoid
              (processed ++ [head.tile])
              (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
              ((rest ++ node :: suffix) ++ expandNode r seen avoid goals allowHazard head) :=
          bfsTraceInvariant_step
            (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
            (processed := processed) (seen := seen) (node := head)
            (queue := rest ++ node :: suffix)
            (by simpa [List.cons_append] using hinv)
        simpa [List.append_assoc] using hraw
      have htarget :=
        ih
          (processed := processed ++ [head.tile])
          (seen := seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
          (suffix := suffix ++ expandNode r seen avoid goals allowHazard head)
          hstepInv
      simpa [bfsAdvanceTrace, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using htarget

/-- 空队列下，`bfsAdvanceTrace` 推进任意步都保持不变。 -/
theorem bfsAdvanceTrace_empty
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    (fuel : Nat) :
    bfsAdvanceTrace r goals avoid allowHazard fuel processed seen [] = (processed, seen, []) := by
  cases fuel <;> simp [bfsAdvanceTrace]

/-- `bfsAdvanceTrace` 的多步推进可以分段组合。 -/
theorem bfsAdvanceTrace_add
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} (fuel₁ fuel₂ : Nat) :
    bfsAdvanceTrace r goals avoid allowHazard (fuel₁ + fuel₂) processed seen queue =
      let s := bfsAdvanceTrace r goals avoid allowHazard fuel₁ processed seen queue
      bfsAdvanceTrace r goals avoid allowHazard fuel₂ s.1 s.2.1 s.2.2 := by
  revert processed seen queue
  induction fuel₁ with
  | zero =>
      intro processed seen queue
      simp [bfsAdvanceTrace]
  | succ fuel₁ ih =>
      intro processed seen queue
      cases queue with
      | nil =>
          simp [bfsAdvanceTrace_empty]
      | cons node rest =>
          rw [Nat.succ_add]
          simp [bfsAdvanceTrace]
          exact ih

/--
任意长度约束后缀的终点 eventually 被 trace 覆盖。

如果当前格子 `cur` 已经由 `processed/queue` 覆盖，并且存在一条满足 BFS 模式约束的
后缀路径从 `cur` 到 `target`，那么推进有限步后 `target` 也会被覆盖。
-/
theorem constrainedSuffix_eventually_traceCovered
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} {cur target : Position} {path : List Position}
    (hsuffix : ConstrainedSuffix r allowHazard goals avoid cur path)
    (hlast : path.getLast? = some target)
    (hinv : BfsTraceInvariant r allowHazard goals avoid processed seen queue)
    (hcover : TraceCovered processed queue cur) :
    ∃ fuel,
      TraceCovered
        (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).1
        (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.2
        target := by
  induction hsuffix generalizing processed seen queue target with
  | single hwalk =>
      simp at hlast
      subst target
      exact ⟨0, by simpa [bfsAdvanceTrace] using hcover⟩
  | cons hwalk hneigh hnext htail ih =>
      rename_i p q rest
      simp at hlast
      unfold TraceCovered at hcover
      rcases hcover with hprocessed | hqueued
      · have hq : TraceCovered processed queue q :=
          hinv.2 p q hprocessed hneigh (by
            cases htail with
            | single hqwalk => exact hqwalk
            | cons hqwalk _ _ _ => exact hqwalk) hnext
        exact ih hlast hinv hq
      · rcases hqueued with ⟨node, hnodeMem, hnodeTile⟩
        rcases list_mem_split hnodeMem with ⟨front, suffix, hsplit⟩
        have hinvQueue :
            BfsTraceInvariant r allowHazard goals avoid processed seen
              (front ++ node :: suffix) := by
          simpa [hsplit] using hinv
        have hfrontier :
            Neighbor node.tile q ∧ walkableForMode r allowHazard q ∧
              (q ∈ goals ∨ q ∉ avoid) := by
          constructor
          · simpa [hnodeTile] using hneigh
          constructor
          · cases htail with
            | single hqwalk => exact hqwalk
            | cons hqwalk _ _ _ => exact hqwalk
          · exact hnext
        let fuel₁ := front.length + 1
        have hqCover :
            TraceCovered
              (bfsAdvanceTrace r goals avoid allowHazard fuel₁ processed seen queue).1
              (bfsAdvanceTrace r goals avoid allowHazard fuel₁ processed seen queue).2.2
              q := by
          have hraw :=
            bfsAdvanceTrace_covers_frontier_of_queued_node
              (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
              (processed := processed) (seen := seen)
              (front := front) (suffix := suffix) (node := node) (fuel := 0)
              hinvQueue hfrontier
          simpa [fuel₁, hsplit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hraw
        have hinvAfter :
            BfsTraceInvariant r allowHazard goals avoid
              (bfsAdvanceTrace r goals avoid allowHazard fuel₁ processed seen queue).1
              (bfsAdvanceTrace r goals avoid allowHazard fuel₁ processed seen queue).2.1
              (bfsAdvanceTrace r goals avoid allowHazard fuel₁ processed seen queue).2.2 :=
          bfsAdvanceTrace_preserves_invariant
            (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
            (processed := processed) (seen := seen) (queue := queue) (fuel := fuel₁)
            hinv
        rcases ih hlast hinvAfter hqCover with ⟨fuel₂, htarget⟩
        refine ⟨fuel₁ + fuel₂, ?_⟩
        simpa [bfsAdvanceTrace_add]
          using htarget

/--
从初始 BFS trace 状态出发，任意长度的约束后缀路径终点 eventually 被覆盖。
-/
theorem constrainedSuffix_initial_eventually_traceCovered
    {r : RoomState} {allowHazard : Bool} {goals avoid : List Position}
    {start target : Position} {path : List Position}
    (hsuffix : ConstrainedSuffix r allowHazard goals avoid start path)
    (hlast : path.getLast? = some target) :
    ∃ fuel,
      TraceCovered
        (bfsAdvanceTrace r goals avoid allowHazard fuel [] [start] [initialBfsNode start]).1
        (bfsAdvanceTrace r goals avoid allowHazard fuel [] [start] [initialBfsNode start]).2.2
        target := by
  exact constrainedSuffix_eventually_traceCovered
    (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
    (processed := []) (seen := [start]) (queue := [initialBfsNode start])
    (cur := start) (target := target) (path := path)
    hsuffix hlast
    (initialBfsTraceInvariant
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (start := start))
    (by
      unfold TraceCovered
      right
      refine ⟨initialBfsNode start, by simp, ?_⟩
      simp [initialBfsNode])

/-- `bfsAdvance` 多步推进保持 BFS 核心状态不变量。 -/
theorem bfsAdvance_preserves_stateInvariant
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid seen : List Position} {queue : List BfsNode} {fuel : Nat}
    (hinv : BfsStateInvariant r allowHazard start seen queue) :
    BfsStateInvariant r allowHazard start
      (bfsAdvance r goals avoid allowHazard fuel seen queue).1
      (bfsAdvance r goals avoid allowHazard fuel seen queue).2 := by
  revert seen queue
  induction fuel with
  | zero =>
      intro seen queue hinv
      simpa [bfsAdvance] using hinv
  | succ fuel ih =>
      intro seen queue hinv
      cases queue with
      | nil =>
          simpa [bfsAdvance] using hinv
      | cons node rest =>
          simp [bfsAdvance]
          exact ih (bfsStateInvariant_step
            (r := r) (allowHazard := allowHazard) (start := start)
            (seen := seen) (avoid := avoid) (goals := goals)
            (node := node) (queue := rest) hinv)

/-- `bfsAdvance` 多步推进不会丢失已经由 `seen + queue` 覆盖的格子。 -/
theorem bfsAdvance_preserves_tileCovered
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid seen : List Position} {queue : List BfsNode}
    {fuel : Nat} {p : Position}
    (hinv : BfsStateInvariant r allowHazard start seen queue)
    (hcover : TileCovered seen queue p) :
    TileCovered
      (bfsAdvance r goals avoid allowHazard fuel seen queue).1
      (bfsAdvance r goals avoid allowHazard fuel seen queue).2
      p := by
  revert seen queue
  induction fuel with
  | zero =>
      intro seen queue hinv hcover
      simpa [bfsAdvance] using hcover
  | succ fuel ih =>
      intro seen queue hinv hcover
      cases queue with
      | nil =>
          simpa [bfsAdvance] using hcover
      | cons node rest =>
          simp [bfsAdvance]
          have hstepInv :
              BfsStateInvariant r allowHazard start
                (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
                (rest ++ expandNode r seen avoid goals allowHazard node) :=
            bfsStateInvariant_step
              (r := r) (allowHazard := allowHazard) (start := start)
              (seen := seen) (avoid := avoid) (goals := goals)
              (node := node) (queue := rest) hinv
          have hstepCover :
              TileCovered
                (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
                (rest ++ expandNode r seen avoid goals allowHazard node)
                p :=
            tileCovered_preserved_after_step_of_invariants
              (r := r) (allowHazard := allowHazard) (start := start)
              (seen := seen) (avoid := avoid) (goals := goals)
              (queue := rest) (node := node) (p := p)
              hinv.1 hinv.2 hcover
          exact ih hstepInv hstepCover

/--
若当前队首节点的一个合法邻居 `p` 是新 frontier，则处理当前节点并继续推进任意多步后，
`p` 仍然被最终的 `seen + queue` 覆盖。
-/
theorem bfsAdvance_covers_frontier_after_head
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid seen : List Position} {node : BfsNode} {queue : List BfsNode}
    {fuel : Nat} {p : Position}
    (hinv : BfsStateInvariant r allowHazard start seen (node :: queue))
    (hfrontier :
      Neighbor node.tile p ∧ walkableForMode r allowHazard p ∧
        (p ∈ goals ∨ p ∉ avoid)) :
    TileCovered
      (bfsAdvance r goals avoid allowHazard (fuel + 1) seen (node :: queue)).1
      (bfsAdvance r goals avoid allowHazard (fuel + 1) seen (node :: queue)).2
      p := by
  simp [bfsAdvance]
  have hstepInv :
      BfsStateInvariant r allowHazard start
        (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        (queue ++ expandNode r seen avoid goals allowHazard node) :=
    bfsStateInvariant_step
      (r := r) (allowHazard := allowHazard) (start := start)
      (seen := seen) (avoid := avoid) (goals := goals)
      (node := node) (queue := queue) hinv
  have hstepCover :
      TileCovered
        (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
        (queue ++ expandNode r seen avoid goals allowHazard node)
        p :=
    tileCovered_step_progress
      (r := r) (allowHazard := allowHazard) (start := start)
      (seen := seen) (avoid := avoid) (goals := goals)
      (queue := queue) (node := node) (p := p)
      hinv.1 hinv.2 (Or.inr hfrontier)
  exact bfsAdvance_preserves_tileCovered
    (r := r) (allowHazard := allowHazard) (start := start)
    (goals := goals) (avoid := avoid)
    (seen := seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard node))
    (queue := queue ++ expandNode r seen avoid goals allowHazard node)
    (fuel := fuel) (p := p)
    hstepInv hstepCover

/--
若队列中某个节点 `node` 的合法邻居 `p` 是 frontier，则 BFS 先处理它前面的队列前缀、
再处理该节点后，`p` 会被覆盖；之后继续推进任意多步也不会丢失该覆盖。
-/
theorem bfsAdvance_covers_frontier_of_queued_node
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid seen : List Position}
    {front suffix : List BfsNode} {node : BfsNode} {fuel : Nat} {p : Position}
    (hinv : BfsStateInvariant r allowHazard start seen (front ++ node :: suffix))
    (hfrontier :
      Neighbor node.tile p ∧ walkableForMode r allowHazard p ∧
        (p ∈ goals ∨ p ∉ avoid)) :
    TileCovered
      (bfsAdvance r goals avoid allowHazard (front.length + 1 + fuel)
        seen (front ++ node :: suffix)).1
      (bfsAdvance r goals avoid allowHazard (front.length + 1 + fuel)
        seen (front ++ node :: suffix)).2
      p := by
  induction front generalizing seen suffix with
  | nil =>
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (bfsAdvance_covers_frontier_after_head
          (r := r) (allowHazard := allowHazard) (start := start)
          (goals := goals) (avoid := avoid) (seen := seen)
          (node := node) (queue := suffix) (fuel := fuel) (p := p)
          hinv hfrontier)
  | cons head rest ih =>
      have hstepInv :
          BfsStateInvariant r allowHazard start
            (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
            (rest ++ node :: (suffix ++ expandNode r seen avoid goals allowHazard head)) := by
        have hraw :
            BfsStateInvariant r allowHazard start
              (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
              ((rest ++ node :: suffix) ++ expandNode r seen avoid goals allowHazard head) :=
          bfsStateInvariant_step
            (r := r) (allowHazard := allowHazard) (start := start)
            (seen := seen) (avoid := avoid) (goals := goals)
            (node := head) (queue := rest ++ node :: suffix)
            (by simpa [List.cons_append] using hinv)
        simpa [List.append_assoc] using hraw
      have htarget :
          TileCovered
            (bfsAdvance r goals avoid allowHazard (rest.length + 1 + fuel)
              (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
              (rest ++ node :: (suffix ++ expandNode r seen avoid goals allowHazard head))).1
            (bfsAdvance r goals avoid allowHazard (rest.length + 1 + fuel)
              (seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
              (rest ++ node :: (suffix ++ expandNode r seen avoid goals allowHazard head))).2
            p :=
        ih (seen := seen ++ bfsNodeTiles (expandNode r seen avoid goals allowHazard head))
          (suffix := suffix ++ expandNode r seen avoid goals allowHazard head)
          hstepInv
      simpa [bfsAdvance, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using htarget

/--
`bfsSearch` 的可靠性核心不变量：如果队列中每个节点都携带有效路径，那么
搜索返回的路径一定到达某个 goal，且这条路径有效。
-/
theorem bfsSearch_sound
    {r : RoomState} {start : Position} {goals avoid seen : List Position}
    {queue : List BfsNode}
    {fuel : Nat} {path : List Position}
    (hqueue : QueueSound r start queue)
    (hfind : bfsSearch r goals avoid false fuel seen queue = some path) :
    ∃ goal, goal ∈ goals ∧ ValidPath r start goal path := by
  revert seen queue path
  induction fuel with
  | zero =>
      intro seen queue path hqueue hfind
      simp [bfsSearch] at hfind
  | succ fuel ih =>
      intro seen queue path hqueue hfind
      cases queue with
      | nil =>
          simp [bfsSearch] at hfind
      | cons node rest =>
          simp [bfsSearch] at hfind
          by_cases hgoal : containsPos goals node.tile
          · simp [hgoal] at hfind
            subst path
            exact ⟨node.tile, by
              unfold containsPos at hgoal
              simpa [List.any_eq_true] using hgoal,
              hqueue node (by simp)⟩
          · simp [hgoal] at hfind
            have hrest : QueueSound r start rest := by
              intro n hn
              exact hqueue n (by simp [hn])
            have hchildren :
                QueueSound r start (expandNode r seen avoid goals false node) :=
              expandNode_queue_sound (hqueue node (by simp))
            have hnext :
                QueueSound r start
                  (rest ++ expandNode r seen avoid goals false node) :=
              queueSound_append hrest hchildren
            exact ih hnext hfind

/--
模式化 `bfsSearch` 可靠性：若队列中每个节点都携带当前 hazard 模式下的有效路径，
则搜索返回的路径一定到达某个 goal，且这条路径在该模式下有效。
-/
theorem bfsSearch_sound_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid seen : List Position} {queue : List BfsNode}
    {fuel : Nat} {path : List Position}
    (hqueue : QueueSoundForMode r allowHazard start queue)
    (hfind : bfsSearch r goals avoid allowHazard fuel seen queue = some path) :
    ∃ goal, goal ∈ goals ∧ ValidPathForMode r allowHazard start goal path := by
  revert seen queue path
  induction fuel with
  | zero =>
      intro seen queue path _hqueue hfind
      simp [bfsSearch] at hfind
  | succ fuel ih =>
      intro seen queue path hqueue hfind
      cases queue with
      | nil =>
          simp [bfsSearch] at hfind
      | cons node rest =>
          simp [bfsSearch] at hfind
          by_cases hgoal : containsPos goals node.tile
          · simp [hgoal] at hfind
            subst path
            exact ⟨node.tile, by
              unfold containsPos at hgoal
              simpa [List.any_eq_true] using hgoal,
              hqueue node (by simp)⟩
          · simp [hgoal] at hfind
            have hrest : QueueSoundForMode r allowHazard start rest := by
              intro n hn
              exact hqueue n (by simp [hn])
            have hchildren :
                QueueSoundForMode r allowHazard start
                  (expandNode r seen avoid goals allowHazard node) :=
              expandNode_queue_sound_mode (hqueue node (by simp))
            have hnext :
                QueueSoundForMode r allowHazard start
                  (rest ++ expandNode r seen avoid goals allowHazard node) :=
              queueSoundForMode_append hrest hchildren
            exact ih hnext hfind

/--
若某个目标节点已经在队列中，并且剩余 fuel 足够处理掉它前面的队列前缀，
则 `bfsSearch` 必然返回某条路径。这个引理刻画了 BFS 不会把已经入队的目标漏掉。
-/
theorem bfsSearch_finds_goal_after_prefix
    {r : RoomState} {allowHazard : Bool} {goals avoid seen : List Position}
    {front suffix : List BfsNode} {node : BfsNode} {fuel : Nat}
    (hgoal : containsPos goals node.tile = true)
    (hfuel : front.length < fuel) :
    ∃ path,
      bfsSearch r goals avoid allowHazard fuel seen (front ++ node :: suffix) = some path := by
  induction front generalizing seen fuel suffix with
  | nil =>
      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          exact ⟨node.path, by simp [bfsSearch, hgoal]⟩
  | cons head rest ih =>
      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          by_cases hheadGoal : containsPos goals head.tile = true
          · exact ⟨head.path, by simp [bfsSearch, hheadGoal]⟩
          ·
            have hheadGoalFalse : containsPos goals head.tile = false := by
              cases h : containsPos goals head.tile
              · rfl
              · exact False.elim (hheadGoal h)
            let children := expandNode r seen avoid goals allowHazard head
            let seen' := seen ++ bfsNodeTiles children
            have hfuelRest : rest.length < fuel := by
              simp at hfuel
              omega
            rcases ih (seen := seen') (fuel := fuel) (suffix := suffix ++ children)
                hfuelRest with
              ⟨path, hpath⟩
            refine ⟨path, ?_⟩
            simp [bfsSearch, hheadGoalFalse]
            simpa [List.append_assoc] using hpath

/--
`bfsSearch` 的无重复不变量：若队列中所有路径无重复且都包含在当前 `seen` 中，
那么搜索返回的路径也无重复。
-/
theorem bfsSearch_nodup
    {r : RoomState} {goals avoid seen : List Position}
    {queue : List BfsNode}
    {fuel : Nat} {path : List Position}
    (hnodup : QueueNoDupPaths queue)
    (hinseen : QueuePathsInSeen seen queue)
    (hfind : bfsSearch r goals avoid false fuel seen queue = some path) :
    path.Nodup := by
  revert seen queue path
  induction fuel with
  | zero =>
      intro seen queue path _hnodup _hinseen hfind
      simp [bfsSearch] at hfind
  | succ fuel ih =>
      intro seen queue path hnodup hinseen hfind
      cases queue with
      | nil =>
          simp [bfsSearch] at hfind
      | cons node rest =>
          simp [bfsSearch] at hfind
          by_cases hgoal : containsPos goals node.tile
          · simp [hgoal] at hfind
            subst path
            exact hnodup node (by simp)
          · simp [hgoal] at hfind
            have hnodeNoDup : NodeNoDup node := hnodup node (by simp)
            have hnodeInSeen : NodePathInSeen seen node := hinseen node (by simp)
            have hrestNoDup : QueueNoDupPaths rest := by
              intro n hn
              exact hnodup n (by simp [hn])
            have hchildrenNoDup :
                QueueNoDupPaths (expandNode r seen avoid goals false node) :=
              expandNode_queue_nodup hnodeNoDup hnodeInSeen
            have hnextNoDup :
                QueueNoDupPaths
                  (rest ++ expandNode r seen avoid goals false node) :=
              queueNoDup_append hrestNoDup hchildrenNoDup
            have hrestSeen :
                QueuePathsInSeen
                  (seen ++ bfsNodeTiles (expandNode r seen avoid goals false node))
                  rest :=
              queuePathsInSeen_extend
                (by
                  intro n hn
                  exact hinseen n (by simp [hn]))
            have hchildrenSeen :
                QueuePathsInSeen
                  (seen ++ bfsNodeTiles (expandNode r seen avoid goals false node))
                  (expandNode r seen avoid goals false node) :=
              expandNode_queue_paths_in_next_seen hnodeInSeen
            have hnextSeen :
                QueuePathsInSeen
                  (seen ++ bfsNodeTiles (expandNode r seen avoid goals false node))
                  (rest ++ expandNode r seen avoid goals false node) :=
              queuePathsInSeen_append hrestSeen hchildrenSeen
            exact ih hnextNoDup hnextSeen hfind

/--
`bfsSearch` 保持 `avoid` 例外不变量：返回路径中的非起点、非目标节点不在 `avoid` 中。
-/
theorem bfsSearch_avoids_except_start_goals
    {r : RoomState} {start : Position} {goals avoid seen : List Position}
    {queue : List BfsNode}
    {fuel : Nat} {path : List Position}
    (havoid : QueueAvoidsExceptStartGoals start goals avoid queue)
    (hfind : bfsSearch r goals avoid false fuel seen queue = some path) :
    ∀ p, p ∈ path → p ≠ start → p ∉ goals → p ∉ avoid := by
  revert seen queue path
  induction fuel with
  | zero =>
      intro seen queue path _havoid hfind
      simp [bfsSearch] at hfind
  | succ fuel ih =>
      intro seen queue path havoid hfind
      cases queue with
      | nil =>
          simp [bfsSearch] at hfind
      | cons node rest =>
          simp [bfsSearch] at hfind
          by_cases hgoal : containsPos goals node.tile
          · simp [hgoal] at hfind
            subst path
            exact havoid node (by simp)
          · simp [hgoal] at hfind
            have hnodeAvoid :
                NodeAvoidsExceptStartGoals start goals avoid node :=
              havoid node (by simp)
            have hrestAvoid :
                QueueAvoidsExceptStartGoals start goals avoid rest := by
              intro n hn
              exact havoid n (by simp [hn])
            have hchildrenAvoid :
                QueueAvoidsExceptStartGoals start goals avoid
                  (expandNode r seen avoid goals false node) :=
              expandNode_queue_avoids_except_start_goals hnodeAvoid
            have hnextAvoid :
                QueueAvoidsExceptStartGoals start goals avoid
                  (rest ++ expandNode r seen avoid goals false node) :=
              queueAvoids_append hrestAvoid hchildrenAvoid
            exact ih hnextAvoid hfind

/--
模式化 `bfsSearch` 保持 `avoid` 例外不变量：该性质与 hazard 模式无关。
-/
theorem bfsSearch_avoids_except_start_goals_mode
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid seen : List Position} {queue : List BfsNode}
    {fuel : Nat} {path : List Position}
    (havoid : QueueAvoidsExceptStartGoals start goals avoid queue)
    (hfind : bfsSearch r goals avoid allowHazard fuel seen queue = some path) :
    ∀ p, p ∈ path → p ≠ start → p ∉ goals → p ∉ avoid := by
  revert seen queue path
  induction fuel with
  | zero =>
      intro seen queue path _havoid hfind
      simp [bfsSearch] at hfind
  | succ fuel ih =>
      intro seen queue path havoid hfind
      cases queue with
      | nil =>
          simp [bfsSearch] at hfind
      | cons node rest =>
          simp [bfsSearch] at hfind
          by_cases hgoal : containsPos goals node.tile
          · simp [hgoal] at hfind
            subst path
            exact havoid node (by simp)
          · simp [hgoal] at hfind
            have hnodeAvoid :
                NodeAvoidsExceptStartGoals start goals avoid node :=
              havoid node (by simp)
            have hrestAvoid :
                QueueAvoidsExceptStartGoals start goals avoid rest := by
              intro n hn
              exact havoid n (by simp [hn])
            have hchildrenAvoid :
                QueueAvoidsExceptStartGoals start goals avoid
                  (expandNode r seen avoid goals allowHazard node) :=
              expandNode_queue_avoids_except_start_goals_mode hnodeAvoid
            have hnextAvoid :
                QueueAvoidsExceptStartGoals start goals avoid
                  (rest ++ expandNode r seen avoid goals allowHazard node) :=
              queueAvoids_append hrestAvoid hchildrenAvoid
            exact ih hnextAvoid hfind

/-- 单点路径 `[start]` 是从 `start` 到 `start` 的有效路径。 -/
theorem singleton_validPath
    {r : RoomState} {start : Position}
    (hstart : walkable r start) :
    ValidPath r start start [start] := by
  unfold ValidPath PathEndpoints PathWalkable
  simp [PathChain, hstart]

/-- 有效路径上的每个格子都属于有限地图枚举 `allPositions`。 -/
theorem validPath_mem_allPositions
    {r : RoomState} {start goal p : Position} {path : List Position}
    (hvalid : ValidPath r start goal path)
    (hp : p ∈ path) :
    p ∈ allPositions := by
  exact inBounds_mem_allPositions (walkable_in_bounds (hvalid.2.1 p hp))

/--
实际 `bfsPath` 的 soundness：若起点可走且 BFS 返回路径，则它到达某个 goal，
并且返回路径是有效路径。
-/
theorem bfsPath_sound
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    ∃ goal, goal ∈ goals ∧ ValidPath r start goal path := by
  unfold bfsPath at hfind
  by_cases hempty : goals.isEmpty
  · simp [hempty] at hfind
  · simp [hempty] at hfind
    by_cases hstartGoal : containsPos goals start
    · simp [hstartGoal] at hfind
      subst path
      exact ⟨start, by
        unfold containsPos at hstartGoal
        simpa [List.any_eq_true] using hstartGoal,
        singleton_validPath hstart⟩
    · simp [hstartGoal] at hfind
      exact bfsSearch_sound
        (by
          intro node hmem
          have hnode : node = initialBfsNode start := by
            simpa using hmem
          rw [hnode]
          exact initialBfsNode_sound hstart)
        hfind

/-- `bfs_sound`：单目标 BFS 返回的路径一定是从起点到该目标的有效路径。 -/
theorem bfs_sound
    {r : RoomState} {start goal : Position} {avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start [goal] avoid false = some path) :
    ValidPath r start goal path := by
  rcases bfsPath_sound hstart hfind with ⟨g, hg, hvalid⟩
  simp at hg
  subst g
  exact hvalid

/-- `bfs_path_nodup`：实际 BFS 返回的路径不含重复节点，不会绕圈。 -/
theorem bfs_path_nodup
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hfind : bfsPath r start goals avoid false = some path) :
    path.Nodup := by
  unfold bfsPath at hfind
  by_cases hempty : goals.isEmpty
  · simp [hempty] at hfind
  · simp [hempty] at hfind
    by_cases hstartGoal : containsPos goals start
    · simp [hstartGoal] at hfind
      subst path
      simp
    · simp [hstartGoal] at hfind
      exact bfsSearch_nodup
        (by
          intro node hmem
          have hnode : node = initialBfsNode start := by
            simpa using hmem
          rw [hnode]
          exact initialBfsNode_nodup start)
        (by
          intro node hmem
          have hnode : node = initialBfsNode start := by
            simpa using hmem
          rw [hnode]
          exact initialBfsNode_path_in_seen start)
        hfind

/-- `bfs_path_nonempty`：实际 BFS 返回的路径非空。 -/
theorem bfs_path_nonempty
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    path ≠ [] := by
  rcases bfsPath_sound hstart hfind with ⟨goal, _hgoal, hvalid⟩
  intro hnil
  unfold ValidPath PathEndpoints at hvalid
  rw [hnil] at hvalid
  simp at hvalid

/-- `bfs_head`：实际 BFS 返回路径的第一个节点是起点。 -/
theorem bfs_head
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    path.head? = some start := by
  rcases bfsPath_sound hstart hfind with ⟨_goal, _hgoal, hvalid⟩
  exact hvalid.1.1

/-- `bfs_last_mem_goals`：实际 BFS 返回路径的最后一个节点属于目标集合。 -/
theorem bfs_last_mem_goals
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    ∃ goal, goal ∈ goals ∧ path.getLast? = some goal := by
  rcases bfsPath_sound hstart hfind with ⟨goal, hgoal, hvalid⟩
  exact ⟨goal, hgoal, hvalid.1.2⟩

/-- `bfs_path_adjacent`：实际 BFS 返回路径中的连续节点都是正交相邻。 -/
theorem bfs_path_adjacent
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    PathChain path := by
  rcases bfsPath_sound hstart hfind with ⟨_goal, _hgoal, hvalid⟩
  exact hvalid.2.2

/-- `bfs_path_in_bounds`：实际 BFS 返回路径上的所有格子都在地图边界内。 -/
theorem bfs_path_in_bounds
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    ∀ p, p ∈ path → InBounds p := by
  rcases bfsPath_sound hstart hfind with ⟨_goal, _hgoal, hvalid⟩
  intro p hp
  exact walkable_in_bounds (hvalid.2.1 p hp)

/-- `bfs_path_not_blocking`：实际 BFS 返回路径不会穿过阻塞格。 -/
theorem bfs_path_not_blocking
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    ∀ p, p ∈ path → isBlocking r p = false := by
  rcases bfsPath_sound hstart hfind with ⟨_goal, _hgoal, hvalid⟩
  intro p hp
  exact walkable_not_blocking (hvalid.2.1 p hp)

/-- `bfs_path_avoids_hazard`：`allowHazard = false` 时实际 BFS 返回路径不经过危险格。 -/
theorem bfs_path_avoids_hazard
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hstart : walkable r start)
    (hfind : bfsPath r start goals avoid false = some path) :
    ∀ p, p ∈ path → isHazardTile r p = false := by
  rcases bfsPath_sound hstart hfind with ⟨_goal, _hgoal, hvalid⟩
  intro p hp
  exact walkable_not_hazard (hvalid.2.1 p hp)

/--
`bfs_internal_avoids_monsters`：把 `avoid` 视为怪物危险区列表时，BFS 返回路径中的
非起点、非目标节点不会进入该禁入集合。目标格允许例外，最终一步安全性由 shield 检查。
-/
theorem bfs_internal_avoids_monsters
    {r : RoomState} {start : Position} {goals avoid path : List Position}
    (hfind : bfsPath r start goals avoid false = some path) :
    ∀ p, p ∈ path → p ≠ start → p ∉ goals → p ∉ avoid := by
  unfold bfsPath at hfind
  by_cases hempty : goals.isEmpty
  · simp [hempty] at hfind
  · simp [hempty] at hfind
    by_cases hstartGoal : containsPos goals start
    · simp [hstartGoal] at hfind
      subst path
      intro p hp hne _hnotGoal
      simp at hp
      subst p
      exfalso
      exact hne rfl
    · simp [hstartGoal] at hfind
      exact bfsSearch_avoids_except_start_goals
        (by
          intro node hmem
          have hnode : node = initialBfsNode start := by
            simpa using hmem
          rw [hnode]
          exact initialBfsNode_avoids_except_start_goals start goals avoid)
        hfind

/-- BFS 约束路径：有效路径还必须满足当前 hazard 模式和 `avoid` 例外规则。 -/
def BfsConstrainedPath
    (r : RoomState) (allowHazard : Bool)
    (start goal : Position) (goals avoid path : List Position) : Prop :=
  ValidPathForMode r allowHazard start goal path ∧
    ∀ p, p ∈ path → p ≠ start → p ∉ goals → p ∉ avoid

/-- BFS 约束可达性：存在一条满足当前 `allowHazard/avoid/goals` 规则的有效路径。 -/
def BfsConstrainedReachable
    (r : RoomState) (allowHazard : Bool)
    (start goal : Position) (goals avoid : List Position) : Prop :=
  ∃ path, BfsConstrainedPath r allowHazard start goal goals avoid path

/-- BFS 约束简单可达性：存在一条无重复的约束路径。 -/
def BfsConstrainedSimpleReachable
    (r : RoomState) (allowHazard : Bool)
    (start goal : Position) (goals avoid : List Position) : Prop :=
  ∃ path, BfsConstrainedPath r allowHazard start goal goals avoid path ∧ path.Nodup

/--
无重复的 BFS 约束路径可以接到初始 trace 覆盖定理：
若存在一条从 `start` 到 `target` 的无重复约束路径，则 trace BFS 推进有限步后覆盖目标。
-/
theorem constrainedPath_nodup_initial_eventually_traceCovered
    {r : RoomState} {allowHazard : Bool} {goals avoid : List Position}
    {start target : Position} {path : List Position}
    (hpath : BfsConstrainedPath r allowHazard start target goals avoid path)
    (hnodup : path.Nodup) :
    ∃ fuel,
      TraceCovered
        (bfsAdvanceTrace r goals avoid allowHazard fuel [] [start] [initialBfsNode start]).1
        (bfsAdvanceTrace r goals avoid allowHazard fuel [] [start] [initialBfsNode start]).2.2
        target := by
  rcases hpath with ⟨hvalid, havoid⟩
  rcases hvalid with ⟨hend, hwalks, hchain⟩
  have hsuffix :
      ConstrainedSuffix r allowHazard goals avoid start path :=
    constrainedSuffix_of_chain
      (path := path) (start := start)
      hend.1 hnodup hwalks hchain havoid
  exact constrainedSuffix_initial_eventually_traceCovered
    (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
    (start := start) (target := target) (path := path)
    hsuffix hend.2

/-- 无环约束可达的目标最终会被初始 trace BFS 覆盖。 -/
theorem constrainedSimpleReachable_initial_eventually_traceCovered
    {r : RoomState} {allowHazard : Bool} {goals avoid : List Position}
    {start target : Position}
    (hreachable : BfsConstrainedSimpleReachable r allowHazard start target goals avoid) :
    ∃ fuel,
      TraceCovered
        (bfsAdvanceTrace r goals avoid allowHazard fuel [] [start] [initialBfsNode start]).1
        (bfsAdvanceTrace r goals avoid allowHazard fuel [] [start] [initialBfsNode start]).2.2
        target := by
  rcases hreachable with ⟨path, hpath, hnodup⟩
  exact constrainedPath_nodup_initial_eventually_traceCovered
    (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
    (start := start) (target := target) (path := path)
    hpath hnodup

/-- `bfsAdvanceTrace` 的 seen/queue 投影与 `bfsAdvance` 完全一致。 -/
theorem bfsAdvanceTrace_project
    {r : RoomState} {allowHazard : Bool} {goals avoid processed seen : List Position}
    {queue : List BfsNode} {fuel : Nat} :
    ((bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.1,
      (bfsAdvanceTrace r goals avoid allowHazard fuel processed seen queue).2.2) =
    bfsAdvance r goals avoid allowHazard fuel seen queue := by
  revert processed seen queue
  induction fuel with
  | zero =>
      intro processed seen queue
      simp [bfsAdvanceTrace, bfsAdvance]
  | succ fuel ih =>
      intro processed seen queue
      cases queue with
      | nil =>
          simp [bfsAdvanceTrace, bfsAdvance]
      | cons node rest =>
          simp [bfsAdvanceTrace, bfsAdvance]
          exact ih

/-- 如果某个 goal tile 已在当前 BFS 队列中，则 `bfsSearch` 用足够 fuel 会返回。 -/
theorem bfsSearch_finds_goal_in_queue
    {r : RoomState} {allowHazard : Bool} {goals avoid seen : List Position}
    {queue : List BfsNode} {goal : Position}
    (hgoal : goal ∈ goals)
    (hqueued : ∃ node, node ∈ queue ∧ node.tile = goal) :
    ∃ path, bfsSearch r goals avoid allowHazard (queue.length + 1) seen queue = some path := by
  rcases hqueued with ⟨node, hmem, htile⟩
  rcases list_mem_split hmem with ⟨front, suffix, hsplit⟩
  have hgoalBool : containsPos goals node.tile = true := by
    rw [htile]
    exact (containsPos_true_iff goals goal).2 hgoal
  rcases bfsSearch_finds_goal_after_prefix
      (r := r) (allowHazard := allowHazard) (goals := goals) (avoid := avoid)
      (seen := seen) (front := front) (suffix := suffix) (node := node)
      (fuel := queue.length + 1)
      hgoalBool
      (by
        rw [hsplit]
        simp
        omega) with
    ⟨path, hpath⟩
  refine ⟨path, ?_⟩
  simpa [hsplit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpath

/--
约束路径的第一步会被初始 BFS 展开发现：如果一条满足当前模式的路径以
`start :: next :: rest` 开头，那么初始节点展开之后，`next` 已经被新的
`seen` 覆盖；若它不是旧 `seen` 中的起点，则它作为 child 进入队列。
-/
theorem constrained_path_first_frontier_covered
    {r : RoomState} {allowHazard : Bool}
    {start next goal : Position} {goals avoid rest : List Position}
    (hpath : BfsConstrainedPath r allowHazard start goal goals avoid
      (start :: next :: rest)) :
    next ∈ [start] ++
        bfsNodeTiles (expandNode r [start] avoid goals allowHazard (initialBfsNode start)) ∧
      (next ∈ [start] ∨
        ∃ child,
          child ∈ expandNode r [start] avoid goals allowHazard (initialBfsNode start) ∧
            child.tile = next) := by
  rcases hpath with ⟨hvalid, havoid⟩
  rcases hvalid with ⟨_hend, hwalks, hchain⟩
  have hneighbor : Neighbor start next := by
    simpa [PathChain] using hchain.1
  have hneighMem : next ∈ gridNeighbors (initialBfsNode start).tile := by
    simpa [initialBfsNode] using neighbor_mem_gridNeighbors hneighbor
  have hwalkBool : walkableBool r next allowHazard = true :=
    walkableBool_complete_mode (hwalks next (by simp))
  have hallowed : allowedByAvoid avoid goals next = true := by
    apply allowedByAvoid_of_goal_or_not_avoid
    by_cases hgoal : next ∈ goals
    · exact Or.inl hgoal
    · right
      exact havoid next (by simp)
        (by
          intro hnextStart
          exact neighbor_ne hneighbor hnextStart.symm)
        hgoal
  exact expandNode_frontier_covered
    (r := r) (allowHazard := allowHazard) (seen := [start])
    (avoid := avoid) (goals := goals) (node := initialBfsNode start)
    (nxt := next) hneighMem hwalkBool hallowed

/--
约束路径的第二步会在有限次 BFS 推进后被覆盖：若路径以
`start :: mid :: next :: rest` 开头，则从初始状态推进若干步后，`next`
出现在 `seen + queue` 覆盖中。
-/
theorem constrained_path_second_frontier_eventually_covered
    {r : RoomState} {allowHazard : Bool}
    {start mid next goal : Position} {goals avoid rest : List Position}
    (hpath : BfsConstrainedPath r allowHazard start goal goals avoid
      (start :: mid :: next :: rest)) :
    ∃ fuel,
      TileCovered
        (bfsAdvance r goals avoid allowHazard fuel [start] [initialBfsNode start]).1
        (bfsAdvance r goals avoid allowHazard fuel [start] [initialBfsNode start]).2
        next := by
  have hpathOrig := hpath
  rcases hpath with ⟨hvalid, havoid⟩
  rcases hvalid with ⟨_hend, hwalks, hchain⟩
  have hstartMid : Neighbor start mid := by
    simpa [PathChain] using hchain.1
  have hmidNext : Neighbor mid next := by
    simpa [PathChain] using hchain.2.1
  by_cases hnextStart : next = start
  · subst next
    exact ⟨0, initial_tileCovered_start start⟩
  have hfirst :
      mid ∈ [start] ++
          bfsNodeTiles (expandNode r [start] avoid goals allowHazard (initialBfsNode start)) ∧
        (mid ∈ [start] ∨
          ∃ child,
            child ∈ expandNode r [start] avoid goals allowHazard (initialBfsNode start) ∧
              child.tile = mid) :=
    constrained_path_first_frontier_covered
      (r := r) (allowHazard := allowHazard) (start := start)
      (next := mid) (goal := goal) (goals := goals) (avoid := avoid)
      (rest := next :: rest) hpathOrig
  have hmidNotStart : mid ≠ start := by
    intro h
    exact neighbor_ne hstartMid h.symm
  rcases hfirst.2 with hmidSeen | hmidChild
  · simp at hmidSeen
    exact False.elim (hmidNotStart hmidSeen)
  · rcases hmidChild with ⟨child, hchildMem, hchildTile⟩
    rcases list_mem_split hchildMem with ⟨front, suffix, hsplit⟩
    have hstepInv :
        BfsStateInvariant r allowHazard start
          ([start] ++ bfsNodeTiles (expandNode r [start] avoid goals allowHazard
            (initialBfsNode start)))
          (front ++ child :: suffix) := by
      have hraw :
          BfsStateInvariant r allowHazard start
            ([start] ++ bfsNodeTiles (expandNode r [start] avoid goals allowHazard
              (initialBfsNode start)))
            ([] ++ expandNode r [start] avoid goals allowHazard (initialBfsNode start)) :=
        bfsStateInvariant_step
          (r := r) (allowHazard := allowHazard) (start := start)
          (seen := [start]) (avoid := avoid) (goals := goals)
          (node := initialBfsNode start) (queue := [])
          (initialBfsStateInvariant
            (r := r) (allowHazard := allowHazard) (start := start)
            (hwalks start (by simp)))
      simpa [hsplit] using hraw
    have hfrontier :
        Neighbor child.tile next ∧ walkableForMode r allowHazard next ∧
          (next ∈ goals ∨ next ∉ avoid) := by
      constructor
      · simpa [hchildTile] using hmidNext
      constructor
      · exact hwalks next (by simp)
      · by_cases hgoal : next ∈ goals
        · exact Or.inl hgoal
        · right
          exact havoid next (by simp)
            hnextStart
            hgoal
    have hcovered :=
      bfsAdvance_covers_frontier_of_queued_node
        (r := r) (allowHazard := allowHazard) (start := start)
        (goals := goals) (avoid := avoid)
        (seen := [start] ++ bfsNodeTiles (expandNode r [start] avoid goals allowHazard
          (initialBfsNode start)))
        (front := front) (suffix := suffix) (node := child) (fuel := 0)
        (p := next) hstepInv hfrontier
    refine ⟨front.length + 2, ?_⟩
    simpa [bfsAdvance, hsplit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hcovered

/--
`bfsPath_constrained_sound`：任意 hazard/avoid 模式下，只要实际 BFS 返回路径，
该路径就满足同一模式下的可行走约束和 `avoid` 例外规则。
-/
theorem bfsPath_constrained_sound
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals avoid path : List Position}
    (hstart : walkableForMode r allowHazard start)
    (hfind : bfsPath r start goals avoid allowHazard = some path) :
    ∃ goal, goal ∈ goals ∧
      BfsConstrainedPath r allowHazard start goal goals avoid path := by
  unfold bfsPath at hfind
  by_cases hempty : goals.isEmpty
  · simp [hempty] at hfind
  · simp [hempty] at hfind
    by_cases hstartGoal : containsPos goals start
    · simp [hstartGoal] at hfind
      subst path
      refine ⟨start, ?_, ?_⟩
      · exact (containsPos_true_iff goals start).1 hstartGoal
      · constructor
        · exact initialBfsNode_sound_mode hstart
        · intro p hp hne _hnotGoal
          simp at hp
          subst p
          exfalso
          exact hne rfl
    · simp [hstartGoal] at hfind
      rcases bfsSearch_sound_mode
          (r := r) (allowHazard := allowHazard) (start := start)
          (goals := goals) (avoid := avoid) (seen := [start])
          (queue := [initialBfsNode start]) (fuel := 80) (path := path)
          (by
            intro node hmem
            have hnode : node = initialBfsNode start := by
              simpa using hmem
            rw [hnode]
            exact initialBfsNode_sound_mode hstart)
          hfind with
        ⟨goal, hgoal, hvalid⟩
      refine ⟨goal, hgoal, ?_⟩
      constructor
      · exact hvalid
      · exact bfsSearch_avoids_except_start_goals_mode
          (start := start) (goals := goals) (avoid := avoid)
          (seen := [start]) (queue := [initialBfsNode start]) (fuel := 80)
          (path := path)
          (by
            intro node hmem
            have hnode : node = initialBfsNode start := by
              simpa using hmem
            rw [hnode]
            exact initialBfsNode_avoids_except_start_goals start goals avoid)
          hfind

/--
`bfs_none_of_unreachable`：若没有任何目标格从起点可达，则实际 BFS 不可能返回路径，
因此结果只能是 `none`。这是 `bfs_none_iff_unreachable` 的 soundness 方向。
-/
theorem bfs_none_of_unreachable
    {r : RoomState} {start : Position} {goals avoid : List Position}
    (hstart : walkable r start)
    (hunreachable : ∀ goal, goal ∈ goals → ¬ Reachable r start goal) :
    bfsPath r start goals avoid false = none := by
  cases hres : bfsPath r start goals avoid false with
  | none => rfl
  | some path =>
      rcases bfsPath_sound hstart hres with ⟨goal, hgoal, hvalid⟩
      exfalso
      exact hunreachable goal hgoal ⟨path, hvalid⟩

/--
`bfs_none_of_constrained_unreachable`：若在当前 hazard/avoid 模式下没有任何目标满足
BFS 约束可达性，则实际 BFS 返回 `none`。
-/
theorem bfs_none_of_constrained_unreachable
    {r : RoomState} {allowHazard : Bool} {start : Position} {goals avoid : List Position}
    (hstart : walkableForMode r allowHazard start)
    (hunreachable :
      ∀ goal, goal ∈ goals →
        ¬ BfsConstrainedReachable r allowHazard start goal goals avoid) :
    bfsPath r start goals avoid allowHazard = none := by
  cases hres : bfsPath r start goals avoid allowHazard with
  | none => rfl
  | some path =>
      rcases bfsPath_constrained_sound hstart hres with ⟨goal, hgoal, hconstrained⟩
      exfalso
      exact hunreachable goal hgoal ⟨path, hconstrained⟩

/-- 一组格子都是从 `start` 可达的。 -/
def ReachableSetSound (r : RoomState) (start : Position) (xs : List Position) : Prop :=
  ∀ p, p ∈ xs → Reachable r start p

/-- 两个可靠可达集合拼接后仍然可靠。 -/
theorem reachableSet_append
    {r : RoomState} {start : Position} {xs ys : List Position}
    (hxs : ReachableSetSound r start xs)
    (hys : ReachableSetSound r start ys) :
    ReachableSetSound r start (xs ++ ys) := by
  intro p hp
  rw [List.mem_append] at hp
  cases hp with
  | inl hx => exact hxs p hx
  | inr hy => exact hys p hy

/-- `reachableTilesSearch` 从一个可达格子展开出的新邻格仍然可达。 -/
theorem reachableTiles_children_sound
    {r : RoomState} {start current : Position} {seen avoid : List Position}
    (hcurrent : Reachable r start current) :
    ReachableSetSound r start
      ((gridNeighbors current).filter (fun nxt =>
        !containsPos seen nxt && !containsPos avoid nxt && walkableBool r nxt false)) := by
  intro nxt hnxt
  simp only [List.mem_filter] at hnxt
  rcases hnxt with ⟨hneighMem, hfilter⟩
  simp at hfilter
  rcases hcurrent with ⟨path, hvalid⟩
  exact ⟨path ++ [nxt],
    validPath_extend hvalid (gridNeighbors_neighbor hneighMem) (walkableBool_sound hfilter.2)⟩

/-- `reachableTilesSearch` 的可靠性不变量：返回集合里的每个格子都确实可达。 -/
theorem reachableTilesSearch_sound
    {r : RoomState} {start : Position} {avoid seen queue : List Position} {fuel : Nat}
    (hseen : ReachableSetSound r start seen)
    (hqueue : ReachableSetSound r start queue) :
    ReachableSetSound r start (reachableTilesSearch r avoid fuel seen queue) := by
  revert seen queue
  induction fuel with
  | zero =>
      intro seen queue hseen _hqueue
      simpa [reachableTilesSearch] using hseen
  | succ fuel ih =>
      intro seen queue hseen hqueue
      cases queue with
      | nil =>
          simpa [reachableTilesSearch] using hseen
      | cons current rest =>
          simp [reachableTilesSearch]
          have hcurrent : Reachable r start current := hqueue current (by simp)
          have hrest : ReachableSetSound r start rest := by
            intro p hp
            exact hqueue p (by simp [hp])
          have hchildren :=
            reachableTiles_children_sound
              (r := r) (start := start) (current := current) (seen := seen) (avoid := avoid)
              hcurrent
          exact ih (reachableSet_append hseen hchildren) (reachableSet_append hrest hchildren)

/--
`reachable_tiles_sound`：`reachableTiles` 返回的每个格子都确实存在一条合法可达路径。
-/
theorem reachable_tiles_sound
    {r : RoomState} {start p : Position}
    (hstart : walkable r start)
    (hp : p ∈ reachableTiles r start []) :
    Reachable r start p := by
  exact reachableTilesSearch_sound
    (r := r) (start := start) (avoid := []) (seen := [start]) (queue := [start]) (fuel := 80)
    (by
      intro q hq
      simp at hq
      subst q
      exact ⟨[start], singleton_validPath hstart⟩)
    (by
      intro q hq
      simp at hq
      subst q
      exact ⟨[start], singleton_validPath hstart⟩)
    p hp

/-!
  ## BFS 完备性与最短性的正确陈述

  `bfsPath` 的运行语义包含 `avoid` 参数，因此不能把完备性/最短性直接陈述成普通
  `Reachable` / `ValidPath`。普通可达路径可能经过 `avoid` 中的禁入格，而 BFS 会
  拒绝这些内部节点。下面先给出一个闭合反例，再把后续规格改成“满足 BFS 约束的
  可达路径”。
-/

/-- 只有 `(0,0) -> (1,0) -> (2,0)` 三个格子打开的走廊反例房间。 -/
def corridorOpenForBfsCounterexample (p : Position) : Bool :=
  p == (0, 0) || p == (1, 0) || p == (2, 0)

/-- 走廊反例房间：除三个走廊格子外，其余格子都是墙。 -/
def corridorRoomForBfsCounterexample : RoomState :=
  { (default : RoomState) with
    walls := allPositions.filter (fun p => !corridorOpenForBfsCounterexample p)
    traps := []
    monsters := []
    chests := []
    npcs := []
    dynamicObjects := []
    defaultSpawn := (0, 0) }

theorem corridor_walkable_00 : walkable corridorRoomForBfsCounterexample (0, 0) := by
  unfold walkable walkableWithHazard
  refine ⟨?_, ?_, ?_⟩
  · unfold InBounds
    omega
  · native_decide
  · intro _
    native_decide

theorem corridor_walkable_10 : walkable corridorRoomForBfsCounterexample (1, 0) := by
  unfold walkable walkableWithHazard
  refine ⟨?_, ?_, ?_⟩
  · unfold InBounds
    omega
  · native_decide
  · intro _
    native_decide

theorem corridor_walkable_20 : walkable corridorRoomForBfsCounterexample (2, 0) := by
  unfold walkable walkableWithHazard
  refine ⟨?_, ?_, ?_⟩
  · unfold InBounds
    omega
  · native_decide
  · intro _
    native_decide

theorem corridor_neighbor_00_10 : Neighbor (0, 0) (1, 0) := by
  right
  constructor <;> omega

theorem corridor_neighbor_10_20 : Neighbor (1, 0) (2, 0) := by
  right
  constructor <;> omega

/-- 普通 `Reachable` 不知道 `avoid`，所以目标在该走廊中是可达的。 -/
theorem bfs_complete_unconstrained_reachable_counterexample :
    Reachable corridorRoomForBfsCounterexample (0, 0) (2, 0) := by
  refine ⟨[(0, 0), (1, 0), (2, 0)], ?_⟩
  unfold ValidPath PathEndpoints PathWalkable
  constructor
  · simp
  constructor
  · intro p hp
    simp at hp
    rcases hp with hp | hp | hp
    · subst p
      exact corridor_walkable_00
    · subst p
      exact corridor_walkable_10
    · subst p
      exact corridor_walkable_20
  · simp [PathChain, corridor_neighbor_00_10, corridor_neighbor_10_20]

/--
但若把唯一中间格 `(1,0)` 放进 `avoid`，实际 BFS 会返回 `none`。
这说明无约束的 `Reachable -> bfsPath returns some` 命题不成立。
-/
theorem bfs_complete_unconstrained_none_counterexample :
    bfsPath corridorRoomForBfsCounterexample (0, 0) [(2, 0)] [(1, 0)] false = none := by
  native_decide

/-- `bfs_complete` 的基例：目标就是起点时，实际 BFS 立即返回单点路径。 -/
theorem bfs_complete_start_goal
    {r : RoomState} {allowHazard : Bool} {start : Position} {avoid : List Position} :
    ∃ path, bfsPath r start [start] avoid allowHazard = some path := by
  exact ⟨[start], by simp [bfsPath, containsPos]⟩

/--
`bfs_complete` 的一步情形：目标是起点的可行邻格时，实际 BFS 第一轮展开后
一定能返回某条路径。目标格允许作为 `avoid` 的例外。
-/
theorem bfs_complete_one_step
    {r : RoomState} {allowHazard : Bool} {start goal : Position} {avoid : List Position}
    (hneighbor : goal ∈ gridNeighbors start)
    (hwalk : walkableBool r goal allowHazard = true)
    (hnotStart : goal ≠ start) :
    ∃ path, bfsPath r start [goal] avoid allowHazard = some path := by
  unfold bfsPath
  have hstartGoal : containsPos [goal] start = false := by
    unfold containsPos
    simp [hnotStart]
  simp [hstartGoal]
  unfold bfsSearch
  have hinitNotGoal : containsPos [goal] (initialBfsNode start).tile = false := by
    unfold initialBfsNode
    exact hstartGoal
  simp [hinitNotGoal]
  have hseen : containsPos [start] goal = false := by
    unfold containsPos
    simp [show ¬ start = goal by
      intro h
      exact hnotStart h.symm]
  have hallowed : allowedByAvoid avoid [goal] goal = true := by
    unfold allowedByAvoid containsPos
    simp
  have hchild :
      { tile := goal, path := [start] ++ [goal] } ∈
        expandNode r [start] avoid [goal] allowHazard (initialBfsNode start) :=
    expandNode_contains_allowed_neighbor
      (node := initialBfsNode start) (nxt := goal)
      (by simpa [initialBfsNode] using hneighbor)
      hseen hwalk hallowed
  rcases list_mem_split hchild with ⟨front, suffix, hsplit⟩
  have hgoalNode :
      containsPos [goal] ({ tile := goal, path := [start] ++ [goal] } : BfsNode).tile = true := by
    unfold containsPos
    simp
  rcases bfsSearch_finds_goal_after_prefix
      (r := r) (allowHazard := allowHazard) (goals := [goal]) (avoid := avoid)
      (seen := [start] ++ bfsNodeTiles (expandNode r [start] avoid [goal] allowHazard
        (initialBfsNode start)))
      (front := front) (suffix := suffix)
      (node := ({ tile := goal, path := [start] ++ [goal] } : BfsNode))
      (fuel := 79)
      hgoalNode
      (by
        have hfrontLen :
            front.length <
              (expandNode r [start] avoid [goal] allowHazard
                (initialBfsNode start)).length + 1 := by
          have hprefixLen :
              front.length + 1 ≤
                (expandNode r [start] avoid [goal] allowHazard
                  (initialBfsNode start)).length := by
            rw [hsplit]
            simp
          omega
        have hchildrenBound :
            (expandNode r [start] avoid [goal] allowHazard
              (initialBfsNode start)).length ≤ 4 := by
          unfold expandNode gridNeighbors initialBfsNode
          by_cases hy : start.2 = 0 <;> by_cases hx : start.1 = 0 <;>
            exact Nat.le_trans (List.length_filterMap_le _ _) (by simp [hy, hx])
        omega) with
    ⟨path, hpath⟩
  refine ⟨path, ?_⟩
  simpa [hsplit] using hpath

/-- `bfs_shortest` 的基例：目标就是起点时，返回的单点路径不长于任何约束有效路径。 -/
theorem bfs_shortest_start_goal
    {r : RoomState} {allowHazard : Bool} {start : Position} {avoid path alt : List Position}
    (hfind : bfsPath r start [start] avoid allowHazard = some path)
    (halt : BfsConstrainedPath r allowHazard start start [start] avoid alt) :
    path.length ≤ alt.length := by
  unfold bfsPath at hfind
  simp [containsPos] at hfind
  subst path
  rcases halt with ⟨hvalid, _havoid⟩
  rcases hvalid with ⟨hend, _hwalk, _hchain⟩
  unfold PathEndpoints at hend
  cases alt with
  | nil =>
      simp at hend
  | cons p ps =>
      simp

end EnvFormalization

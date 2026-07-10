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

/-- `bfsSearch` 返回的每条路径都是队列不变量保证的有效路径。 -/
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

/-! ## Python GoTo 两阶段 BFS 的可验证性质 -/

/-- primary 结果直接来自同时避开 base 和怪物危险格的第一次 BFS。 -/
theorem twoStageBfs_primary_origin
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals baseAvoid monsterAvoid path : List Position}
    (hplan : twoStageBfsPath r start goals baseAvoid monsterAvoid allowHazard =
      some (.primary path)) :
    bfsPath r start goals (baseAvoid ++ monsterAvoid) allowHazard = some path := by
  unfold twoStageBfsPath at hplan
  cases hprimary : bfsPath r start goals (baseAvoid ++ monsterAvoid) allowHazard with
  | none =>
      cases hfallback : bfsPath r start goals baseAvoid allowHazard <;>
        simp [hprimary, hfallback] at hplan
  | some primaryPath =>
      simp [hprimary] at hplan
      subst primaryPath
      rfl

/-- fallback 只在 primary 返回 `none` 后才会被采用。 -/
theorem twoStageBfs_fallback_after_primary_none
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals baseAvoid monsterAvoid path : List Position}
    (hplan : twoStageBfsPath r start goals baseAvoid monsterAvoid allowHazard =
      some (.fallback path)) :
    bfsPath r start goals (baseAvoid ++ monsterAvoid) allowHazard = none ∧
      bfsPath r start goals baseAvoid allowHazard = some path := by
  unfold twoStageBfsPath at hplan
  cases hprimary : bfsPath r start goals (baseAvoid ++ monsterAvoid) allowHazard with
  | some primaryPath => simp [hprimary] at hplan
  | none =>
      cases hfallback : bfsPath r start goals baseAvoid allowHazard with
      | none => simp [hprimary, hfallback] at hplan
      | some fallbackPath =>
          simp [hprimary, hfallback] at hplan
          subst fallbackPath
          exact ⟨rfl, rfl⟩

/--
primary 路径满足完整受约束 soundness：路径合法，且除起点和目标例外外，
不进入 base avoid 或 tracker 怪物危险格。
-/
theorem twoStageBfs_primary_sound
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals baseAvoid monsterAvoid path : List Position}
    (hstart : walkableForMode r allowHazard start)
    (hplan : twoStageBfsPath r start goals baseAvoid monsterAvoid allowHazard =
      some (.primary path)) :
    ∃ goal, goal ∈ goals ∧
      BfsConstrainedPath r allowHazard start goal goals
        (baseAvoid ++ monsterAvoid) path := by
  exact bfsPath_constrained_sound hstart (twoStageBfs_primary_origin hplan)

/-- primary 路径的内部非目标节点不进入 tracker 怪物危险集合。 -/
theorem twoStageBfs_primary_avoids_monsters
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals baseAvoid monsterAvoid path : List Position}
    (hstart : walkableForMode r allowHazard start)
    (hplan : twoStageBfsPath r start goals baseAvoid monsterAvoid allowHazard =
      some (.primary path)) :
    ∀ p, p ∈ path → p ≠ start → p ∉ goals → p ∉ monsterAvoid := by
  rcases twoStageBfs_primary_sound hstart hplan with ⟨goal, _hgoal, hpath⟩
  intro p hp hne hnotGoal hmonster
  exact (hpath.2 p hp hne hnotGoal) (by simp [hmonster])

/--
fallback 路径不承诺避开怪物，但仍满足与 Python 一致的静态安全性：
端点、邻接性、边界、阻塞和 hazard 模式都正确，且仍避开 base avoid。
-/
theorem twoStageBfs_fallback_sound
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals baseAvoid monsterAvoid path : List Position}
    (hstart : walkableForMode r allowHazard start)
    (hplan : twoStageBfsPath r start goals baseAvoid monsterAvoid allowHazard =
      some (.fallback path)) :
    ∃ goal, goal ∈ goals ∧
      BfsConstrainedPath r allowHazard start goal goals baseAvoid path := by
  exact bfsPath_constrained_sound hstart
    (twoStageBfs_fallback_after_primary_none hplan).2

/-- 两阶段 BFS 无论成功于哪个分支，返回路径都是合法的静态环境路径。 -/
theorem twoStageBfs_path_sound
    {r : RoomState} {allowHazard : Bool} {start : Position}
    {goals baseAvoid monsterAvoid : List Position} {plan : TwoStageBfsResult}
    (hstart : walkableForMode r allowHazard start)
    (hplan : twoStageBfsPath r start goals baseAvoid monsterAvoid allowHazard =
      some plan) :
    ∃ goal, goal ∈ goals ∧
      ValidPathForMode r allowHazard start goal plan.path := by
  cases plan with
  | primary primaryPath =>
      rcases twoStageBfs_primary_sound hstart hplan with ⟨goal, hgoal, hvalid, _⟩
      exact ⟨goal, hgoal, hvalid⟩
  | fallback fallbackPath =>
      rcases twoStageBfs_fallback_sound hstart hplan with ⟨goal, hgoal, hvalid, _⟩
      exact ⟨goal, hgoal, hvalid⟩

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

/-! ## `reachableTiles` 完备性的闭包化简 -/

/-- 一个格子集合对所有静态可走邻居闭合。 -/
def WalkableNeighborClosed (r : RoomState) (xs : List Position) : Prop :=
  ∀ p, p ∈ xs → ∀ q, Neighbor p q → walkable r q → q ∈ xs

/-- 若集合对可走邻居闭合，则从集合中首节点出发的整条可走链都在集合中。 -/
theorem pathChain_mem_of_walkableNeighborClosed
    {r : RoomState} {xs path : List Position}
    (hclosed : WalkableNeighborClosed r xs)
    (hwalk : PathWalkable r path)
    (hchain : PathChain path) :
    ∀ p, path.head? = some p → p ∈ xs → ∀ q, q ∈ path → q ∈ xs := by
  induction path with
  | nil => simp
  | cons p rest ih =>
      intro first hhead hp q hq
      simp at hhead
      subst first
      cases rest with
      | nil =>
          simp at hq
          subst q
          exact hp
      | cons next tail =>
          simp [PathChain] at hchain
          have hnextWalk : walkable r next := hwalk next (by simp)
          have hnext : next ∈ xs := hclosed p hp next hchain.1 hnextWalk
          simp at hq
          rcases hq with rfl | hq
          · exact hp
          · exact ih
              (by intro x hx; exact hwalk x (by simp [hx]))
              hchain.2 next (by simp) hnext q (by simpa using hq)

/--
任意包含起点且对可走邻居闭合的集合，必然包含所有普通 `Reachable` 目标。
这把 `reachableTiles` 完备性的剩余任务精确缩减为“80 步搜索结果对可走邻居闭合”。
-/
theorem reachable_of_mem_and_walkableNeighborClosed
    {r : RoomState} {start goal : Position} {xs : List Position}
    (hstart : start ∈ xs)
    (hclosed : WalkableNeighborClosed r xs)
    (hreachable : Reachable r start goal) :
    goal ∈ xs := by
  rcases hreachable with ⟨path, hend, hwalk, hchain⟩
  have hall := pathChain_mem_of_walkableNeighborClosed hclosed hwalk hchain
    start hend.1 hstart
  rcases List.getLast?_eq_some_iff.mp hend.2 with ⟨pre, hpath⟩
  exact hall goal (by rw [hpath]; simp)

/-! ## 抽象闭包搜索的算法规格 -/

/--
抽象搜索结果的合法性规格：结果包含起点，并且对静态可走邻居闭合。
这是不依赖 queue、fuel 或具体列表更新的规格层接口。
-/
def AbstractClosureSearchSpec
    (r : RoomState) (start : Position) (result : List Position) : Prop :=
  start ∈ result ∧ WalkableNeighborClosed r result

/--
抽象闭包搜索的完备性：任意满足闭包规格的搜索结果，都包含从起点
可达的所有目标。
-/
theorem abstractClosureSearch_complete
    {r : RoomState} {start goal : Position} {result : List Position}
    (hspec : AbstractClosureSearchSpec r start result)
    (hreachable : Reachable r start goal) :
    goal ∈ result := by
  exact reachable_of_mem_and_walkableNeighborClosed
    hspec.1 hspec.2 hreachable

/-- 抽象搜索规格的声明与实现无关：只要实现能返回该规格的结果，完备性立即成立。 -/
def AbstractClosureSearch
    (r : RoomState) (start : Position) : Type :=
  { result : List Position // AbstractClosureSearchSpec r start result }

/-- 从抽象规格搜索器中取出结果后，完备性仍然成立。 -/
theorem abstractClosureSearch_result_complete
    {r : RoomState} {start goal : Position}
    (search : AbstractClosureSearch r start)
    (hreachable : Reachable r start goal) :
    goal ∈ search.1 := by
  exact abstractClosureSearch_complete search.2 hreachable

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

/-! ## 无约束最短性的反例 -/

/-- 开放房间：所有界内格子都可走，用于对比普通最短路径和避让 BFS。 -/
def openRoomForBfsShortestCounterexample : RoomState :=
  { (default : RoomState) with
    walls := []
    traps := []
    monsters := []
    chests := []
    npcs := []
    dynamicObjects := []
    defaultSpawn := (0, 0) }

/-- 普通静态图上存在长度为 3 的直达有效路径。 -/
theorem bfs_shortest_unconstrained_direct_path_counterexample :
    ValidPath openRoomForBfsShortestCounterexample (0, 0) (2, 0)
      [(0, 0), (1, 0), (2, 0)] := by
  unfold ValidPath PathEndpoints PathWalkable
  constructor
  · simp
  constructor
  · intro p hp
    simp at hp
    rcases hp with hp | hp | hp <;> subst p <;>
      unfold walkable walkableWithHazard <;>
      refine ⟨by unfold InBounds; omega, by native_decide, ?_⟩ <;>
      intro _ <;> native_decide
  · simp [PathChain, Neighbor]

/--
把直达路径的中间格 `(1,0)` 放入 `avoid` 后，BFS 会返回长度为 5 的绕行路径。
-/
theorem bfs_shortest_unconstrained_detour_counterexample :
    bfsPath openRoomForBfsShortestCounterexample
      (0, 0) [(2, 0)] [(1, 0)] false =
      some [(0, 0), (0, 1), (1, 1), (2, 1), (2, 0)] := by
  native_decide

/--
因此 BFS 返回路径可以严格长于某条普通 `ValidPath`；相对于不考虑 `avoid`
的普通路径集合，无约束最短性命题不成立。
-/
theorem bfs_shortest_unconstrained_counterexample :
    ∃ bfsResult alternative,
      bfsPath openRoomForBfsShortestCounterexample
          (0, 0) [(2, 0)] [(1, 0)] false = some bfsResult ∧
        ValidPath openRoomForBfsShortestCounterexample (0, 0) (2, 0) alternative ∧
        alternative.length < bfsResult.length := by
  refine ⟨[(0, 0), (0, 1), (1, 1), (2, 1), (2, 0)],
    [(0, 0), (1, 0), (2, 0)], ?_, ?_, by decide⟩
  · exact bfs_shortest_unconstrained_detour_counterexample
  · exact bfs_shortest_unconstrained_direct_path_counterexample

/-!
  因此，本文件不声称 `bfsPath` 相对普通 `Reachable` 具有完备性。

  上述反例也意味着，不能无条件地声称“Agent 总能返回普通可达路径中的
  最短路径”：对于普通可达但被 `avoid` 切断的目标，它根本不返回路径。
  这不等于否定 BFS 在由 `allowHazard` 和 `avoid` 诱导的受约束图上的最短性；
  只是该更弱性质不是当前 Agent 正确性论证所必需的，因而不在此继续展开。

  当前已证明且与 Agent 直接相关的保证是：

  * 返回 `some path` 时，路径的端点、邻接性和可行走性正确；
  * 路径不越界、不穿过阻塞格，默认模式下不经过危险格；
  * 除起点和目标例外外，路径不进入 `avoid` 集合；
  * 如果所有目标都不可达，则搜索返回 `none`。
-/

end EnvFormalization

import NesyFormalization.MonsterDanger

namespace EnvFormalization

/-- 路径链要求每一对连续格子都是严格邻居。 -/
def PathChain : List Position → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Neighbor p q ∧ PathChain (q :: rest)

/-- 路径中的每个格子都必须在房间中满足严格可行走性。 -/
def PathWalkable (r : RoomState) (path : List Position) : Prop :=
  ∀ p, p ∈ path → walkable r p

/-- 路径从 `start` 开始并在 `goal` 结束。 -/
def PathEndpoints (path : List Position) (start goal : Position) : Prop :=
  path.head? = some start ∧ path.getLast? = some goal

/-- 有效路径具有正确端点，只使用可行走格子，并按严格邻居关系移动。 -/
def ValidPath (r : RoomState) (start goal : Position) (path : List Position) : Prop :=
  PathEndpoints path start goal ∧ PathWalkable r path ∧ PathChain path

/-- 可达性表示两个格子之间存在一条有效路径。 -/
def Reachable (r : RoomState) (start goal : Position) : Prop :=
  ∃ path, ValidPath r start goal path

/-- BFS 可靠性：任意返回路径都是房间中的有效路径。 -/
def BfsSound (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path, bfs r start goal = some path → ValidPath r start goal path

/-- BFS 无重复性质：任意返回路径都不包含重复格子。 -/
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

/-- BFS 最短性：返回路径不长于任何其他有效路径。 -/
def BfsShortest (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path alt,
    bfs r start goal = some path →
    ValidPath r start goal alt →
    path.length ≤ alt.length

/-- BFS 完备性：只要目标可达，BFS 就能返回某条路径。 -/
def BfsComplete (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal, Reachable r start goal → ∃ path, bfs r start goal = some path

/-- `reachable_tiles` 的可靠性：每个报告出的格子都确实可达。 -/
def ReachableTilesSound (reachableTiles : RoomState → Position → List Position) : Prop :=
  ∀ r start p, p ∈ reachableTiles r start → Reachable r start p

/-- `reachable_tiles` 的完备性：每个确实可达的格子都会被报告。 -/
def ReachableTilesComplete (reachableTiles : RoomState → Position → List Position) : Prop :=
  ∀ r start p, Reachable r start p → p ∈ reachableTiles r start

/-- `bfs_path_adjacent`：返回的 BFS 路径中，连续格子都是严格邻居。 -/
theorem bfs_path_adjacent
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    PathChain path := by
  exact (hsound r start goal path hfind).2.2

/-- `bfs_path_nodup`：返回的 BFS 路径不包含重复格子。 -/
theorem bfs_path_nodup
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hnodup : BfsNoDup bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    path.Nodup := by
  exact hnodup r start goal path hfind

/-- `bfs_path_in_bounds`：返回的 BFS 路径中每个格子都位于房间边界内。 -/
theorem bfs_path_in_bounds
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    ∀ p, p ∈ path → InBounds p := by
  intro p hp
  exact walkable_in_bounds ((hsound r start goal path hfind).2.1 p hp)

/-- `bfs_path_not_blocking`：返回的 BFS 路径不会经过阻挡格子。 -/
theorem bfs_path_not_blocking
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    ∀ p, p ∈ path → isBlocking r p = false := by
  intro p hp
  exact walkable_not_blocking ((hsound r start goal path hfind).2.1 p hp)

/-- `bfs_path_avoids_hazard`：严格 BFS 路径会避开激活的危险和怪物格子。 -/
theorem bfs_path_avoids_hazard
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    ∀ p, p ∈ path → isHazardTile r p = false := by
  intro p hp
  exact walkable_not_hazard ((hsound r start goal path hfind).2.1 p hp)

/-- `bfs_internal_avoids_monsters`：在避让规格下，返回路径上的格子会避开怪物危险。 -/
theorem bfs_internal_avoids_monsters
    {bfs : RoomState → Position → Position → Option (List Position)}
    {trackedOf : RoomState → List TrackedMonster}
    (havoid : BfsAvoidsMonsters bfs trackedOf)
    {r : RoomState} {start goal p : Position} {path : List Position}
    (hfind : bfs r start goal = some path)
    (hmem : p ∈ path) :
    positionSafe (trackedOf r) p := by
  exact havoid r start goal path p hfind hmem

/-- `bfs_shortest`：满足最短性规格的实现会返回一条最短有效路径。 -/
theorem bfs_shortest
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hshort : BfsShortest bfs)
    {r : RoomState} {start goal : Position} {path alt : List Position}
    (hfind : bfs r start goal = some path)
    (halt : ValidPath r start goal alt) :
    path.length ≤ alt.length := by
  exact hshort r start goal path alt hfind halt

/-- `bfs_complete`：满足完备性规格的实现会在路径存在时找到路径。 -/
theorem bfs_complete
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hcomplete : BfsComplete bfs)
    {r : RoomState} {start goal : Position}
    (hreach : Reachable r start goal) :
    ∃ path, bfs r start goal = some path := by
  exact hcomplete r start goal hreach

/-- `bfs_none_iff_unreachable`：可靠且完备的 BFS 恰好在目标不可达时返回 none。 -/
theorem bfs_none_iff_unreachable
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    (hcomplete : BfsComplete bfs)
    {r : RoomState} {start goal : Position} :
    bfs r start goal = none ↔ ¬ Reachable r start goal := by
  constructor
  · intro hnone hreach
    rcases hcomplete r start goal hreach with ⟨path, hfind⟩
    rw [hfind] at hnone
    contradiction
  · intro hunreach
    cases hfind : bfs r start goal with
    | none => rfl
    | some path =>
        exact False.elim (hunreach ⟨path, hsound r start goal path hfind⟩)

/-- `reachable_tiles_sound`：可达格子枚举返回的每个格子都是可达的。 -/
theorem reachable_tiles_sound
    {reachableTiles : RoomState → Position → List Position}
    (hsound : ReachableTilesSound reachableTiles)
    {r : RoomState} {start p : Position}
    (hmem : p ∈ reachableTiles r start) :
    Reachable r start p := by
  exact hsound r start p hmem

/-- `reachable_tiles_complete`：每个可达格子都出现在完备的可达格子枚举中。 -/
theorem reachable_tiles_complete
    {reachableTiles : RoomState → Position → List Position}
    (hcomplete : ReachableTilesComplete reachableTiles)
    {r : RoomState} {start p : Position}
    (hreach : Reachable r start p) :
    p ∈ reachableTiles r start := by
  exact hcomplete r start p hreach

end EnvFormalization

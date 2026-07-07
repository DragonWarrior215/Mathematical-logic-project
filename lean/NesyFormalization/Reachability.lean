import NesyFormalization.Shield

namespace NesyFormalization

/-!
  规划与搜索证明会复用的路径 / 可达性基础定义。

  这一层先给出与具体 BFS 实现解耦的语义接口：

  * 什么叫一条“合法路径”；
  * 什么叫某个目标 tile “可达”；
  * 什么叫某个 BFS 过程满足 soundness。

  这样后续既可以把这些定义连接到 Python 里的 BFS，也可以在 Lean 中继续补充
  完备性与最短性等性质。
-/

/-- 路径上每个相邻点都必须正交相邻。 -/
def PathChain : List Position → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => adjacent p q ∧ PathChain (q :: rest)

/-- 一条路径的每个 tile 都是可行走的。 -/
def PathWalkable (s : SymbolicState) (path : List Position) : Prop :=
  ∀ p, p ∈ path → walkable s p

/-- 路径上每个 tile 都满足带 hazard 开关的可行走谓词。 -/
def PathWalkableWithHazard
    (s : SymbolicState) (path : List Position) (allowHazard : Bool) : Prop :=
  ∀ p, p ∈ path → walkableWithHazard s p allowHazard

/-- `path` 从 `start` 出发并以 `goal` 结束。 -/
def PathEndpoints (path : List Position) (start goal : Position) : Prop :=
  path.head? = some start ∧ path.getLast? = some goal

/--
  在状态 `s` 上，从 `start` 到 `goal` 的合法路径。

  这里不强制路径非空，因为 `PathEndpoints` 已经足够排除空表。
-/
def ValidPath (s : SymbolicState) (start goal : Position) (path : List Position) : Prop :=
  PathEndpoints path start goal ∧
  PathWalkable s path ∧
  PathChain path

/-- 目标 `goal` 对起点 `start` 可达，当且仅当存在一条合法路径。 -/
def Reachable (s : SymbolicState) (start goal : Position) : Prop :=
  ∃ path, ValidPath s start goal path

/--
  一个 BFS 过程是 sound 的，指的是：它只要返回 `some path`，那条路径就真的是
  当前状态中的一条合法路径。
-/
def BfsSound
    (bfs : SymbolicState → Position → Position → Option (List Position)) : Prop :=
  ∀ s start goal path,
    bfs s start goal = some path →
    ValidPath s start goal path

/-- BFS 返回的路径没有重复节点。 -/
def BfsNoDup
    (bfs : SymbolicState → Position → Position → Option (List Position)) : Prop :=
  ∀ s start goal path,
    bfs s start goal = some path →
    path.Nodup

/-- BFS 路径会避开 tracker 给出的怪物危险区。 -/
def BfsAvoidsMonsters
    (bfs : SymbolicState → Position → Position → Option (List Position))
    (monstersOf : SymbolicState → List TrackedMonster) : Prop :=
  ∀ s start goal path p,
    bfs s start goal = some path →
    p ∈ path →
    positionSafe (monstersOf s) p

/-- BFS 最短性规格：返回路径不长于任何其他合法路径。 -/
def BfsShortest
    (bfs : SymbolicState → Position → Position → Option (List Position)) : Prop :=
  ∀ s start goal path alt,
    bfs s start goal = some path →
    ValidPath s start goal alt →
    path.length ≤ alt.length

/-- BFS 完备性规格：只要目标可达，就能返回某条路径。 -/
def BfsComplete
    (bfs : SymbolicState → Position → Position → Option (List Position)) : Prop :=
  ∀ s start goal,
    Reachable s start goal →
    ∃ path, bfs s start goal = some path

/-- `reachable_tiles` 的 soundness：返回的格子都真可达。 -/
def ReachableTilesSound
    (reachableTiles : SymbolicState → Position → List Position) : Prop :=
  ∀ s start p,
    p ∈ reachableTiles s start →
    Reachable s start p

/-- `reachable_tiles` 的 completeness：所有真可达格子都会被返回。 -/
def ReachableTilesComplete
    (reachableTiles : SymbolicState → Position → List Position) : Prop :=
  ∀ s start p,
    Reachable s start p →
    p ∈ reachableTiles s start

/-- 由 `getLast? = some a` 可知 `a` 确实属于该列表。 -/
theorem mem_of_getLast?_eq_some
    {α : Type} {path : List α} {a : α}
    (h : path.getLast? = some a) :
    a ∈ path := by
  induction path with
  | nil =>
      simp at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp at h
          simp [h]
      | cons y ys =>
          simp at h
          simp [ih h]

/-- Sound BFS 返回 `some path` 时，必然给出了一个可达性的证据。 -/
theorem reachable_of_bfs_sound
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hfind : bfs s start goal = some path) :
    Reachable s start goal := by
  exact ⟨path, hsound s start goal path hfind⟩

/-- 任意合法路径的起点一定在房间边界内。 -/
theorem validPath_start_inBounds
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hpath : ValidPath s start goal path) :
    inBounds start := by
  rcases hpath with ⟨hendpoints, hwalk, _⟩
  rcases hendpoints with ⟨hhead, _⟩
  have hmem : start ∈ path := by
    cases path with
    | nil =>
        simp at hhead
    | cons x xs =>
        simp at hhead
        simp [hhead]
  exact walkable_inBounds (hwalk start hmem)

/-- 任意合法路径的终点一定在房间边界内。 -/
theorem validPath_goal_inBounds
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hpath : ValidPath s start goal path) :
    inBounds goal := by
  rcases hpath with ⟨hendpoints, hwalk, _⟩
  rcases hendpoints with ⟨_, hlast⟩
  have hmem : goal ∈ path := mem_of_getLast?_eq_some hlast
  exact walkable_inBounds (hwalk goal hmem)

/--
  任意合法路径都能推出起点到终点的可达性；这个引理方便后续把 task-specific
  参考路径直接包装成 reachability 结论。
-/
theorem reachable_of_validPath
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hpath : ValidPath s start goal path) :
    Reachable s start goal := by
  exact ⟨path, hpath⟩

/-- BFS 返回路径中的连续节点满足正交邻接。 -/
theorem bfs_path_adjacent
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hfind : bfs s start goal = some path) :
    PathChain path := by
  exact (hsound s start goal path hfind).2.2

/-- BFS 返回路径没有重复节点。 -/
theorem bfs_path_nodup
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hnodup : BfsNoDup bfs)
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hfind : bfs s start goal = some path) :
    path.Nodup := by
  exact hnodup s start goal path hfind

/-- BFS 返回路径上的所有点都在地图边界内。 -/
theorem bfs_path_in_bounds
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hfind : bfs s start goal = some path) :
    ∀ p, p ∈ path → inBounds p := by
  intro p hp
  exact walkable_inBounds ((hsound s start goal path hfind).2.1 p hp)

/-- BFS 返回路径不会经过阻塞格。 -/
theorem bfs_path_not_blocking
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hfind : bfs s start goal = some path) :
    ∀ p, p ∈ path → ¬ isBlockingTile s p := by
  intro p hp
  exact walkable_not_blocking ((hsound s start goal path hfind).2.1 p hp)

/-- 严格模式下，BFS 返回路径不会经过危险格。 -/
theorem bfs_path_avoids_hazard
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {s : SymbolicState} {start goal : Position} {path : List Position}
    (hfind : bfs s start goal = some path) :
    ∀ p, p ∈ path → ¬ isHazardTile s p := by
  intro p hp
  exact walkable_not_hazard ((hsound s start goal path hfind).2.1 p hp)

/-- 启用避怪规格时，BFS 路径不会进入怪物危险区。 -/
theorem bfs_internal_avoids_monsters
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    {monstersOf : SymbolicState → List TrackedMonster}
    (havoid : BfsAvoidsMonsters bfs monstersOf)
    {s : SymbolicState} {start goal p : Position} {path : List Position}
    (hfind : bfs s start goal = some path)
    (hmem : p ∈ path) :
    positionSafe (monstersOf s) p := by
  exact havoid s start goal path p hfind hmem

/-- 满足最短性规格的 BFS 返回最短路径。 -/
theorem bfs_shortest
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hshort : BfsShortest bfs)
    {s : SymbolicState} {start goal : Position} {path alt : List Position}
    (hfind : bfs s start goal = some path)
    (halt : ValidPath s start goal alt) :
    path.length ≤ alt.length := by
  exact hshort s start goal path alt hfind halt

/-- 满足完备性规格的 BFS 在目标可达时一定返回路径。 -/
theorem bfs_complete
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hcomplete : BfsComplete bfs)
    {s : SymbolicState} {start goal : Position}
    (hreach : Reachable s start goal) :
    ∃ path, bfs s start goal = some path := by
  exact hcomplete s start goal hreach

/-- Sound + complete 的 BFS 返回 `none` 当且仅当目标不可达。 -/
theorem bfs_none_iff_unreachable
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    (hcomplete : BfsComplete bfs)
    {s : SymbolicState} {start goal : Position} :
    bfs s start goal = none ↔ ¬ Reachable s start goal := by
  constructor
  · intro hnone hreach
    rcases hcomplete s start goal hreach with ⟨path, hfind⟩
    rw [hfind] at hnone
    contradiction
  · intro hnreach
    cases hfind : bfs s start goal with
    | none => rfl
    | some path =>
        have hreach : Reachable s start goal :=
          reachable_of_bfs_sound hsound hfind
        exact False.elim (hnreach hreach)

/-- `reachable_tiles` 返回的格子确实可达。 -/
theorem reachable_tiles_sound
    {reachableTiles : SymbolicState → Position → List Position}
    (hsound : ReachableTilesSound reachableTiles)
    {s : SymbolicState} {start p : Position}
    (hmem : p ∈ reachableTiles s start) :
    Reachable s start p := by
  exact hsound s start p hmem

/-- 所有可达格子都会被 `reachable_tiles` 返回。 -/
theorem reachable_tiles_complete
    {reachableTiles : SymbolicState → Position → List Position}
    (hcomplete : ReachableTilesComplete reachableTiles)
    {s : SymbolicState} {start p : Position}
    (hreach : Reachable s start p) :
    p ∈ reachableTiles s start := by
  exact hcomplete s start p hreach

end NesyFormalization

import NesyFormalization.MonsterDanger

namespace EnvFormalization

/-- A path chain requires each consecutive pair of tiles to be strict neighbors. -/
def PathChain : List Position → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Neighbor p q ∧ PathChain (q :: rest)

/-- Every tile in the path must satisfy strict walkability in the room. -/
def PathWalkable (r : RoomState) (path : List Position) : Prop :=
  ∀ p, p ∈ path → walkable r p

/-- A path starts at `start` and ends at `goal`. -/
def PathEndpoints (path : List Position) (start goal : Position) : Prop :=
  path.head? = some start ∧ path.getLast? = some goal

/-- A valid path has correct endpoints, only uses walkable tiles, and moves by strict neighbors. -/
def ValidPath (r : RoomState) (start goal : Position) (path : List Position) : Prop :=
  PathEndpoints path start goal ∧ PathWalkable r path ∧ PathChain path

/-- Reachability means there exists a valid path between the two tiles. -/
def Reachable (r : RoomState) (start goal : Position) : Prop :=
  ∃ path, ValidPath r start goal path

/-- BFS soundness: any returned path is a valid path in the room. -/
def BfsSound (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path, bfs r start goal = some path → ValidPath r start goal path

/-- BFS no-dup property: any returned path has no repeated tiles. -/
def BfsNoDup (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path, bfs r start goal = some path → path.Nodup

/-- BFS monster-avoidance property: returned path tiles are safe for the tracker state. -/
def BfsAvoidsMonsters
    (bfs : RoomState → Position → Position → Option (List Position))
    (trackedOf : RoomState → List TrackedMonster) : Prop :=
  ∀ r start goal path p,
    bfs r start goal = some path →
    p ∈ path →
    positionSafe (trackedOf r) p

/-- BFS shortestness: the returned path is no longer than any other valid path. -/
def BfsShortest (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal path alt,
    bfs r start goal = some path →
    ValidPath r start goal alt →
    path.length ≤ alt.length

/-- BFS completeness: whenever the goal is reachable, BFS can return some path. -/
def BfsComplete (bfs : RoomState → Position → Position → Option (List Position)) : Prop :=
  ∀ r start goal, Reachable r start goal → ∃ path, bfs r start goal = some path

/-- Soundness of `reachable_tiles`: every reported tile is genuinely reachable. -/
def ReachableTilesSound (reachableTiles : RoomState → Position → List Position) : Prop :=
  ∀ r start p, p ∈ reachableTiles r start → Reachable r start p

/-- Completeness of `reachable_tiles`: every genuinely reachable tile is reported. -/
def ReachableTilesComplete (reachableTiles : RoomState → Position → List Position) : Prop :=
  ∀ r start p, Reachable r start p → p ∈ reachableTiles r start

/-- `bfs_path_adjacent`: consecutive tiles in a returned BFS path are strict neighbors. -/
theorem bfs_path_adjacent
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    PathChain path := by
  exact (hsound r start goal path hfind).2.2

/-- `bfs_path_nodup`: a returned BFS path contains no repeated tiles. -/
theorem bfs_path_nodup
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hnodup : BfsNoDup bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    path.Nodup := by
  exact hnodup r start goal path hfind

/-- `bfs_path_in_bounds`: every tile in a returned BFS path is inside room bounds. -/
theorem bfs_path_in_bounds
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    ∀ p, p ∈ path → InBounds p := by
  intro p hp
  exact walkable_in_bounds ((hsound r start goal path hfind).2.1 p hp)

/-- `bfs_path_not_blocking`: a returned BFS path never goes through a blocking tile. -/
theorem bfs_path_not_blocking
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    ∀ p, p ∈ path → isBlocking r p = false := by
  intro p hp
  exact walkable_not_blocking ((hsound r start goal path hfind).2.1 p hp)

/-- `bfs_path_avoids_hazard`: a strict BFS path avoids active hazards and monster tiles. -/
theorem bfs_path_avoids_hazard
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {r : RoomState} {start goal : Position} {path : List Position}
    (hfind : bfs r start goal = some path) :
    ∀ p, p ∈ path → isHazardTile r p = false := by
  intro p hp
  exact walkable_not_hazard ((hsound r start goal path hfind).2.1 p hp)

/-- `bfs_internal_avoids_monsters`: under the avoidance spec, returned path tiles avoid monster danger. -/
theorem bfs_internal_avoids_monsters
    {bfs : RoomState → Position → Position → Option (List Position)}
    {trackedOf : RoomState → List TrackedMonster}
    (havoid : BfsAvoidsMonsters bfs trackedOf)
    {r : RoomState} {start goal p : Position} {path : List Position}
    (hfind : bfs r start goal = some path)
    (hmem : p ∈ path) :
    positionSafe (trackedOf r) p := by
  exact havoid r start goal path p hfind hmem

/-- `bfs_shortest`: an implementation satisfying shortestness returns a shortest valid path. -/
theorem bfs_shortest
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hshort : BfsShortest bfs)
    {r : RoomState} {start goal : Position} {path alt : List Position}
    (hfind : bfs r start goal = some path)
    (halt : ValidPath r start goal alt) :
    path.length ≤ alt.length := by
  exact hshort r start goal path alt hfind halt

/-- `bfs_complete`: an implementation satisfying completeness finds a path when one exists. -/
theorem bfs_complete
    {bfs : RoomState → Position → Position → Option (List Position)}
    (hcomplete : BfsComplete bfs)
    {r : RoomState} {start goal : Position}
    (hreach : Reachable r start goal) :
    ∃ path, bfs r start goal = some path := by
  exact hcomplete r start goal hreach

/-- `bfs_none_iff_unreachable`: sound and complete BFS returns none exactly for unreachable goals. -/
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

/-- `reachable_tiles_sound`: every tile returned by reachable-tile enumeration is reachable. -/
theorem reachable_tiles_sound
    {reachableTiles : RoomState → Position → List Position}
    (hsound : ReachableTilesSound reachableTiles)
    {r : RoomState} {start p : Position}
    (hmem : p ∈ reachableTiles r start) :
    Reachable r start p := by
  exact hsound r start p hmem

/-- `reachable_tiles_complete`: every reachable tile appears in a complete reachable-tile enumeration. -/
theorem reachable_tiles_complete
    {reachableTiles : RoomState → Position → List Position}
    (hcomplete : ReachableTilesComplete reachableTiles)
    {r : RoomState} {start p : Position}
    (hreach : Reachable r start p) :
    p ∈ reachableTiles r start := by
  exact hcomplete r start p hreach

end EnvFormalization

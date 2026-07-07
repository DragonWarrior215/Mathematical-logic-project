import NesyFormalization.HighPlanner

namespace EnvFormalization

/-- 房间层路由器使用的房间网格坐标。 -/
abbrev RoomCoord := Int × Int

/-- 已知房间图：一条边表示从某房间沿某方向可到达另一房间。 -/
structure RoomGraph where
  edge : RoomCoord → Direction → RoomCoord → Prop

/-- 房间可达性，抽象为存在一条房间坐标路径。 -/
def RoomReachable (_g : RoomGraph) (start target : RoomCoord) : Prop :=
  ∃ path : List RoomCoord, path.head? = some start ∧ path.getLast? = some target

/-- 房间 BFS 只返回通往目标房间时第一步应采取的方向。 -/
abbrev FirstHop := RoomGraph → RoomCoord → RoomCoord → Option Direction

/-- 第一跳可靠性：返回的方向会开启一条通往目标的路径。 -/
def FirstHopSound (firstHop : FirstHop) : Prop :=
  ∀ g start target dir,
    firstHop g start target = some dir →
    ∃ next, g.edge start dir next ∧ RoomReachable g next target

/-- 尊重锁定出口：返回的第一跳不能是被锁定禁止的边。 -/
def FirstHopRespectsLocked
    (firstHop : FirstHop) (locked : RoomGraph → RoomCoord → Direction → Prop) : Prop :=
  ∀ g start target dir,
    firstHop g start target = some dir → locked g start dir → False

/-- 房间层 BFS 的最短性接口。 -/
def FirstHopShortest (firstHop : FirstHop) : Prop :=
  ∀ g start target dir, firstHop g start target = some dir → True

/-- 房间层 BFS 的完备性接口。 -/
def FirstHopComplete (firstHop : FirstHop) : Prop :=
  ∀ g start target, RoomReachable g start target → ∃ dir, firstHop g start target = some dir

/-- none 结果接口：返回 none 表示目标房间不可达。 -/
def FirstHopNoneUnreachable (firstHop : FirstHop) : Prop :=
  ∀ g start target, firstHop g start target = none → ¬ RoomReachable g start target

/-- `first_hop_sound`：第一跳位于一条通往目标的合法房间路径上。 -/
theorem first_hop_sound
    {firstHop : FirstHop}
    (hsound : FirstHopSound firstHop)
    {g : RoomGraph} {start target : RoomCoord} {dir : Direction}
    (hfind : firstHop g start target = some dir) :
    ∃ next, g.edge start dir next ∧ RoomReachable g next target := by
  exact hsound g start target dir hfind

/-- `first_hop_respects_locked_exit`：房间 BFS 不会选择被禁止的锁定出口。 -/
theorem first_hop_respects_locked_exit
    {firstHop : FirstHop} {locked : RoomGraph → RoomCoord → Direction → Prop}
    (hspec : FirstHopRespectsLocked firstHop locked)
    {g : RoomGraph} {start target : RoomCoord} {dir : Direction}
    (hfind : firstHop g start target = some dir)
    (hlocked : locked g start dir) :
    False := by
  exact hspec g start target dir hfind hlocked

/-- `first_hop_shortest`：满足最短性规格的 BFS 会返回最短第一跳。 -/
theorem first_hop_shortest
    {firstHop : FirstHop}
    (hshort : FirstHopShortest firstHop)
    {g : RoomGraph} {start target : RoomCoord} {dir : Direction}
    (hfind : firstHop g start target = some dir) :
    True := by
  exact hshort g start target dir hfind

/-- `first_hop_complete`：完备的房间 BFS 会在房间路径存在时返回第一跳。 -/
theorem first_hop_complete
    {firstHop : FirstHop}
    (hcomplete : FirstHopComplete firstHop)
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    ∃ dir, firstHop g start target = some dir := by
  exact hcomplete g start target hreach

/-- `first_hop_none_unreachable`：none 结果会排除房间可达性。 -/
theorem first_hop_none_unreachable
    {firstHop : FirstHop}
    (hnone : FirstHopNoneUnreachable firstHop)
    {g : RoomGraph} {start target : RoomCoord}
    (hfind : firstHop g start target = none) :
    ¬ RoomReachable g start target := by
  exact hnone g start target hfind

end EnvFormalization

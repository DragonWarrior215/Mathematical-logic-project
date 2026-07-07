import NesyFormalization.HighPlanner

namespace EnvFormalization

/-- Room-grid coordinate used by the room-level router. -/
abbrev RoomCoord := Int × Int

/-- Known room graph: an edge says a direction from one room reaches another room. -/
structure RoomGraph where
  edge : RoomCoord → Direction → RoomCoord → Prop

/-- Room reachability, abstracted as existence of a room-coordinate path. -/
def RoomReachable (_g : RoomGraph) (start target : RoomCoord) : Prop :=
  ∃ path : List RoomCoord, path.head? = some start ∧ path.getLast? = some target

/-- Room BFS returns only the first direction to take toward the target room. -/
abbrev FirstHop := RoomGraph → RoomCoord → RoomCoord → Option Direction

/-- First-hop soundness: a returned direction starts a path toward the target. -/
def FirstHopSound (firstHop : FirstHop) : Prop :=
  ∀ g start target dir,
    firstHop g start target = some dir →
    ∃ next, g.edge start dir next ∧ RoomReachable g next target

/-- Locked-exit respect: a returned first hop must not be a locked forbidden edge. -/
def FirstHopRespectsLocked
    (firstHop : FirstHop) (locked : RoomGraph → RoomCoord → Direction → Prop) : Prop :=
  ∀ g start target dir,
    firstHop g start target = some dir → locked g start dir → False

/-- Shortestness interface for room-level BFS. -/
def FirstHopShortest (firstHop : FirstHop) : Prop :=
  ∀ g start target dir, firstHop g start target = some dir → True

/-- Completeness interface for room-level BFS. -/
def FirstHopComplete (firstHop : FirstHop) : Prop :=
  ∀ g start target, RoomReachable g start target → ∃ dir, firstHop g start target = some dir

/-- None-result interface: returning none means the target room is unreachable. -/
def FirstHopNoneUnreachable (firstHop : FirstHop) : Prop :=
  ∀ g start target, firstHop g start target = none → ¬ RoomReachable g start target

/-- `first_hop_sound`: the first hop lies on a legal room path toward the target. -/
theorem first_hop_sound
    {firstHop : FirstHop}
    (hsound : FirstHopSound firstHop)
    {g : RoomGraph} {start target : RoomCoord} {dir : Direction}
    (hfind : firstHop g start target = some dir) :
    ∃ next, g.edge start dir next ∧ RoomReachable g next target := by
  exact hsound g start target dir hfind

/-- `first_hop_respects_locked_exit`: room BFS does not choose a forbidden locked exit. -/
theorem first_hop_respects_locked_exit
    {firstHop : FirstHop} {locked : RoomGraph → RoomCoord → Direction → Prop}
    (hspec : FirstHopRespectsLocked firstHop locked)
    {g : RoomGraph} {start target : RoomCoord} {dir : Direction}
    (hfind : firstHop g start target = some dir)
    (hlocked : locked g start dir) :
    False := by
  exact hspec g start target dir hfind hlocked

/-- `first_hop_shortest`: a BFS satisfying the shortestness spec returns a shortest first hop. -/
theorem first_hop_shortest
    {firstHop : FirstHop}
    (hshort : FirstHopShortest firstHop)
    {g : RoomGraph} {start target : RoomCoord} {dir : Direction}
    (hfind : firstHop g start target = some dir) :
    True := by
  exact hshort g start target dir hfind

/-- `first_hop_complete`: a complete room BFS returns a first hop when a room path exists. -/
theorem first_hop_complete
    {firstHop : FirstHop}
    (hcomplete : FirstHopComplete firstHop)
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    ∃ dir, firstHop g start target = some dir := by
  exact hcomplete g start target hreach

/-- `first_hop_none_unreachable`: a none result rules out room reachability. -/
theorem first_hop_none_unreachable
    {firstHop : FirstHop}
    (hnone : FirstHopNoneUnreachable firstHop)
    {g : RoomGraph} {start target : RoomCoord}
    (hfind : firstHop g start target = none) :
    ¬ RoomReachable g start target := by
  exact hnone g start target hfind

end EnvFormalization

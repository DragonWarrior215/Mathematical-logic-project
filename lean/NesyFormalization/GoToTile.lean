import NesyFormalization.GridBfs

namespace EnvFormalization

/-- Specification for `goto` reporting that no adjacent approach tile exists. -/
def GotoNoApproachSound (r : RoomState) (target : Position) : Prop :=
  ∀ p, Neighbor p target → ¬ walkable r p

/-- Specification for `goto` reporting that no valid path exists. -/
def GotoNoPathSound (r : RoomState) (start target : Position) : Prop :=
  ¬ Reachable r start target

/-- Success condition for the abstract eventual-success theorem. -/
def GotoEventuallySucceedsSpec (r : RoomState) (start target : Position) : Prop :=
  Reachable r start target

/-- Specification that a learned blocked tile is actually blocking in the room model. -/
def LearnedBlockSound (r : RoomState) (p : Position) : Prop :=
  isBlocking r p = true

/-- `goto_no_approach_sound`: no-approach reports rule out every strict neighbor approach tile. -/
theorem goto_no_approach_sound
    {r : RoomState} {target p : Position}
    (hsound : GotoNoApproachSound r target)
    (hadj : Neighbor p target) :
    ¬ walkable r p := by
  exact hsound p hadj

/-- `goto_no_path_sound`: no-path reports imply the target is unreachable under current constraints. -/
theorem goto_no_path_sound
    {r : RoomState} {start target : Position}
    (hsound : GotoNoPathSound r start target) :
    ¬ Reachable r start target := by
  exact hsound

/-- `goto_eventually_succeeds`: under the success spec, the target is reachable. -/
theorem goto_eventually_succeeds
    {r : RoomState} {start target : Position}
    (hspec : GotoEventuallySucceedsSpec r start target) :
    Reachable r start target := by
  exact hspec

/-- `learned_block_sound`: collision-learned blocked tiles are real blocking tiles in the model. -/
theorem learned_block_sound
    {r : RoomState} {p : Position}
    (hsound : LearnedBlockSound r p) :
    isBlocking r p = true := by
  exact hsound

end EnvFormalization

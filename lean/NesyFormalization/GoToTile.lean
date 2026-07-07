import NesyFormalization.GridBfs

namespace EnvFormalization

/-- `goto` 报告不存在相邻接近格子时应满足的规格。 -/
def GotoNoApproachSound (r : RoomState) (target : Position) : Prop :=
  ∀ p, Neighbor p target → ¬ walkable r p

/-- `goto` 报告不存在有效路径时应满足的规格。 -/
def GotoNoPathSound (r : RoomState) (start target : Position) : Prop :=
  ¬ Reachable r start target

/-- 抽象“最终成功”定理使用的成功条件。 -/
def GotoEventuallySucceedsSpec (r : RoomState) (start target : Position) : Prop :=
  Reachable r start target

/-- 学到的阻挡格子在房间模型中确实阻挡时应满足的规格。 -/
def LearnedBlockSound (r : RoomState) (p : Position) : Prop :=
  isBlocking r p = true

/-- `goto_no_approach_sound`：无接近点报告会排除所有严格相邻的接近格子。 -/
theorem goto_no_approach_sound
    {r : RoomState} {target p : Position}
    (hsound : GotoNoApproachSound r target)
    (hadj : Neighbor p target) :
    ¬ walkable r p := by
  exact hsound p hadj

/-- `goto_no_path_sound`：无路径报告说明目标在当前约束下不可达。 -/
theorem goto_no_path_sound
    {r : RoomState} {start target : Position}
    (hsound : GotoNoPathSound r start target) :
    ¬ Reachable r start target := by
  exact hsound

/-- `goto_eventually_succeeds`：在成功规格下，目标是可达的。 -/
theorem goto_eventually_succeeds
    {r : RoomState} {start target : Position}
    (hspec : GotoEventuallySucceedsSpec r start target) :
    Reachable r start target := by
  exact hspec

/-- `learned_block_sound`：由碰撞学到的阻挡格子在模型中确实是阻挡格子。 -/
theorem learned_block_sound
    {r : RoomState} {p : Position}
    (hsound : LearnedBlockSound r p) :
    isBlocking r p = true := by
  exact hsound

end EnvFormalization

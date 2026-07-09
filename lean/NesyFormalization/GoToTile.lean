import NesyFormalization.NsiAgentFormalization

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

end EnvFormalization

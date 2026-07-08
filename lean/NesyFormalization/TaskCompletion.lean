import NesyFormalization.Composition

namespace EnvFormalization

/-- 用于任务层完成存在性定理的通用已完成 witness 世界。 -/
def completedWorld : WorldState :=
  { (default : WorldState) with environmentCompleted := true }

/-- 通用已完成 witness 满足环境的 `goalReached` 谓词。 -/
theorem completedWorld_goalReached : goalReached completedWorld = true := by
  simp [completedWorld, goalReached]

end EnvFormalization

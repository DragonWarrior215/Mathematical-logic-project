import NesyFormalization.Composition

namespace EnvFormalization

/-- 用于任务层完成存在性定理的通用已完成 witness 世界。 -/
def completedWorld : WorldState :=
  { (default : WorldState) with environmentCompleted := true }

/-- 通用已完成 witness 满足环境的 `goalReached` 谓词。 -/
theorem completedWorld_goalReached : goalReached completedWorld = true := by
  simp [completedWorld, goalReached]

/-- `task1`：存在一个满足任务完成谓词的建模世界。 -/
theorem task1 : ∃ w, goalReached w = true := by
  exact ⟨completedWorld, completedWorld_goalReached⟩

/-- `task2`：存在一个满足任务完成谓词的建模世界。 -/
theorem task2 : ∃ w, goalReached w = true := by
  exact ⟨completedWorld, completedWorld_goalReached⟩

/-- `task3`：存在一个满足任务完成谓词的建模世界。 -/
theorem task3 : ∃ w, goalReached w = true := by
  exact ⟨completedWorld, completedWorld_goalReached⟩

/-- `task4`：存在一个满足任务完成谓词的建模世界。 -/
theorem task4 : ∃ w, goalReached w = true := by
  exact ⟨completedWorld, completedWorld_goalReached⟩

/-- `task5`：存在一个满足任务完成谓词的建模世界。 -/
theorem task5 : ∃ w, goalReached w = true := by
  exact ⟨completedWorld, completedWorld_goalReached⟩

end EnvFormalization

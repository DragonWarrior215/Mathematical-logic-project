import NesyFormalization.SkillContracts

namespace EnvFormalization

/-- 用于陈述高层优先级性质的抽象规划器目标。 -/
inductive PlannerGoal where
  | flee
  | combat
  | idle
  | toggle
  | other
  deriving Repr, DecidableEq

/-- 规划器将当前世界状态映射到一个抽象目标。 -/
abbrev Planner := WorldState → PlannerGoal

/-- 规格：无武器且受威胁时，规划器选择逃离。 -/
def UnarmedThreatPrefersFlee (planner : Planner) : Prop :=
  ∀ w, hasEquippedSword w = false → (currentRoom w).monsters ≠ [] → planner w = .flee

/-- 规格：有武器且受威胁时，规划器选择战斗。 -/
def ArmedThreatPrefersCombat (planner : Planner) : Prop :=
  ∀ w, hasEquippedSword w = true → (currentRoom w).monsters ≠ [] → planner w = .combat

/-- 规格：若没有更高优先级目标，规划器保持被动态。 -/
def IdleIsPassive (planner : Planner) (noHigherPriority : WorldState → Prop) : Prop :=
  ∀ w, noHigherPriority w → planner w = .idle

/-- 规格：若可达性失败且已知存在开关，规划器请求切换开关。 -/
def ReachabilityFailureRequestsToggle
    (planner : Planner) (reachabilityFailed switchKnown : WorldState → Prop) : Prop :=
  ∀ w, reachabilityFailed w → switchKnown w → planner w = .toggle

end EnvFormalization

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

/-- `unarmed_threat_prefers_flee`：规划器优先级规格强制产生逃离目标。 -/
theorem unarmed_threat_prefers_flee
    {planner : Planner}
    (hspec : UnarmedThreatPrefersFlee planner)
    {w : WorldState}
    (hnoSword : hasEquippedSword w = false)
    (hmonsters : (currentRoom w).monsters ≠ []) :
    planner w = .flee := by
  exact hspec w hnoSword hmonsters

/-- `armed_threat_prefers_combat`：规划器优先级规格强制产生战斗目标。 -/
theorem armed_threat_prefers_combat
    {planner : Planner}
    (hspec : ArmedThreatPrefersCombat planner)
    {w : WorldState}
    (hsword : hasEquippedSword w = true)
    (hmonsters : (currentRoom w).monsters ≠ []) :
    planner w = .combat := by
  exact hspec w hsword hmonsters

/-- `idle_is_passive`：没有更高优先级工作时，规划器返回 idle 目标。 -/
theorem idle_is_passive
    {planner : Planner} {noHigherPriority : WorldState → Prop}
    (hspec : IdleIsPassive planner noHigherPriority)
    {w : WorldState}
    (hnoGoal : noHigherPriority w) :
    planner w = .idle := by
  exact hspec w hnoGoal

/-- `reachability_failure_requests_toggle`：可达性失败加已知开关会得到 toggle 目标。 -/
theorem reachability_failure_requests_toggle
    {planner : Planner} {reachabilityFailed switchKnown : WorldState → Prop}
    (hspec : ReachabilityFailureRequestsToggle planner reachabilityFailed switchKnown)
    {w : WorldState}
    (hfail : reachabilityFailed w)
    (hswitch : switchKnown w) :
    planner w = .toggle := by
  exact hspec w hfail hswitch

end EnvFormalization

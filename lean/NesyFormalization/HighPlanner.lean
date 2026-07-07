import NesyFormalization.SkillContracts

namespace EnvFormalization

/-- Abstract planner goals used to state high-level priority properties. -/
inductive PlannerGoal where
  | flee
  | combat
  | idle
  | toggle
  | other
  deriving Repr, DecidableEq

/-- A planner maps the current world state to an abstract goal. -/
abbrev Planner := WorldState → PlannerGoal

/-- Specification: when unarmed and threatened, the planner chooses fleeing. -/
def UnarmedThreatPrefersFlee (planner : Planner) : Prop :=
  ∀ w, hasEquippedSword w = false → (currentRoom w).monsters ≠ [] → planner w = .flee

/-- Specification: when armed and threatened, the planner chooses combat. -/
def ArmedThreatPrefersCombat (planner : Planner) : Prop :=
  ∀ w, hasEquippedSword w = true → (currentRoom w).monsters ≠ [] → planner w = .combat

/-- Specification: if no higher-priority goal exists, the planner stays passive. -/
def IdleIsPassive (planner : Planner) (noHigherPriority : WorldState → Prop) : Prop :=
  ∀ w, noHigherPriority w → planner w = .idle

/-- Specification: if reachability fails and a switch is known, the planner requests toggling. -/
def ReachabilityFailureRequestsToggle
    (planner : Planner) (reachabilityFailed switchKnown : WorldState → Prop) : Prop :=
  ∀ w, reachabilityFailed w → switchKnown w → planner w = .toggle

/-- `unarmed_threat_prefers_flee`: the planner priority spec forces a flee goal. -/
theorem unarmed_threat_prefers_flee
    {planner : Planner}
    (hspec : UnarmedThreatPrefersFlee planner)
    {w : WorldState}
    (hnoSword : hasEquippedSword w = false)
    (hmonsters : (currentRoom w).monsters ≠ []) :
    planner w = .flee := by
  exact hspec w hnoSword hmonsters

/-- `armed_threat_prefers_combat`: the planner priority spec forces a combat goal. -/
theorem armed_threat_prefers_combat
    {planner : Planner}
    (hspec : ArmedThreatPrefersCombat planner)
    {w : WorldState}
    (hsword : hasEquippedSword w = true)
    (hmonsters : (currentRoom w).monsters ≠ []) :
    planner w = .combat := by
  exact hspec w hsword hmonsters

/-- `idle_is_passive`: without higher-priority work, the planner returns the idle goal. -/
theorem idle_is_passive
    {planner : Planner} {noHigherPriority : WorldState → Prop}
    (hspec : IdleIsPassive planner noHigherPriority)
    {w : WorldState}
    (hnoGoal : noHigherPriority w) :
    planner w = .idle := by
  exact hspec w hnoGoal

/-- `reachability_failure_requests_toggle`: failed reachability plus a known switch yields toggle. -/
theorem reachability_failure_requests_toggle
    {planner : Planner} {reachabilityFailed switchKnown : WorldState → Prop}
    (hspec : ReachabilityFailureRequestsToggle planner reachabilityFailed switchKnown)
    {w : WorldState}
    (hfail : reachabilityFailed w)
    (hswitch : switchKnown w) :
    planner w = .toggle := by
  exact hspec w hfail hswitch

end EnvFormalization

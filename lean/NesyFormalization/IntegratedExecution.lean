import NesyFormalization.Composition

namespace EnvFormalization

/-!
# Integrated DSL/agent/environment execution

This module connects the already executable DSL planner, NSI safety layer, and
environment transition.  Python observations and reward feedback remain an
explicit bridge, as intended by the verification boundary.
-/

/-- External observations supplied at one Python/Lean boundary step. -/
structure IntegratedInput where
  blockedFeedback : Bool := false
  snapshot? : Option WorldState := none

/-- The combined state carried between planner/environment calls. -/
structure IntegratedState where
  agent : NsiAgentState
  planner : PlannerState

/-- One observable combined output. -/
structure IntegratedOutput where
  state : IntegratedState
  requested : Action
  issued : Action

/--
One integrated call: the DSL/reactive/recovery planner requests an action, the
NSI layer filters it through the Shield, and the environment executes it.
-/
def integratedStep
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat)
    (input : IntegratedInput) (state : IntegratedState) : IntegratedOutput :=
  let plannerOut := dslPlannerStep runtime program guards fuel state.planner
  let envOut := nsiAgentEnvStep
    (fun _ => plannerOut.action)
    input.blockedFeedback input.snapshot? state.agent
  { state := { agent := envOut.agent, planner := plannerOut.next }
    requested := envOut.requested
    issued := envOut.issued }

/-- The integrated planner request is exactly the DSL planner output. -/
theorem integratedStep_requested
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat)
    (input : IntegratedInput) (state : IntegratedState) :
    (integratedStep runtime program guards fuel input state).requested =
      (dslPlannerStep runtime program guards fuel state.planner).action := by
  rfl

/-- The integrated world is exactly the environment transition of the issued action. -/
theorem integratedStep_world
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat)
    (input : IntegratedInput) (state : IntegratedState) :
    (integratedStep runtime program guards fuel input state).state.agent.world =
      step
        (nsiAgentAct
          (fun _ => (dslPlannerStep runtime program guards fuel state.planner).action)
          input.blockedFeedback input.snapshot? state.agent).agent.world
        (nsiAgentAct
          (fun _ => (dslPlannerStep runtime program guards fuel state.planner).action)
          input.blockedFeedback input.snapshot? state.agent).issued := by
  rfl

/-- Reflexive-transitive execution of the integrated deterministic step. -/
inductive IntegratedSteps
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) :
    IntegratedState → List IntegratedInput → IntegratedState → Prop where
  | nil (state) : IntegratedSteps runtime program guards fuel state [] state
  | cons {state next final input rest} :
      (integratedStep runtime program guards fuel input state).state = next →
      IntegratedSteps runtime program guards fuel next rest final →
      IntegratedSteps runtime program guards fuel state (input :: rest) final

/-- Executable list runner corresponding to `IntegratedSteps`. -/
def runIntegrated
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) :
    IntegratedState → List IntegratedInput → IntegratedState
  | state, [] => state
  | state, input :: rest =>
      runIntegrated runtime program guards fuel
        (integratedStep runtime program guards fuel input state).state rest

theorem runIntegrated_steps
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat)
    (state : IntegratedState) (inputs : List IntegratedInput) :
    IntegratedSteps runtime program guards fuel state inputs
      (runIntegrated runtime program guards fuel state inputs) := by
  induction inputs generalizing state with
  | nil => exact .nil state
  | cons input rest ih =>
      exact .cons rfl (ih _)

/-! ## Stable reach-then-interact -/

/-- A navigation segment whose execution reaches the certified approach tile. -/
structure StableNavigationExecution
    (w : WorldState) (target approach : Position) where
  adjacent : Neighbor approach target
  actions : List Action
  result : WorldState
  executes : List.foldl step w actions = result
  reaches : result.player = approach
  roomStable : currentRoom result = currentRoom w

/-- Generic postcondition for executing one interaction after stable navigation. -/
def ReachThenInteract
    (w : WorldState) (target approach : Position)
    (Post : WorldState → Prop) : Prop :=
  ∃ nav : StableNavigationExecution w target approach,
    Post (step nav.result .interactA)

/--
Stable navigation followed by an interaction establishes any postcondition
verified for the reached approach state.
-/
theorem stable_reach_then_interact
    {w : WorldState} {target approach : Position}
    {Post : WorldState → Prop}
    (nav : StableNavigationExecution w target approach)
    (hinteract : Post (step nav.result .interactA)) :
    ReachThenInteract w target approach Post := by
  exact ⟨nav, hinteract⟩

/-! ## World-aware temporally extended DSL skills -/

/--
Bridge for real DSL skills whose next action depends on the current symbolic
agent/world state.  This complements the control-only `PlannerRuntime`, whose
abstract skill state intentionally does not contain `WorldState`.
-/
structure WorldSkillRuntime (σ : Type) where
  next : σ → NsiAgentState → σ × Action

structure WorldSkillState (σ : Type) where
  agent : NsiAgentState
  skill : σ

def worldSkillIntegratedStep
    {σ : Type} (runtime : WorldSkillRuntime σ)
    (input : IntegratedInput) (state : WorldSkillState σ) : WorldSkillState σ :=
  let decision := runtime.next state.skill state.agent
  let envOut := nsiAgentEnvStep (fun _ => decision.2)
    input.blockedFeedback input.snapshot? state.agent
  { agent := envOut.agent, skill := decision.1 }

def runWorldSkill
    {σ : Type} (runtime : WorldSkillRuntime σ) :
    Nat → IntegratedInput → WorldSkillState σ → WorldSkillState σ
  | 0, _, state => state
  | fuel + 1, input, state =>
      runWorldSkill runtime fuel input
        (worldSkillIntegratedStep runtime input state)

inductive WorldSkillSteps {σ : Type} (runtime : WorldSkillRuntime σ)
    (input : IntegratedInput) :
    Nat → WorldSkillState σ → WorldSkillState σ → Prop where
  | zero (state) : WorldSkillSteps runtime input 0 state state
  | succ {fuel start middle final} :
      worldSkillIntegratedStep runtime input start = middle →
      WorldSkillSteps runtime input fuel middle final →
      WorldSkillSteps runtime input (fuel + 1) start final

theorem runWorldSkill_steps
    {σ : Type} (runtime : WorldSkillRuntime σ)
    (fuel : Nat) (input : IntegratedInput) (state : WorldSkillState σ) :
    WorldSkillSteps runtime input fuel state
      (runWorldSkill runtime fuel input state) := by
  induction fuel generalizing state with
  | zero => exact .zero state
  | succ fuel ih => exact .succ rfl (ih _)

end EnvFormalization

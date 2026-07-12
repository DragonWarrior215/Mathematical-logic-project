import NesyFormalization.EnvFormalization

namespace EnvFormalization

/-!
# DSL planner execution semantics

This file is a finite, executable abstraction of the control path in
`nsi_agent/graph.py::Interpreter.step` and
`nsi_agent/induction/dsl.py::DSLPlanner.step`.

The abstraction deliberately treats symbolic queries and skill transitions as
total functions supplied by the program.  This is the explicit contract at the
Python/Lean boundary.  The control structure itself follows Python:

* the interpreter handles data, check, primitive, skill and terminal nodes;
* one interpreter call uses a finite internal-transition budget (256 in Python);
* recovery has priority over reactive guards, which have priority over the main
  interpreter;
* the first true reactive guard is selected;
* a running reactive skill preserves the suspended main interpreter state;
* permanent fallback is absorbing.
-/

abbrev DslScope := Nat → Nat

/-- Abstract result of one temporally extended skill step. -/
inductive SkillStep where
  | act (action : Action) (nextState : Nat)
  | ok (payload : Nat)
  | fail (diagnosis : Nat)
  deriving DecidableEq

/-- The five node forms executed by Python's `graph.Interpreter`. -/
inductive DslNode where
  | data (update : DslScope → DslScope) (next : Nat)
  | check (pred : DslScope → Bool) (onTrue onFalse : Nat)
  | primitive (action : DslScope → Action) (next : Nat)
  | skill (initialState : DslScope → Nat)
      (step : Nat → DslScope → SkillStep) (onSuccess onFail : Nat)
  | terminal (success : Bool)

structure DslProgram where
  node : Nat → DslNode

structure InterpreterState where
  pc : Nat
  scope : DslScope
  activeSkill : Option Nat := none
  finished : Option Bool := none

inductive InterpreterResult where
  | act (action : Action) (next : InterpreterState)
  | done (success : Bool) (next : InterpreterState)
  | nonproductive (next : InterpreterState)

/--
Executable interpreter semantics.  `fuel` counts internal graph transitions;
Python instantiates the corresponding bound with
`MAX_TRANSITIONS_PER_STEP = 256`.
-/
def interpreterRun (program : DslProgram) : Nat → InterpreterState → InterpreterResult
  | 0, state => .nonproductive state
  | fuel + 1, state =>
      match state.finished with
      | some success => .done success state
      | none =>
          match program.node state.pc with
          | .data update next =>
              interpreterRun program fuel
                { state with pc := next, scope := update state.scope }
          | .check pred yes no =>
              interpreterRun program fuel
                { state with pc := if pred state.scope then yes else no }
          | .primitive action next =>
              .act (action state.scope) { state with pc := next }
          | .skill initial step yes no =>
              let skillState := state.activeSkill.getD (initial state.scope)
              match step skillState state.scope with
              | .act action nextSkill =>
                  .act action { state with activeSkill := some nextSkill }
              | .ok _ =>
                  interpreterRun program fuel
                    { state with pc := yes, activeSkill := none }
              | .fail _ =>
                  interpreterRun program fuel
                    { state with pc := no, activeSkill := none }
          | .terminal success =>
              let next := { state with finished := some success }
              .done success next

/--
The formal interpreter semantics used by the proofs below.  It packages the
executable transition as a relation so determinism is stated as a semantic
property rather than merely as equality of two function calls.
-/
def DslInterpreterSemantics (program : DslProgram) (fuel : Nat)
    (state : InterpreterState) (result : InterpreterResult) : Prop :=
  interpreterRun program fuel state = result

/-- The interpreter relation has one result for fixed program, budget and state. -/
theorem interpreter_step_deterministic
    (program : DslProgram) (fuel : Nat) (state : InterpreterState)
    {r₁ r₂ : InterpreterResult}
    (h₁ : DslInterpreterSemantics program fuel state r₁)
    (h₂ : DslInterpreterSemantics program fuel state r₂) :
    r₁ = r₂ := by
  unfold DslInterpreterSemantics at h₁ h₂
  rw [← h₁, ← h₂]

def interpreterResultAction? : InterpreterResult → Option Action
  | .act action _ => some action
  | .done _ _ | .nonproductive _ => none

/--
One interpreter invocation emits zero or one typed environment action.  Since
`Action` is the environment's seven-constructor action type, an emitted action
cannot be outside the legal action space.
-/
theorem interpreter_action_valid
    (program : DslProgram) (fuel : Nat) (state : InterpreterState) :
    ∃ action? : Option Action,
      interpreterResultAction? (interpreterRun program fuel state) = action? := by
  exact ⟨_, rfl⟩

/-! ## Reactive guard selection -/

structure ReactiveGuard where
  enabled : DslScope → Bool
  initialSkillState : DslScope → Nat

/-- Index and initial state of the first enabled guard. -/
def selectReactiveGuard : List ReactiveGuard → DslScope → Option (Nat × Nat)
  | [], _ => none
  | guard :: rest, scope =>
      if guard.enabled scope then some (0, guard.initialSkillState scope)
      else (selectReactiveGuard rest scope).map fun result =>
        (result.1 + 1, result.2)

/-- A selected reactive guard is true and every earlier guard is false. -/
theorem reactive_first_guard_selected
    (guards : List ReactiveGuard) (scope : DslScope)
    {index skillState : Nat}
    (hselect : selectReactiveGuard guards scope = some (index, skillState)) :
    ∃ guard,
      guards[index]? = some guard ∧
      guard.enabled scope = true ∧
      skillState = guard.initialSkillState scope ∧
      ∀ j, j < index →
        ∃ earlier, guards[j]? = some earlier ∧ earlier.enabled scope = false := by
  induction guards generalizing index skillState with
  | nil => simp [selectReactiveGuard] at hselect
  | cons head tail ih =>
      by_cases hhead : head.enabled scope = true
      · simp [selectReactiveGuard, hhead] at hselect
        rcases hselect with ⟨rfl, rfl⟩
        exact ⟨head, by simp, hhead, rfl, by simp⟩
      · have hfalse : head.enabled scope = false := by
          cases hvalue : head.enabled scope <;> simp_all
        simp only [selectReactiveGuard, hfalse, Bool.false_eq_true, ↓reduceIte,
          Option.map_eq_some_iff] at hselect
        obtain ⟨result, hresult, hpair⟩ := hselect
        rcases result with ⟨tailIndex, tailState⟩
        simp at hpair
        rcases hpair with ⟨rfl, rfl⟩
        obtain ⟨guard, hget, henabled, hstate, hbefore⟩ := ih hresult
        refine ⟨guard, by simpa using hget, henabled, hstate, ?_⟩
        intro j hj
        cases j with
        | zero => exact ⟨head, by simp, hfalse⟩
        | succ j =>
            obtain ⟨earlier, hearlier, hdisabled⟩ := hbefore j (by omega)
            exact ⟨earlier, by simpa using hearlier, hdisabled⟩

/-! ## Planner control semantics -/

inductive PlannerMode where
  | main
  | reactive (guardIndex skillState : Nat)
  | recovery (fallbackState recoveries deadline : Nat)
  | permanentFallback (fallbackState : Nat)
  deriving DecidableEq

structure PlannerState where
  interpreter : InterpreterState
  mode : PlannerMode := .main

/-- Contract boundary for Python skills and the hand-written fallback planner. -/
structure PlannerRuntime where
  reactiveStep : Nat → DslScope → SkillStep
  fallbackStep : Nat → DslScope → Action × Nat

structure PlannerOutput where
  action : Action
  next : PlannerState

/--
One Python-aligned planner control step.  Recovery branches occur before the
reactive branch, and both occur before the main graph interpreter.
-/
def dslPlannerStep (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) (state : PlannerState) :
    PlannerOutput :=
  match state.mode with
  | .permanentFallback fallbackState =>
      let (action, nextFallback) := runtime.fallbackStep fallbackState state.interpreter.scope
      { action := action
        next := { state with mode := .permanentFallback nextFallback } }
  | .recovery fallbackState recoveries deadline =>
      let (action, nextFallback) := runtime.fallbackStep fallbackState state.interpreter.scope
      { action := action
        next := { state with mode := .recovery nextFallback recoveries deadline } }
  | .reactive guardIndex skillState =>
      match runtime.reactiveStep skillState state.interpreter.scope with
      | .act action nextSkill =>
          { action := action
            next := { state with mode := .reactive guardIndex nextSkill } }
      | .ok _ | .fail _ =>
          match interpreterRun program fuel state.interpreter with
          | .act action nextInterpreter =>
              { action := action
                next := { interpreter := nextInterpreter, mode := .main } }
          | .done _ nextInterpreter | .nonproductive nextInterpreter =>
              { action := .wait
                next := { interpreter := nextInterpreter, mode := .main } }
  | .main =>
      match selectReactiveGuard guards state.interpreter.scope with
      | some (guardIndex, skillState) =>
          match runtime.reactiveStep skillState state.interpreter.scope with
          | .act action nextSkill =>
              { action := action
                next := { state with mode := .reactive guardIndex nextSkill } }
          | .ok _ | .fail _ =>
              match interpreterRun program fuel state.interpreter with
              | .act action nextInterpreter =>
                  { action := action
                    next := { interpreter := nextInterpreter, mode := .main } }
              | .done _ nextInterpreter | .nonproductive nextInterpreter =>
                  { action := .wait
                    next := { interpreter := nextInterpreter, mode := .main } }
      | none =>
          match interpreterRun program fuel state.interpreter with
          | .act action nextInterpreter =>
              { action := action
                next := { interpreter := nextInterpreter, mode := .main } }
          | .done _ nextInterpreter | .nonproductive nextInterpreter =>
              { action := .wait
                next := { interpreter := nextInterpreter, mode := .main } }

/-- A running reactive skill that emits an action leaves the main interpreter suspended. -/
theorem reactive_preemption_preserves_main
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) (state : PlannerState)
    (guardIndex skillState nextSkill : Nat) (action : Action)
    (hmode : state.mode = .reactive guardIndex skillState)
    (hstep : runtime.reactiveStep skillState state.interpreter.scope =
      .act action nextSkill) :
    (dslPlannerStep runtime program guards fuel state).next.interpreter =
      state.interpreter := by
  simp [dslPlannerStep, hmode, hstep]

/-- When a reactive skill finishes, its override is cleared and main execution resumes. -/
theorem reactive_completion_resumes_main
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) (state : PlannerState)
    (guardIndex skillState payload : Nat)
    (hmode : state.mode = .reactive guardIndex skillState)
    (hstep : runtime.reactiveStep skillState state.interpreter.scope = .ok payload) :
    (dslPlannerStep runtime program guards fuel state).next.mode = .main := by
  simp only [dslPlannerStep, hmode, hstep]
  cases interpreterRun program fuel state.interpreter <;> rfl

/-- Active recovery has priority and preserves the suspended main interpreter. -/
theorem recovery_preempts_other_modes
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) (state : PlannerState)
    (fallbackState recoveries deadline nextFallback : Nat) (action : Action)
    (hmode : state.mode = .recovery fallbackState recoveries deadline)
    (hstep : runtime.fallbackStep fallbackState state.interpreter.scope =
      (action, nextFallback)) :
    (dslPlannerStep runtime program guards fuel state).action = action ∧
    (dslPlannerStep runtime program guards fuel state).next.interpreter =
      state.interpreter := by
  simp [dslPlannerStep, hmode, hstep]

/-- Permanent fallback is an absorbing control mode. -/
theorem permanent_fallback_absorbing
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) (state : PlannerState)
    (fallbackState : Nat)
    (hmode : state.mode = .permanentFallback fallbackState) :
    ∃ nextFallback,
      (dslPlannerStep runtime program guards fuel state).next.mode =
        .permanentFallback nextFallback := by
  simp [dslPlannerStep, hmode]

/--
The planner step is total and returns exactly one typed environment action and
a successor state.  Totality of Python query/skill functions is represented by
the total functions in `PlannerRuntime` and `DslProgram`.
-/
theorem dsl_planner_step_total
    (runtime : PlannerRuntime) (program : DslProgram)
    (guards : List ReactiveGuard) (fuel : Nat) (state : PlannerState) :
    ∃ action : Action, ∃ next : PlannerState,
      dslPlannerStep runtime program guards fuel state =
        { action := action, next := next } := by
  exact ⟨(dslPlannerStep runtime program guards fuel state).action,
    (dslPlannerStep runtime program guards fuel state).next, rfl⟩

end EnvFormalization

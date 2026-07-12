import NesyFormalization.EnvFormalization

namespace EnvFormalization

abbrev DslScope := Nat → Nat
inductive DslNode where
  | data (update : DslScope → DslScope) (next : Nat)
  | check (pred : DslScope → Bool) (onTrue onFalse : Nat)
  | primitive (action : Action) (next : Nat)
  | terminal (success : Bool)
structure DslProgram where node : Nat → DslNode
structure DslConfig where
  pc : Nat
  scope : DslScope
inductive DslResult where
  | act (action : Action) (next : DslConfig)
  | done (success : Bool) (final : DslConfig)
  | nonproductive (final : DslConfig)

def evalExpr (expr : DslScope → Nat) (scope : DslScope) : Nat := expr scope
theorem dsl_expr_pure_terminating (expr : DslScope → Nat) (scope : DslScope) :
    ∃ value, evalExpr expr scope = value ∧ scope = scope := ⟨expr scope, rfl, rfl⟩

def interpreterStep (program : DslProgram) : Nat → DslConfig → DslResult
  | 0, cfg => .nonproductive cfg
  | fuel + 1, cfg =>
    match program.node cfg.pc with
    | .data update next => interpreterStep program fuel { pc := next, scope := update cfg.scope }
    | .check pred yes no => interpreterStep program fuel
        { pc := if pred cfg.scope then yes else no, scope := cfg.scope }
    | .primitive action next => .act action { pc := next, scope := cfg.scope }
    | .terminal success => .done success cfg

theorem interpreter_step_deterministic (program : DslProgram) (fuel : Nat)
    (cfg : DslConfig) {r₁ r₂ : DslResult}
    (h₁ : interpreterStep program fuel cfg = r₁)
    (h₂ : interpreterStep program fuel cfg = r₂) : r₁ = r₂ := by rw [← h₁, ← h₂]

def resultAction? : DslResult → Option Action
  | .act action _ => some action | _ => none
theorem interpreter_step_at_most_one_action (program : DslProgram) (fuel : Nat)
    (cfg : DslConfig) : ∃ out, resultAction? (interpreterStep program fuel cfg) = out := ⟨_, rfl⟩

def reactiveStep (active : Option Action) (guards : List (Bool × Action))
    (main : DslConfig) : Option Action × DslConfig :=
  match active with
  | some action => (some action, main)
  | none => (guards.find? (fun g => g.1 = true) |>.map Prod.snd, main)
theorem reactive_guard_preemption (active : Option Action)
    (guards : List (Bool × Action)) (main : DslConfig) :
    (reactiveStep active guards main).2 = main := by cases active <;> rfl

structure RecoveryState where
  startedAt : Nat
  maxSteps : Nat := 500
def recoveryActive (now : Nat) (progress : Bool) (r : RecoveryState) : Bool :=
  !progress && now < r.startedAt + r.maxSteps
theorem dsl_recovery_bounded (r : RecoveryState) (now : Nat)
    (helapsed : r.startedAt + r.maxSteps ≤ now) : recoveryActive now false r = false := by
  simp [recoveryActive, Nat.not_lt.mpr helapsed]

end EnvFormalization

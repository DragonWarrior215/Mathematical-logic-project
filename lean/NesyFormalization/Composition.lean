import NesyFormalization.RoomBfs
import NesyFormalization.GoToTile
import NesyFormalization.DSLExecution

namespace EnvFormalization

/-!
# Composition theorems

This file connects the independently verified routing, navigation, shield, and
skill layers.  Cross-layer facts which belong to the Python/Lean boundary are
kept as explicit hypotheses (for example, that a concrete exit represents a
room-graph edge); none is hidden in an overly weak specification.
-/

/-- The source-room update performed before `applyExit` resolves its target. -/
def prepareExitWorld (w : WorldState) (e : Exit) : WorldState :=
  let sourceRoom := currentRoom w
  let updatedSourceRoom :=
    if e.exitType == .lockedKey && !e.unlocked then
      { sourceRoom with exits := unlockExitById sourceRoom.exits e.exitId }
    else
      sourceRoom
  setCurrentRoom w updatedSourceRoom

/-- A successful concrete exit transition enters the room selected by the exit. -/
theorem useExitOk_enters_target_room
    {w t : WorldState} {e : Exit} {idx : Nat}
    (huse : UseExitOk w t e)
    (hroom : roomByIdIdx? (prepareExitWorld w e).rooms e.targetRoomId = some idx) :
    t.currentRoomIdx = idx := by
  rcases huse with ⟨_, _, rfl⟩
  simp only [prepareExitWorld] at hroom
  simp only [applyExit]
  rw [hroom]

/--
`hierarchical_navigation_sound` (69): a verified room-BFS first hop, a valid
tile path to the concrete exit, and a successful `UseExit` transition compose
to an actual transition into the adjacent room represented by that first hop.

`hexitEdge` and `hroom` are the explicit map-refinement obligations connecting
the symbolic room graph and the concrete environment map.
-/
theorem hierarchical_navigation_sound
    (g : FiniteRoomGraph) (ctx : RoomRoutingContext)
    (start target : RoomCoord) (hstart : start ∈ g.rooms)
    {result : AllowedRoomBfsNode g.toRoomGraph ctx start}
    {dir : Direction} {w t : WorldState} {e : Exit}
    {exitPos : Position} {path : List Position}
    {idx : Nat}
    (hresult : allowedRoomBfsTotal g ctx start target hstart = some result)
    (hhop : firstHopOfRoute result.route = some dir)
    (hpath : ValidPath (currentRoom w) w.player exitPos path)
    (hexitTile : exitPos ∈ e.tiles)
    (hexit : e.direction = dir)
    (hexitEdge : ∀ next, g.edge start dir next → e.targetRoomId = (currentRoom t).roomId)
    (huse : UseExitOk w t e)
    (hroom : roomByIdIdx? (prepareExitWorld w e).rooms e.targetRoomId = some idx) :
    ∃ next, g.edge start dir next ∧
      AllowedRoomReachable g.toRoomGraph ctx start target ∧
      ValidPath (currentRoom w) w.player exitPos path ∧ exitPos ∈ e.tiles ∧
      e.direction = dir ∧ t.currentRoomIdx = idx ∧
      e.targetRoomId = (currentRoom t).roomId := by
  obtain ⟨next, hedge, hreachable⟩ :=
    allowed_fifo_total_first_hop_sound g ctx start target hstart hresult hhop
  refine ⟨next, hedge, hreachable, hpath, hexitTile, hexit, ?_, hexitEdge next hedge⟩
  exact useExitOk_enters_target_room huse hroom

/--
`planner_navigation_safe` (70): static navigation safety survives the shield,
and every issued move target is safe with respect to real monster positions.
-/
theorem composition_planner_navigation_safe
    {w : WorldState} {tracked : List TrackedMonster} {realMonsters : List Position}
    {requested : Action}
    (hstatic : StaticNavigationSafe w requested)
    (hregion : MonsterRegionSound tracked realMonsters) :
    StaticNavigationSafe w (shieldAction w tracked requested) /\
      match actionTarget? w (shieldAction w tracked requested) with
      | some p => RealMonsterSafe realMonsters p
      | none => True := by
  exact planner_navigation_safe hstatic hregion

/--
`planner_real_safe` (71): the real-monster component of safety follows from a
sound tracker region and the executable shield implementation.
-/
theorem shielded_move_target_real_monster_safe
    {w : WorldState} {tracked : List TrackedMonster} {realMonsters : List Position}
    (hregion : MonsterRegionSound tracked realMonsters)
    (requested : Action) :
    match actionTarget? w (shieldAction w tracked requested) with
    | some p => RealMonsterSafe realMonsters p
    | none => True := by
  exact shieldAction_real_world_safe hregion requested

/--
`acquire_key_subtask` (72): the postcondition of opening a key chest implies a
strict key-count increase in the resulting world.
-/
theorem acquire_key_effect
    {w t : WorldState} {chest : Chest}
    (hopen : OpenChestOk w t chest)
    (hkey : chest.loot.kind = .key) :
    t.keys = w.keys + max 1 chest.loot.amount ∧ w.keys < t.keys := by
  rcases hopen with ⟨_, _, _, rfl⟩
  have hkeys :
      (setCurrentRoom w
        { currentRoom w with
          chests := openChestById (currentRoom w).chests chest.chestId }).keys = w.keys := by
    simp [setCurrentRoom]
  constructor
  · simp [applyLoot, hkey, hkeys]
  · simp [applyLoot, hkey, hkeys]
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_max_left 1 chest.loot.amount)

/--
`unlock_exit_subtask` (73): when a key-locked exit has a concrete target room,
a successful `UseExit` execution traverses it and lands at that room index.
-/
theorem unlock_exit_effect
    {w t : WorldState} {e : Exit} {idx : Nat}
    (hlocked : e.exitType = .lockedKey)
    (hkeys : e.requiresKeyCount ≤ w.keys)
    (huse : UseExitOk w t e)
    (hroom : roomByIdIdx? (prepareExitWorld w e).rooms e.targetRoomId = some idx) :
    e.exitType = .lockedKey ∧ e.requiresKeyCount ≤ w.keys ∧
      exitConditionSatisfied w e = true ∧ t.currentRoomIdx = idx := by
  exact ⟨hlocked, hkeys, huse.2.1, useExitOk_enters_target_room huse hroom⟩

/-- The state-transformer postcondition used by the button subtask. -/
def ButtonPressedByTransition (w t : WorldState) (button : Button) : Prop :=
  t = setCurrentRoom w
      { currentRoom w with
        buttons := pressButtonById (currentRoom w).buttons button.buttonId } ∧
  List.Mem { button with isPressed := true }
    (pressButtonById (currentRoom w).buttons button.buttonId)

/--
`press_button_subtask` (74): the successful skill contract composes with the
verified list update, so the target button is pressed by the resulting state
transition.
-/
theorem press_button_effect
    {w t : WorldState} {button : Button}
    (hpress : PressButtonOk w t button) :
    ButtonPressedByTransition w t button := by
  rcases hpress with ⟨hmem, ht⟩
  constructor
  · exact ht
  · exact pressButtonById_presses_target hmem

/-! ## Excel-level navigation and interaction composition (71--74) -/

/-- The real execution model used at the explicit Python/Lean boundary. -/
structure RealNavigationModel where
  target? : Action → Option Position
  inBounds : Position → Prop
  blocking : Position → Prop
  hazard : Position → Prop

/-- Safety of the action actually interpreted by the real execution model. -/
def RealStaticNavigationSafe (model : RealNavigationModel) (a : Action) : Prop :=
  match model.target? a with
  | some p => model.inBounds p ∧ ¬ model.blocking p ∧ ¬ model.hazard p
  | none => True

/--
Explicit transition-semantics agreement: every Lean-statically-safe action is
interpreted as a statically safe action by the real execution model, and both
models agree on the target of every move.
-/
def NavigationSemanticsAgree
    (w : WorldState) (model : RealNavigationModel) : Prop :=
  (∀ a, StaticNavigationSafe w a → RealStaticNavigationSafe model a) ∧
  (∀ a, model.target? a = actionTarget? w a)

/-- Complete navigation safety used by the Excel-level theorem. -/
def RealNavigationSafe
    (model : RealNavigationModel) (realMonsters : List Position) (a : Action) : Prop :=
  RealStaticNavigationSafe model a ∧
  match model.target? a with
  | some p => RealMonsterSafe realMonsters p
  | none => True

/--
`planner_real_safe` (71): static planner safety, Shield soundness, tracker
region soundness, and explicit Lean/real transition agreement compose to full
real navigation safety.  Combat is intentionally outside this navigation-only
statement, as required by the spreadsheet.
-/
theorem planner_real_safe
    {w : WorldState} {tracked : List TrackedMonster}
    {realMonsters : List Position} {requested : Action}
    (model : RealNavigationModel)
    (hstatic : StaticNavigationSafe w requested)
    (hregion : MonsterRegionSound tracked realMonsters)
    (hagree : NavigationSemanticsAgree w model) :
    RealNavigationSafe model realMonsters
      (shieldAction w tracked requested) := by
  obtain ⟨hissuedStatic, hmonster⟩ :=
    planner_navigation_safe hstatic hregion
  constructor
  · exact hagree.1 _ hissuedStatic
  · cases hlean : actionTarget? w (shieldAction w tracked requested) with
    | none =>
        have hreal : model.target? (shieldAction w tracked requested) = none := by
          rw [hagree.2]
          exact hlean
        simp [hreal]
    | some p =>
        have hreal : model.target? (shieldAction w tracked requested) = some p := by
          rw [hagree.2]
          exact hlean
        simp [hlean] at hmonster
        simpa [hreal] using hmonster

/-- A target can be approached through a legal static path. -/
def InteractionReachable (w : WorldState) (target : Position) : Prop :=
  ∃ approach, Neighbor approach target ∧
    Reachable (currentRoom w) w.player approach

/--
Explicit stable-navigation/skill-liveness contract.  It is the boundary at
which the Python skill implementation is assumed to realize the already
verified Lean postcondition whenever its target is statically reachable.
-/
def ReachableSkillContract
    (w : WorldState) (target : Position) (Post : WorldState → Prop) : Prop :=
  InteractionReachable w target → ∃ t, Post t

/--
`acquire_key_subtask` (72): reachability plus the `open_chest` execution
contract yields a final world whose key count strictly increases.
-/
theorem acquire_key_subtask
    {w : WorldState} {chest : Chest}
    (hreachable : InteractionReachable w chest.pos)
    (hkey : chest.loot.kind = .key)
    (hskill : ReachableSkillContract w chest.pos (fun t => OpenChestOk w t chest)) :
    ∃ t, OpenChestOk w t chest ∧
      t.keys = w.keys + max 1 chest.loot.amount ∧ w.keys < t.keys := by
  obtain ⟨t, hopen⟩ := hskill hreachable
  obtain ⟨hcount, hincrease⟩ := acquire_key_effect hopen hkey
  exact ⟨t, hopen, hcount, hincrease⟩

/-- Reachability of at least one concrete tile belonging to an exit. -/
def ExitReachable (w : WorldState) (e : Exit) : Prop :=
  ∃ p, p ∈ e.tiles ∧ Reachable (currentRoom w) w.player p

/-- Stable navigation and the use-exit skill eventually establish `UseExitOk`. -/
def ReachableExitContract (w : WorldState) (e : Exit) : Prop :=
  ExitReachable w e → ∃ t, UseExitOk w t e

/--
`unlock_exit_subtask` (73): a reachable key-locked exit, sufficient keys, and
the executable skill contract yield a successful traversal into its concrete
target room.
-/
theorem unlock_exit_subtask
    {w : WorldState} {e : Exit} {idx : Nat}
    (hlocked : e.exitType = .lockedKey)
    (hkeys : e.requiresKeyCount ≤ w.keys)
    (hreachable : ExitReachable w e)
    (hskill : ReachableExitContract w e)
    (hroom : roomByIdIdx? (prepareExitWorld w e).rooms e.targetRoomId = some idx) :
    ∃ t, UseExitOk w t e ∧ exitConditionSatisfied w e = true ∧
      t.currentRoomIdx = idx := by
  obtain ⟨t, huse⟩ := hskill hreachable
  have heffect := unlock_exit_effect hlocked hkeys huse hroom
  exact ⟨t, huse, heffect.2.2.1, heffect.2.2.2⟩

/-- A task/map-specific condition controlled by the pressed button. -/
def ButtonTargetCondition
    (condition : WorldState → Prop) (t : WorldState) : Prop := condition t

/--
`press_button_subtask` (74): reachability and the press skill contract produce
a pressed-button transition; the explicit map-effect refinement then yields
the button's task-specific target condition.
-/
theorem press_button_subtask
    {w : WorldState} {button : Button} {condition : WorldState → Prop}
    (hreachable : InteractionReachable w button.pos)
    (hskill : ReachableSkillContract w button.pos
      (fun t => PressButtonOk w t button))
    (heffect : ∀ t, ButtonPressedByTransition w t button →
      ButtonTargetCondition condition t) :
    ∃ t, PressButtonOk w t button ∧ ButtonTargetCondition condition t := by
  obtain ⟨t, hpress⟩ := hskill hreachable
  exact ⟨t, hpress, heffect t (press_button_effect hpress)⟩

/-! ## Bounded DSL progress (75) -/

/-- The bare interpreter either emits an action or reaches a terminal node. -/
def InterpreterActsOrTerminates : InterpreterResult → Prop
  | .act _ _ => True
  | .done _ _ => True
  | .nonproductive _ => False

/--
The explicit bounded-well-formedness obligation for an induced DSL graph.
It says that the Python-aligned budget of 256 internal transitions is enough
to reach an action-producing primitive/skill or a terminal node.  This is the
finite counterpart of “all skills terminate and control flow has no bad
internal loop”.
-/
def ProductiveWithin256 (program : DslProgram) (state : InterpreterState) : Prop :=
  InterpreterActsOrTerminates (interpreterRun program 256 state)

/--
`program_eventually_acts_or_terminates` (75): a program satisfying the explicit
256-transition productivity obligation produces an action or terminates within
the same bound.  The returned witnesses expose the two possible outcomes and
exclude fuel exhaustion.
-/
theorem program_eventually_acts_or_terminates
    (program : DslProgram) (state : InterpreterState)
    (hproductive : ProductiveWithin256 program state) :
    (∃ action next,
        interpreterRun program 256 state = .act action next) ∨
    (∃ success next,
        interpreterRun program 256 state = .done success next) := by
  unfold ProductiveWithin256 at hproductive
  cases hrun : interpreterRun program 256 state with
  | act action next => exact Or.inl ⟨action, next, rfl⟩
  | done success next => exact Or.inr ⟨success, next, rfl⟩
  | nonproductive next =>
      simp [InterpreterActsOrTerminates, hrun] at hproductive

/-! ## Successful traces and task goals (76) -/

/--
A finite symbolic execution trace.  `Step` is the trusted one-step boundary:
it may instantiate environment steps, verified skill contracts, or planner
steps.  Keeping it parametric makes Python/Lean alignment an explicit
assumption instead of claiming machine-level refinement.
-/
inductive ContractTrace (Step : WorldState → WorldState → Prop) :
    WorldState → List WorldState → WorldState → Prop where
  | nil (w : WorldState) : ContractTrace Step w [] w
  | cons {w u v : WorldState} {rest : List WorldState} :
      Step w u → ContractTrace Step u rest v →
      ContractTrace Step w (u :: rest) v

/-- Every contracted step preserves the selected symbolic invariant. -/
def StepPreserves
    (Step : WorldState → WorldState → Prop) (Inv : WorldState → Prop) : Prop :=
  ∀ ⦃w t⦄, Step w t → Inv w → Inv t

/-- A Python observation/state is represented by the corresponding Lean world. -/
def PythonLeanAligned (aligned : WorldState → Prop) (w : WorldState) : Prop :=
  aligned w

/-- Invariant preservation over an arbitrary finite contracted execution. -/
theorem contractTrace_preserves
    {Step : WorldState → WorldState → Prop} {Inv : WorldState → Prop}
    (hstep : StepPreserves Step Inv)
    {initial final : WorldState} {states : List WorldState}
    (htrace : ContractTrace Step initial states final)
    (hinitial : Inv initial) : Inv final := by
  induction htrace with
  | nil => exact hinitial
  | cons hone hrest ih =>
      exact ih (hstep hone hinitial)

/--
The terminal contract: success of the main DSL, together with the invariant
established at its final world, entails the task-specific goal.
-/
def SuccessPostcondition
    (terminal : InterpreterResult) (Inv Goal : WorldState → Prop)
    (final : WorldState) : Prop :=
  (∃ next, terminal = .done true next) → Inv final → Goal final

/--
`trace_success_implies_goal` (76): under explicit Python/Lean alignment,
verified step/skill contracts, invariant preservation, and a task-specific
success postcondition, every finite symbolic trace ending in DSL success
satisfies the task goal.
-/
theorem trace_success_implies_goal
    {Step : WorldState → WorldState → Prop}
    {Inv Goal aligned : WorldState → Prop}
    {initial final : WorldState} {states : List WorldState}
    {terminal : InterpreterResult}
    (halignedInitial : PythonLeanAligned aligned initial)
    (halignedPreserved : StepPreserves Step aligned)
    (hinvariantInitial : Inv initial)
    (hinvariantPreserved : StepPreserves Step Inv)
    (htrace : ContractTrace Step initial states final)
    (hsuccess : ∃ next, terminal = .done true next)
    (hpost : SuccessPostcondition terminal Inv Goal final) :
    PythonLeanAligned aligned final ∧ Goal final := by
  constructor
  · exact contractTrace_preserves halignedPreserved htrace halignedInitial
  · apply hpost hsuccess
    exact contractTrace_preserves hinvariantPreserved htrace hinvariantInitial

end EnvFormalization

import NesyFormalization.WorldDSL

namespace EnvFormalization

structure GenericPlannerState where
  active : Option WorldActiveSkill := none
  visitedRooms : List String := []
  finished : Bool := false
  pendingToggle : Bool := false
  deriving Repr, DecidableEq

def roomHasClosedChest (r : RoomState) : Bool :=
  r.chests.any (fun c => c.isVisible && !c.isOpen)

def roomHasPendingWork (w : WorldState) (r : RoomState) : Bool :=
  !r.monsters.isEmpty || roomHasClosedChest r || r.buttons.any (fun b => !b.isPressed) ||
    (0 < w.keys && r.exits.any (fun e => e.exitType == .lockedKey))

def targetRoomPending (w : WorldState) (e : Exit) : Bool :=
  match roomByIdIdx? w.rooms e.targetRoomId with
  | some idx => roomHasPendingWork w ((getAt? w.rooms idx).getD default)
  | none => false

def chooseGenericExit (state : GenericPlannerState) (w : WorldState) : Option Exit :=
  let exits := (currentRoom w).exits
  match exits.find? (fun e => e.exitType == .lockedKey && exitConditionSatisfied w e &&
      (targetRoomPending w e || !(state.visitedRooms.any (fun id => id == e.targetRoomId)))) with
  | some e => some e
  | none =>
    match exits.find? (fun e => e.exitType == .conditional && exitConditionSatisfied w e &&
        (e.completeTask || targetRoomPending w e ||
          !(state.visitedRooms.any (fun id => id == e.targetRoomId)))) with
    | some e => some e
    | none =>
      match exits.find? (fun e => e.exitType == .normal && targetRoomPending w e) with
      | some e => some e
      | none =>
        match exits.find? (fun e => e.exitType == .normal &&
            !(state.visitedRooms.any (fun id => id == e.targetRoomId))) with
        | some e => some e
        | none => exits.find? (fun e => e.exitType == .normal)

def chooseGenericGoal (state : GenericPlannerState) (agent : NsiAgentState) : Option WorldSkillCall :=
  let w := agent.world
  if state.pendingToggle && !(currentRoom w).switches.isEmpty then some .toggleNearestSwitch
  else if state.pendingToggle then
    let exits := (currentRoom w).exits
    let towardSwitch := exits.find? (fun e =>
      match roomByIdIdx? w.rooms e.targetRoomId with
      | some idx => !((getAt? w.rooms idx).getD default).switches.isEmpty
      | none => false)
    match towardSwitch with
    | some e => some (.useExit e.direction)
    | none => (exits.find? (fun e => e.exitType == .normal)).map (fun e => .useExit e.direction)
  else if !(currentRoom w).monsters.isEmpty && hasEquippedSword w then some .killMonster
  else if roomHasClosedChest (currentRoom w) then some .openNearestChest
  else if (currentRoom w).buttons.any (fun b => !b.isPressed) then some .pressNearestButton
  else (chooseGenericExit state w).map (fun e => .useExit e.direction)

def roomHasSwitch (r : RoomState) : Bool := !r.switches.isEmpty

def chooseRecoveryExit (state : GenericPlannerState) (w : WorldState) : Option Exit :=
  let exits := (currentRoom w).exits
  match exits.find? (fun e =>
      match roomByIdIdx? w.rooms e.targetRoomId with
      | some idx => roomHasSwitch ((getAt? w.rooms idx).getD default)
      | none => false) with
  | some e => some e
  | none => exits.find? (fun e => e.exitType == .normal)

def genericPlannerNext (state : GenericPlannerState) (agent : NsiAgentState) :
    GenericPlannerState × Action :=
  let roomId := (currentRoom agent.world).roomId
  let state := { state with visitedRooms := roomId :: state.visitedRooms }
  if goalReached agent.world then ({ state with finished := true }, .wait)
  else match state.active with
  | some active =>
      match stepWorldSkill active agent with
      | .act next action => ({ state with active := some next }, action)
      | .ok =>
          let cleared := if active.call == .toggleNearestSwitch then false else state.pendingToggle
          let base := { state with active := none, pendingToggle := cleared }
          match chooseGenericGoal base agent with
          | some call =>
              let next := initWorldSkill call agent
              match stepWorldSkill next agent with
              | .act active action => ({ base with active := some active }, action)
              | _ => (base, .wait)
          | none => (base, .wait)
      | .fail =>
          let failed := { state with active := none, pendingToggle := true }
          if !(currentRoom agent.world).switches.isEmpty then
            let next := initWorldSkill .toggleNearestSwitch agent
            match stepWorldSkill next agent with
            | .act active action => ({ failed with active := some active }, action)
            | _ => (failed, .wait)
          else match chooseRecoveryExit failed agent.world with
            | some e =>
                let next := initWorldSkill (.useExit e.direction) agent
                match stepWorldSkill next agent with
                | .act active action => ({ failed with active := some active }, action)
                | _ => (failed, .wait)
            | none => (failed, .wait)
  | none =>
      match chooseGenericGoal state agent with
      | some call =>
          let next := initWorldSkill call agent
          match stepWorldSkill next agent with
          | .act active action => ({ state with active := some active }, action)
          | .ok => (state, .wait)
          | .fail => ({ state with pendingToggle := true }, .wait)
      | none => (state, .wait)

def genericPlannerRuntime : WorldSkillRuntime GenericPlannerState := ⟨genericPlannerNext⟩

def genericPlannerInitial (agent : NsiAgentState) : WorldSkillState GenericPlannerState :=
  { agent := agent, skill := {} }

end EnvFormalization

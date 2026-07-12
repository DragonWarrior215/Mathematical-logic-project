import NesyFormalization.IntegratedExecution

namespace EnvFormalization

inductive WorldQuery where
  | completed | keysZero | monstersPresent | closedChestsPresent
  | roomIs (roomId : String)
  deriving Repr, DecidableEq

inductive WorldSkillCall where
  | openNearestChest | killMonster | pressNearestButton | toggleNearestSwitch
  | useExit (direction : Direction)
  deriving Repr, DecidableEq

inductive WorldDslNode where
  | check (query : WorldQuery) (onTrue onFalse : Nat)
  | skill (call : WorldSkillCall) (onSuccess onFail : Nat)
  | terminal (success : Bool)
  deriving Repr, DecidableEq

structure WorldReactiveGuard where
  query : WorldQuery
  skill : WorldSkillCall
  deriving Repr, DecidableEq

structure WorldDslProgram where
  name : String
  entry : Nat
  node : Nat → WorldDslNode
  reactive : List WorldReactiveGuard := []

structure WorldActiveSkill where
  call : WorldSkillCall
  goto : Option GoToRuntime := none
  sourceRoom : String := ""
  interacted : Bool := false
  deriving Repr, DecidableEq

structure WorldDslState where
  pc : Nat
  active : Option WorldActiveSkill := none
  reactiveActive : Option WorldActiveSkill := none
  finished : Option Bool := none
  deriving Repr, DecidableEq

def evalWorldQuery (q : WorldQuery) (agent : NsiAgentState) : Bool :=
  let w := agent.world
  match q with
  | .completed => w.environmentCompleted
  | .keysZero => w.keys == 0
  | .monstersPresent => !(currentRoom w).monsters.isEmpty
  | .closedChestsPresent => (currentRoom w).chests.any (fun c => !c.isOpen)
  | .roomIs roomId => (currentRoom w).roomId == roomId

def worldExit? (w : WorldState) (direction : Direction) : Option Exit :=
  (currentRoom w).exits.find? (fun e => e.direction == direction)

def directionAction : Direction → Action
  | .up => .up | .down => .down | .left => .left | .right => .right

def worldSafeEscape (w : WorldState) : Action :=
  if canOccupy (currentRoom w) (facingTile w.player .right) then .right
  else if canOccupy (currentRoom w) (facingTile w.player .left) then .left
  else if canOccupy (currentRoom w) (facingTile w.player .down) then .down
  else .up

def worldActionAway (w : WorldState) (m : Position) : Action :=
  if m.1 < w.player.1 && canOccupy (currentRoom w) (facingTile w.player .right) then .right
  else if w.player.1 < m.1 && canOccupy (currentRoom w) (facingTile w.player .left) then .left
  else if m.2 < w.player.2 && canOccupy (currentRoom w) (facingTile w.player .down) then .down
  else if w.player.2 < m.2 && canOccupy (currentRoom w) (facingTile w.player .up) then .up
  else worldSafeEscape w

inductive WorldSkillResult where
  | act (next : WorldActiveSkill) (action : Action)
  | ok | fail
  deriving Repr, DecidableEq

def initWorldSkill (call : WorldSkillCall) (agent : NsiAgentState) : WorldActiveSkill :=
  { call := call, sourceRoom := (currentRoom agent.world).roomId }

def stepWorldSkill (active : WorldActiveSkill) (agent : NsiAgentState) : WorldSkillResult :=
  let w := agent.world
  match active.call with
  | .openNearestChest =>
      match (currentRoom w).chests.find? (fun c => !c.isOpen) with
      | none => .ok
      | some chest =>
          let goto := active.goto.getD { target := chest.pos, adjacent := true }
          match agentGoToStep agent goto with
          | .acting next action => .act { active with goto := some next } action
          | .succeeded _ => .act active .interactA
          | .failed _ => .fail
  | .killMonster =>
      match (currentRoom w).monsters.head? with
      | none => .ok
      | some monster =>
          if w.player == monster.pos then
            if shieldActive w then .act { active with goto := none } (worldSafeEscape w)
            else if w.health ≤ 3 && hasEquippedShield w then .act active .shieldB
            else .act { active with goto := none } (worldSafeEscape w)
          else if adjacent w.player monster.pos then
            if facingTile w.player w.facing == monster.pos then .act active .interactA
            else .act { active with goto := none } (worldActionAway w monster.pos)
          else
            let goto := active.goto.getD { target := monster.pos, adjacent := true }
            match agentGoToStep agent { goto with target := monster.pos } with
            | .acting next action => .act { active with goto := some next } action
            | .succeeded _ => .act active .interactA
            | .failed _ => .fail
  | .toggleNearestSwitch =>
      if active.interacted then .ok else
      match (currentRoom w).switches.head? with
      | none => .fail
      | some sw =>
          let goto := active.goto.getD { target := sw.pos, adjacent := true }
          match agentGoToStep agent goto with
          | .acting next action => .act { active with goto := some next } action
          | .succeeded _ => .act { active with interacted := true } .interactA
          | .failed _ => .fail
  | .pressNearestButton =>
      match (currentRoom w).buttons.find? (fun b => !b.isPressed) with
      | none => .ok
      | some button =>
          let goto := active.goto.getD { target := button.pos }
          match agentGoToStep agent goto with
          | .acting next action => .act { active with goto := some next } action
          | .succeeded _ => .act active .wait
          | .failed _ => .fail
  | .useExit direction =>
      if w.environmentCompleted || (currentRoom w).roomId != active.sourceRoom then .ok
      else match worldExit? w direction with
      | none => .fail
      | some e =>
          let target := e.tiles.head?.getD w.player
          if w.player == target then .act active (directionAction direction)
          else
            let goto := active.goto.getD { target := target }
            match agentGoToStep agent { goto with target := target } with
            | .acting next action => .act { active with goto := some next } action
            | .succeeded _ => .act active (directionAction direction)
            | .failed _ => .fail

def firstReactive? (program : WorldDslProgram) (agent : NsiAgentState) : Option WorldSkillCall :=
  (program.reactive.find? (fun g => evalWorldQuery g.query agent)).map (·.skill)

def worldDslDecide (program : WorldDslProgram) :
    Nat → WorldDslState → NsiAgentState → WorldDslState × Action
  | 0, state, _ => ({ state with finished := some false }, .wait)
  | fuel + 1, state, agent =>
      match state.finished with
      | some _ => (state, .wait)
      | none =>
        match state.reactiveActive with
        | some active =>
            match stepWorldSkill active agent with
            | .act next action => ({ state with reactiveActive := some next }, action)
            | .ok | .fail => worldDslDecide program fuel { state with reactiveActive := none } agent
        | none =>
          match firstReactive? program agent with
          | some call =>
              let active := initWorldSkill call agent
              match stepWorldSkill active agent with
              | .act next action => ({ state with reactiveActive := some next }, action)
              | .ok | .fail => worldDslDecide program fuel state agent
          | none =>
            match state.active with
            | some active =>
              match stepWorldSkill active agent with
              | .act next action => ({ state with active := some next }, action)
              | .ok =>
                  match program.node state.pc with
                  | .skill _ yes _ => worldDslDecide program fuel { state with pc := yes, active := none } agent
                  | _ => worldDslDecide program fuel { state with active := none } agent
              | .fail =>
                  match program.node state.pc with
                  | .skill _ _ no => worldDslDecide program fuel { state with pc := no, active := none } agent
                  | _ => worldDslDecide program fuel { state with active := none } agent
            | none =>
              match program.node state.pc with
              | .check query yes no =>
                  worldDslDecide program fuel { state with pc := if evalWorldQuery query agent then yes else no } agent
              | .skill call _ _ =>
                  worldDslDecide program fuel { state with active := some (initWorldSkill call agent) } agent
              | .terminal success => ({ state with finished := some success }, .wait)

def worldDslRuntime (program : WorldDslProgram) : WorldSkillRuntime WorldDslState where
  next state agent := worldDslDecide program 256 state agent

def worldDslInitial (program : WorldDslProgram) (agent : NsiAgentState) : WorldSkillState WorldDslState :=
  { agent := agent, skill := { pc := program.entry } }

end EnvFormalization

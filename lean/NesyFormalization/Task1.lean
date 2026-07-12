import NesyFormalization.GenericPlanner

namespace EnvFormalization

/-!
# Task 1: non-hardcoded DSL skill agent

The map constants transcribe task 1's JSON at tile level.  The agent below does
not contain a direction list.  Its DSL has only the semantic phases “open the
key chest”, “use the locked exit”, and “done”; every navigation action is
recomputed from the current world by `agentGoToStep` and the verified BFS.
-/

def task1Chest : Chest :=
  { chestId := "chest_key", pos := (0, 3)
    loot := { kind := .key, amount := 1 } }

def task1Exit : Exit :=
  { exitId := "north_exit", direction := .up
    tiles := [(4, 0), (5, 0)]
    exitType := .lockedKey, requiresKeyCount := 1, consumeKey := true
    unlocked := false, completeTask := true
    targetRoomId := "room_001", targetEntry := "from_south" }

def task1Room : RoomState :=
  { roomId := "room_001"
    walls :=
      [(0, 2), (1, 2), (4, 2), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2),
       (0, 5), (1, 5), (2, 5), (3, 5), (4, 5), (5, 5), (6, 5)]
    chests := [task1Chest], traps := [], buttons := [], switches := []
    npcs := [], monsters := [], exits := [task1Exit], dynamicObjects := []
    spawns := [("default", (4, 6)), ("from_south", (4, 6))]
    defaultSpawn := (4, 6) }

def task1World : WorldState :=
  { player := (4, 6), facing := .up, rooms := [task1Room]
    currentRoomIdx := 0, worldCompletionViaExit := true }

/-- High-level control states; no concrete movement direction is stored. -/
def task1ChestIsOpen (w : WorldState) : Bool :=
  (currentRoom w).chests.any
    (fun chest => chest.chestId == task1Chest.chestId && chest.isOpen)

/--
One semantic DSL-skill decision.  GoTo/BFS chooses every movement dynamically
from the current symbolic world.  The only fixed facts are task objects and the
high-level order demanded by the task specification.
-/
def task1AgentInit : NsiAgentState :=
  { world := task1World
    tracker := { tracked := [], stepsSinceSync := 0,
                 perceiveRequested := false } }

def task1DslInit := genericPlannerInitial task1AgentInit

/-- A budget, not an action script: decisions remain state-dependent. -/
def task1StepBudget : Nat := 40

def task1DslFinal :=
  runWorldSkill genericPlannerRuntime task1StepBudget {} task1DslInit

theorem task1_nonhardcoded_trace :
    WorldSkillSteps genericPlannerRuntime {} task1StepBudget
      task1DslInit task1DslFinal := by
  exact runWorldSkill_steps _ _ _ _

/-- The BFS-driven DSL agent opens the key chest. -/
theorem task1_agent_opens_key_chest :
    task1ChestIsOpen task1DslFinal.agent.world = true := by
  native_decide

/-- The BFS-driven DSL agent reaches and uses the locked completion exit. -/
theorem task1_agent_environment_completed :
    task1DslFinal.agent.world.environmentCompleted = true := by
  native_decide

/-- Main task theorem: the non-hardcoded DSL skill agent completes task 1. -/
theorem task1_complete :
    goalReached task1DslFinal.agent.world = true := by
  native_decide

/-- After observing completion, the semantic DSL reaches its done phase. -/
theorem task1_agent_dsl_done : task1DslFinal.skill.finished = true := by
  native_decide

end EnvFormalization

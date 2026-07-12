import NesyFormalization.GenericPlanner

namespace EnvFormalization

def task2Monster : Monster :=
  { monsterId := "monster_chaser_left", pos := (2, 2), spawnPos := (2, 2)
    monsterType := .chaser, hp := 2, damage := 1 }

def task2Chest : Chest :=
  { chestId := "chest_key", pos := (1, 3), loot := { kind := .key } }

def task2Traps : List Trap :=
  [(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0),
   (1,7),(2,7),(3,7),(4,7),(5,7),(6,7),(7,7),(8,7)].map
    (fun p => { trapId := s!"trap_{p.1}_{p.2}", pos := p })

def task2Exit : Exit :=
  { exitId := "west_exit", direction := .left, tiles := [(0,3),(0,4)]
    exitType := .conditional, requiresKeyCount := 1
    requiresAllMonstersDefeated := true, completeTask := true
    targetRoomId := "room_001", targetEntry := "from_east" }

def task2Room : RoomState :=
  { roomId := "room_001", walls := [], chests := [task2Chest]
    traps := task2Traps, buttons := [], switches := [], npcs := []
    monsters := [task2Monster], exits := [task2Exit], dynamicObjects := []
    spawns := [("default",(7,3)),("from_east",(8,4))], defaultSpawn := (7,3) }

def task2World : WorldState :=
  { player := (7,3), facing := .left, rooms := [task2Room]
    items := ["sword","shield"], tools := ["sword","shield"]
    equippedA := "sword", equippedB := "shield" }

def task2Agent : NsiAgentState :=
  { world := task2World
    tracker := { tracked := [], stepsSinceSync := 0,
                 perceiveRequested := false } }
def task2Init := genericPlannerInitial task2Agent
def task2Budget := 100
def task2Final := runWorldSkill genericPlannerRuntime task2Budget {} task2Init

theorem task2_nonhardcoded_trace : WorldSkillSteps genericPlannerRuntime {} task2Budget task2Init task2Final :=
  runWorldSkill_steps _ _ _ _
theorem task2_complete : goalReached task2Final.agent.world = true := by native_decide
theorem task2_dsl_done : task2Final.skill.finished = true := by native_decide
theorem task2_monster_defeated : (currentRoom task2Final.agent.world).monsters = [] := by
  native_decide
theorem task2_key_chest_opened :
    (currentRoom task2Final.agent.world).chests.all (fun c => c.isOpen) = true := by
  native_decide

end EnvFormalization

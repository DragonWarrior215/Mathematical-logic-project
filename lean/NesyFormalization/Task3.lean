import NesyFormalization.Task2

namespace EnvFormalization

def task3StartWest : Exit :=
  { exitId := "west_exit", direction := .left, tiles := [(0,3),(0,4)]
    targetRoomId := "monster_hall", targetEntry := "from_east" }
def task3StartEast : Exit :=
  { exitId := "locked_right_exit", direction := .right, tiles := [(9,3),(9,4)]
    exitType := .lockedKey, requiresKeyCount := 1, consumeKey := true
    unlocked := false, completeTask := true
    targetRoomId := "start_room", targetEntry := "from_east" }
def task3StartRoom : RoomState :=
  { roomId := "start_room", walls := [], chests := [], traps := [], buttons := []
    switches := []
    npcs := [{
      npcId := "start_hint"
      pos := (4,1)
      text := "Find the key west, then return."
    }]
    monsters := [], exits := [task3StartWest,task3StartEast], dynamicObjects := []
    spawns := [("default",(4,4)),("from_west",(1,4)),("from_east",(8,4))]
    defaultSpawn := (4,4) }

def task3HallMonster : Monster :=
  { monsterId := "hall_chaser", pos := (5,3), spawnPos := (5,3)
    monsterType := .chaser, hp := 2, damage := 1 }
def task3HallEast : Exit :=
  { exitId := "east_exit", direction := .right, tiles := [(9,3),(9,4)]
    targetRoomId := "start_room", targetEntry := "from_west" }
def task3HallWest : Exit :=
  { exitId := "west_exit", direction := .left, tiles := [(0,3),(0,4)]
    targetRoomId := "key_room", targetEntry := "from_east" }
def task3HallRoom : RoomState :=
  { roomId := "monster_hall", walls := [], chests := [], traps := [], buttons := []
    switches := [], npcs := [], monsters := [task3HallMonster]
    exits := [task3HallEast,task3HallWest], dynamicObjects := []
    spawns := [("default",(8,4)),("from_east",(8,4)),("from_west",(1,4))]
    defaultSpawn := (8,4) }

def task3KeyChest : Chest :=
  { chestId := "return_key_chest", pos := (5,4), loot := { kind := .key } }
def task3KeyEast : Exit :=
  { exitId := "east_exit", direction := .right, tiles := [(9,3),(9,4)]
    targetRoomId := "monster_hall", targetEntry := "from_west" }
def task3KeyRoom : RoomState :=
  { roomId := "key_room", walls := [], chests := [task3KeyChest], traps := []
    buttons := [], switches := [], npcs := [], monsters := [], exits := [task3KeyEast]
    dynamicObjects := [], spawns := [("default",(8,4)),("from_east",(8,4))]
    defaultSpawn := (8,4) }

def task3World : WorldState :=
  { player := (4,4), facing := .down
    rooms := [task3StartRoom,task3HallRoom,task3KeyRoom]
    items := ["sword","shield"], tools := ["sword","shield"]
    equippedA := "sword", equippedB := "shield" }

def task3Agent : NsiAgentState :=
  { world := task3World
    tracker := { tracked := [], stepsSinceSync := 0,
                 perceiveRequested := false } }
def task3Init := genericPlannerInitial task3Agent
def task3Budget := 200
def task3Final := runWorldSkill genericPlannerRuntime task3Budget {} task3Init

theorem task3_nonhardcoded_trace : WorldSkillSteps genericPlannerRuntime {} task3Budget task3Init task3Final :=
  runWorldSkill_steps _ _ _ _
theorem task3_complete : goalReached task3Final.agent.world = true := by native_decide
theorem task3_dsl_done : task3Final.skill.finished = true := by native_decide
theorem task3_hall_monster_defeated :
    ((getAt? task3Final.agent.world.rooms 1).getD default).monsters = [] := by
  native_decide
theorem task3_return_key_chest_opened :
    ((getAt? task3Final.agent.world.rooms 2).getD default).chests.all
      (fun c => c.isOpen) = true := by
  native_decide

end EnvFormalization

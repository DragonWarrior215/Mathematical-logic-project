import NesyFormalization.GenericPlanner

namespace EnvFormalization

def t5Exit (id : String) (d : Direction) (tiles : List Position)
    (target entry : String) (kind : ExitType := .normal) : Exit :=
  { exitId := id, direction := d, tiles := tiles, exitType := kind
    targetRoomId := target, targetEntry := entry }

def task5Start : RoomState :=
  { roomId := "room_0_0", walls := [(5,1),(5,2),(3,3),(4,3),(6,5)]
    chests := [{ chestId := "start_chest", pos := (4,2), loot := { kind := .gold, amount := 2 } }]
    traps := [], buttons := [{ buttonId := "button_1", pos := (2,6) }], switches := []
    npcs := [{ npcId := "npc", pos := (7,6), text := "Find a key in the south room." }]
    monsters := [{
      monsterId := "start_monster"
      pos := (7,4)
      spawnPos := (7,4)
      monsterType := .chaser
      hp := 2 }]
    exits := [
      { (t5Exit "east_exit" .right [(9,3),(9,4)] "room_1_0" "from_west" .lockedKey) with
        requiresKeyCount := 1, consumeKey := true, unlocked := false },
      t5Exit "west_exit" .left [(0,3),(0,4)] "room_-1_0" "from_east",
      { (t5Exit "south_exit" .down [(4,7),(5,7)] "room_0_1" "from_north" .conditional) with
        requiresButtonId := some "button_1" }]
    dynamicObjects := []
    spawns := [("default",(1,1)),("from_east",(1,4)),("from_south",(4,1)),("from_west",(8,4))]
    defaultSpawn := (1,1) }

def task5South : RoomState :=
  { roomId := "room_0_1", walls := [(2,2),(3,2),(4,2),(5,2),(6,2),(7,2),(4,6)]
    chests := [{ chestId := "key_chest", pos := (8,5), loot := { kind := .key } }]
    traps := [{ trapId := "trap_1", pos := (1,5), damage := 1, respawnTo := "from_north" }]
    buttons := [], switches := []
    npcs := [{ npcId := "npc", pos := (2,1), text := "Bring the key back." }]
    monsters := [{
      monsterId := "south_monster"
      pos := (6,6)
      spawnPos := (6,6)
      monsterType := .patroller
      hp := 3
      patrolSpanTiles := 2 }]
    exits := [t5Exit "north_exit" .up [(4,0),(5,0)] "room_0_0" "from_south"]
    dynamicObjects := [], spawns := [("default",(4,1)),("from_north",(4,1))]
    defaultSpawn := (4,1) }

def task5East : RoomState :=
  { roomId := "room_1_0", walls := [(2,2),(2,3),(2,4),(5,4),(6,4)]
    chests := [{ chestId := "heal_chest", pos := (7,1), loot := { kind := .heal } }]
    traps := [], buttons := [], switches := []
    npcs := [{ npcId := "npc", pos := (7,6), text := "Behind the locked gate." }]
    monsters := [{
      monsterId := "east_monster"
      pos := (7,5)
      spawnPos := (7,5)
      monsterType := .ambusher
      hp := 2
      ambushRangeTiles := 2 }]
    exits := [t5Exit "west_exit" .left [(0,3),(0,4)] "room_0_0" "from_east"]
    dynamicObjects := [], spawns := [("default",(1,4)),("from_west",(1,4))]
    defaultSpawn := (1,4) }

def task5West : RoomState :=
  { roomId := "room_-1_0", walls := [(1,2),(2,2),(5,5),(4,6),(5,6)]
    chests := [{ chestId := "gold_chest", pos := (2,6), loot := { kind := .gold, amount := 5 } }]
    traps := [], buttons := [], switches := []
    npcs := [{ npcId := "npc", pos := (7,6), text := "No locked exits." }]
    monsters := [
      { monsterId := "west_chaser", pos := (2,4), spawnPos := (2,4), monsterType := .chaser, hp := 2 },
      { monsterId := "west_ambusher", pos := (6,3), spawnPos := (6,3), monsterType := .ambusher,
        ambushRangeTiles := 3, hp := 2 }]
    exits := [t5Exit "east_exit" .right [(9,3),(9,4)] "room_0_0" "from_west"]
    dynamicObjects := [], spawns := [("default",(8,4)),("from_east",(8,4))]
    defaultSpawn := (8,4) }

def task5World : WorldState :=
  { player := (1,1), facing := .down, health := 5
    items := ["sword","shield"], tools := ["sword","shield"]
    equippedA := "sword", equippedB := "shield"
    rooms := [task5Start,task5East,task5South,task5West]
    currentRoomIdx := 0, worldCompletionViaExit := false }

def task5Agent : NsiAgentState :=
  { world := task5World
    tracker := { tracked := [], stepsSinceSync := 0, perceiveRequested := false } }
def task5Init := genericPlannerInitial task5Agent
def task5Budget := 700
def task5Final := runWorldSkill genericPlannerRuntime task5Budget {} task5Init

theorem task5_generic_trace :
    WorldSkillSteps genericPlannerRuntime {} task5Budget task5Init task5Final :=
  runWorldSkill_steps _ _ _ _
theorem task5_complete : goalReached task5Final.agent.world = true := by native_decide
theorem task5_dsl_done : task5Final.skill.finished = true := by native_decide
theorem task5_survives : 0 < task5Final.agent.world.health := by native_decide

end EnvFormalization

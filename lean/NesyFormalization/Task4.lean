import NesyFormalization.GenericPlanner

namespace EnvFormalization

def task4Bridge : DynamicObject :=
  { objectId := "center_bridge", initialState := "west_to_north"
    states := [
      { stateId := "west_to_north", tiles :=
        [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(0,4),(1,4),(2,4),(3,4),(4,4),(5,4),
         (4,0),(5,0),(4,1),(5,1),(4,2),(5,2)] },
      { stateId := "west_to_east", tiles :=
        [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3),(8,3),(9,3),
         (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(7,4),(8,4),(9,4)] },
      { stateId := "west_to_south", tiles :=
        [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(0,4),(1,4),(2,4),(3,4),(4,4),(5,4),
         (4,5),(5,5),(4,6),(5,6),(4,7),(5,7)] }]
    backgroundTile := .none, activeTile := .bridge, currentState := "west_to_north" }

def task4CenterTraps : List Trap := allPositions.map (fun p =>
  { trapId := s!"abyss_{p.1}_{p.2}", pos := p, trapType := .abyss,
    damage := 1, respawnDelaySteps := 2 })

def t4Exit (id : String) (d : Direction) (tiles : List Position)
    (target entry : String) (kind : ExitType := .normal) : Exit :=
  { exitId := id, direction := d, tiles := tiles, exitType := kind
    targetRoomId := target, targetEntry := entry }

def task4Switch : Switch :=
  { switchId := "bridge_switch", pos := (4,4), targetObjectId := "center_bridge"
    order := ["west_to_north","west_to_east","west_to_south"] }

def task4EWalls : List Position :=
  (List.range 10).map (fun x => (x,0)) ++ (List.range 10).map (fun x => (x,7)) ++
  [(0,1),(9,1),(0,2),(9,2),(0,5),(9,5),(0,6),(9,6)]

def task4NorthWalls : List Position :=
  (List.range 10).map (fun x => (x,0)) ++
  [(0,1),(9,1),(0,2),(9,2),(0,3),(9,3),(0,4),(9,4),(0,5),(9,5),(0,6),(9,6),
   (0,7),(1,7),(2,7),(3,7),(6,7),(7,7),(8,7),(9,7)]

def task4SouthWalls : List Position :=
  [(0,0),(1,0),(2,0),(3,0),(6,0),(7,0),(8,0),(9,0),
   (0,1),(9,1),(0,2),(9,2),(0,3),(9,3),(0,4),(9,4),(0,5),(9,5),(0,6),(9,6)] ++
  (List.range 10).map (fun x => (x,7))

def task4West : RoomState :=
  { roomId := "west", walls := task4EWalls, chests := [], traps := [], buttons := []
    switches := [task4Switch], npcs := [], monsters := []
    exits := [t4Exit "east_exit" .right [(9,3),(9,4)] "center" "west_door"]
    dynamicObjects := [], spawns := [("default",(7,4)),("east_door",(8,4))]
    defaultSpawn := (7,4) }

def task4FinalChest : Chest :=
  { chestId := "final_chest", pos := (4,4), loot := { kind := .gold }
    isVisible := false, revealOnAllMonstersDefeated := true
    revealTriggerRoomId := some "south" }

def task4Center : RoomState :=
  { roomId := "center", walls := [], chests := [task4FinalChest]
    traps := task4CenterTraps, buttons := [], switches := [], npcs := [], monsters := []
    exits := [
      t4Exit "west_exit" .left [(0,3),(0,4)] "west" "east_door",
      { (t4Exit "east_exit" .right [(9,3),(9,4)] "east" "west_door" .lockedKey) with
        requiresKeyCount := 1, consumeKey := false, unlocked := false },
      t4Exit "north_exit" .up [(4,0),(5,0)] "north" "from_south",
      t4Exit "south_exit" .down [(4,7),(5,7)] "south" "from_north"]
    dynamicObjects := [task4Bridge]
    spawns := [("default",(1,4)),("west_door",(1,4)),("east_door",(8,4)),
      ("from_north",(4,1)),("from_south",(4,6))]
    defaultSpawn := (1,4) }

def task4North : RoomState :=
  { roomId := "north", walls := task4NorthWalls,
    chests := [{ chestId := "key_chest", pos := (4,3), loot := { kind := .key } }]
    traps := [], buttons := [], switches := [], npcs := [], monsters := []
    exits := [t4Exit "south_exit" .down [(4,7),(5,7)] "center" "from_north"]
    dynamicObjects := [], spawns := [("default",(4,6)),("from_south",(4,6))]
    defaultSpawn := (4,6) }

def task4East : RoomState :=
  { roomId := "east", walls := task4EWalls
    chests := [{
      chestId := "sword_chest"
      pos := (5,4)
      loot := {
        kind := .item
        itemName := some "sword"
        toolName := some "sword"
        equipSlot := some .A
      }
    }]
    traps := [], buttons := [], switches := [], npcs := [], monsters := []
    exits := [t4Exit "west_exit" .left [(0,3),(0,4)] "center" "east_door"]
    dynamicObjects := [], spawns := [("default",(1,4)),("west_door",(1,4))]
    defaultSpawn := (1,4) }

def task4South : RoomState :=
  { roomId := "south", walls := task4SouthWalls, chests := [], traps := [], buttons := []
    switches := [], npcs := []
    monsters := [{
      monsterId := "guardian"
      pos := (4,4)
      spawnPos := (4,4)
      monsterType := .chaser
      hp := 1
    }]
    exits := [t4Exit "north_exit" .up [(4,0),(5,0)] "center" "from_south"]
    dynamicObjects := [], spawns := [("default",(4,1)),("from_north",(4,1))]
    defaultSpawn := (4,1) }

def task4World : WorldState :=
  { player := (7,4), facing := .left
    items := ["shield"], tools := ["shield"], equippedB := "shield"
    rooms := [task4West,task4Center,task4North,task4East,task4South]
    currentRoomIdx := 0, worldCompletionViaExit := false }

def task4Agent : NsiAgentState :=
  { world := task4World
    tracker := { tracked := [], stepsSinceSync := 0, perceiveRequested := false } }
def task4Init := genericPlannerInitial task4Agent
def task4Budget := 400
def task4Final := runWorldSkill genericPlannerRuntime task4Budget {} task4Init

theorem task4_generic_trace :
    WorldSkillSteps genericPlannerRuntime {} task4Budget task4Init task4Final :=
  runWorldSkill_steps _ _ _ _
theorem task4_complete : goalReached task4Final.agent.world = true := by native_decide
theorem task4_dsl_done : task4Final.skill.finished = true := by native_decide
theorem task4_guardian_defeated :
    ((getAt? task4Final.agent.world.rooms 4).getD default).monsters = [] := by native_decide
theorem task4_final_chest_opened :
    ((getAt? task4Final.agent.world.rooms 1).getD default).chests.all
      (fun c => c.isVisible && c.isOpen) = true := by native_decide

end EnvFormalization

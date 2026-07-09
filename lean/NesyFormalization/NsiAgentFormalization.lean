import NesyFormalization.MapSemantics

namespace EnvFormalization

/-!
Lean 层的 `nsi_agent` 运行语义。

这个文件不是把 Python 的 VLM、浮点像素 AABB、`deque`/`dict` 实现逐字翻译成 Lean；
它把 `nsi_agent.agent.Policy.act` 的核心控制流翻译成可调用的小步语义：

1. 根据上一帧 reward 反馈修正 tracker。
2. 若 tracker 要求关键帧，则用 grounding snapshot 同步记忆和怪物跟踪器。
3. 调用 planner 产生请求动作。
4. 用 safety shield 过滤危险移动。
5. 将动作送入环境语义 `step`，并更新 tracker 的死推演状态。

外部黑箱保留为参数：
- grounding snapshot 对应 Python `backend.ground(obs)` 的结果；
- planner 对应 Python `planner.step(ctx)` 的结果。

这样，别的 Lean 文件可以围绕 `nsiAgentAct` / `nsiAgentEnvStep` 证明性质，而不是
先假设某个 BFS、shield 或 tracker 已经可靠。
-/

/-! ## 0. Agent 中使用的怪物危险运行定义 -/

/-- 跟踪器抽象：怪物位置加上一个不确定性半径。 -/
structure TrackedMonster where
  pos : Position
  uncertainty : Nat := 0
  deriving Repr, DecidableEq

/-- 自然数坐标上的绝对差。 -/
def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- Chebyshev 距离，对应怪物周围的方形不确定区域。 -/
def chebyshev (p q : Position) : Nat :=
  Nat.max (absDiff p.1 q.1) (absDiff p.2 q.2)

/-- 已跟踪怪物的保守危险半径。 -/
def dangerRadius (m : TrackedMonster) : Nat :=
  m.uncertainty + 1

/-- 若格子在边界内且位于半径加安全边距的范围内，则它被怪物区域阻挡。 -/
def monsterBlockedTile (m : TrackedMonster) (margin : Nat) (p : Position) : Prop :=
  InBounds p ∧ chebyshev p m.pos ≤ dangerRadius m + margin

/-- 一个格子位于单个怪物的不确定危险区域内。 -/
def inMonsterDanger (p : Position) (m : TrackedMonster) : Prop :=
  chebyshev p m.pos ≤ dangerRadius m

/-- 一个格子位于至少一个已跟踪怪物的危险区域内。 -/
def inDangerRegion (monsters : List TrackedMonster) (p : Position) : Prop :=
  ∃ m, m ∈ monsters ∧ inMonsterDanger p m

/-- 符号安全表示不处于任何已跟踪怪物的危险区域中。 -/
def positionSafe (monsters : List TrackedMonster) (p : Position) : Prop :=
  ¬ inDangerRegion monsters p

/-- 真实世界安全性：候选格子不与任何真实怪物严格相邻。 -/
def RealMonsterSafe (realMonsters : List Position) (p : Position) : Prop :=
  ∀ real, real ∈ realMonsters → ¬ Neighbor p real

/-- 将符号怪物区域与真实怪物位置连接起来的接口条件。 -/
def MonsterRegionSound
    (tracked : List TrackedMonster) (realMonsters : List Position) : Prop :=
  ∀ p, positionSafe tracked p → RealMonsterSafe realMonsters p

/-! ## 1. Agent 中使用的 BFS / GoTo / shield 运行定义 -/

/-- 路径链要求每一对连续格子都是严格邻居。 -/
def PathChain : List Position → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Neighbor p q ∧ PathChain (q :: rest)

/-- 路径中的每个格子都必须在房间中满足严格可行走性。 -/
def PathWalkable (r : RoomState) (path : List Position) : Prop :=
  ∀ p, p ∈ path → walkable r p

/-- 路径从 `start` 开始并在 `goal` 结束。 -/
def PathEndpoints (path : List Position) (start goal : Position) : Prop :=
  path.head? = some start ∧ path.getLast? = some goal

/-- 有效路径具有正确端点，只使用可行走格子，并按严格邻居关系移动。 -/
def ValidPath (r : RoomState) (start goal : Position) (path : List Position) : Prop :=
  PathEndpoints path start goal ∧ PathWalkable r path ∧ PathChain path

/-- 可达性表示两个格子之间存在一条有效路径。 -/
def Reachable (r : RoomState) (start goal : Position) : Prop :=
  ∃ path, ValidPath r start goal path

/-- Python `neighbors(tile)` 的 Lean 版本：上、下、左、右四邻格。 -/
def gridNeighbors (p : Position) : List Position :=
  (if p.2 = 0 then [] else [(p.1, p.2 - 1)]) ++
  [(p.1, p.2 + 1)] ++
  (if p.1 = 0 then [] else [(p.1 - 1, p.2)]) ++
  [(p.1 + 1, p.2)]

/-- Python `walkable(ctx, tile, allow_hazard=False)` 的布尔版本。 -/
def walkableBool (r : RoomState) (p : Position) (allowHazard : Bool := false) : Bool :=
  inBounds p && !isBlocking r p && (allowHazard || !isHazardTile r p)

/-- BFS 队列中的节点：当前位置加上从起点到当前位置的路径。 -/
structure BfsNode where
  tile : Position
  path : List Position
  deriving Repr, DecidableEq

/-- 队列节点的路径语义：`path` 是一条从 `start` 到 `tile` 的有效路径。 -/
def NodeSound (r : RoomState) (start : Position) (node : BfsNode) : Prop :=
  ValidPath r start node.tile node.path

/-- Python `nxt in forbidden` / monster shield 之外的额外避让集合。 -/
def allowedByAvoid (avoid : List Position) (goals : List Position) (p : Position) : Bool :=
  !containsPos avoid p || containsPos goals p

/--
从一个 BFS 节点展开下一层候选。对应 Python 中：
`for nxt in neighbors(current)`，过滤 visited、walkable、forbidden 后入队。
-/
def expandNode
    (r : RoomState) (seen avoid goals : List Position)
    (allowHazard : Bool) (node : BfsNode) : List BfsNode :=
  (gridNeighbors node.tile).filterMap (fun nxt =>
    if containsPos seen nxt then
      none
    else if walkableBool r nxt allowHazard && allowedByAvoid avoid goals nxt then
      some { tile := nxt, path := node.path ++ [nxt] }
    else
      none)

/-- BFS 初始队列节点：从 `start` 到 `start` 的零长度路径。 -/
def initialBfsNode (start : Position) : BfsNode :=
  { tile := start, path := [start] }

/-- 取出一批 BFS 节点所在的格子，用来更新 visited/seen 集合。 -/
def bfsNodeTiles (nodes : List BfsNode) : List Position :=
  nodes.map (fun node => node.tile)

/-- 可执行 BFS 主循环，对应 Python `bfs_path` 的 `queue + parent` 搜索结构。 -/
def bfsSearch
    (r : RoomState) (goals avoid : List Position) (allowHazard : Bool) :
    Nat → List Position → List BfsNode → Option (List Position)
  | 0, _, _ => none
  | _ + 1, _seen, [] => none
  | fuel + 1, seen, node :: queue =>
      if containsPos goals node.tile then
        some node.path
      else
        let children := expandNode r seen avoid goals allowHazard node
        let seen' := seen ++ bfsNodeTiles children
        bfsSearch r goals avoid allowHazard fuel seen' (queue ++ children)

/-- Python `skills.bfs_path` 的 tile 层 Lean 版本。 -/
def bfsPath
    (r : RoomState) (start : Position) (goals : List Position)
    (avoid : List Position := []) (allowHazard : Bool := false) : Option (List Position) :=
  if goals.isEmpty then
    none
  else if containsPos goals start then
    some [start]
  else
    bfsSearch r goals avoid allowHazard 80 [start] [initialBfsNode start]

/-- reachable_tiles 的循环：持续展开队列，返回 seen。 -/
def reachableTilesSearch
    (r : RoomState) (avoid : List Position) :
    Nat → List Position → List Position → List Position
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | fuel + 1, seen, current :: queue =>
      let nexts :=
        (gridNeighbors current).filter (fun nxt =>
          !containsPos seen nxt && !containsPos avoid nxt && walkableBool r nxt false)
      reachableTilesSearch r avoid fuel (seen ++ nexts) (queue ++ nexts)

/-- Python `reachable_tiles` 的 Lean 版本。 -/
def reachableTiles
    (r : RoomState) (start : Position) (avoid : List Position := []) : List Position :=
  reachableTilesSearch r avoid 80 [start] [start]

/-- `GoToTile` 的关键运行状态，保留证明最关心的字段。 -/
structure GoToRuntime where
  target : Position
  adjacent : Bool := false
  align : Bool := false
  maxSteps : Nat := 900
  steps : Nat := 0
  avoid : List Position := []
  waypoint? : Option Position := none
  bumpStreak : Nat := 0
  deriving Repr, DecidableEq

/-- GoTo 的单步结果：发动作、成功或失败。 -/
inductive GoToStepResult where
  | acting (next : GoToRuntime) (action : Action)
  | succeeded (pos : Position)
  | failed (reason : String)
  deriving Repr, DecidableEq

/-- 目标格本身，或目标周围的可走接近格。 -/
def goToGoals (r : RoomState) (target : Position) (adjacent : Bool) : List Position :=
  if adjacent then
    (gridNeighbors target).filter (fun p => walkableBool r p false)
  else
    [target]

/-- tile 层向 waypoint 前进一步的动作选择。 -/
def moveTowardTile (here waypoint : Position) : Option Action :=
  if here.1 < waypoint.1 then
    some .right
  else if waypoint.1 < here.1 then
    some .left
  else if here.2 < waypoint.2 then
    some .down
  else if waypoint.2 < here.2 then
    some .up
  else
    none

/-- Lean 版 `GoToTile.step` 的核心。monster shield 在 agent 层统一处理。 -/
def goToTileStep (r : RoomState) (here : Position) (st : GoToRuntime) : GoToStepResult :=
  let st := { st with steps := st.steps + 1 }
  if st.steps > st.maxSteps then
    GoToStepResult.failed "timeout"
  else
    let goals := goToGoals r st.target st.adjacent
    if goals.isEmpty then
      GoToStepResult.failed "no_approach"
    else if containsPos goals here then
      GoToStepResult.succeeded here
    else
      match bfsPath r here goals st.avoid false with
      | none => GoToStepResult.failed "no_path"
      | some path =>
          let waypoint := match getAt? path 1 with
            | some p => p
            | none => here
          match moveTowardTile here waypoint with
          | some action => GoToStepResult.acting { st with waypoint? := some waypoint } action
          | none => GoToStepResult.acting { st with waypoint? := some waypoint } .wait

/-- 移动动作的目标格子；对被动或非移动动作返回 `none`。 -/
def actionTarget? (w : WorldState) : Action → Option Position
  | .up => some (facingTile w.player .up)
  | .down => some (facingTile w.player .down)
  | .left => some (facingTile w.player .left)
  | .right => some (facingTile w.player .right)
  | .wait => none
  | .interactA => none
  | .shieldB => none

/-! ## 4. Memory 核心子集 -/

/-- Python `RoomMemory.learned_blocked` 的 Lean 条目：格子和过期步数。 -/
structure LearnedBlock where
  pos : Position
  expiresAt : Nat
  deriving Repr, DecidableEq

/--
Lean 版 agent memory 的核心子集。

这里只保留规划/证明最常用的持久信息：当前房间坐标、learned blocked、
已确认打开/按下/访问过的对象，以及 inventory view。
-/
structure AgentMemory where
  currentCoord : Int × Int := (0, 0)
  learnedBlocked : List LearnedBlock := []
  openedChests : List Position := []
  pressedButtons : List Position := []
  visitedExits : List Direction := []
  keys : Nat := 0
  gold : Nat := 0
  items : List String := []
  tools : List String := []
  hpEstimate : Nat := 5
  stepCount : Nat := 0
  deriving Repr, DecidableEq

/-- learned-blocked 条目在当前步是否仍有效。 -/
def learnedBlockActive (now : Nat) (entry : LearnedBlock) : Bool :=
  now < entry.expiresAt

/-- 查询某格是否被有效的 learned-blocked 记录阻挡。 -/
def learnedBlockingAt (mem : AgentMemory) (p : Position) : Bool :=
  mem.learnedBlocked.any (fun entry => entry.pos == p && learnedBlockActive mem.stepCount entry)

/-- Python `mark_blocked` 的 Lean 版本：只记录界内格子，并设置 TTL。 -/
def markLearnedBlocked (mem : AgentMemory) (p : Position) (ttl : Nat := 300) : AgentMemory :=
  if inBounds p then
    { mem with learnedBlocked := { pos := p, expiresAt := mem.stepCount + ttl } :: mem.learnedBlocked }
  else
    mem

/-- 感知到新 keyframe 后，删除已过期的 learned-blocked 记录。 -/
def pruneExpiredLearnedBlocks (mem : AgentMemory) : AgentMemory :=
  { mem with learnedBlocked := mem.learnedBlocked.filter (fun entry => learnedBlockActive mem.stepCount entry) }

/-- 结合房间静态阻挡和 learned-blocked 的 planner 阻挡查询。 -/
def memoryIsBlocking (mem : AgentMemory) (r : RoomState) (p : Position) : Bool :=
  learnedBlockingAt mem p || isBlocking r p

/-- 结合 memory 的 walkable 查询，对应 Python `Memory.is_blocking/is_hazard` 后的 `walkable`。 -/
def memoryWalkable (mem : AgentMemory) (r : RoomState) (p : Position)
    (allowHazard : Bool := false) : Bool :=
  inBounds p && !memoryIsBlocking mem r p && (allowHazard || !isHazardTile r p)

/-- inventory view 中是否有盾。 -/
def memoryHasShield (mem : AgentMemory) : Bool :=
  containsString mem.tools "shield"

/-- inventory view 中是否有剑。 -/
def memoryHasSword (mem : AgentMemory) : Bool :=
  containsString mem.tools "sword"

/-! ## 2. Safety shield 与 monster uncertainty -/

/-- Lean 版 tracker 状态，对应 Python `Tracker` 中和证明相关的离散字段。 -/
structure NsiTracker where
  tracked : List TrackedMonster := []
  stepsSinceSync : Nat := 1000000000
  perceiveRequested : Bool := true
  lastActionWasMove : Bool := false
  lastMoveBlocked : Bool := false
  previousPlayer? : Option Position := none
  deriving Repr, DecidableEq

/-- Lean 版 agent 状态：当前符号世界、tracker，以及 grounding 失败后的 backoff。 -/
structure NsiAgentState where
  world : WorldState
  memory : AgentMemory := {}
  tracker : NsiTracker := {}
  groundBackoff : Nat := 0
  deriving Repr, DecidableEq

/-- 一次 act 的可观察输出：发出的动作和更新后的 agent 状态。 -/
structure NsiActResult where
  agent : NsiAgentState
  requested : Action
  issued : Action
  deriving Repr, DecidableEq

/-- 一次 agent+environment 联合步进的输出。 -/
structure NsiEnvStepResult where
  agent : NsiAgentState
  requested : Action
  issued : Action
  worldAfter : WorldState
  deriving Repr, DecidableEq

/-- 当前房间中的怪物转成 tracker 的离散怪物状态；关键帧同步时不确定性重置为 0。 -/
def trackedMonstersOfRoom (r : RoomState) : List TrackedMonster :=
  r.monsters.map (fun m => { pos := m.pos, uncertainty := 0 })

/-- 一个真实怪物位置被某个 tracked monster 的危险半径覆盖。 -/
def realMonsterCoveredByTracked (real : Position) (tracked : TrackedMonster) : Prop :=
  chebyshev real tracked.pos ≤ dangerRadius tracked

/-- tracker 的怪物集合覆盖所有真实怪物位置。 -/
def trackerCoversRealMonsters (tracked : List TrackedMonster) (real : List Position) : Prop :=
  ∀ p, p ∈ real → ∃ m, m ∈ tracked ∧ realMonsterCoveredByTracked p m

/-- 关键帧同步后的 tracker 精确覆盖当前房间内的怪物 tile。 -/
def trackerSyncedWithRoom (tracked : List TrackedMonster) (r : RoomState) : Prop :=
  tracked = trackedMonstersOfRoom r

/-- 关键帧同步：信任 grounding snapshot，并重置怪物不确定圈。 -/
def syncFromGrounding (snapshot : WorldState) (s : NsiAgentState) : NsiAgentState :=
  { s with
    world := snapshot
    memory := pruneExpiredLearnedBlocks s.memory
    tracker := {
      s.tracker with
      tracked := trackedMonstersOfRoom (currentRoom snapshot)
      stepsSinceSync := 0
      perceiveRequested := false
      lastMoveBlocked := false
      previousPlayer? := none
    }
    groundBackoff := 0
  }

/-- 移动动作对应的朝向；非移动动作返回 `none`。 -/
def moveDirection? : Action → Option Direction
  | .up => some .up
  | .down => some .down
  | .left => some .left
  | .right => some .right
  | .wait => none
  | .interactA => none
  | .shieldB => none

/-- A/B 交互可能改变世界，Python tracker 会要求下一步重新感知。 -/
def actionRequestsPerceive : Action → Bool
  | .interactA => true
  | .shieldB => true
  | _ => false

/-- tracker 死推演中，每步怪物不确定性扩大一格层级。 -/
def growTrackedMonsters (ms : List TrackedMonster) : List TrackedMonster :=
  ms.map (fun m => { m with uncertainty := m.uncertainty + 1 })

/-! ## 3. Reward feedback 与 learned-blocked -/

/-- reward invalid-action 反馈：若上一动作是移动，则撤回乐观移动并记录撞墙。 -/
def applyRewardBlockedFeedback (blocked : Bool) (s : NsiAgentState) : NsiAgentState :=
  if blocked && s.tracker.lastActionWasMove then
    let restoredWorld :=
      match s.tracker.previousPlayer? with
      | some previous => { s.world with player := previous }
      | none => s.world
    { s with world := restoredWorld, tracker := { s.tracker with lastMoveBlocked := true } }
  else
    { s with tracker := { s.tracker with lastMoveBlocked := false } }

/--
GoTo 的 bump/stall 反馈：连续撞向同一个 waypoint 时，将该 waypoint 记为
learned-blocked，后续 BFS 会绕开它。
-/
def applyWaypointBumpFeedback
    (waypoint? : Option Position) (bumpThreshold : Nat)
    (s : NsiAgentState) : NsiAgentState :=
  if s.tracker.lastMoveBlocked && bumpThreshold ≤ s.tracker.stepsSinceSync then
    match waypoint? with
    | some waypoint => { s with memory := markLearnedBlocked s.memory waypoint }
    | none => s
  else
    s

/-- tracker 在动作发出后的离散更新。 -/
def trackerAfterIssuedAction (t : NsiTracker) (issued : Action) : NsiTracker :=
  { t with
    stepsSinceSync := t.stepsSinceSync + 1
    perceiveRequested := t.perceiveRequested || actionRequestsPerceive issued
    lastActionWasMove := moveDirection? issued |>.isSome
    lastMoveBlocked := false
    tracked := growTrackedMonsters t.tracked
  }

/-- 带当前位置的 tracker 动作后更新：若动作是移动，记录上一格用于 reward 回退。 -/
def trackerAfterIssuedActionAt (player : Position) (t : NsiTracker) (issued : Action) : NsiTracker :=
  let updated := trackerAfterIssuedAction t issued
  if (moveDirection? issued).isSome then
    { updated with previousPlayer? := some player }
  else
    { updated with previousPlayer? := none }

/-- 与 Python `should_perceive` 对应的简化关键帧调度。 -/
def shouldPerceive (t : NsiTracker) (calmInterval : Nat := 24) : Bool :=
  t.perceiveRequested || t.stepsSinceSync ≥ calmInterval

/-- 若需要关键帧且提供了 snapshot，则同步；若 grounding 失败，则进入短暂 backoff。 -/
def maybeGroundAndSync (snapshot? : Option WorldState) (s : NsiAgentState) : NsiAgentState :=
  if shouldPerceive s.tracker && s.groundBackoff = 0 then
    match snapshot? with
    | some snapshot => syncFromGrounding snapshot s
    | none => { s with groundBackoff := 3 }
  else if s.groundBackoff > 0 then
    { s with groundBackoff := s.groundBackoff - 1 }
  else
    s

/-- 没有盾时用 wait 兜底；有盾时用 B 兜底，对应 Python `shielded`。 -/
def shieldFallback (w : WorldState) : Action :=
  if hasEquippedShield w then .shieldB else .wait

/-- 可执行版怪物危险检查。 -/
def inMonsterDangerBool (p : Position) (m : TrackedMonster) : Bool :=
  decide (chebyshev p m.pos ≤ dangerRadius m)

/-- 可执行版 `positionSafe`，用于 agent 运行语义中的 shield 判断。 -/
def positionSafeBool (monsters : List TrackedMonster) (p : Position) : Bool :=
  !(monsters.any (fun m => inMonsterDangerBool p m))

/-- 可执行版怪物阻挡格集合检查，包含额外 safety margin。 -/
def monsterBlockedTileBool (m : TrackedMonster) (margin : Nat) (p : Position) : Bool :=
  inBounds p && decide (chebyshev p m.pos ≤ dangerRadius m + margin)

/-- 某个 tile 是否被任意 tracked monster 的不确定区域阻挡。 -/
def blockedByTrackedMonstersBool
    (tracked : List TrackedMonster) (margin : Nat) (p : Position) : Bool :=
  tracked.any (fun m => monsterBlockedTileBool m margin p)

/-- 可执行版 safety shield：非移动动作透传，安全移动透传，危险移动换成 fallback。 -/
def shieldAction (w : WorldState) (tracked : List TrackedMonster) (requested : Action) : Action :=
  match actionTarget? w requested with
  | none => requested
  | some p =>
      if positionSafeBool tracked p then
        requested
      else
        shieldFallback w

/-! ## 1. BFS / GoTo 与 agent 运行逻辑的连接 -/

/-- 在当前 agent state 中，使用 memory learned-blocked 过滤出来的 BFS 避让集合。 -/
def learnedAvoidTiles (s : NsiAgentState) : List Position :=
  s.memory.learnedBlocked.filterMap (fun entry =>
    if learnedBlockActive s.memory.stepCount entry then some entry.pos else none)

/-- agent 当前房间里的 BFS 路径查询。 -/
def agentBfsPath
    (s : NsiAgentState) (start : Position) (goals : List Position)
    (extraAvoid : List Position := []) : Option (List Position) :=
  bfsPath (currentRoom s.world) start goals (learnedAvoidTiles s ++ extraAvoid) false

/-- agent 当前房间里的 GoTo 单步。 -/
def agentGoToStep (s : NsiAgentState) (goto : GoToRuntime) : GoToStepResult :=
  goToTileStep (currentRoom s.world) s.world.player { goto with avoid := learnedAvoidTiles s ++ goto.avoid }

/--
Lean 版 `Policy.act`。

`planner` 是符号 planner 的一步函数；`snapshot?` 是本步可用的 grounding 结果。
-/
def nsiAgentAct
    (planner : NsiAgentState → Action)
    (blockedFeedback : Bool)
    (snapshot? : Option WorldState)
    (s : NsiAgentState) : NsiActResult :=
  let afterFeedback := applyRewardBlockedFeedback blockedFeedback s
  let afterGrounding := maybeGroundAndSync snapshot? afterFeedback
  let requested := planner afterGrounding
  let issued := shieldAction afterGrounding.world afterGrounding.tracker.tracked requested
  let afterTracker :=
    { afterGrounding with
      tracker := trackerAfterIssuedActionAt afterGrounding.world.player afterGrounding.tracker issued
      memory := { afterGrounding.memory with stepCount := afterGrounding.memory.stepCount + 1 } }
  { agent := afterTracker, requested := requested, issued := issued }

/-- 将 `nsiAgentAct` 发出的动作接到环境 `step` 上，得到一次联合小步语义。 -/
def nsiAgentEnvStep
    (planner : NsiAgentState → Action)
    (blockedFeedback : Bool)
    (snapshot? : Option WorldState)
    (s : NsiAgentState) : NsiEnvStepResult :=
  let actResult := nsiAgentAct planner blockedFeedback snapshot? s
  let worldAfter := step actResult.agent.world actResult.issued
  { agent := { actResult.agent with world := worldAfter }
    requested := actResult.requested
    issued := actResult.issued
    worldAfter := worldAfter
  }

end EnvFormalization

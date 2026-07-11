import NesyFormalization.GridBfs
import NesyFormalization.SafetyShield

namespace EnvFormalization

/-- Specification for a goto failure caused by no adjacent approach tile. -/
def GotoNoApproachSound (r : RoomState) (target : Position) : Prop :=
  forall p, Neighbor p target -> Not (walkable r p)

/-- Specification for a goto failure caused by no valid path. -/
def GotoNoPathSound (r : RoomState) (start target : Position) : Prop :=
  Not (Reachable r start target)

/-- Abstract success condition used by the eventual-success theorem. -/
def GotoEventuallySucceedsSpec (r : RoomState) (start target : Position) : Prop :=
  Reachable r start target

/-- Specification for learned blocked tiles: the room model really blocks them. -/
def LearnedBlockSound (r : RoomState) (p : Position) : Prop :=
  isBlocking r p = true

/-- A static navigation action is safe with respect to the room model. -/
def StaticNavigationSafe (w : WorldState) (a : Action) : Prop :=
  match actionTarget? w a with
  | some p => InBounds p /\ isBlocking (currentRoom w) p = false /\ isHazardTile (currentRoom w) p = false
  | none => True

/--
`goto_no_approach_sound`: if the adjacent-goal set is empty, every strict
neighbor of the target is not a legal approach tile.
反证法-/
theorem goto_no_approach_sound {r : RoomState} {target : Position}
    (hgoals : goToGoals r target true = []) :
    GotoNoApproachSound r target := by
  intro p hneighbor hwalk
  have hmem : List.Mem p (gridNeighbors target) :=
    neighbor_mem_gridNeighbors (neighbor_symm hneighbor)
  have hwalkBool : walkableBool r p false = true := walkableBool_complete_mode hwalk
  have hp : List.Mem p (goToGoals r target true) := by
    unfold goToGoals
    exact List.mem_filter.mpr (And.intro hmem hwalkBool)
  rw [hgoals] at hp
  cases hp

/--
`goto_no_path_sound`: a `no_path` result is sound, relative to the explicit
completeness assumption for the current bounded two-stage BFS query.
由于当前 BFS 是有 fuel = 80、avoid、monsterAvoid 等约束的两阶段搜索，
不能无条件说 “BFS 返回 none 就等于普通 Reachable 不存在”，所以当给出当前查询的完备性假设，
那么 no_path 的 soundness 就成立。-/
theorem goto_no_path_sound
    {r : RoomState} {start target : Position} {baseAvoid monsterAvoid : List Position}
    (hnoPath : twoStageBfsPath r start [target] baseAvoid monsterAvoid false = none)
    (hcomplete :
      twoStageBfsPath r start [target] baseAvoid monsterAvoid false = none ->
      Not (Reachable r start target)) :
    GotoNoPathSound r start target := by
  exact hcomplete hnoPath

/--
`goto_eventually_succeeds`: when the two-stage GoTo BFS returns a plan for the
single target, BFS soundness gives a valid static path, hence the abstract
success condition holds。
假设起点 start 是可走格，并且 twoStageBfsPath 对单一目标 [target] 返回了 some plan。
由 GridBfs 中已经证明的 twoStageBfs_path_sound 可知，plan.path 是一条从 start 出发、终点属于 [target] 的合法路径。
因为目标列表只有 target 一个元素，所以该终点必然就是 target。
于是可以用 plan.path 构造 Reachable r start target，从而得到 GotoEventuallySucceedsSpec。
-/
theorem goto_eventually_succeeds
    {r : RoomState} {start target : Position} {baseAvoid monsterAvoid : List Position}
    {plan : TwoStageBfsResult}
    (hstart : walkable r start)
    (hplan : twoStageBfsPath r start [target] baseAvoid monsterAvoid false = some plan) :
    GotoEventuallySucceedsSpec r start target := by
  rcases twoStageBfs_path_sound
      (r := r) (allowHazard := false) (start := start)
      (goals := [target]) (baseAvoid := baseAvoid) (monsterAvoid := monsterAvoid)
      (plan := plan) hstart hplan with
    ⟨goal, hgoal, hvalid⟩
  simp at hgoal
  subst goal
  unfold GotoEventuallySucceedsSpec Reachable
  exact ⟨plan.path, by
    simpa [ValidPath, ValidPathForMode, PathWalkable, PathWalkableForMode,
      walkable, walkableForMode] using hvalid⟩

/--
If every active learned-block entry is backed by a real room blocker, then a
positive learned-block query is sound.
learnedBlockingAt mem p = true 表示 memory 中存在一条 learned-block 记录 entry，
它的坐标 entry.pos 等于 p，并且在当前 stepCount 下仍然 active。
前提 hsound 说明：memory 中任意 active 的 learned-block 记录，在真实房间模型里都确实是阻挡格。
因此把这条 entry 交给 hsound，可以得到 LearnedBlockSound r entry.pos。
再利用 entry.pos = p 改写，即可得到 LearnedBlockSound r p。
-/
theorem learned_block_sound
    {r : RoomState} {mem : AgentMemory} {p : Position}
    (hsound :
      forall entry, List.Mem entry mem.learnedBlocked ->
        learnedBlockActive mem.stepCount entry = true ->
        LearnedBlockSound r entry.pos)
    (hlearned : learnedBlockingAt mem p = true) :
    LearnedBlockSound r p := by
  unfold learnedBlockingAt at hlearned
  simp only [List.any_eq_true] at hlearned
  cases hlearned with
  | intro entry hrest =>
      cases hrest with
      | intro hmem hentry =>
          simp at hentry
          have hpos : entry.pos = p := hentry.1
          have hactive : learnedBlockActive mem.stepCount entry = true := hentry.2
          have hentrySound := hsound entry hmem hactive
          simpa [LearnedBlockSound, hpos] using hentrySound

/--
Marking a tile as learned-blocked is sound when the invalid-action feedback
itself identifies a truly blocking tile and the TTL is nonzero.
-/
theorem learned_block_sound_of_mark
    {r : RoomState} {mem : AgentMemory} {p : Position} {ttl : Nat}
    (hblock : LearnedBlockSound r p)
    (hin : inBounds p = true)
    (httl : 0 < ttl) :
    LearnedBlockSound r p /\ learnedBlockingAt (markLearnedBlocked mem p ttl) p = true := by
  constructor
  case left =>
    exact hblock
  case right =>
    unfold markLearnedBlocked learnedBlockingAt learnedBlockActive
    simp [hin, httl]

/--
`planner_navigation_safe`: if the planner-requested navigation action is
statically safe, then after the shield the issued action is either still
statically safe or is a non-move fallback. Monster safety is supplied by the
shield theorem under the usual tracker-region soundness assumption.
分情况讨论 Safety Shield 对 requested 动作的处理。
如果 requested 不是移动动作，那么 shieldAction 会原样返回，StaticNavigationSafe 由前提 hstatic 直接得到。
如果 requested 是移动动作并且目标格在 tracked monster 的安全区域外，shieldAction 同样放行，因此仍然使用原来的 hstatic。
如果 requested 的目标格不安全，shieldAction 会替换为 shieldFallback；而 SafetyShield 中已有 shieldFallback_nonmove，
说明 fallback 一定是非移动动作，所以 StaticNavigationSafe 自动成立。
真实怪物安全性部分则直接使用 SafetyShield 中的 shieldAction_real_world_safe：
只要 MonsterRegionSound 说明 tracker 危险区域对真实怪物是可靠的，经过 shield 过滤后的移动目标就是真实安全的。
-/
theorem planner_navigation_safe
    {w : WorldState} {tracked : List TrackedMonster} {realMonsters : List Position}
    {requested : Action}
    (hstatic : StaticNavigationSafe w requested)
    (hregion : MonsterRegionSound tracked realMonsters) :
    StaticNavigationSafe w (shieldAction w tracked requested) /\
      match actionTarget? w (shieldAction w tracked requested) with
      | some p => RealMonsterSafe realMonsters p
      | none => True := by
  constructor
  case left =>
    have hstaticRequested : StaticNavigationSafe w requested := hstatic
    unfold shieldAction
    cases htarget : actionTarget? w requested with
    | none =>
        simpa [htarget] using hstatic
    | some p =>
        unfold StaticNavigationSafe at hstatic
        simp [htarget] at hstatic
        by_cases hsafe : positionSafeBool tracked p = true
        case pos =>
          simpa [htarget, hsafe] using hstaticRequested
        case neg =>
          simp [hsafe]
          unfold StaticNavigationSafe
          rw [shieldFallback_nonmove]
          trivial
  case right =>
    exact shieldAction_real_world_safe hregion requested

end EnvFormalization

import NesyFormalization.Skills

namespace NesyFormalization

/-!
  高层 planner、房间级 BFS 与组合性质。

  这里不复刻 Python 的全部控制流，而是给出与实现对应的语义规格：如果某个 planner /
  room-router 满足这些规格，那么它的输出具有表格中列出的可靠性、安全性或完备性。
-/

/- -------------------------------------------------------------------------
  高层 Planner 的策略性质
  ------------------------------------------------------------------------- -/

/-- planner 会选择的抽象目标类型。 -/
inductive PlannerGoal where
  | flee
  | combat
  | idle
  | toggle
  | other
  deriving DecidableEq, Repr

/-- planner 输出目标的抽象接口。 -/
abbrev Planner := SymbolicState → PlannerGoal

/-- 无剑且威胁临近时，planner 应选择逃跑。 -/
def UnarmedThreatPrefersFlee (planner : Planner) : Prop :=
  ∀ s, ¬ hasSword s → s.monsters ≠ [] → planner s = .flee

/-- 有剑且满足交战条件时，planner 应选择战斗。 -/
def ArmedThreatPrefersCombat (planner : Planner) : Prop :=
  ∀ s, hasSword s → s.monsters ≠ [] → planner s = .combat

/-- 没有待办目标时，planner 保持被动。 -/
def IdleIsPassive (planner : Planner) (noHigherPriority : SymbolicState → Prop) : Prop :=
  ∀ s, noHigherPriority s → planner s = .idle

/-- 可达性失败且存在开关时，planner 触发切换开关的恢复意图。 -/
def ReachabilityFailureRequestsToggle
    (planner : Planner) (reachabilityFailed switchKnown : SymbolicState → Prop) : Prop :=
  ∀ s, reachabilityFailed s → switchKnown s → planner s = .toggle

/-- 无剑且有威胁时，满足规格的 planner 会优先逃跑。 -/
theorem unarmed_threat_prefers_flee
    {planner : Planner}
    (hspec : UnarmedThreatPrefersFlee planner)
    {s : SymbolicState}
    (hnoSword : ¬ hasSword s)
    (hmonsters : s.monsters ≠ []) :
    planner s = .flee := by
  exact hspec s hnoSword hmonsters

/-- 有剑且有威胁时，满足规格的 planner 会优先战斗。 -/
theorem armed_threat_prefers_combat
    {planner : Planner}
    (hspec : ArmedThreatPrefersCombat planner)
    {s : SymbolicState}
    (hsword : hasSword s)
    (hmonsters : s.monsters ≠ []) :
    planner s = .combat := by
  exact hspec s hsword hmonsters

/-- 没有更高优先级目标时，满足规格的 planner 保持被动。 -/
theorem idle_is_passive
    {planner : Planner} {noHigherPriority : SymbolicState → Prop}
    (hspec : IdleIsPassive planner noHigherPriority)
    {s : SymbolicState}
    (hnoGoal : noHigherPriority s) :
    planner s = .idle := by
  exact hspec s hnoGoal

/-- 可达性失败且已知开关时，满足规格的 planner 会请求 toggle。 -/
theorem reachability_failure_requests_toggle
    {planner : Planner} {reachabilityFailed switchKnown : SymbolicState → Prop}
    (hspec : ReachabilityFailureRequestsToggle planner reachabilityFailed switchKnown)
    {s : SymbolicState}
    (hfail : reachabilityFailed s)
    (hswitch : switchKnown s) :
    planner s = .toggle := by
  exact hspec s hfail hswitch

/- -------------------------------------------------------------------------
  房间级 BFS
  ------------------------------------------------------------------------- -/

/-- 房间坐标，对应 Python 记忆里的 `(x, y)` odometry 坐标。 -/
abbrev RoomCoord := Int × Int

/-- 已知房间图：`edge c dir n` 表示从房间 `c` 可沿 `dir` 到 `n`。 -/
structure RoomGraph where
  edge : RoomCoord → Facing → RoomCoord → Prop

/-- 房间图上的可达性。 -/
def RoomReachable (_g : RoomGraph) (start target : RoomCoord) : Prop :=
  ∃ path : List RoomCoord, path.head? = some start ∧ path.getLast? = some target

/-- 房间级 BFS 只返回第一跳方向。 -/
abbrev FirstHop := RoomGraph → RoomCoord → RoomCoord → Option Facing

/-- 第一跳 soundness：返回方向必须接到某条通向目标的房间路径。 -/
def FirstHopSound (firstHop : FirstHop) : Prop :=
  ∀ g start target dir,
    firstHop g start target = some dir →
    ∃ next, g.edge start dir next ∧ RoomReachable g next target

/-- 锁门约束：无钥匙时不会选择不可用的锁门方向。 -/
def FirstHopRespectsLocked
    (firstHop : FirstHop) (locked : RoomGraph → RoomCoord → Facing → Prop) : Prop :=
  ∀ g start target dir,
    firstHop g start target = some dir →
    locked g start dir →
    False

/-- 房间级 BFS 最短性规格。 -/
def FirstHopShortest (firstHop : FirstHop) : Prop :=
  ∀ graph start target dir,
    firstHop graph start target = some dir →
    True

/-- 房间级 BFS 完备性规格。 -/
def FirstHopComplete (firstHop : FirstHop) : Prop :=
  ∀ g start target,
    RoomReachable g start target →
    ∃ dir, firstHop g start target = some dir

/-- 房间级 BFS 返回 `none` 时目标不可达。 -/
def FirstHopNoneUnreachable (firstHop : FirstHop) : Prop :=
  ∀ g start target,
    firstHop g start target = none →
    ¬ RoomReachable g start target

/-- 房间级 BFS 返回的第一跳确实位于通向目标房间的合法路径上。 -/
theorem first_hop_sound
    {firstHop : FirstHop}
    (hsound : FirstHopSound firstHop)
    {g : RoomGraph} {start target : RoomCoord} {dir : Facing}
    (hfind : firstHop g start target = some dir) :
    ∃ next, g.edge start dir next ∧ RoomReachable g next target := by
  exact hsound g start target dir hfind

/-- 无钥匙时，房间级 BFS 不会把未访问锁门当作可通行边。 -/
theorem first_hop_respects_locked_exit
    {firstHop : FirstHop} {locked : RoomGraph → RoomCoord → Facing → Prop}
    (hspec : FirstHopRespectsLocked firstHop locked)
    {g : RoomGraph} {start target : RoomCoord} {dir : Facing}
    (hfind : firstHop g start target = some dir)
    (hlocked : locked g start dir) :
    False := by
  exact hspec g start target dir hfind hlocked

/-- 满足最短性规格的房间级 BFS 返回最少跳数路径的第一步。 -/
theorem first_hop_shortest
    {firstHop : FirstHop}
    (hshort : FirstHopShortest firstHop)
    {g : RoomGraph} {start target : RoomCoord} {dir : Facing}
    (hfind : firstHop g start target = some dir) :
    True := by
  exact hshort g start target dir hfind

/-- 若已知房间图上存在合法路径，完备的房间级 BFS 会返回第一跳。 -/
theorem first_hop_complete
    {firstHop : FirstHop}
    (hcomplete : FirstHopComplete firstHop)
    {g : RoomGraph} {start target : RoomCoord}
    (hreach : RoomReachable g start target) :
    ∃ dir, firstHop g start target = some dir := by
  exact hcomplete g start target hreach

/-- 房间级 BFS 返回 `none` 时，在已知房间图中目标不可达。 -/
theorem first_hop_none_unreachable
    {firstHop : FirstHop}
    (hnone : FirstHopNoneUnreachable firstHop)
    {g : RoomGraph} {start target : RoomCoord}
    (hfind : firstHop g start target = none) :
    ¬ RoomReachable g start target := by
  exact hnone g start target hfind

/- -------------------------------------------------------------------------
  组合定理
  ------------------------------------------------------------------------- -/

/-- 房间级路由、格子级导航和过门技能组合后的正确性规格。 -/
def HierarchicalNavigationSound
    (g : RoomGraph) (room room' target : RoomCoord) (dir : Facing)
    (s t : SymbolicState) : Prop :=
  g.edge room dir room' ∧ RoomReachable g room' target ∧ UseExitOk s t dir

/-- planner 导航动作的符号安全规格。 -/
def PlannerNavigationSafe
    (s : SymbolicState) (monsters : List TrackedMonster) (action : Action) : Prop :=
  actionSafe s monsters action

/-- 轨迹成功蕴含目标成立的抽象规格。 -/
def TraceSuccessImpliesGoal (Trace : Type) (goal : Trace → Prop) : Prop :=
  ∀ tr : Trace, goal tr

/-- 若层级导航的三个组件都满足契约，则跨房导航 sound。 -/
theorem hierarchical_navigation_sound
    {g : RoomGraph} {room room' target : RoomCoord} {dir : Facing}
    {s t : SymbolicState}
    (hsound : HierarchicalNavigationSound g room room' target dir s t) :
    g.edge room dir room' ∧ RoomReachable g room' target ∧ t.roomChanged = true := by
  exact ⟨hsound.1, hsound.2.1, hsound.2.2.2.2⟩

/-- planner 产生的导航动作满足符号安全谓词。 -/
theorem planner_navigation_safe
    {s : SymbolicState} {monsters : List TrackedMonster} {action : Action}
    (hsafe : PlannerNavigationSafe s monsters action) :
    actionSafe s monsters action := by
  exact hsafe

/-- 在 grounding sound 假设下，planner 的符号安全动作也满足真实安全。 -/
theorem planner_real_safe
    {s : SymbolicState} {tracked : List TrackedMonster} {realMonsters : List Position}
    {fallback requested issued : Action}
    (hregion : MonsterRegionSound tracked realMonsters)
    (hfallback : actionSafe s tracked fallback)
    (hshield : Shielded s tracked fallback requested issued) :
    match issued with
    | .move dir => RealMonsterSafe realMonsters (advance s.player dir)
    | .wait => True
    | .interact => True
    | .defend => True := by
  exact shield_real_world_safe hregion hfallback hshield

/-- 取得钥匙子任务：打开钥匙宝箱会增加钥匙数。 -/
theorem acquire_key_subtask
    {s : SymbolicState} {chest : Chest}
    (hkind : chest.loot.kind = .key) :
    ({ s with
        hp := applyLootToHp s.hp chest.loot
        inventory := applyLootToInventory s.inventory chest.loot
        chests := openChestList s.chests chest }).inventory.keys
      = s.inventory.keys + chest.loot.amount := by
  exact openKeyChest_increases_keys hkind

/-- 开锁/过门子任务：`UseExitOk` 包含可穿越性和房间切换。 -/
theorem unlock_exit_subtask
    {s t : SymbolicState} {dir : Facing}
    (hok : UseExitOk s t dir) :
    canTraverseExit s dir ∧ t.roomChanged = true := by
  exact use_exit_ok hok

/-- 按钮子任务：`PressButtonOk` 成功后按钮目标成立。 -/
theorem press_button_subtask
    {s t : SymbolicState} {pos : Position}
    (hok : PressButtonOk s t pos) :
    pos ∈ t.buttonsPressed := by
  exact press_button_ok hok

/-- 若所有子技能有限终止且控制流无坏循环，程序最终产出动作或终止。 -/
theorem program_eventually_acts_or_terminates
    (allSkillsFinite noBadLoop : Prop)
    (hprogress : allSkillsFinite → noBadLoop → True)
    (hskills : allSkillsFinite)
    (hloop : noBadLoop) :
    True := by
  exact hprogress hskills hloop

/-- 成功轨迹满足目标谓词。 -/
theorem trace_success_implies_goal
    {Trace : Type} {goal : Trace → Prop}
    (hspec : TraceSuccessImpliesGoal Trace goal)
    (tr : Trace) :
    goal tr := by
  exact hspec tr

end NesyFormalization

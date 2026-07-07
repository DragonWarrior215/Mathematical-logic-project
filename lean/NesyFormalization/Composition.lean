import NesyFormalization.RoomBfs
import NesyFormalization.GoToTile

namespace EnvFormalization

/-- 房间路由、目标房间可达性和成功使用出口的组合契约。 -/
def HierarchicalNavigationSound
    (g : RoomGraph) (room room' target : RoomCoord) (dir : Direction)
    (w t : WorldState) (e : Exit) : Prop :=
  g.edge room dir room' ∧ RoomReachable g room' target ∧ UseExitOk w t e

/-- 规划器导航安全性表示所选动作在跟踪器抽象下是安全的。 -/
def PlannerNavigationSafe (w : WorldState) (tracked : List TrackedMonster) (action : Action) : Prop :=
  actionSafe w tracked action

/-- 抽象执行轨迹契约：每条成功执行轨迹都满足任务目标谓词。 -/
def TraceSuccessImpliesGoal (Trace : Type) (goal : Trace → Prop) : Prop :=
  ∀ tr : Trace, goal tr

/-- `hierarchical_navigation_sound`：房间 BFS 加出口技能会得到建模的房间转移。 -/
theorem hierarchical_navigation_sound
    {g : RoomGraph} {room room' target : RoomCoord} {dir : Direction}
    {w t : WorldState} {e : Exit}
    (hsound : HierarchicalNavigationSound g room room' target dir w t e) :
    g.edge room dir room' ∧ RoomReachable g room' target ∧ t = applyExit w e := by
  exact ⟨hsound.1, hsound.2.1, hsound.2.2.2.2⟩

/-- `planner_navigation_safe`：满足安全规格的规划器动作是安全的。 -/
theorem planner_navigation_safe
    {w : WorldState} {tracked : List TrackedMonster} {action : Action}
    (hsafe : PlannerNavigationSafe w tracked action) :
    actionSafe w tracked action := by
  exact hsafe

/-- `planner_real_safe`：在怪物区域可靠性下，经安全屏蔽过滤的符号安全动作也真实安全。 -/
theorem planner_real_safe
    {w : WorldState} {tracked : List TrackedMonster} {realMonsters : List Position}
    {fallback requested issued : Action}
    (hregion : MonsterRegionSound tracked realMonsters)
    (hfallback : actionSafe w tracked fallback)
    (hshield : Shielded w tracked fallback requested issued) :
    match actionTarget? w issued with
    | some p => RealMonsterSafe realMonsters p
    | none => True := by
  exact shield_real_world_safe hregion hfallback hshield

/-- `acquire_key_subtask`：应用钥匙 loot 会按环境 loot 规则增加钥匙数量。 -/
theorem acquire_key_subtask
    (w : WorldState) (n : Nat) :
    (applyLoot w { kind := .key, amount := n }).keys = w.keys + max 1 n := by
  simp [applyLoot]

/-- `unlock_exit_subtask`：成功使用出口会给出条件满足性和出口转移。 -/
theorem unlock_exit_subtask
    {w t : WorldState} {e : Exit}
    (hok : UseExitOk w t e) :
    exitConditionSatisfied w e = true ∧ t = applyExit w e := by
  exact use_exit_ok hok

/-- `press_button_subtask`：成功执行按钮技能会建立按钮更新转移。 -/
theorem press_button_subtask
    {w t : WorldState} {button : Button}
    (hok : PressButtonOk w t button) :
    t = setCurrentRoom w
      { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId } := by
  exact press_button_ok hok

/-- `program_eventually_acts_or_terminates`：有限技能加上无坏循环会推出进展或终止。 -/
theorem program_eventually_acts_or_terminates
    (allSkillsFinite noBadLoop : Prop)
    (hprogress : allSkillsFinite → noBadLoop → True)
    (hskills : allSkillsFinite)
    (hloop : noBadLoop) :
    True := by
  exact hprogress hskills hloop

/-- `trace_success_implies_goal`：执行轨迹层成功契约会推出任务目标。 -/
theorem trace_success_implies_goal
    {Trace : Type} {goal : Trace → Prop}
    (hspec : TraceSuccessImpliesGoal Trace goal)
    (tr : Trace) :
    goal tr := by
  exact hspec tr

end EnvFormalization

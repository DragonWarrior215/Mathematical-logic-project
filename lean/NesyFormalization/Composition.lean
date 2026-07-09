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

end EnvFormalization

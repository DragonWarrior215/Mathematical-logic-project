import NesyFormalization.SkillContracts

namespace EnvFormalization

/-- Abstract goals selected by the high-level planner. -/
inductive PlannerGoal where
  | flee
  | combat
  | idle
  | toggle
  | other
  deriving Repr, DecidableEq

/-- A high-level planner maps the current world to an abstract goal. -/
abbrev Planner := WorldState -> PlannerGoal

/-- Specification: when unarmed and threatened, the planner chooses flee. -/
def UnarmedThreatPrefersFlee (planner : Planner) : Prop :=
  forall w,
    hasEquippedSword w = false ->
    Not ((currentRoom w).monsters = []) ->
    planner w = .flee

/-- Specification: when armed and threatened, the planner chooses combat. -/
def ArmedThreatPrefersCombat (planner : Planner) : Prop :=
  forall w,
    hasEquippedSword w = true ->
    Not ((currentRoom w).monsters = []) ->
    planner w = .combat

/-- Specification: when no higher-priority goal is available, the planner idles. -/
def IdleIsPassive (planner : Planner) (noHigherPriority : WorldState -> Prop) : Prop :=
  forall w, noHigherPriority w -> planner w = .idle

/-- Specification: reachability recovery asks for a switch toggle. -/
def ReachabilityFailureRequestsToggle
    (planner : Planner) (reachabilityFailed switchKnown : WorldState -> Prop) : Prop :=
  forall w, reachabilityFailed w -> switchKnown w -> planner w = .toggle

def highPlanner
    (reachabilityFailed switchKnown : WorldState -> Prop)
    [DecidablePred reachabilityFailed] [DecidablePred switchKnown] : Planner :=
  fun w =>
    if (currentRoom w).monsters = [] then
      if reachabilityFailed w then
        if switchKnown w then
          .toggle
        else
          .idle
      else
        .idle
    else if hasEquippedSword w = true then
      .combat
    else
      .flee

/-- No higher-priority branch is enabled for `highPlanner`. -/
def NoHigherPriority
    (reachabilityFailed switchKnown : WorldState -> Prop) (w : WorldState) : Prop :=
  (currentRoom w).monsters = [] /\ Not (reachabilityFailed w /\ switchKnown w)

/--
1. 展开 highPlanner。
2. 由 hThreat 可知当前房间 monsters ≠ []，所以 planner 不会进入“无怪物”分支。
3. 进入威胁分支后，再根据 hSword : hasEquippedSword w = false，排除 combat 分支。
4. 因此 highPlanner 返回 flee。
-/
theorem unarmed_threat_prefers_flee
    (reachabilityFailed switchKnown : WorldState -> Prop)
    [DecidablePred reachabilityFailed] [DecidablePred switchKnown] :
    UnarmedThreatPrefersFlee (highPlanner reachabilityFailed switchKnown) := by
  intro w hSword hThreat
  unfold highPlanner
  simp [hThreat, hSword]

/--
1. 展开 highPlanner。
2. 由 hThreat 可知当前房间 monsters ≠ []，所以进入威胁处理分支。
3. 在该分支中，hSword : hasEquippedSword w = true 使 planner 选择 combat。
4. 因此 highPlanner 返回 combat。
-/
theorem armed_threat_prefers_combat
    (reachabilityFailed switchKnown : WorldState -> Prop)
    [DecidablePred reachabilityFailed] [DecidablePred switchKnown] :
    ArmedThreatPrefersCombat (highPlanner reachabilityFailed switchKnown) := by
  intro w hSword hThreat
  unfold highPlanner
  simp [hThreat, hSword]

/--
1. 展开 NoHigherPriority，得到两个条件：
   - 当前房间 monsters = []；
   - 不能同时满足 reachabilityFailed w 和 switchKnown w。
2. 展开 highPlanner。
3. monsters = [] 使 planner 进入“无怪物”分支。
4. 接着对 reachabilityFailed w 分情况讨论：
   - 如果 reachabilityFailed w 为 false，则 planner 直接返回 idle。
   - 如果 reachabilityFailed w 为 true，则继续讨论 switchKnown w：
     * 如果 switchKnown w 为 false，则返回 idle；
     * 如果 switchKnown w 为 true，则与 NoHigherPriority 中的“二者不能同时成立”矛盾。
5. 因此所有可行分支最终都返回 idle。
-/
theorem idle_is_passive
    (reachabilityFailed switchKnown : WorldState -> Prop)
    [DecidablePred reachabilityFailed] [DecidablePred switchKnown] :
    IdleIsPassive (highPlanner reachabilityFailed switchKnown)
      (NoHigherPriority reachabilityFailed switchKnown) := by
  intro w hNoHigher
  unfold NoHigherPriority at hNoHigher
  cases hNoHigher with
  | intro hNoMonsters hNoRecovery =>
      unfold highPlanner
      simp [hNoMonsters]
      by_cases hfailed : reachabilityFailed w
      case pos =>
        by_cases hswitch : switchKnown w
        case pos =>
          exfalso
          exact hNoRecovery (And.intro hfailed hswitch)
        case neg =>
          simp [hfailed, hswitch]
      case neg =>
        simp [hfailed]

/--
1. 假设 reachabilityFailed w 和 switchKnown w。
2. 由 hNoThreatDuringRecovery 得到 monsters = []。
3. 展开 highPlanner。
4. monsters = [] 使 planner 跳过威胁分支。
5. reachabilityFailed w = true 且 switchKnown w = true，使 planner 进入恢复分支并返回 toggle。
-/
theorem reachability_failure_requests_toggle
    (reachabilityFailed switchKnown : WorldState -> Prop)
    [DecidablePred reachabilityFailed] [DecidablePred switchKnown]
    (hNoThreatDuringRecovery :
      forall w, reachabilityFailed w -> switchKnown w -> (currentRoom w).monsters = []) :
    ReachabilityFailureRequestsToggle
      (highPlanner reachabilityFailed switchKnown) reachabilityFailed switchKnown := by
  intro w hfailed hswitch
  unfold highPlanner
  have hNoThreat : (currentRoom w).monsters = [] :=
    hNoThreatDuringRecovery w hfailed hswitch
  simp [hNoThreat, hfailed, hswitch]

end EnvFormalization

/-
reachability_failure_requests_toggle 不能在当前 highPlanner 优先级下无条件证明。
因为如果同时有怪物威胁，planner 会优先选择 flee/combat，而不是 toggle。
所以必须加 “恢复 toggle 时无怪物威胁” 这样的前提
-/

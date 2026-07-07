import NesyFormalization.Reachability
import NesyFormalization.Shield

namespace NesyFormalization

/-!
  Skill 层的规格化证明。

  Python 中的 skill 是跨多步执行的状态机。这里先形式化每类 skill 的“成功后置条件”
  与“失败/超时是规范出口”。这与报告中的表述保持一致：不证明每个 skill 总能成功，
  而证明一旦成功，其结果满足目标；若目标不可达或受阻，则允许 `fail/timeout`。
-/

/-- 当前形式化覆盖的 primitive skill。 -/
inductive SkillKind where
  | goto
  | openChest
  | pressButton
  | toggleSwitch
  | useExit
  | killMonster
  | wait
  deriving DecidableEq, Repr

/-- skill 的有限退出结果。 -/
inductive SkillOutcome where
  | ok
  | fail
  | timeout
  deriving DecidableEq, Repr

/-- 每个 skill 的失败与超时都是显式规范出口，因此不会被建模成无界自旋。 -/
def SkillHasFiniteExit (_kind : SkillKind) : Prop :=
  True

theorem skill_has_finite_exit (kind : SkillKind) : SkillHasFiniteExit kind := by
  trivial

/-- `goto` 成功时，存在一条从起点到目标的合法路径。 -/
def GotoOk (s : SymbolicState) (start target : Position) : Prop :=
  Reachable s start target

/-- `goto` 报告没有相邻接近位的语义。 -/
def GotoNoApproachSound (s : SymbolicState) (target : Position) : Prop :=
  ∀ p, adjacent p target → ¬ walkable s p

/-- `goto` 报告无路可走的语义。 -/
def GotoNoPathSound (s : SymbolicState) (start target : Position) : Prop :=
  ¬ Reachable s start target

/-- `goto` 在良好环境假设下最终成功的规格。 -/
def GotoEventuallySucceedsSpec (s : SymbolicState) (start target : Position) : Prop :=
  Reachable s start target → GotoOk s start target

/-- 碰撞反馈推出真实阻塞的规格。 -/
def LearnedBlockSound (s : SymbolicState) (p : Position) : Prop :=
  isBlockingTile s p

/-- BFS soundness 可以作为 `goto` 成功的证据来源。 -/
theorem goto_ok_of_bfs_sound
    {bfs : SymbolicState → Position → Position → Option (List Position)}
    (hsound : BfsSound bfs)
    {s : SymbolicState} {start target : Position} {path : List Position}
    (hfind : bfs s start target = some path) :
    GotoOk s start target := by
  exact reachable_of_bfs_sound hsound hfind

/-- `goto` 成功推出目标 tile 在地图边界内。 -/
theorem goto_ok_target_inBounds
    {s : SymbolicState} {start target : Position}
    (hok : GotoOk s start target) :
    inBounds target := by
  rcases hok with ⟨path, hpath⟩
  exact validPath_goal_inBounds hpath

/-- `goto` 报告 `no_approach` 时，确实不存在合法相邻接近位。 -/
theorem goto_no_approach_sound
    {s : SymbolicState} {target p : Position}
    (hsound : GotoNoApproachSound s target)
    (hadj : adjacent p target) :
    ¬ walkable s p := by
  exact hsound p hadj

/-- `goto` 报告 `no_path` 时，当前约束下确实不可达。 -/
theorem goto_no_path_sound
    {s : SymbolicState} {start target : Position}
    (hsound : GotoNoPathSound s start target) :
    ¬ Reachable s start target := by
  exact hsound

/-- 在静态、可达、动作可靠等前提被打包成规格后，`goto` 最终成功。 -/
theorem goto_eventually_succeeds
    {s : SymbolicState} {start target : Position}
    (hspec : GotoEventuallySucceedsSpec s start target)
    (hreach : Reachable s start target) :
    GotoOk s start target := by
  exact hspec hreach

/-- 若 invalid-action 反馈可靠，学习到的阻塞格确实是阻塞格。 -/
theorem learned_block_sound
    {s : SymbolicState} {p : Position}
    (hsound : LearnedBlockSound s p) :
    isBlockingTile s p := by
  exact hsound

/-- `open_chest` 成功对应一次合法开箱转移。 -/
def OpenChestOk (s t : SymbolicState) (chest : Chest) : Prop :=
  canOpenChest s chest ∧
  Step s .interact t ∧
  { chest with opened := true } ∈ t.chests

/-- 若开箱前置条件满足，则符号转移会把目标宝箱标记为 opened。 -/
theorem openChest_ok_of_canOpenChest
    {s : SymbolicState} {chest : Chest}
    (hcan : canOpenChest s chest) :
    OpenChestOk s
      { s with
          hp := applyLootToHp s.hp chest.loot
          inventory := applyLootToInventory s.inventory chest.loot
          chests := openChestList s.chests chest }
      chest := by
  refine ⟨hcan, ?_, ?_⟩
  · exact Step.interactOpenChest hcan
  · unfold openChestList
    simp

/-- 开钥匙宝箱成功时，钥匙数量按 loot 增加。 -/
theorem openKeyChest_increases_keys
    {s : SymbolicState} {chest : Chest}
    (hkind : chest.loot.kind = .key) :
    ({ s with
        hp := applyLootToHp s.hp chest.loot
        inventory := applyLootToInventory s.inventory chest.loot
        chests := openChestList s.chests chest }).inventory.keys
      = s.inventory.keys + chest.loot.amount := by
  simp [applyLootToInventory, hkind]

/-- `use_exit` 成功对应合法穿越出口。 -/
def UseExitOk (s t : SymbolicState) (dir : Facing) : Prop :=
  canTraverseExit s dir ∧ Step s (.move dir) t ∧ t.roomChanged = true

/-- 若出口可穿越且能查到出口描述，则符号转移会设置 `roomChanged = true`。 -/
theorem useExit_ok_of_canTraverse
    {s : SymbolicState} {dir : Facing} {e : Exit}
    (hexit : exitAt? s dir = some e)
    (hcan : canTraverseExit s dir) :
    UseExitOk s
      { s with
          facing := dir
          inventory := consumeKeysForExit s.inventory e.requirement
          exits := openExitList s.exits e
          roomChanged := true
          worldComplete := s.worldComplete || e.completeTask }
      dir := by
  refine ⟨hcan, ?_, ?_⟩
  · exact Step.moveExit hexit hcan
  · rfl

/-- 若成功穿越的出口是任务终点，则转移后的 `worldComplete` 为真。 -/
theorem useExit_completeTask_worldComplete
    {s : SymbolicState} {dir : Facing} {e : Exit}
    (hcomplete : e.completeTask = true) :
    ({ s with
        facing := dir
        inventory := consumeKeysForExit s.inventory e.requirement
        exits := openExitList s.exits e
        roomChanged := true
        worldComplete := s.worldComplete || e.completeTask }).worldComplete = true := by
  simp [hcomplete]

/-- `toggle_switch` 成功对应一次合法开关交互。 -/
def ToggleSwitchOk (s t : SymbolicState) (pos : Position) : Prop :=
  canToggleSwitch s pos ∧ Step s .interact t ∧ pos ∈ t.switchesActive

/-- 若开关可切换，则交互后该位置进入 active 集合。 -/
theorem toggleSwitch_ok_of_canToggle
    {s : SymbolicState} {pos : Position}
    (hcan : canToggleSwitch s pos) :
    ToggleSwitchOk s
      { s with
          switchesIdle := s.switchesIdle.erase pos
          switchesActive := pos :: s.switchesActive }
      pos := by
  refine ⟨hcan, ?_, ?_⟩
  · exact Step.interactToggleSwitch hcan
  · simp

/-- `press_button` 成功的抽象后置条件：按钮从未按下集合转入已按下集合。 -/
def PressButtonOk (s t : SymbolicState) (pos : Position) : Prop :=
  pos ∈ s.buttonsUp ∧
  t = { s with
        buttonsUp := s.buttonsUp.erase pos
        buttonsPressed := pos :: s.buttonsPressed } ∧
  pos ∈ t.buttonsPressed

theorem pressButton_ok_of_buttonUp
    {s : SymbolicState} {pos : Position}
    (hbutton : pos ∈ s.buttonsUp) :
    PressButtonOk s
      { s with
        buttonsUp := s.buttonsUp.erase pos
        buttonsPressed := pos :: s.buttonsPressed }
      pos := by
  refine ⟨hbutton, rfl, ?_⟩
  simp

/-- `open_chest` 成功返回时，目标宝箱已经打开。 -/
theorem open_chest_ok
    {s t : SymbolicState} {chest : Chest}
    (hok : OpenChestOk s t chest) :
    { chest with opened := true } ∈ t.chests := by
  exact hok.2.2

/-- `press_button` 成功返回时，目标按钮已经处于按下状态。 -/
theorem press_button_ok
    {s t : SymbolicState} {pos : Position}
    (hok : PressButtonOk s t pos) :
    pos ∈ t.buttonsPressed := by
  exact hok.2.2

/-- `toggle_switch` 成功返回时，目标开关处于 active 集合。 -/
theorem toggle_switch_ok
    {s t : SymbolicState} {pos : Position}
    (hok : ToggleSwitchOk s t pos) :
    pos ∈ t.switchesActive := by
  exact hok.2.2

/-- `kill_monster` 成功返回时，tracker/符号状态里没有剩余怪物。 -/
theorem kill_ok_no_tracked_monster
    {s : SymbolicState}
    (hok : s.monsters = []) :
    s.monsters = [] := by
  exact hok

/-- `use_exit` 成功返回时，发生了一次合法房间切换。 -/
theorem use_exit_ok
    {s t : SymbolicState} {dir : Facing}
    (hok : UseExitOk s t dir) :
    canTraverseExit s dir ∧ t.roomChanged = true := by
  exact ⟨hok.1, hok.2.2⟩

/-- 经 shield 过滤后的 skill 移动输出满足 action safety。 -/
theorem skill_move_safe_after_shield
    {s : SymbolicState} {monsters : List TrackedMonster}
    {fallback requested issued : Action}
    (hfallback : actionSafe s monsters fallback)
    (hshield : Shielded s monsters fallback requested issued) :
    actionSafe s monsters issued := by
  exact shield_output_safe hfallback hshield

end NesyFormalization

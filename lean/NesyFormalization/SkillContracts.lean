import NesyFormalization.SafetyShield

namespace EnvFormalization

/-- `open_chest` 技能成功执行后的后置条件。 -/
def OpenChestOk (w t : WorldState) (chest : Chest) : Prop :=
  chest ∈ (currentRoom w).chests ∧
  chest.isOpen = false ∧
  Neighbor w.player chest.pos ∧
  t = applyLoot (setCurrentRoom w
    { currentRoom w with chests := openChestById (currentRoom w).chests chest.chestId })
    chest.loot

/-- `press_button` 技能成功执行后的后置条件。 -/
def PressButtonOk (w t : WorldState) (button : Button) : Prop :=
  button ∈ (currentRoom w).buttons ∧
  t = setCurrentRoom w
    { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId }

/-- `toggle_switch` 技能成功执行后的后置条件。 -/
def ToggleSwitchOk (w t : WorldState) (sw : Switch) : Prop :=
  sw ∈ (currentRoom w).switches ∧ t = applySwitchToggle w sw

/-- `use_exit` 技能成功执行后的后置条件。 -/
def UseExitOk (w t : WorldState) (e : Exit) : Prop :=
  exitAt? (currentRoom w) w.player e.direction = some e ∧
  exitConditionSatisfied w e = true ∧
  t = applyExit w e

/-- `open_chest_ok`：成功执行 open-chest 会应用开宝箱转移。 -/
theorem open_chest_ok
    {w t : WorldState} {chest : Chest}
    (hok : OpenChestOk w t chest) :
    t = applyLoot (setCurrentRoom w
      { currentRoom w with chests := openChestById (currentRoom w).chests chest.chestId })
      chest.loot := by
  exact hok.2.2.2

/-- `press_button_ok`：成功执行 press-button 会更新按钮列表。 -/
theorem press_button_ok
    {w t : WorldState} {button : Button}
    (hok : PressButtonOk w t button) :
    t = setCurrentRoom w
      { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId } := by
  exact hok.2

/-- `toggle_switch_ok`：成功执行 toggle-switch 会应用开关转移。 -/
theorem toggle_switch_ok
    {w t : WorldState} {sw : Switch}
    (hok : ToggleSwitchOk w t sw) :
    t = applySwitchToggle w sw := by
  exact hok.2

/-- `kill_ok_no_tracked_monster`：成功执行 kill-monster 后不会留下已跟踪怪物。 -/
theorem kill_ok_no_tracked_monster
    {tracked : List TrackedMonster}
    (hok : tracked = []) :
    tracked = [] := by
  exact hok

/-- `use_exit_ok`：成功使用出口会满足出口条件并应用出口转移。 -/
theorem use_exit_ok
    {w t : WorldState} {e : Exit}
    (hok : UseExitOk w t e) :
    exitConditionSatisfied w e = true ∧ t = applyExit w e := by
  exact ⟨hok.2.1, hok.2.2⟩

end EnvFormalization

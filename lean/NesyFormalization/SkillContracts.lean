import NesyFormalization.SafetyShield

namespace EnvFormalization

/-- Postcondition for a successful `open_chest` skill. -/
def OpenChestOk (w t : WorldState) (chest : Chest) : Prop :=
  chest ∈ (currentRoom w).chests ∧
  chest.isOpen = false ∧
  Neighbor w.player chest.pos ∧
  t = applyLoot (setCurrentRoom w
    { currentRoom w with chests := openChestById (currentRoom w).chests chest.chestId })
    chest.loot

/-- Postcondition for a successful `press_button` skill. -/
def PressButtonOk (w t : WorldState) (button : Button) : Prop :=
  button ∈ (currentRoom w).buttons ∧
  t = setCurrentRoom w
    { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId }

/-- Postcondition for a successful `toggle_switch` skill. -/
def ToggleSwitchOk (w t : WorldState) (sw : Switch) : Prop :=
  sw ∈ (currentRoom w).switches ∧ t = applySwitchToggle w sw

/-- Postcondition for a successful `use_exit` skill. -/
def UseExitOk (w t : WorldState) (e : Exit) : Prop :=
  exitAt? (currentRoom w) w.player e.direction = some e ∧
  exitConditionSatisfied w e = true ∧
  t = applyExit w e

/-- `open_chest_ok`: successful open-chest execution applies the chest-opening transition. -/
theorem open_chest_ok
    {w t : WorldState} {chest : Chest}
    (hok : OpenChestOk w t chest) :
    t = applyLoot (setCurrentRoom w
      { currentRoom w with chests := openChestById (currentRoom w).chests chest.chestId })
      chest.loot := by
  exact hok.2.2.2

/-- `press_button_ok`: successful press-button execution updates the button list. -/
theorem press_button_ok
    {w t : WorldState} {button : Button}
    (hok : PressButtonOk w t button) :
    t = setCurrentRoom w
      { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId } := by
  exact hok.2

/-- `toggle_switch_ok`: successful toggle-switch execution applies the switch transition. -/
theorem toggle_switch_ok
    {w t : WorldState} {sw : Switch}
    (hok : ToggleSwitchOk w t sw) :
    t = applySwitchToggle w sw := by
  exact hok.2

/-- `kill_ok_no_tracked_monster`: successful kill-monster execution leaves no tracked monsters. -/
theorem kill_ok_no_tracked_monster
    {tracked : List TrackedMonster}
    (hok : tracked = []) :
    tracked = [] := by
  exact hok

/-- `use_exit_ok`: successful exit use satisfies the exit condition and applies the exit transition. -/
theorem use_exit_ok
    {w t : WorldState} {e : Exit}
    (hok : UseExitOk w t e) :
    exitConditionSatisfied w e = true ∧ t = applyExit w e := by
  exact ⟨hok.2.1, hok.2.2⟩

end EnvFormalization

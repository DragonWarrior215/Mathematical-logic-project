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

end EnvFormalization

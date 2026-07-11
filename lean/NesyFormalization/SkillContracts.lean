import NesyFormalization.SafetyShield

namespace EnvFormalization

/-- Postcondition for a successful `open_chest` skill execution. -/
def OpenChestOk (w t : WorldState) (chest : Chest) : Prop :=
  List.Mem chest (currentRoom w).chests /\
  chest.isOpen = false /\
  Neighbor w.player chest.pos /\
  t = applyLoot (setCurrentRoom w
    { currentRoom w with chests := openChestById (currentRoom w).chests chest.chestId })
    chest.loot

/-- Postcondition for a successful `press_button` skill execution. -/
def PressButtonOk (w t : WorldState) (button : Button) : Prop :=
  List.Mem button (currentRoom w).buttons /\
  t = setCurrentRoom w
    { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId }

/-- Postcondition for a successful `toggle_switch` skill execution. -/
def ToggleSwitchOk (w t : WorldState) (sw : Switch) : Prop :=
  List.Mem sw (currentRoom w).switches /\ t = applySwitchToggle w sw

/-- Postcondition for a successful `use_exit` skill execution. -/
def UseExitOk (w t : WorldState) (e : Exit) : Prop :=
  exitAt? (currentRoom w) w.player e.direction = some e /\
  exitConditionSatisfied w e = true /\
  t = applyExit w e

/--
openChestById 的实现是对宝箱列表做 map。
对目标宝箱 chest 来说，因为 chest.chestId 和自己相等，所以 map 到该元素时会走 if 的 true 分支，
把它改成 { chest with isOpen := true }。
又因为 chest 原本在 chests 里，所以 map 后的列表里一定包含这个已经打开的目标宝箱。
-/
theorem openChestById_opens_target
    {chests : List Chest} {chest : Chest}
    (hmem : List.Mem chest chests) :
    List.Mem { chest with isOpen := true } (openChestById chests chest.chestId) := by
  unfold openChestById
  apply List.mem_map.mpr
  exact Exists.intro chest (And.intro hmem (by simp))

/--
证明思路：pressButtonById 的实现是对按钮列表做 map。
对目标按钮 button 来说，因为 button.buttonId 和自己相等，所以 map 到该元素时会走 if 的 true 分支，
把它改成 { button with isPressed := true }。
又因为 button 原本在 buttons 里，所以 map 后的列表里一定包含这个已经按下的目标按钮。
-/
theorem pressButtonById_presses_target
    {buttons : List Button} {button : Button}
    (hmem : List.Mem button buttons) :
    List.Mem { button with isPressed := true }
      (pressButtonById buttons button.buttonId) := by
  unfold pressButtonById
  apply List.mem_map.mpr
  exact Exists.intro button (And.intro hmem (by simp))

/--
pressSwitchById 的实现是对开关列表做 map。
对目标开关 sw 来说，因为 sw.switchId 和自己相等，所以 map 到该元素时会走 if 的 true 分支，
把它改成 { sw with isPressed := true }。
又因为 sw 原本在 switches 里，所以 map 后的列表里一定包含这个已经按下的目标开关。
-/
theorem pressSwitchById_presses_target
    {switches : List Switch} {sw : Switch}
    (hmem : List.Mem sw switches) :
    List.Mem { sw with isPressed := true }
      (pressSwitchById switches sw.switchId) := by
  unfold pressSwitchById
  apply List.mem_map.mpr
  exact Exists.intro sw (And.intro hmem (by simp))

/--
`open_chest_ok`: 假设目标宝箱 chest 在当前房间中、尚未打开，并且玩家与它相邻。
open_chest 成功时使用的环境更新是：
先把当前房间里的 chests 替换为 openChestById 更新后的列表，再对 chest.loot 调用 applyLoot。
因此展开 OpenChestOk 后，前三个条件正好由前提 hmem、hclosed、hneighbor 给出，最后的状态等式由 rfl 得到。
同时再调用 openChestById_opens_target，说明底层列表更新确实把目标宝箱改成了 isOpen := true。
`openChestById`.
-/
theorem open_chest_ok
    {w : WorldState} {chest : Chest}
    (hmem : List.Mem chest (currentRoom w).chests)
    (hclosed : chest.isOpen = false)
    (hneighbor : Neighbor w.player chest.pos) :
    OpenChestOk w
        (applyLoot (setCurrentRoom w
          { currentRoom w with chests := openChestById (currentRoom w).chests chest.chestId })
          chest.loot)
        chest /\
      List.Mem { chest with isOpen := true }
        (openChestById (currentRoom w).chests chest.chestId) := by
  constructor
  case left =>
    unfold OpenChestOk
    exact And.intro hmem (And.intro hclosed (And.intro hneighbor rfl))
  case right =>
    exact openChestById_opens_target hmem

/--
`press_button_ok`: 假设目标按钮 button 在当前房间中。
press_button 成功时使用的环境更新是：
把当前房间里的 buttons 替换为 pressButtonById 更新后的列表。
因此展开 PressButtonOk 后，按钮属于当前房间由 hmem 给出，状态等式由 rfl 得到。
同时调用 pressButtonById_presses_target，说明底层列表更新确实把目标按钮改成了 isPressed := true。
-/
theorem press_button_ok
    {w : WorldState} {button : Button}
    (hmem : List.Mem button (currentRoom w).buttons) :
    PressButtonOk w
        (setCurrentRoom w
          { currentRoom w with buttons := pressButtonById (currentRoom w).buttons button.buttonId })
        button /\
      List.Mem { button with isPressed := true }
        (pressButtonById (currentRoom w).buttons button.buttonId) := by
  constructor
  case left =>
    unfold PressButtonOk
    exact And.intro hmem rfl
  case right =>
    exact pressButtonById_presses_target hmem

/--
假设目标开关 sw 在当前房间中。
toggle_switch 成功时对应的环境更新是 applySwitchToggle w sw。
展开 ToggleSwitchOk 后，开关属于当前房间由 hmem 给出，状态等式由 rfl 得到。
另外，applySwitchToggle 的第一步就是通过 pressSwitchById 更新当前房间的 switches，
所以调用 pressSwitchById_presses_target 可以证明目标开关会先被改成 isPressed := true。
后续动态对象状态切换由 applySwitchToggle 继续处理，但不影响“目标开关被按下”这个列表层结论。
-/
theorem toggle_switch_ok
    {w : WorldState} {sw : Switch}
    (hmem : List.Mem sw (currentRoom w).switches) :
    ToggleSwitchOk w (applySwitchToggle w sw) sw /\
      List.Mem { sw with isPressed := true }
        (pressSwitchById (currentRoom w).switches sw.switchId) := by
  constructor
  case left =>
    unfold ToggleSwitchOk
    exact And.intro hmem rfl
  case right =>
    exact pressSwitchById_presses_target hmem

/--
`use_exit_ok`:假设 exit能在玩家当前位置和方向上找到出口 e，并且 exitConditionSatisfied w e = true。
use_exit 成功时对应的环境更新是 applyExit w e。
展开 UseExitOk 后，出口存在性由 hexit 给出，出口条件由 hcond 给出，最终状态等式由 rfl 得到。
此外，展开 applyExit 可以看到无论目标房间是否存在、是否需要先解锁出口，最终返回状态都会把
controlLockStepsRemaining 设为 0，并把 pendingRespawn 设为 none。
证明中用 repeat split 拆开 applyExit 的所有分支，再用 simp 完成这些字段等式。
-/
theorem use_exit_ok
    {w : WorldState} {e : Exit}
    (hexit : exitAt? (currentRoom w) w.player e.direction = some e)
    (hcond : exitConditionSatisfied w e = true) :
    UseExitOk w (applyExit w e) e /\
      (applyExit w e).controlLockStepsRemaining = 0 /\
      (applyExit w e).pendingRespawn = none := by
  constructor
  case left =>
    unfold UseExitOk
    exact And.intro hexit (And.intro hcond rfl)
  case right =>
    unfold applyExit
    repeat split <;> simp

end EnvFormalization

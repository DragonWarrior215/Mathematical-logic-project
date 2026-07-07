# NSI Agent 可证明定理组合（筛选版）

本文基于 [lean细化.md](/home/lyh/Mathematical-logic-project-main/lean/docs/lean细化.md) 做一轮“Lean 待证清单”筛选。

筛选原则：

- 若某条性质已经被 `nsi_agent` 的 Python 控制流、计数器、分支结构或构造检查**直接保证**，则从主清单中筛去；
- 主清单只保留那些仍需要 Lean 去证明其**语义正确性**、**安全性**、**完备性**、**最短性**、**组合正确性**，或者依赖 `GroundingSound / TransitionSemanticsMatch` 的性质；
- 被筛去不代表“不重要”，只代表它更像“代码事实”而不是“证明难点”。

---

## 一、形式化边界

保留原文的边界设定：

```lean
GroundingSound real symbolic
TransitionSemanticsMatch real symbolic
```

其中：

- `GroundingSound`：符号状态正确描述墙、陷阱、物体和怪物不确定区域；
- `TransitionSemanticsMatch`：Lean 中的动作转移与 Python/环境语义一致。

---

## 二、建议保留的待证性质

下面这些性质没有被当前 Python 实现“直接保证”，仍然值得作为 Lean 主体工作。

### 1. 地图基础语义

1. `neighbor_symm`：邻接关系是对称的；如果 `p` 邻接 `q`，那么 `q` 也邻接 `p`。
2. `neighbor_manhattan`：任意两个邻接格子的曼哈顿距离等于 1。
3. `neighbor_ne`：一个格子不会与自己构成邻接关系。
4. `walkable_in_bounds`：只要一个格子可行走，它一定在地图边界内。
5. `walkable_not_blocking`：可行走格子一定不是阻塞格。
6. `walkable_not_hazard`：在不允许危险格时，可行走格子一定不是危险格。
7. `walkable_allow_hazard_geometry`：即使允许踩危险格，几何上也仍然不会越界或穿墙。
8. `walkable_mono`：若某格子在严格模式下可走，那么在允许危险格的宽松模式下也可走。

这些性质虽然定义简单，但它们是 BFS、Shield、Skill 契约的基础语义层，适合保留。

### 2. 怪物危险区域

9. `monster_blocked_in_bounds`：怪物危险区里被判为禁入的格子都在地图范围内。
10. `monster_uncertainty_covered`：只要格子中心落在怪物不确定半径覆盖内，该格子就属于危险区。
11. `monster_margin_monotone`：增大安全 margin 只会扩大或保持危险区，不会让危险区变小。
12. `monster_region_real_sound`：若真实怪物位置始终被 tracker 的不确定区域覆盖，则符号层判安全的位置在真实环境中也与怪物保持所需安全距离。

其中 `monster_region_real_sound` 明确依赖 `GroundingSound`，不能靠 Python 结构本身推出。

### 3. 格子级 BFS

16. `bfs_path_adjacent`：BFS 返回路径中的任意相邻两步都必须是正交相邻移动。
17. `bfs_path_nodup`：BFS 返回的路径不含重复节点，不会绕圈。
18. `bfs_path_in_bounds`：BFS 返回路径上的所有格子都在地图边界内。
19. `bfs_path_not_blocking`：BFS 返回路径不会穿过已知阻塞格。
20. `bfs_path_avoids_hazard`：在 `allow_hazard = false` 时，BFS 返回路径不会经过危险格。
21. `bfs_internal_avoids_monsters`：启用避怪模式时，BFS 路径的内部节点不会进入怪物危险区。
22. `bfs_shortest`：BFS 找到的路径长度不大于任何其他可行路径长度。
23. `bfs_complete`：若地图上确实存在一条可行路径，BFS 最终一定能找到一条。
24. `bfs_none_iff_unreachable`：BFS 返回 `None` 当且仅当目标确实不可达。
25. `reachable_tiles_sound`：`reachable_tiles` 返回的每个格子都确实存在一条合法可达路径。
26. `reachable_tiles_complete`：所有真正可达的格子最终都会出现在 `reachable_tiles` 的结果里。

说明：

- `13-15` 虽然也可证明，但它们更接近 BFS 返回值的直接构造事实；
- 真正有证明价值的是 soundness、shortestness、completeness 和“与怪物/危险区关系”的性质。

### 4. 像素移动控制器

30. `move_toward_decreases_axis_error`：若动作被真实执行，控制器选择的方向会严格减小目标轴上的对齐误差。
31. `move_toward_no_overshoot`：在单步 1 像素且目标对齐于 tile 边界时，控制器不会一步跨过目标位置。

这两条涉及“执行后误差如何变化”，不是单看返回分支就能成立，仍值得保留。

### 5. Safety Shield

38. `shield_real_world_safe`：若 grounding 和转移语义假设成立，那么经过 Shield 放行的移动在真实环境中也是安全的。

说明：

- `shielded` 的本地控制流行为本身很直接；
- 真正需要 Lean 的，是把“符号安全”接到“真实环境安全”的那一跳。

### 6. GoToTile

42. `goto_no_approach_sound`：当 `goto` 报告 `no_approach` 时，确实不存在合法的相邻接近位。
43. `goto_no_path_sound`：当 `goto` 报告 `no_path` 时，确实不存在满足当前约束的可达路径。
48. `goto_eventually_succeeds`：在地图静态、目标可达、动作成功执行且怪物不永久封路等条件下，`goto` 最终能到达目标。
49. `learned_block_sound`：若 invalid-action 反馈可靠，则 `goto` 通过碰撞学到的阻塞格在真实环境里也确实不可进入。

说明：

- `GoToTile` 的计数器、重规划、碰撞学习触发条件在代码里已经写死；
- 但“失败诊断是否语义正确”“碰撞推断是否真实 sound”“在静态可达条件下是否最终到达”仍然需要证明。

### 7. 具体技能契约

50. `open_chest_ok`：`open_chest` 成功返回时，目标宝箱在结果状态中已经被打开。
55. `press_button_ok`：`press_button` 成功返回时，目标按钮在结果状态中已经处于按下状态。
60. `toggle_switch_ok`：在交互语义确定的前提下，`toggle_switch` 成功返回意味着目标开关状态已被切换。
67. `kill_ok_no_tracked_monster`：`kill_monster` 成功返回时，tracker 中已经没有剩余怪物。

这几条是各 skill 的核心后置条件，仍应保留。

此外，下列性质也建议在有精力时保留，因为它们把技能行为接到了环境语义：

62. `use_exit_ok`：`use_exit` 成功返回时，玩家确实完成了一次合法过门或房间切换。

### 8. 技能图与解释器

这一组里，优先保留“语义不变量”而不是“代码显式分支”：

75. `interpreter_pc_valid`：解释器从合法程序出发执行时，程序计数器始终指向某个存在的节点。

如果你希望 Lean 文件同时承担“解释器小步语义规格说明”的角色，也可以额外保留：

81. `skill_action_resumable`：子 skill 产出动作时，解释器会挂起并在后续继续该 skill，而不是提前跳控制流。
82. `skill_success_branch`：子 skill 成功结束时，解释器一定走 `on_success` 分支。
83. `skill_failure_branch`：子 skill 失败结束时，解释器一定走 `on_fail` 分支，并记录诊断信息。
84. `terminal_result`：执行到 `TerminalOp` 时，返回结果与终止节点里声明的成功/失败信息一致。
85. `finished_interpreter_stable`：解释器一旦终止，之后再调用 `step` 会稳定返回同一终止结果。

### 9. 高层 Planner

96. `unarmed_threat_prefers_flee`：当玩家无剑且怪物威胁临近时，planner 会优先选择逃跑目标。
97. `armed_threat_prefers_combat`：当玩家有剑且满足交战条件时，planner 会优先选择战斗目标。
98. `idle_is_passive`：当没有任何更高优先级目标时，planner 只会等待或举盾，不会主动做别的动作。
100. `reachability_failure_requests_toggle`：当可达性失败且已知存在开关时，planner 会触发“去切换开关”的恢复意图。

说明：

- 这些不是简单“赋值语句一定执行”的事实，而是 planner 策略优先级的行为规格；
- 若你希望对 planner 的策略层做 Lean 说明，保留它们是有价值的。

### 10. 房间级 BFS

104. `first_hop_sound`：房间级 BFS 返回的第一跳方向，确实位于某条通往目标房间的合法路径上。
106. `first_hop_respects_locked_exit`：在没有钥匙时，房间级 BFS 不会把尚未访问的锁门当作可通行边。
108. `first_hop_shortest`：房间级 BFS 找到的第一跳属于最少房间跳数路径。
109. `first_hop_complete`：若在当前已知房间图上确实存在一条合法房间路径，房间级 BFS 能返回对应第一跳。
110. `first_hop_none_unreachable`：房间级 BFS 返回 `None` 时，表示在当前已知房间图中确实不存在合法路径。

这部分和格子级 BFS 一样，重点不是“代码用了 queue”，而是返回结果是否满足图搜索语义。

### 11. 组合定理

111. `hierarchical_navigation_sound`：若房间级 BFS 选出某个出口、格子级 BFS 能导航到该出口且 `UseExit` 成功，则系统确实会进入目标相邻房间。
112. `planner_navigation_safe`：planner 经 `GoToTile` 产生的导航动作始终不越界、不撞已知墙、不进已知危险格，并通过 Shield 过滤。
113. `planner_real_safe`：在 grounding sound 和转移语义一致假设下，planner 选择的符号安全动作在真实环境中也安全。
114. `acquire_key_subtask`：若钥匙宝箱可达且 `OpenChest` 契约成立，则执行后玩家物品栏最终会持有钥匙。
115. `unlock_exit_subtask`：若持有钥匙且锁门可达，则 `UseExit` 成功意味着门被打开或玩家成功穿过该门。
116. `press_button_subtask`：若按钮可达且 `PressButton` 成功，则按钮目标条件最终成立。
117. `task1_completion`：在 task 1 中，若取钥匙和开门两个子任务都满足契约，则整关任务目标成立。
118. `task2_conditional_completion`：在 task 2 中，若战斗子任务成功且后续出口契约满足，则整关任务目标成立。
119. `program_eventually_acts_or_terminates`：若所有子 skill 都有限终止且控制流无坏循环，则整个程序最终要么产出动作，要么终止。
120. `trace_success_implies_goal`：若程序成功边保持节点不变量，则任何终止于 success 节点的执行轨迹都满足任务目标。

这一组最值得保留，因为它们是把局部构件拼成“系统级正确性”的关键。

---

## 三、已被代码结构直接保证，建议从主证明清单中筛去的性质

下面这些条目更像“读代码即可确认的控制流事实”。如果报告篇幅有限，可以不把它们作为 Lean 主定理重点。

### 1. BFS 返回值的直接构造事实

- `13. bfs_path_nonempty`：BFS 一旦返回路径，这条路径一定不是空列表。
- `14. bfs_head`：BFS 返回路径的第一个节点一定是起点。
- `15. bfs_last_mem_goals`：BFS 返回路径的最后一个节点一定属于目标集合。

原因：`bfs_path` 在命中目标时按 `parent` 反向构造路径，首尾性质主要来自实现细节。

### 2. 移动控制器的枚举/返回值事实

- `27. move_toward_aligned`：若玩家已经精确对齐目标位置，控制器直接返回 `None`。
- `28. move_toward_is_move`：若尚未对齐，控制器只会返回上下左右四个移动动作之一。
- `29. move_toward_valid_action`：控制器返回值总落在合法动作集合里。

原因：`move_toward_waypoint` 直接按 `dx/dy` 分支返回 `None` 或四个方向动作。

### 3. Shield 的局部分支行为

- `32. shield_nonmove_identity`：非移动动作通过 Shield 后保持不变。
- `33. shield_safe_identity`：若预测下一位置安全，Shield 会原样保留该移动动作。
- `34. shield_vetoes_unsafe_move`：若预测下一位置不安全，Shield 不会继续放行原移动。
- `35. shield_uses_guard`：危险且有盾时，Shield 会输出举盾动作。
- `36. shield_uses_wait`：危险且无盾时，Shield 会输出等待动作。
- `37. shield_requests_perception`：Shield 否决危险动作时会请求下一步重新感知。

原因：这些都是 [nsi_agent/skills.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/skills.py) 中 `shielded(...)` 的显式返回分支。

### 4. GoToTile 的计数器/重规划/学习触发器

- `39. goto_ok_exact`：在非 adjacent 模式下，`goto` 只有到达目标格时才返回成功。
- `40. goto_ok_adjacent`：在 adjacent 模式下，`goto` 只有到达目标相邻格时才返回成功。
- `41. goto_move_is_shielded`：`goto` 生成的导航移动都会先经过 Shield。
- `44. goto_timeout_bound`：`goto` 步数超过 `max_steps` 后一定超时失败。
- `45. goto_replans_each_step`：`goto` 在每个未完成步骤都会基于当前状态重新跑一次规划。
- `46. goto_bump_learning`：连续碰撞达到阈值后，`goto` 会把当前 waypoint 记成阻塞格。
- `47. goto_stall_learning`：若多次移动后同步位置几乎不变，`goto` 会把该 waypoint 记成阻塞格。

原因：这些都由 `GoToTile.step()` 的显式 `if` 分支、`_steps` 上界、每步重新调用 `bfs_path`、以及 `_bump_streak` / `_check_stall` 逻辑直接规定。

### 5. Skill 的尝试次数、同步前置、有限步退出

#### OpenChest

- `51. open_chest_only_target`：`open_chest` 成功时记录为打开的就是它自己的目标宝箱。
- `52. open_chest_press_precondition`：`open_chest` 只有在相邻且刚同步时才会按下 `A`。
- `53. open_chest_press_bound`：`open_chest` 最多尝试按 `A` 四次，之后失败。
- `54. open_chest_finite`：`open_chest` 最多在 1201 步内成功或失败退出。

#### PressButton

- `56. press_button_waits_on_target`：到达按钮目标后，`press_button` 只等待并请求验证，不做无关交互。
- `57. press_button_verify_bound`：按钮验证失败最多重试三次，之后返回失败。

#### ToggleSwitch

- `58. toggle_press_precondition`：`toggle_switch` 只有在足够接近且刚同步时才会按 `A`。
- `59. toggle_single_press`：一次 `toggle_switch` 执行过程中最多主动按一次 `A`。
- `61. toggle_finite`：`toggle_switch` 最多在 901 步内成功或失败退出。

#### UseExit

- `63. exit_push_precondition`：`use_exit` 只有在玩家位于出口格并像素对齐后才会朝边界推门。
- `64. exit_push_direction`：`use_exit` 对四个方向出口使用的推门方向与出口边界一致。
- `65. exit_blocked_bound`：若连续确认出口阻挡且推门次数达到上限，`use_exit` 会失败退出。
- `66. use_exit_finite`：`use_exit` 最多在 901 步内成功或失败退出。

#### KillMonster

- `68. kill_without_sword_fails`：若还有怪物但玩家没有剑，`kill_monster` 会直接失败。
- `69. swing_when_aligned`：若攻击几何窗口成立且朝向正确，`kill_monster` 会选择挥剑。
- `70. turn_before_swing`：若攻击窗口成立但朝向不对，`kill_monster` 会先转向再攻击。
- `71. guard_imminent_contact`：若接触风险临近且有盾，`kill_monster` 会优先举盾。
- `72. combat_timeout_bound`：`kill_monster` 超过 `max_steps` 后会超时失败。

原因：这些都能直接在 skill 的局部状态机里读出来，属于“实现策略事实”。

### 6. 解释器的构造检查和小步控制流事实

- `73. validated_program_entry_exists`：通过构造检查的程序，其入口节点一定存在。
- `74. validated_program_edges_closed`：通过构造检查的程序，所有控制流后继节点一定都存在。
- `76. interpreter_one_action_per_step`：解释器一次 `step` 调用最多只会产出一个环境动作。
- `77. data_op_advances`：执行 `DataOp` 后，解释器会跳转到它声明的 `next` 节点。
- `78. check_op_true_branch`：`CheckOp` 条件为真时，解释器会跳到 `on_true`。
- `79. check_op_false_branch`：`CheckOp` 条件为假时，解释器会跳到 `on_false`。
- `80. primitive_op_emits`：执行 `PrimitiveOp` 时，解释器会输出该节点计算出的动作并前进。
- `86. nonproductive_loop_bounded`：若内部连续 256 次跳转仍不产生活动，则解释器会以 `nonproductive_loop` 失败。
- `87. interpreter_reset`：执行 `reset` 后，解释器会回到入口并清空活动子 skill 与结束状态。
- `88. program_complexity`：程序复杂度就是节点数量。

原因：这些都由 [nsi_agent/graph.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/graph.py) 中 `__post_init__`、`step()` 的显式结构和常量 `MAX_TRANSITIONS_PER_STEP` 直接决定。

### 7. Planner 的局部控制流和账本更新

- `89. planner_action_valid`：planner 输出的动作编号总在环境合法动作集合里。
- `90. goal_switch_bounded`：planner 在一个环境步内最多切换六次目标。
- `91. planner_returns_skill_action`：若当前 skill 给出动作，planner 会原样返回该动作。
- `92. failed_goal_cooldown`：目标失败后，planner 会为它设置一个固定长度的 cooldown。
- `93. cooldown_prevents_retry`：在 cooldown 结束前，同一目标不会被立刻重试。
- `94. new_key_clears_probes`：当钥匙数增加时，planner 会清除锁门探测记录以便重新尝试。
- `95. combat_interrupt`：若战斗威胁足够近，planner 会中断非战斗目标。
- `99. failure_records_diagnosis`：技能失败后，planner 会把目标和诊断记入失败日志。
- `101. successful_toggle_clears_cooldowns`：成功切换开关后，planner 会清空 cooldown 并增加 toggle 计数。
- `102. toggle_attempts_bounded`：planner 的恢复逻辑不会无限次尝试切换开关。

原因：这些本质上是 `FallbackPlanner.step()`、`_cooled()`、`_on_success()`、`_abandon()` 等函数中的直接赋值与分支效果。

### 8. 房间级 BFS 的实现细节事实

- `103. first_hop_is_current_exit`：房间级 BFS 返回的第一跳一定是当前房间的某个出口方向。
- `105. first_hop_no_fake_exit`：房间级 BFS 不会把状态为 `"-"` 的方向当作可走出口。
- `107. first_hop_nodup`：房间级 BFS 搜索时不会重复扩展已经访问过的房间。

原因：这些主要来自 `_first_hop()` 对 `room.state.exits.items()` 的遍历方式、`"-"` 过滤和 `parent` 去重。

---

## 四、推荐的 Lean 主线

如果你想把证明工作集中在“最有含金量”的部分，我建议优先顺序改成：

1. 地图基础语义：`4-8`
2. 格子级 BFS：`16-26`
3. 危险区与真实安全：`9-12, 38`
4. Skill 核心后置条件：`42, 43, 48, 49, 50, 55, 60, 62, 67`
5. 房间级 BFS：`104, 106, 108, 109, 110`
6. 系统组合定理：`111-120`

如果篇幅再紧一些，报告里最值得留下的主定理可以压缩成：

- `walkable_not_blocking`：可行走格一定不是阻塞格。
- `walkable_not_hazard`：可行走格一定不是危险格。
- `bfs_path_adjacent`：BFS 返回路径的每一步都合法相邻。
- `bfs_path_not_blocking`：BFS 返回路径不会穿过阻塞格。
- `bfs_shortest`：BFS 返回最短路径。
- `bfs_complete`：只要路径存在，BFS 最终能找到。
- `shield_real_world_safe`：Shield 放行的动作在真实环境中也安全。
- `goto_no_path_sound`：`goto` 返回无路可走时，语义上确实无路可走。
- `use_exit_ok`：`use_exit` 成功意味着一次真实合法过门。
- `first_hop_sound`：房间级 BFS 返回的第一跳方向确实正确。
- `planner_navigation_safe`：planner 导航动作在符号层安全。
- `task1_completion`：task 1 的子任务契约可组合成整关完成性。

---

## 五、使用方式

这份筛选版的意思不是“筛掉的性质不该证明”，而是：

- 筛掉项更适合在报告中写成“由实现直接保证”；
- 保留项更适合作为 Lean 证明的主体；
- 如果后续你把 Python 实现改成更抽象的版本，一些目前筛掉的控制流性质也可能重新变成值得形式化的 theorem。

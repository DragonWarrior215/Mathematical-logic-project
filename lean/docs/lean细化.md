# NSI Agent 可证明定理组合

本文整理 `nsi_agent` 当前算法中适合在 Lean 4 中形式化的性质。证明重点是 VLM 后面的符号规划、安全过滤、技能契约和控制流。视觉识别正确性作为前提，不主张证明神经网络对任意图像都正确。

## 一、形式化边界

建议定义 `Tile`、`Action`、`TileKind`、`World`、`AgentState`、`Inventory`、`SkillResult`、`Goal` 和 `ProgramNode`。对于端到端结论，统一使用以下假设：

```lean
GroundingSound real symbolic
TransitionSemanticsMatch real symbolic
```

前者表示符号状态正确描述玩家、墙、陷阱和物体，且怪物不确定区域覆盖其真实位置；后者表示 Lean 的动作转移与 Python 环境语义一致。

## 二、地图基础性质

对应 `skills.py` 的 `neighbors`、`in_bounds`、`walkable`。

1. `neighbor_symm`：`Neighbor p q → Neighbor q p`。
2. `neighbor_manhattan`：`Neighbor p q → manhattan p q = 1`。
3. `neighbor_ne`：邻居不等于自身。
4. `walkable_in_bounds`：`Walkable w p h → InBounds p`。
5. `walkable_not_blocking`：`Walkable w p h → ¬ Blocking w p`。
6. `walkable_not_hazard`：`Walkable w p false → ¬ Hazard w p`。
7. `walkable_allow_hazard_geometry`：允许陷阱时仍保证不越界、不进墙。
8. `walkable_mono`：`Walkable w p false → Walkable w p true`。

## 三、怪物危险区域

对应 `monster_blocked_tiles`。

9. `monster_blocked_in_bounds`：禁区中的格子均在地图内。
10. `monster_uncertainty_covered`：格子中心落在怪物估计半径内，则属于禁区。
11. `monster_margin_monotone`：增大安全 margin 不会缩小禁区。
12. `monster_region_real_sound`：若真实怪物位于 Tracker 不确定区域内，则禁区外格子与怪物保持指定安全距离。

第 12 条依赖 `GroundingSound`。

## 四、格子级 BFS

对应 `bfs_path` 和 `reachable_tiles`。建议定义：

```lean
def ValidPath (w : World) (path : List Tile) (allowHazard : Bool) : Prop :=
  path.Pairwise Neighbor ∧
  path.Forall (fun p => Walkable w p allowHazard)
```

13. `bfs_path_nonempty`：返回的路径非空。
14. `bfs_head`：返回路径的首节点是 `start`。
15. `bfs_last_mem_goals`：末节点属于 `goals`。
16. `bfs_path_adjacent`：路径中连续节点正交相邻。
17. `bfs_path_nodup`：路径没有重复节点。
18. `bfs_path_in_bounds`：路径中的节点均在边界内。
19. `bfs_path_not_blocking`：路径不经过已知墙体或阻塞格。
20. `bfs_path_avoids_hazard`：`allow_hazard = false` 时不经过已知陷阱。
21. `bfs_internal_avoids_monsters`：开启避怪时，中间节点不属于怪物禁区。
22. `bfs_shortest`：返回路径长度不大于任意其他可行路径。
23. `bfs_complete`：若有限地图中存在可行路径，则 BFS 返回一条路径。
24. `bfs_none_iff_unreachable`：返回 `None` 当且仅当不存在可行路径。
25. `reachable_tiles_sound`：`reachable_tiles` 中的格子确实存在可行路径。
26. `reachable_tiles_complete`：所有存在可行路径的格子都被遍历到。

当前实现接受目标节点时没有检查 `nxt ∉ forbidden`，所以第 21 条只能覆盖中间节点，不能声称终点也避开怪物。若修正该条件，即可证明整条路径避怪。

## 五、像素移动控制器

对应 `move_toward_waypoint`。

27. `move_toward_aligned`：已精确对齐时返回 `None`。
28. `move_toward_is_move`：未对齐时只返回上下左右动作。
29. `move_toward_valid_action`：返回值一定属于合法动作集合。
30. `move_toward_decreases_axis_error`：若动作执行成功，所选轴上的像素误差严格减小。
31. `move_toward_no_overshoot`：单步为 1 像素且目标在整数 tile 边界时不会跨过目标坐标。

第 30、31 条需要假设环境实际执行了该移动，没有被碰撞截断。

## 六、Safety Shield

对应 `shielded`。

32. `shield_nonmove_identity`：非移动动作保持不变。
33. `shield_safe_identity`：预测下一位置安全时保留原移动。
34. `shield_vetoes_unsafe_move`：预测下一位置不安全时不返回移动动作。
35. `shield_uses_guard`：危险且有盾时返回 `BUTTON_B`。
36. `shield_uses_wait`：危险且无盾时返回 `NOOP`。
37. `shield_requests_perception`：否决危险动作时请求重新感知。
38. `shield_real_world_safe`：若 `GroundingSound` 成立，则 Shield 放行的移动在真实环境中满足对应安全距离。

这是最适合作为“可验证安全层”的定理组。

## 七、GoToTile

39. `goto_ok_exact`：非 adjacent 模式返回 `ok` 时玩家位于目标格。
40. `goto_ok_adjacent`：adjacent 模式返回 `ok` 时玩家与目标正交相邻。
41. `goto_move_is_shielded`：导航产生的移动动作均经过 Safety Shield。
42. `goto_no_approach_sound`：没有可行相邻格时返回 `no_approach`。
43. `goto_no_path_sound`：普通和放宽避怪后的 BFS 都失败时返回 `no_path`。
44. `goto_timeout_bound`：执行步数超过 `max_steps` 后一定失败退出。
45. `goto_replans_each_step`：每个未完成步骤都根据当前符号状态重新规划。
46. `goto_bump_learning`：连续四次碰撞后将当前 waypoint 标记为阻塞。
47. `goto_stall_learning`：两次同步之间多次移动但位置几乎不变时标记 waypoint。
48. `goto_eventually_succeeds`：在地图正确且静态、目标可达、动作成功执行、怪物不永久封路的条件下最终到达目标。
49. `learned_block_sound`：若 invalid-action reward 可靠，则碰撞推断出的阻塞格真实不可进入。

第 48、49 条必须保留条件，不能无条件证明。

## 八、具体技能契约

可统一使用 Hoare 风格：`{pre} skill {post}`。

### OpenChest

50. `open_chest_ok`：返回 `ok` 时目标在感知中为打开宝箱。
51. `open_chest_only_target`：成功记录的宝箱坐标等于技能目标。
52. `open_chest_press_precondition`：只有与目标相邻且刚同步时才按 A。
53. `open_chest_press_bound`：最多尝试按 A 四次，之后报告失败。
54. `open_chest_finite`：最多 1201 个技能步骤后成功或失败。

### PressButton

55. `press_button_ok`：返回 `ok` 时目标被感知为已按下按钮。
56. `press_button_waits_on_target`：到达目标后只等待并请求验证，不执行无关交互。
57. `press_button_verify_bound`：三次验证后仍未按下则失败。

### ToggleSwitch

58. `toggle_press_precondition`：只在与开关距离不超过 1 且刚同步时按 A。
59. `toggle_single_press`：一次技能执行最多主动按 A 一次。
60. `toggle_switch_ok`：若环境满足“相邻按 A 必然切换”，技能成功意味着开关状态发生变化。
61. `toggle_finite`：最多 901 步后成功或失败。

`ToggleSwitch` 没有视觉确认远端连通性，第 60 条必须带环境确定性假设。

### UseExit

62. `use_exit_ok`：成功只发生在 Tracker 报告 `moved` 后。
63. `exit_push_precondition`：推向边界前玩家位于对应出口格并完成像素对齐。
64. `exit_push_direction`：四个出口使用的推送方向与边界方向一致。
65. `exit_blocked_bound`：确认阻挡且推送次数达到上限后失败。
66. `use_exit_finite`：最多 901 步后成功或失败。

### KillMonster

67. `kill_ok_no_tracked_monster`：返回 `ok` 时 Tracker 怪物集合为空。
68. `kill_without_sword_fails`：没有剑且仍有怪物时返回 `no_sword`。
69. `swing_when_aligned`：攻击几何条件满足且朝向正确时按 A。
70. `turn_before_swing`：攻击几何条件满足但朝向错误时先选择对应移动方向。
71. `guard_imminent_contact`：未击晕、接触临近且有盾时按 B。
72. `combat_timeout_bound`：超过 `max_steps` 后失败。

不建议证明“战斗一定成功”或“一定无伤”。

## 九、技能图与解释器

对应 `graph.py` 的 `SkillProgram`、`Interpreter`。

73. `validated_program_entry_exists`：通过构造检查后 entry 存在。
74. `validated_program_edges_closed`：所有控制流后继节点均存在。
75. `interpreter_pc_valid`：从合法程序开始执行时 PC 始终指向已有节点。
76. `interpreter_one_action_per_step`：一次 `step` 最多输出一个环境动作。
77. `data_op_advances`：DataOp 执行数据函数后转到 `next`。
78. `check_op_true_branch`：谓词为真时只走 `on_true`。
79. `check_op_false_branch`：谓词为假时只走 `on_false`。
80. `primitive_op_emits`：PrimitiveOp 输出其函数产生的动作并前进。
81. `skill_action_resumable`：子技能产生动作时 PC 不提前跳转。
82. `skill_success_branch`：子技能成功只走 `on_success`。
83. `skill_failure_branch`：子技能失败只走 `on_fail` 并保存 diagnosis。
84. `terminal_result`：TerminalOp 返回与节点标记一致的 `Outcome`。
85. `finished_interpreter_stable`：已终止后再次调用仍返回相同结果。
86. `nonproductive_loop_bounded`：连续 256 次内部转移未产生动作或终止时，以 `nonproductive_loop` 失败。
87. `interpreter_reset`：reset 后 PC 回到 entry，active skill 和 finished 清空。
88. `program_complexity`：`complexity = nodes.length`。

## 十、高层 Planner

对应 `FallbackPlanner`。

89. `planner_action_valid`：Planner 输出属于 0–6 的合法动作集合。
90. `goal_switch_bounded`：一个环境步内最多切换六次目标。
91. `planner_returns_skill_action`：当前技能返回动作时 Planner 原样返回。
92. `failed_goal_cooldown`：目标失败后 cooldown 设置为当前步加固定等待期。
93. `cooldown_prevents_retry`：等待期结束前 `_cooled` 为假。
94. `new_key_clears_probes`：钥匙数量增加时清除房间锁门探测记录。
95. `combat_interrupt`：有剑且威胁足够近时中断非战斗技能。
96. `unarmed_threat_prefers_flee`：无剑、怪物靠近且存在逃跑格时优先选择 `goto(flee)`。
97. `armed_threat_prefers_combat`：有剑、满足 engagement 条件且不在 cooldown 时选择战斗。
98. `idle_is_passive`：没有目标时只等待或举盾。
99. `failure_records_diagnosis`：技能失败后记录目标与诊断。
100. `reachability_failure_requests_toggle`：已知开关且可达性失败时设置 `pending_toggle`。
101. `successful_toggle_clears_cooldowns`：成功切换后清空 cooldown 并增加计数。
102. `toggle_attempts_bounded`：恢复逻辑不会超过 `MAX_TOGGLES`。

## 十一、房间级 BFS

对应 `_first_hop`。

103. `first_hop_is_current_exit`：返回方向确实是当前房间的出口。
104. `first_hop_sound`：返回方向是某条通往目标房间路径的第一步。
105. `first_hop_no_fake_exit`：不经过状态为 `"-"` 的方向。
106. `first_hop_respects_locked_exit`：无钥匙时不经过尚未访问的锁门。
107. `first_hop_nodup`：搜索不会重复扩展已发现房间。
108. `first_hop_shortest`：找到的是已知房间图中的最少跳数路径。
109. `first_hop_complete`：符合锁门约束的房间路径存在时返回第一跳。
110. `first_hop_none_unreachable`：返回 `None` 时已知房间图中不存在允许的路径。

## 十二、组合定理

111. `hierarchical_navigation_sound`：房间级 BFS 选择出口，格子级 BFS 到达出口，`UseExit` 成功后进入对应相邻房间。
112. `planner_navigation_safe`：由 `GoToTile` 产生的移动不越界、不进墙、不进已知陷阱，并通过 Safety Shield。
113. `planner_real_safe`：在 `GroundingSound` 和语义一致假设下，符号安全动作在真实环境中安全。
114. `acquire_key_subtask`：钥匙宝箱可达且 OpenChest 契约成功时，最终物品栏拥有钥匙。
115. `unlock_exit_subtask`：持有钥匙且锁门可达时，UseExit 成功意味着门被打开或穿越。
116. `press_button_subtask`：按钮可达且 PressButton 成功时，按钮目标成立。
117. `task1_completion`：在钥匙宝箱和锁门均满足可达性及技能契约时，完成“取钥匙—开门”。
118. `task2_conditional_completion`：在战斗成功作为前提时，后续出口技能成功可完成关卡。
119. `program_eventually_acts_or_terminates`：若所有技能有限终止且控制流存在良基排序，程序最终产生动作或终止。
120. `trace_success_implies_goal`：若技能图的每条成功边均保持节点不变量，终止于 success 节点的轨迹满足任务目标。

## 十三、不能无条件声称的结论

1. VLM 对所有图像识别正确。
2. Agent 对任意布局都必然通关。
3. 战斗一定成功或无伤。
4. Safety Shield 对真实怪物绝对安全，除非 Tracker 误差界可靠。
5. ToggleSwitch 返回成功就代表远端地图已改变，除非交互语义确定。
6. 当前 BFS 整条路径都避怪；终点尚未检查 forbidden。
7. 所有 Planner 移动都经过 Shield；战斗技能部分动作没有统一过滤。
8. 五关训练产物均正确。当前 task 5 artifact 与 task 2 的名称和结构相同，应先验证。

## 十四、推荐证明顺序

第一阶段完成 1–8、13–21、27–38；这些是基础安全性质，最容易做到无 `sorry`。

第二阶段完成 22–26 的 BFS 最短性和完备性，以及 73–88 的解释器性质。

第三阶段完成 39–72 的技能契约，把视觉正确性和环境确定性明确列为前置条件。

第四阶段重点组合 103–120。报告建议列出以下主定理：

- `walkable_not_blocking`
- `walkable_not_hazard`
- `bfs_path_adjacent`
- `bfs_path_not_blocking`
- `bfs_shortest`
- `bfs_complete`
- `shield_vetoes_unsafe_move`
- `goto_ok_exact` / `goto_ok_adjacent`
- `validated_program_edges_closed`
- `interpreter_one_action_per_step`
- `skill_success_branch`
- `first_hop_sound`
- `hierarchical_navigation_sound`
- `planner_navigation_safe`
- `task1_completion`

这组定理覆盖环境抽象、搜索、安全层、技能、控制流和任务目标，并且都能与当前 Python 实现建立明确对应关系。

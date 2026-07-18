# Lean 形式化设计与验证报告

## 1. 概述

本项目的 Lean 部分是一个可执行的符号语义层：它抽取 Python `nsi_agent` 中可验证的决策与执行逻辑，对环境、Tracker、搜索、Safety Shield、skill、DSL 和任务模型进行形式化，再在这些定义上证明局部安全性、搜索健全性、控制流性质、跨层组合性质和五个具体任务的有界执行结果。

报告将“形式化”和“证明”分开叙述：第一部分回答“Lean 中定义了什么，它与 Python 实现如何对应”；第二部分回答“证明了什么，证明强度和前提是什么”。这一区分也对应课程评分中的“环境形式化”与“策略形式化与证明”。

`nsi_agent` 可分为从 `obs` 中提取结构化信息的感知层，以及依据符号信息选择动作的决策层。Lean 主要验证后者；VLM 感知本身作为外部输入，它的正确性没有被无条件证明。当结论需要迁移到真实像素环境时，报告会显式列出 grounding soundness 和 Python–Lean 语义对齐等前提。

---

## 2. 课程要求与本项目的覆盖范围

`docs/Mathematical_logic/README.md` 对 Lean 工作的要求可归纳为两类。

| 课程要求 | 本项目的落地方式 | 主要位置 |
|---|---|---|
| 建模对象、属性、状态、动作、转移、交互和目标 | 定义 tile-level 世界、小步环境语义、地图语义与任务谓词 | `EnvFormalization.lean`、`MapSemantics.lean` |
| 尽可能与 Python 环境及策略语义一致 | 按 Python 模块抽取 Tracker、Memory、BFS、Shield、planner、DSL 和 skill，并声明对齐接口 | `NsiAgentFormalization.lean` 及各专项模块 |
| 证明基本安全性或不变量 | 证明合法移动不越界、不穿墙，危险区与 Shield 的条件安全性 | `EnvFormalization.lean`、`MonsterDanger.lean`、`SafetyShield.lean` |
| 形式化并证明可验证策略层 | 证明搜索返回路径的健全性、房间 BFS 完备/最短性、GoTo 条件活性、DSL 控制流和 skill 合同 | `GridBfs.lean`、`RoomBfs.lean`、`GoToTile.lean`、`DSLExecution.lean`、`SkillContracts.lean` |
| 证明关键子任务或任务目标 | 组合路由、导航、交互合同，并对五个具体符号任务运行有界 witness | `Composition.lean`、`Task1.lean`—`Task5.lean` |
| 不要求证明神经网络本身 | 不证明 VLM 对所有像素输入正确；验证 grounding 之后的 Tracker、planner、Shield 和轨迹检查层 | `TrackerFormalization.lean`、`Composition.lean` |

---

## 第一部分：形式化设计

本部分只解释形式化对象、语义边界与 Python–Lean 对应。

## 3. Python 实现与 Lean 模块的对应关系

| Python 层 | Lean 主要文件 | 对应内容 |
|---|---|---|
| `nesylink/core/*` | `EnvFormalization.lean` | 世界状态、移动、交互、机关、怪物、出口、伤害和任务完成 |
| `grounding/schema.py` | `EnvFormalization.lean`、`MapSemantics.lean` | 10×8 网格、对象、阻挡、hazard 和符号状态谓词 |
| `tracker.py` | `NsiAgentFormalization.lean`、`TrackerFormalization.lean` | 关键帧同步、死推演、blocked feedback、怪物不确定球 |
| `memory.py` | `NsiAgentFormalization.lean` | learned-blocked、物品栏、闩锁和步数的核心子集 |
| `skills.py::bfs_path` | `GridBfs.lean` | 四邻接 BFS、avoid/hazard 约束、路径健全性与反例 |
| `skills.py::shielded` | `SafetyShield.lean` | 危险移动过滤、举盾/等待回退、条件式真实安全 |
| `skills.py::GoToTile` | `GoToTile.lean` | 目标/相邻目标、寻路失败诊断、条件式最终到达 |
| 其他原语技能 | `SkillContracts.lean` | 开箱、按钮、开关、过门的成功后置条件 |
| `planner.py` | `HighPlanner.lean`、`GenericPlanner.lean` | 优先级规格与可执行通用任务规划器 |
| 房间记忆和 `hop_toward` | `RoomBfs.lean` | 有限房间图、锁门过滤、最短/完备的 total BFS |
| `graph.py`、`induction/dsl.py` | `DSLExecution.lean`、`WorldDSL.lean` | 图解释器、reactive、recovery、world-aware skills |
| `Policy.act` 的组合路径 | `IntegratedExecution.lean` | planner 请求、Shield 过滤、环境执行和状态递推 |
| 任务 1–5 | `Task1.lean` … `Task5.lean` | 具体 tile 地图上的预算执行 witness 和目标证明 |

其中 `DSLExecution.lean` 侧重抽象控制流性质，`WorldDSL.lean` 侧重具体世界执行；

---

## 4. 形式化中采用的主要抽象

### 4.1 tile 级环境而不是完整像素环境

Python 环境中玩家和怪物具有像素坐标与 16×16 AABB，玩家移动速度为 1px/step；Lean 的`EnvFormalization` 将一次符号移动抽象成一个 tile 转移。由此可以证明格子级不越界、不进入已知阻挡等性质，但不能直接得到连续像素轨迹的逐步等价。

`TrackerFormalization.lean` 单独使用“半像素单位”恢复了怪物 0.5px/step 的速度上界，用于证明不确定球覆盖性；它仍没有建模完整的浮点 AABB 与渲染过程。

### 4.2 有限列表代替 Python 容器

Python 中的字典、集合、deque 和运行时对象，在 Lean 中主要用 `List`、结构体和纯函数表达。证明针对这些数学结构成立，而非针对 CPython 容器实现本身成立。

### 4.3 神经感知作为外部输入

`syncFromGrounding` 接受一个符号 snapshot。Lean 不证明 snapshot 一定来自正确的像素识别。涉及真实安全时，正确性通过 `MonsterRegionSound`、`NavigationSemanticsAgree`、`PythonLeanAligned` 等显式前提接入。

### 4.4 Planner 与 skill 的不同证明层次

部分控制器是 Python planner 的策略骨架抽象，例如 `HighPlanner`；部分是为了五关 witness 构造的可执行 `GenericPlanner`。它们保留“根据状态重新选择目标”的核心思想，但不逐分支覆盖 Python 中的 `FallbackPlanner`，也没有形式化 task 5 的完整 HP 阶段评分器。

### 4.5 怪物模型是保守但非逐步等价的抽象

Lean 将怪物抽象到 tile，并省略 Python 的部分移动周期、连续碰撞和击退。环境文件中让怪物每步更新，可视为对较慢怪物的保守过近似；但只有在其他抽象保持安全关系时，才能把 Lean 安全结论迁移到 Python。

---

## 5. 形式化模块与可执行语义

下面按文件说明定义了哪些数据、函数、谓词和执行器。为便于对照源码，同时简要标出该模块承载的证明；对证明成果的统一分类和口径见第二部分。

### 5.0 核心定理索引

下表汇总第 5 节涉及的核心公开结论。为保持可读性，功能相近的定理合并列出，队列、列表、算术和递归不变量等证明内部辅助引理不逐条展开。表中的“完备性”“最短性”和“安全性”都只在相应定理的显式前提与抽象层次内成立。

| Lean 文件与定理名 | 定理含义 | 性质类别/意义 |
|---|---|---|
| `EnvFormalization.lean`：`inBounds_of_canOccupy`、`free_basicMove_stays_in_bounds` | 可占据格和成功移动后的玩家位置均在地图边界内 | 环境边界安全性 |
| `EnvFormalization.lean`：`blocked_basicMove_keeps_player`、`free_basicMove_moves_player` | 阻挡时位置不变；合法时准确移动到目标格 | 移动语义正确性 |
| `EnvFormalization.lean`：`heal_loot_preserves_max_health`、`spike_trap_never_increases_health`、`abyss_trap_never_increases_health` | 治疗不超过最大 HP，陷阱不会增加 HP | 生命值不变量 |
| `EnvFormalization.lean`：`bridge_hides_trap`、`sword_loot_equips_slotA`、`shieldB_without_shield_does_not_raise` | 桥、剑和盾的状态转换符合环境规则 | 装备与机关语义正确性 |
| `EnvFormalization.lean`：`locked_exit_without_keys_denied` | 钥匙不足时不能通过锁门 | 门禁安全性 |
| `EnvFormalization.lean`：`goalReached_of_allChestsOpened`、`applyExit_completeTask_sets_goalReached` | 全部宝箱打开或通过完成出口能够推出任务目标成立 | 任务完成条件正确性 |
| `MapSemantics.lean`：`neighbor_symm`、`neighbor_manhattan`、`neighbor_ne` | 邻接关系对称，邻接格不同且曼哈顿距离为 1 | 网格几何性质 |
| `MapSemantics.lean`：`walkable_in_bounds`、`walkable_not_blocking`、`walkable_not_hazard`、`walkable_allow_hazard_geometry`、`walkable_mono` | 可走格满足边界、阻挡和 hazard 模式约束，严格模式可单调放宽 | 可走性语义正确性 |
| `MonsterDanger.lean`：`monster_blocked_in_bounds`、`monster_uncertainty_covered`、`monster_margin_monotone` | 危险区不越界、覆盖不确定半径，增大 margin 不会缩小危险区 | 危险区域覆盖与单调性 |
| `MonsterDanger.lean`：`monster_region_real_sound` | 若符号危险区覆盖真实怪物，则符号安全能够推出真实怪物语义安全 | 条件式真实安全性 |
| `TrackerFormalization.lean`：`pixelChebyshev_triangle` | 像素级 Chebyshev 距离满足三角不等式 | Tracker 距离基础性质 |
| `TrackerFormalization.lean`：`syncMonster_uncertainty_zero`、`syncMonster_covers_observed`、`tracker_ball_invariant` | 正确同步后不确定半径归零并覆盖观测；在速度上界下持续覆盖真实位置 | Tracker 条件式覆盖不变量 |
| `TrackerFormalization.lean`：`predict_move_engine_consistent`、`blocked_feedback_sound`、`player_tile_consistent` | 在阻挡集合、反馈和像素误差等前提下，预测移动、回滚及 tile 归属与真实语义一致 | Tracker 条件式一致性 |
| `GridBfs.lean`：`bfsPath_sound`、`bfs_sound` | BFS 一旦返回路径，该路径确实连接起点和目标并且合法 | BFS 路径健全性 |
| `GridBfs.lean`：`bfs_head`、`bfs_last_mem_goals`、`bfs_path_adjacent`、`bfs_path_nodup` | 返回路径端点正确、连续节点相邻且没有重复节点 | BFS 路径结构正确性 |
| `GridBfs.lean`：`bfs_path_in_bounds`、`bfs_path_not_blocking`、`bfs_path_avoids_hazard`、`bfs_internal_avoids_monsters` | 返回路径不越界、不穿墙，并遵守 hazard/avoid 规则 | BFS 静态安全与约束遵守性 |
| `GridBfs.lean`：`bfsPath_constrained_sound` | 任意 hazard/avoid 模式下，返回路径满足同一模式的全部约束 | 受约束 BFS 健全性 |
| `GridBfs.lean`：`twoStageBfs_primary_sound`、`twoStageBfs_primary_avoids_monsters`、`twoStageBfs_fallback_sound`、`twoStageBfs_path_sound` | primary 路径避怪；fallback 至少保持静态安全；两个分支返回的路径都合法 | 两阶段 BFS 健全性 |
| `GridBfs.lean`：`bfs_none_of_unreachable`、`bfs_none_of_constrained_unreachable` | 若普通图或受约束图中确实不存在目标路径，则 BFS 返回 `none` | 不可达时失败的正确性；不是完备性逆向 |
| `GridBfs.lean`：`reachable_tiles_sound` | `reachableTiles` 返回的每个格子确实可达 | 可达集合健全性 |
| `GridBfs.lean`：`reachable_of_mem_and_walkableNeighborClosed`、`abstractClosureSearch_complete`、`abstractClosureSearch_result_complete` | 包含起点且对合法邻居闭合的抽象搜索结果包含全部可达格 | 抽象闭包搜索完备性，不是当前 fuel 实现完备性 |
| `GridBfs.lean`：`bfs_complete_unconstrained_reachable_counterexample`、`bfs_complete_unconstrained_none_counterexample` | 普通图中目标可达，但加入 `avoid` 后实际 BFS 返回 `none` | 相对普通 `Reachable` 的完备性反例 |
| `GridBfs.lean`：`bfs_shortest_unconstrained_direct_path_counterexample`、`bfs_shortest_unconstrained_detour_counterexample`、`bfs_shortest_unconstrained_counterexample` | 普通图存在更短路径，但受 `avoid` 约束的 BFS 返回更长绕路 | 相对普通 `ValidPath` 的最短性反例 |
| `SafetyShield.lean`：`inMonsterDangerBool_true_iff`、`positionSafeBool_true_iff` | 危险与安全的布尔判断和命题规格一致 | 判定过程正确性 |
| `SafetyShield.lean`：`shieldFallback_nonmove`、`shieldAction_spec` | 危险移动被替换成非移动回退动作，安全动作原样透传 | Shield 过滤规格 |
| `SafetyShield.lean`：`shield_real_world_safe`、`shieldAction_real_world_safe` | 在危险区覆盖真实怪物的前提下，Shield 发出的移动目标对真实怪物安全 | 条件式真实导航安全性 |
| `GoToTile.lean`：`goto_no_approach_sound`、`goto_no_path_sound` | 报告没有接近格或约束路径时，相应候选或路径确实不存在 | 导航失败诊断健全性 |
| `GoToTile.lean`：`goto_eventually_succeeds` | 在每步满足抽象 progress 条件时，距离递减并最终到达 | 条件式导航活性/终止性 |
| `GoToTile.lean`：`learned_block_sound`、`learned_block_sound_of_mark` | 在 blocked feedback 可靠时，学习并记录的阻挡格确实阻挡 | 条件式阻挡学习健全性 |
| `GoToTile.lean`：`planner_navigation_safe` | 静态安全请求经过 Shield 后保持静态安全，并获得条件式怪物安全 | 导航与 Shield 组合安全性 |
| `SkillContracts.lean`：`open_chest_ok`、`press_button_ok`、`toggle_switch_ok`、`use_exit_ok` | 开箱、按钮、开关和过门的 Lean 状态转换满足各自成功后置条件 | Skill 后置条件正确性 |
| `HighPlanner.lean`：`unarmed_threat_prefers_flee`、`armed_threat_prefers_combat`、`idle_is_passive`、`reachability_failure_requests_toggle` | 抽象 planner 按威胁、装备和恢复条件选择逃跑、战斗、空闲或开关目标 | Planner 优先级正确性 |
| `RoomBfs.lean`：`allowed_room_bfs_total_sound`、`allowed_fifo_total_first_hop_sound` | total allowed BFS 返回合法路线，第一跳位于通向目标的允许路径上 | 房间路由健全性 |
| `RoomBfs.lean`：`allowed_fifo_total_respects_locked_exit` | 无钥匙且锁门未访问时，第一跳不会选择该锁门边 | 锁门约束安全性 |
| `RoomBfs.lean`：`allowed_room_bfs_total_shortest` | total allowed BFS 的路线在允许边图中最短 | 受约束房间 BFS 最短性 |
| `RoomBfs.lean`：`allowed_room_bfs_total_complete`、`allowed_fifo_total_first_hop_complete`、`allowed_room_bfs_total_none_unreachable` | 允许路径存在时能够找到；返回 `none` 时在允许图中不可达 | 受约束房间 BFS 完备性 |
| `RoomBfs.lean`：`room_bfs_locked_exit_counterexample` | 旧版无上下文 BFS 可能选择锁门边 | 旧规格的锁门安全性反例 |
| `DSLExecution.lean`：`interpreter_step_deterministic`、`interpreter_action_valid` | 固定输入下解释结果唯一，输出动作属于合法动作集合 | DSL 确定性与动作合法性 |
| `DSLExecution.lean`：`reactive_first_guard_selected`、`reactive_preemption_preserves_main`、`reactive_completion_resumes_main` | reactive 选择首个真 guard，抢占时保存主状态，完成后恢复主解释器 | Reactive 控制流正确性 |
| `DSLExecution.lean`：`recovery_preempts_other_modes`、`permanent_fallback_absorbing` | recovery 具有优先权，permanent fallback 一旦进入便保持 | Recovery/fallback 控制流不变量 |
| `DSLExecution.lean`：`dsl_planner_step_total` | 在 skill/fallback total contract 下，planner step 有限返回合法动作 | 条件式总性 |
| `Composition.lean`：`useExitOk_enters_target_room`、`hierarchical_navigation_sound` | 合法房间第一跳、tile 路径和过门合同可组合为进入目标房间 | 分层导航组合健全性 |
| `Composition.lean`：`planner_real_safe` | 静态导航、Tracker 覆盖、Shield 和语义对齐共同推出真实导航安全 | 跨层条件式真实安全性 |
| `Composition.lean`：`acquire_key_effect`、`unlock_exit_effect`、`press_button_effect` | 开钥匙箱、穿锁门和按按钮产生预期地图效果 | 交互效果组合正确性 |
| `Composition.lean`：`acquire_key_subtask`、`unlock_exit_subtask`、`press_button_subtask` | 导航/技能合同与交互效果可组成可完成的子任务 | 子任务合同组合性 |
| `Composition.lean`：`program_eventually_acts_or_terminates` | 在 `ProductiveWithin256` 前提下，程序于预算内产出动作或终止 | 条件式生产性 |
| `Composition.lean`：`trace_success_implies_goal` | 在对齐、invariant、skill 合同和 success 后置条件下，成功轨迹满足任务目标 | 条件式端到端组合正确性 |
| `IntegratedExecution.lean`：`integratedStep_requested`、`integratedStep_world` | 联合单步中的请求动作和环境后继状态与底层定义一致 | 联合执行单步一致性 |
| `IntegratedExecution.lean`：`runIntegrated_steps`、`stable_reach_then_interact`、`runWorldSkill_steps` | runner 对应递归执行关系，稳定导航可接续交互，world skill runner 产生合法多步关系 | 多步执行与组合正确性 |
| `Task1.lean`：`task1_nonhardcoded_trace`、`task1_agent_opens_key_chest`、`task1_agent_environment_completed`、`task1_complete`、`task1_agent_dsl_done` | 通用 planner 在预算内打开钥匙箱、完成出口和任务 | Task 1 具体模型计算证明 |
| `Task2.lean`：`task2_nonhardcoded_trace`、`task2_monster_defeated`、`task2_key_chest_opened`、`task2_complete`、`task2_dsl_done` | 通用 planner 在预算内击败怪物、打开钥匙箱并完成任务 | Task 2 具体模型计算证明 |
| `Task3.lean`：`task3_nonhardcoded_trace`、`task3_hall_monster_defeated`、`task3_return_key_chest_opened`、`task3_complete`、`task3_dsl_done` | 通用 planner 在预算内完成多房间战斗、取钥匙、返回和完成流程 | Task 3 具体模型计算证明 |
| `Task4.lean`：`task4_generic_trace`、`task4_guardian_defeated`、`task4_final_chest_opened`、`task4_complete`、`task4_dsl_done` | 通用 planner 在预算内击败 guardian、打开最终宝箱并完成任务 | Task 4 具体模型计算证明 |
| `Task5.lean`：`task5_generic_trace`、`task5_complete`、`task5_dsl_done`、`task5_survives` | 通用 planner 在预算内完成任务且最终 HP 大于 0 | Task 5 具体模型计算证明 |
| `TaskCompletion.lean`：`completedWorld_goalReached` | 构造的已完成世界满足通用目标谓词 | 通用完成状态 witness |

`NsiAgentFormalization.lean`、`WorldDSL.lean` 和 `GenericPlanner.lean` 主要提供可执行定义，没有需要在本表中单列的终端 theorem；它们的行为通过后续专项定理、组合定理和 Task 1–5 的计算证明验证。

### 5.1 `EnvFormalization.lean`：环境状态与小步语义

这是整个形式化的基础文件，对应 `nesylink/core/state.py`、地图 schema、移动、交互、战斗、装备和进度模块。

主要定义包括：

- `Position`、`Direction` 和七种 `Action`；
- 宝箱、loot、陷阱、按钮、开关、NPC、怪物、出口和动态桥；
- `RoomState`、`WorldState`、装备槽、动作持续时间、控制锁和重生状态；
- `isBlocking`、`canOccupy`、`trapAt?`、`goalReached`；
- `basicMove`、`interactStep`、`applyExit`、`resolveMonsterContact`；
- `actionStep`、`postActionResolve` 和完整 `step`。

已经闭合的基础结论包括（括号中为 Lean 定理名）：

- `inBounds_of_canOccupy`：可占据格一定在 10×8 边界内；
- `blocked_basicMove_keeps_player`：目标不可占据时玩家不移动；
- `free_basicMove_moves_player`、`free_basicMove_stays_in_bounds`：合法移动到达目标且不越界；
- 治疗不超过最大 HP（`heal_loot_preserves_max_health`），尖刺和深渊不会增加 HP
  （`spike_trap_never_increases_health`、`abyss_trap_never_increases_health`）；
- 桥覆盖时下方陷阱不生效（`bridge_hides_trap`）；
- 剑 loot 正确装备到 A 槽（`sword_loot_equips_slotA`）；
- 钥匙不足时锁门不可通过（`locked_exit_without_keys_denied`）；
- 完成出口和“全部宝箱打开”能够推出 `goalReached`
  （`applyExit_completeTask_sets_goalReached`、`goalReached_of_allChestsOpened`）；
- 未装备盾时按 B 不会启动盾动作（`shieldB_without_shield_does_not_raise`）。

### 5.2 `MapSemantics.lean`：地图基础语义

该文件证明后续搜索依赖的最小几何事实：

- 邻接关系对称且邻接格不同（`neighbor_symm`、`neighbor_ne`）；
- 邻接格曼哈顿距离等于 1（`neighbor_manhattan`）；
- `walkable` 推出界内、非阻挡、默认非 hazard
  （`walkable_in_bounds`、`walkable_not_blocking`、`walkable_not_hazard`）；
- 允许 hazard 时仍不越界、不穿墙（`walkable_allow_hazard_geometry`）；
- 严格可走性对宽松可走性单调（`walkable_mono`）。

这些定理虽然简单，但为 BFS 的路径节点合法性提供了统一语义，而不是在每个搜索证明中重复展开环境定义。

### 5.3 `NsiAgentFormalization.lean`：Agent 可执行核心语义

该文件是后续证明使用的运行定义中心，本身主要提供定义而非大量终端定理。它对应 `Policy.act`、`Tracker`、`Memory`、`bfs_path`、`GoToTile` 和 `shielded` 的关键控制流。

它定义了：

- `TrackedMonster`、Chebyshev 危险区域和 `MonsterRegionSound`；
- `ValidPath`、`Reachable`、`bfsSearch`、`bfsPath` 和两阶段 BFS；
- `GoToRuntime`、`goToTileStep`、移动动作生成；
- learned-blocked、300 步 TTL 和 Agent memory 核心子集；
- `NsiTracker`、grounding 同步、不确定性增长和 blocked feedback；
- `shieldAction`、`agentBfsPlan`、`agentGoToStep`；
- `nsiAgentAct` 与 `nsiAgentEnvStep`。

与 Python 相比，它保留了“反馈修正 → 可选 grounding → planner 请求 → shield → tracker 更新 → 环境 step”的组合顺序。外部 grounding 和 planner 被参数化，不声称 Lean 已证明 VLM 或 Python planner 的每个内部细节。

### 5.4 `MonsterDanger.lean`：怪物危险区域的集合性质

主要证明：

- 危险区内格子一定在地图边界内（`monster_blocked_in_bounds`）；
- 位于不确定半径内的格子被纳入危险区（`monster_uncertainty_covered`）；
- 增大 margin 不会缩小危险区（`monster_margin_monotone`）；
- 在 `MonsterRegionSound` 前提下，符号层安全可推出真实怪物语义安全
  （`monster_region_real_sound`）。

最后一条不是无条件安全证明。`MonsterRegionSound` 正是“Tracker 的符号危险区覆盖真实怪物位置”的接口条件，覆盖性本身由下一文件在速度假设下进一步论证。

### 5.5 `TrackerFormalization.lean`：半像素 Tracker 正确性

该文件用 `HalfPx` 将 0.5px 表示为自然数单位 1，避免浮点证明。

关键结论包括：

- `pixelChebyshev_triangle`：像素级 Chebyshev 距离满足三角不等式；
- grounding 同步后不确定半径归零并覆盖观测位置
  （`syncMonster_uncertainty_zero`、`syncMonster_covers_observed`）；
- `tracker_ball_invariant`：若真实怪物每步位移不超过速度上界、Tracker 中心保持在
  上次观测位置且半径按同一上界增长，则整个 dead-reckoning 期间持续覆盖真实位置；
- `predict_move_engine_consistent`：已知阻挡谓词与真实阻挡谓词一致时，tile 预测移动
  与抽象引擎移动一致；
- `blocked_feedback_sound`：在反馈可靠且保存的旧位置正确时，回滚恢复真实位置；
- `player_tile_consistent`：预测与真实中心误差不超过半像素且远离 tile 边界时，两者
  归入同一 tile。

### 5.6 `GridBfs.lean`：格子 BFS 的健全性、约束和反例

这是证明量最大的模块之一。它围绕 Python `skills.py::bfs_path` 的 Lean 版本建立队列、seen、路径、avoid 和 hazard 不变量。

已证明的正面性质包括：

- 返回路径具有正确起点和目标（`bfs_head`、`bfs_last_mem_goals`）；
- 连续节点正交相邻（`bfs_path_adjacent`）；
- 路径不重复（`bfs_path_nodup`）；
- 所有节点在界内且不穿过已知阻挡
  （`bfs_path_in_bounds`、`bfs_path_not_blocking`）；
- `allowHazard = false` 时不经过 hazard（`bfs_path_avoids_hazard`）；
- monster avoid 模式下，除实现允许的起点/目标例外外，不进入 avoid 区域
  （`bfs_internal_avoids_monsters`）；
- `bfsPath_constrained_sound`：在给定 hazard/avoid 模式下，返回路径满足对应约束；
- primary/fallback 两阶段 BFS 返回的路径都满足静态路径健全性，primary 额外避怪
  （`twoStageBfs_primary_sound`、`twoStageBfs_primary_avoids_monsters`、
  `twoStageBfs_fallback_sound`、`twoStageBfs_path_sound`）；
- `reachableTiles` 的返回结果具有可达性 soundness（`reachable_tiles_sound`）；
- 如果目标确实不可达，则 BFS 返回 `none`（`bfs_none_of_unreachable`；受约束版本为
  `bfs_none_of_constrained_unreachable`）。

#### 被证伪的两个强结论

无约束 BFS 最短性和完备性标记为“证伪”。我们也在 Lean 文件中给出的证伪的证据：

1. **无约束完备性反例**：走廊 `(0,0) → (1,0) → (2,0)` 在普通 `Reachable` 意义下
   可达，但把唯一中间格 `(1,0)` 放入 `avoid` 后，实际 `bfsPath` 返回 `none`
   （`bfs_complete_unconstrained_reachable_counterexample`、
   `bfs_complete_unconstrained_none_counterexample`）。
2. **无约束最短性反例**：开放地图上存在长度 3 的直达路径，但 `avoid = [(1,0)]`
   迫使 BFS 返回长度 5 的绕行路径
   （`bfs_shortest_unconstrained_direct_path_counterexample`、
   `bfs_shortest_unconstrained_detour_counterexample`、
   `bfs_shortest_unconstrained_counterexample`）。

这并不说明 BFS 算法本身错误。理论上，标准 bfs 在一个固定、有限的受约束图上，如果搜索资源充足，仍然具有完备性和最短性。Agent 加入避怪规则后，使得最终得出的结果不一定具备完备性以及最短性。但如果实现一个更智能的“卖血”机制，即在上述无约束完备性反例中使 Agent 具备穿过怪物，主动卖血的机制的话，那么完备性是成立的。

`reachable_tiles_complete` 也没有针对当前具体实现闭合；文件只证明了满足抽象闭包搜索规格的结果具有完备性。这是“抽象规格的完备性”，不是当前 fuel-bounded 实现的完整证明。

### 5.7 `SafetyShield.lean`：安全动作过滤

该文件把 Python `shielded(action)` 抽象为可执行 `shieldAction` 和关系式 `Shielded`。

已证明：

- 布尔危险判断与命题版定义一致
  （`inMonsterDangerBool_true_iff`、`positionSafeBool_true_iff`）；
- 回退动作总是非移动动作（`shieldFallback_nonmove`）；
- `shieldAction_spec` 完整描述安全动作透传和危险动作替换；
- 在 `MonsterRegionSound` 下，经 Shield 发出的移动目标对真实怪物位置安全
  （`shield_real_world_safe`、`shieldAction_real_world_safe`）；
- 非移动回退动作没有新的移动目标，因此在该导航规格下是被动的
  （由 `shieldFallback_nonmove` 与 `shieldAction_spec` 组合得到）。

这里证明的是“Shield 不把玩家移动到已建模危险区”，不是“玩家在整个游戏中绝不掉血”。陷阱、战斗主动接近、漏检怪物和错误速度上界都在该定理范围之外。

### 5.8 `GoToTile.lean`：导航技能的局部正确性

该文件证明：

- `goto_no_approach_sound`：相邻模式无候选时确实不存在合法接近格；
- `goto_no_path_sound`：在相应搜索约束下报告无路径时，不存在满足该约束的路径；
- `goto_eventually_succeeds`：在抽象 progress 条件下，距离度量递减，导航最终成功；
- `learned_block_sound`：在 blocked feedback 的真实性假设下，碰撞学习出的格子确实阻挡；
- `planner_navigation_safe`：静态安全请求经过 Shield 后仍满足静态安全，并获得条件式怪物安全。

`goto_eventually_succeeds` 是条件活性定理，不表示动态怪物、地图变化、持续 grounding 错误或动作未被环境执行时仍必然成功。

### 5.9 `SkillContracts.lean`：交互技能后置条件

该文件定义并证明四类成功契约：

- `OpenChestOk` / `open_chest_ok`：目标宝箱存在，结果状态等于开箱并应用 loot 的状态；
- `PressButtonOk` / `press_button_ok`：目标按钮经列表更新成为 pressed；
- `ToggleSwitchOk` / `toggle_switch_ok`：目标开关被按下并执行动态对象切换；
- `UseExitOk` / `use_exit_ok`：出口存在、条件满足，结果为 `applyExit` 的状态。

这些定理严格证明 Lean 状态转换器满足契约。不是直接证明 Python 的时间扩展技能必然走到成功分支；从“目标可达”连接到“Python skill 最终返回 ok”仍通过后续组合文件的 `ReachableSkillContract` 等显式接口条件表达。

表中列出的 `kill_ok_no_tracked_monster` 当前没有对应的同名 Lean 定理；战斗结果主要在环境语义、`WorldDSL.stepWorldSkill` 以及任务 2–5 的具体执行 witness 中体现。

### 5.10 `HighPlanner.lean`：高层优先级规格

`HighPlanner` 是一个小型抽象 planner，用于说明策略优先级：

- 无剑且有怪物威胁时选择 `flee`（`unarmed_threat_prefers_flee`）；
- 有剑且有怪物威胁时选择 `combat`（`armed_threat_prefers_combat`）；
- 没有更高优先级条件时选择 `idle`（`idle_is_passive`）；
- 可达性失败且已知开关时选择 `toggle`
  （`reachability_failure_requests_toggle`）。

最后一条不能无条件成立：如果同时存在怪物威胁，战斗/逃跑具有更高优先级。

这些定理验证的是抽象 `highPlanner`，不是直接解析 Python `FallbackPlanner._choose_goal` 得到的证明。二者策略意图对应，但仍需要 Python–Lean refinement 才能迁移结论。

### 5.11 `RoomBfs.lean`：房间图搜索

该文件同时保留了多种逐步演进的房间 BFS 定义，最终的主要结果来自带 `RoomRoutingContext` 的 total allowed BFS：

- 返回路线由真实房间图中的允许边组成（`allowed_room_bfs_total_sound`）；
- 第一跳位于一条通往目标的合法路径上（`allowed_fifo_total_first_hop_sound`）；
- 没有钥匙且锁门未访问时，该边不会被当作允许边
  （`roomEdgeAllowed_locked_no_key_unvisited`、`locked_no_key_unvisited_not_allowed`、
  `allowed_fifo_total_respects_locked_exit`）；
- total BFS 相对允许边图具有最短性（`allowed_room_bfs_total_shortest`）；
- 若允许路径存在则能找到（`allowed_room_bfs_total_complete`、
  `allowed_fifo_total_first_hop_complete`）；
- 返回 `none` 推出允许图中不可达（`allowed_room_bfs_total_none_unreachable`）；
- 搜索通过有限房间集合和递减 measure 证明终止，而不只是依赖任意 fuel。

### 5.12 `DSLExecution.lean`：DSL 与混合控制权语义

该文件对应 `graph.Interpreter` 和 `DSLPlanner` 的控制结构，定义：

- data/check/primitive/skill/terminal 五类节点；
- fuel-bounded 小步解释器；
- reactive guard 的顺序选择；
- main、reactive、recovery、permanent fallback 四种控制模式；
- skill 和 fallback 的抽象 total runtime。

已证明：

- 固定程序、状态和 fuel 下解释结果唯一（`interpreter_step_deterministic`）；
- 每次调用至多输出一个七种环境动作之一（`interpreter_action_valid`）；
- reactive 选择第一个为真的 guard（`reactive_first_guard_selected`）；
- reactive 抢占期间主解释器状态保持（`reactive_preemption_preserves_main`）；
- reactive 完成后恢复主解释器（`reactive_completion_resumes_main`）；
- recovery 优先于其他模式（`recovery_preempts_other_modes`）；
- permanent fallback 是吸收态（`permanent_fallback_absorbing`）；
- 在 skill/fallback total contract 下，planner step 有限返回合法动作
  （`dsl_planner_step_total`）。

表达式求值与 skill step 被当作 total function 参数，因此 `dsl_planner_step_total` 的含义是：在这些边界组件满足总性契约时，控制器本身不会卡在无返回状态。

### 5.13 `Composition.lean`：跨层组合定理

该文件把独立证明的路线、导航、Shield 和技能契约连接起来。

主要结论包括：

- `hierarchical_navigation_sound`：房间 BFS 的第一跳、通往出口的合法 tile 路径和
  `UseExitOk` 可以组合成进入相邻目标房间的结论；其中技能合同到目标房间的直接连接由
  `useExitOk_enters_target_room` 给出；
- `planner_real_safe`：静态导航安全、Tracker 区域 soundness、Shield 和真实转移模型
  对齐共同推出真实导航安全；
- 开钥匙宝箱会严格增加钥匙数（`acquire_key_effect`；子任务包装为
  `acquire_key_subtask`）；
- 有足够钥匙且 `UseExitOk` 成立时，能够穿越具体锁门（`unlock_exit_effect`；子任务包装为
  `unlock_exit_subtask`）；
- 按钮技能契约与地图效果契约可组合为任务条件（`press_button_effect`；子任务包装为
  `press_button_subtask`）；
- `program_eventually_acts_or_terminates`：若显式满足 `ProductiveWithin256`，解释器在
  256 次内部转移内产出动作或终止；
- `trace_success_implies_goal`：在 Python–Lean 对齐、step 保持 invariant、skill 契约和
  success 后置条件均成立时，success trace 满足任务目标。

### 5.14 `IntegratedExecution.lean`：Planner、Agent 与环境的联合执行

该文件定义 `integratedStep`：

1. DSL planner 请求动作；
2. `nsiAgentAct` 应用 blocked feedback、snapshot 和 Shield；
3. `nsiAgentEnvStep` 把实际 issued action 送入环境 `step`；
4. 同时更新 planner 和 Agent 状态。

已证明单步请求字段、环境字段与底层定义一致（`integratedStep_requested`、`integratedStep_world`），并建立列表 runner 与`IntegratedSteps` 的对应（`runIntegrated_steps`）、稳定导航后交互（`stable_reach_then_interact`），以及通用 runner 与 `WorldSkillSteps` 的对应（`runWorldSkill_steps`）。

这里的 external snapshot 和 feedback 仍是输入，并没有证明它们一定等于 Python 运行时观测。

### 5.15 `WorldDSL.lean`：携带世界状态的可执行技能 DSL

该文件将抽象图控制流具体化到 Lean 世界：

- 查询任务是否完成、是否有钥匙、怪物、宝箱或是否位于指定房间；
- 调用开箱、杀怪、按钮、开关和过门技能；
- 每个技能内部使用 `agentGoToStep` 动态重算导航；
- 支持 reactive skill；
- `worldDslRuntime` 每次使用 256 的内部决策预算。

它是任务级可执行模型，不提供大量独立 theorem；其正确性主要通过底层模块和任务文件的 `native_decide` 结果体现。

### 5.16 `GenericPlanner.lean`：五关 witness 使用的通用规划器

`GenericPlanner` 根据当前世界动态选择：杀怪、开箱、按按钮、使用满足条件的出口，或者在失败后寻找开关和恢复出口。规划器只保存当前 active skill、访问房间、完成标志和 pending toggle，不保存预先写死的动作序列。

该文件是一个可执行策略，被 Task 1–5 的有限预算 runner 实际求值。它与 Python `FallbackPlanner` 的高层意图一致，但规模和细节明显更小，进行了一定的简化。

### 5.17 `Task1.lean`—`Task5.lean`：具体任务模型

五个文件分别建立 task-level 房间、对象、初始 Agent、预算和最终执行状态，并证明：

| 文件 | 预算 | 已证明结果 |
|---|---:|---|
| `Task1.lean` | 40 | 通用轨迹 `task1_nonhardcoded_trace`；打开钥匙箱 `task1_agent_opens_key_chest`；完成环境与目标 `task1_agent_environment_completed`、`task1_complete`；planner 完成 `task1_agent_dsl_done` |
| `Task2.lean` | 100 | 通用轨迹 `task2_nonhardcoded_trace`；击败怪物 `task2_monster_defeated`；打开钥匙箱 `task2_key_chest_opened`；完成目标与 planner `task2_complete`、`task2_dsl_done` |
| `Task3.lean` | 200 | 通用轨迹 `task3_nonhardcoded_trace`；击败大厅怪物 `task3_hall_monster_defeated`；打开钥匙箱 `task3_return_key_chest_opened`；完成目标与 planner `task3_complete`、`task3_dsl_done` |
| `Task4.lean` | 400 | 通用轨迹 `task4_generic_trace`；击败 guardian `task4_guardian_defeated`；打开最终宝箱 `task4_final_chest_opened`；完成目标与 planner `task4_complete`、`task4_dsl_done` |
| `Task5.lean` | 700 | 通用轨迹 `task5_generic_trace`；完成目标与 planner `task5_complete`、`task5_dsl_done`；最终存活 `task5_survives` |

`*_nonhardcoded_trace` / `*_generic_trace` 说明最终状态来自通用 runtime 的重复执行；具体目标主要由 `native_decide` 对闭合有限模型求值证明。

这些结论的证明强度是：

- 对文件中定义的固定 tile-level 世界和初始状态成立；
- 使用状态依赖的通用 planner，而不是硬编码方向动作列表；
- 在给定预算内成立。

>  但此处的预算并不是完全对齐python中的步数预算，由于lean本身环境就是简化后的环境，即把像素级移动变为格子级的移动，因此lean的步数明显会比 python 的步数预算少上不少。

它们不是：

- 对所有 seed 或地图变体的量化定理；
- 对 VLM 像素输入的端到端证明；
- 对当前 `selection.json` 中 task 1–4 的具体 JSON DSL 工件逐字执行证明；
- 对 Python task 5 完整周期掉血与资源评分策略的等价证明。

### 5.18 `TaskCompletion.lean` 与 `TheoremList.lean`

`TaskCompletion.lean` 只有一个通用“已完成世界”witness，证明 `completedWorld` 满足 `goalReached`。它不是五关完成性的主体；真正的任务执行证明已经位于 `Task1`—`Task5`。

`TheoremList.lean` 是上层 import 聚合文件，使主要证明模块通过一个入口参与构建。它不定义新的实质定理。根文件 `NesyFormalization.lean` 则聚合整个库。

## 第二部分：证明内容与结果

本部分以“定理究竟证明了多强的结论”为主线，区分无条件结构定理、条件定理、合同组合定理、具体模型计算证明和反例，而不仅按文件罗列 theorem。

## 6. 证明结果的五种强度

为了避免把不同证明强度混在一起，可以把当前成果分为五类。

### 6.1 无额外外部假设的闭合结构定理

例如：地图邻接性质、环境纯函数局部性质、BFS 返回路径的 constrained soundness、解释器控制流确定性、reactive/recovery 优先级。这些定理只依赖文件中定义的数据结构和函数。

### 6.2 带显式环境或感知假设的条件定理

例如：

- Tracker 球覆盖依赖真实怪物速度上界和初始同步正确；
- Shield 的真实安全依赖 `MonsterRegionSound`；
- `planner_real_safe` 依赖 `NavigationSemanticsAgree`；
- `trace_success_implies_goal` 依赖 Python–Lean 对齐、invariant 和 success postcondition；
- learned-block soundness 依赖 blocked feedback 可靠。

这些仍然是正常、有效的 Lean 定理，只是结论必须与前提一起引用。

### 6.3 抽象 contract 下的组合定理

`ReachableSkillContract`、`ReachableExitContract` 和 total `PlannerRuntime` 将尚未逐行验证的 Python skill/fallback 行为作为接口契约。Lean 证明了“若实现满足接口，则组合结论成立”。

### 6.4 有限具体模型上的计算证明

Task 1–5 使用 `native_decide` 对具体初始世界和固定预算运行可执行 planner。这是闭合证明，但量化范围只包含该模型，不应宣传为所有地图上的普遍定理。

### 6.5 反例证明

当前有至少三组重要反例结论：

- 格子 BFS 相对普通无约束 `Reachable` 不完备；
- 格子 BFS 相对普通无约束路径不保证最短；
- 不带 lock context 的旧房间 BFS 会选择锁门边。

这些反例不是形式化工作的失败，而是对原始自然语言命题进行了规格纠正。

## 第三部分：评价

## 10. 形式化工作的主要价值

1. **明确了系统可信边界**：神经感知与符号执行被清晰分开。
2. **验证了返回结果而非算法名称**：BFS 使用了 queue 不代表自动完备，Lean 发现并修正了
   avoid 约束下的错误规格。
3. **把安全论证拆成可审查前提**：速度上界、区域覆盖、Shield 和真实语义对齐分别表达。
4. **验证了混合控制器的优先级**：reactive、recovery 和 permanent fallback 的状态转换可执行。
5. **提供了系统级组合路径**：从房间路由、格子导航、技能合同到任务目标都有对应模块。
6. **任务证明不是固定动作脚本**：具体 witness 使用状态依赖的通用 planner 和每步 BFS。

## 11. 风险与后续改进

### 高优先级

1. 建立 `SymbolicState` 到 Lean `WorldState` 的显式编码/验证器，减少 `PythonLeanAligned`
   仅作为逻辑参数的距离。
2. 为 `policy_act_total` 建立更接近 Python `Policy.act` 的异常和 backoff 模型。
3. 补充 `hp_estimate_conservative`；当前 Python 中 `Memory.on_step` 与 `OpenChest` 都可能处理
   heal，尤其需要先统一事件来源再证明。
4. 为战斗补充 `kill_swing_safe` 或更谨慎的战斗结算定理，并明确其只覆盖挥剑窗口。
5. 对冻结 JSON artifact 建立 parser/translation，使 Lean 能证明实际 selected DSL，而不是仅证明
   手工建立的 WorldDSL/GenericPlanner。

### 中优先级

1. 将 `opened_exit_sound`、房间 odometry 和行为闩锁加入 memory/refinement 层。
2. 如果项目确实需要 BFS 最短性，应针对 `allowHazard + avoid` 诱导的受约束图重新陈述并证明，
   不再使用普通 `ValidPath` 作为比较集合。
3. 闭合具体 `reachableTiles` 的完备性，或在 API 文档中只保留 soundness。
4. 给 Task 1–5 加入地图常量与 JSON 的自动一致性检查，避免手工模型随地图更新而过时。
5. 精简 `RoomBfs.lean` 中历史版本定义，保留 total allowed BFS 作为正式公开接口，反例作为
   规格演进记录。

## 12. 总结

本项目构建了一套从环境语义到任务执行的 Lean 符号验证层。形式化内容覆盖 tile-level 世界状态与转移、Tracker、怪物危险区、格子与房间 BFS、Safety Shield、导航与交互技能、Planner、DSL 控制流以及 Planner–Agent–环境的联合执行。它是对 Agent 决策层中适合验证的核心逻辑进行可执行抽象。

当前成果可以概括为以下五点：

1. **环境和基础算法具有可检查的局部正确性。** Lean 已证明合法移动不越界、不穿墙，环境交互满足关键状态转换规则，BFS 返回的路径端点、邻接关系、边界、阻挡以及 hazard/avoid 约束均正确。
2. **安全结论明确保留必要前提。** Tracker 覆盖、Shield 的真实怪物安全和跨层导航安全分别依赖速度上界、正确同步、`MonsterRegionSound`、`NavigationSemanticsAgree` 等条件。因此，Lean 证明的是“在这些条件成立时，符号安全结论可以迁移到真实语义”，而不是无条件证明 Agent 永远安全。
3. **搜索规格得到了区分和修正。** 格子 BFS 已闭合普通及受约束路径的健全性，但相对普通无约束 `Reachable` 的完备性和最短性被 `avoid` 反例否定；相对受约束图的完备性和最短性仍需进一步证明。房间 total allowed BFS 则已经在允许边图上证明健全性、完备性、最短性和锁门约束正确性。
4. **控制器和技能能够跨层组合。** DSL 的确定性、reactive/recovery 优先级、skill 后置条件、分层导航和联合执行关系均有对应定理。组合结论说明，在显式 contract、invariant 和 Python–Lean 对齐条件下，局部证明可以连接到任务目标。
5. **五个任务具有具体模型上的有限执行证明。** Task 1–5 使用状态依赖的通用 planner 和动态 BFS，在各自预算内计算得到满足任务目标的最终状态。这些 witness 证明固定 Lean 模型可完成，但不等价于对所有 seed、地图变体、像素观测或 Python 运行轨迹的普遍端到端证明。

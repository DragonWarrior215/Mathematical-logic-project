# Lean 形式化设计与验证报告

> 仓库：NesyLink / Mathematical Logic Project  
> 设计对象：`lean/NesyFormalization/` 及其与 `nesylink/`、`nsi_agent/` 的对应关系  
> 参考清单：`lean/docs/定理列表3.0.xlsx`  
> 报告日期：2026-07-15

## 1. 概述

​        本项目的 lean 部分是一个可执行的符号语义层，提取了 Python 中 nsi_agent 的核心运行逻辑，并基于部分假设和简化上建立的一个符号语义模块。我们使用构建出来的 lean 模块完成了 nsi_agent 的各模块重要定理的证明，五个测试任务的完备性证明等等。

​        其中对于 nsi_agent ，其可以分为两部分，一个是从环境 obs 中提取出结构化信息的观测层，一个是根据提取出的结构化信息来进行动作选择的决策层。本项目的 lean 部分针对第二部分进行了相关定理的证明，第一部分由于我们认为 VLM 本身的决策过程更像是一个黑盒，因此就不对其进行证明。

### Python 代码文件与 lean 文件的对应关系

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

两个底层文件：`EnvFormalization.lean` 

二者分别解决“控制流性质”和“具体世界执行”问题，不能简单视为同一个解释器的两份重复代码。

## 3. 形式化中采用的主要抽象

### 3.1 tile 级环境而不是完整像素环境

Python 环境中玩家和怪物具有像素坐标与 16×16 AABB，玩家移动速度为 1px/step；
Lean 的 `EnvFormalization` 将一次符号移动抽象成一个 tile 转移。由此可以证明格子级
不越界、不进入已知阻挡等性质，但不能直接得到连续像素轨迹的逐步等价。

`TrackerFormalization.lean` 单独使用“半像素单位”恢复了怪物 0.5px/step 的速度
上界，用于证明不确定球覆盖性；它仍没有建模完整的浮点 AABB 与渲染过程。

### 3.2 有限列表代替 Python 容器

Python 中的字典、集合、deque 和运行时对象，在 Lean 中主要用 `List`、结构体和纯函数
表达。证明针对这些数学结构成立，而非针对 CPython 容器实现本身成立。

### 3.3 神经感知作为外部输入

`syncFromGrounding` 接受一个符号 snapshot。Lean 不证明 snapshot 一定来自正确的像素
识别。涉及真实安全时，正确性通过 `MonsterRegionSound`、`NavigationSemanticsAgree`、
`PythonLeanAligned` 等显式前提接入。

### 3.4 Planner 与 skill 的不同证明层次

部分控制器是 Python planner 的策略骨架抽象，例如 `HighPlanner`；部分是为了五关
witness 构造的可执行 `GenericPlanner`。它们保留“根据状态重新选择目标”的核心思想，
但不逐分支覆盖 Python 中超过 1500 行的 `FallbackPlanner`，也没有形式化 task 5 的
完整 HP 阶段评分器。

### 3.5 怪物模型是保守但非逐步等价的抽象

Lean 将怪物抽象到 tile，并省略 Python 的部分移动周期、连续碰撞和击退。环境文件中
让怪物每步更新，可视为对较慢怪物的保守过近似；但只有在其他抽象保持安全关系时，
才能把 Lean 安全结论迁移到 Python。

## 4. 逐文件设计与证明内容

### 4.1 `EnvFormalization.lean`：环境状态与小步语义

这是整个形式化的基础文件，对应 `nesylink/core/state.py`、地图 schema、移动、交互、
战斗、装备和进度模块。

主要定义包括：

- `Position`、`Direction` 和七种 `Action`；
- 宝箱、loot、陷阱、按钮、开关、NPC、怪物、出口和动态桥；
- `RoomState`、`WorldState`、装备槽、动作持续时间、控制锁和重生状态；
- `isBlocking`、`canOccupy`、`trapAt?`、`goalReached`；
- `basicMove`、`interactStep`、`applyExit`、`resolveMonsterContact`；
- `actionStep`、`postActionResolve` 和完整 `step`。

已经闭合的基础结论包括：

- `inBounds_of_cnOccupy`：可占据格一定在 10×8 边界内；
- `blocked_basicMove_keeps_player`：目标不可占据时玩家不移动；
- `free_basicMove_moves_player`、`free_basicMove_stays_in_bounds`：合法移动到达目标且不越界；
- 治疗不超过最大 HP，尖刺和深渊不会增加 HP；
- 桥覆盖时下方陷阱不生效；
- 剑 loot 正确装备到 A 槽；
- 钥匙不足时锁门不可通过；
- 完成出口和“全部宝箱打开”能够推出 `goalReached`；
- 未装备盾时按 B 不会启动盾动作。

证明范围是 tile-level 环境函数本身。`定理列表3.0.xlsx` 中把交互距离、伤害、开箱、
机关等若干项列为“定义”，它们确实已在环境执行函数中建模，但当前文件没有为表中
每一句自然语言说明都提供一个独立同名 theorem。

### 4.2 `MapSemantics.lean`：地图基础语义

该文件证明后续搜索依赖的最小几何事实：

- `neighbor_symm`、`neighbor_ne`；
- 邻接格曼哈顿距离等于 1；
- `walkable` 推出界内、非阻挡、默认非 hazard；
- 允许 hazard 时仍不越界、不穿墙；
- 严格可走性对宽松可走性单调。

这些定理虽然简单，但为 BFS 的路径节点合法性提供了统一语义，而不是在每个搜索证明中
重复展开环境定义。

### 4.3 `NsiAgentFormalization.lean`：Agent 可执行核心语义

该文件是后续证明使用的运行定义中心，本身主要提供定义而非大量终端定理。它对应
`Policy.act`、`Tracker`、`Memory`、`bfs_path`、`GoToTile` 和 `shielded` 的关键控制流。

它定义了：

- `TrackedMonster`、Chebyshev 危险区域和 `MonsterRegionSound`；
- `ValidPath`、`Reachable`、`bfsSearch`、`bfsPath` 和两阶段 BFS；
- `GoToRuntime`、`goToTileStep`、移动动作生成；
- learned-blocked、300 步 TTL 和 Agent memory 核心子集；
- `NsiTracker`、grounding 同步、不确定性增长和 blocked feedback；
- `shieldAction`、`agentBfsPlan`、`agentGoToStep`；
- `nsiAgentAct` 与 `nsiAgentEnvStep`。

与 Python 相比，它保留了“反馈修正 → 可选 grounding → planner 请求 → shield → tracker
更新 → 环境 step”的组合顺序。外部 grounding 和 planner 被参数化，不声称 Lean 已证明
VLM 或 Python planner 的每个内部细节。

### 4.4 `MonsterDanger.lean`：怪物危险区域的集合性质

主要证明：

- 危险区内格子一定在地图边界内；
- 位于不确定半径内的格子被纳入危险区；
- 增大 margin 不会缩小危险区；
- 在 `MonsterRegionSound` 前提下，符号层安全可推出真实怪物语义安全。

最后一条不是无条件安全证明。`MonsterRegionSound` 正是“Tracker 的符号危险区覆盖真实
怪物位置”的接口条件，覆盖性本身由下一文件在速度假设下进一步论证。

### 4.5 `TrackerFormalization.lean`：半像素 Tracker 正确性

该文件用 `HalfPx` 将 0.5px 表示为自然数单位 1，避免浮点证明。

关键结论包括：

- `pixelChebyshev_triangle`：像素级 Chebyshev 距离满足三角不等式；
- grounding 同步后不确定半径归零并覆盖观测位置；
- `tracker_ball_invariant`：若真实怪物每步位移不超过速度上界、Tracker 中心保持在
  上次观测位置且半径按同一上界增长，则整个 dead-reckoning 期间持续覆盖真实位置；
- `predict_move_engine_consistent`：已知阻挡谓词与真实阻挡谓词一致时，tile 预测移动
  与抽象引擎移动一致；
- `blocked_feedback_sound`：在反馈可靠且保存的旧位置正确时，回滚恢复真实位置；
- `player_tile_consistent`：预测与真实中心误差不超过半像素且远离 tile 边界时，两者
  归入同一 tile。

这些结论都明确暴露了侧条件。特别是 `tracker_ball_invariant` 不证明 VLM 没有漏检怪物，
而是从一次正确同步和真实速度上界推出同步后的持续覆盖。

### 4.6 `GridBfs.lean`：格子 BFS 的健全性、约束和反例

这是证明量最大的模块之一。它围绕 Python `skills.py::bfs_path` 的 Lean 版本建立队列、
seen、路径、avoid 和 hazard 不变量。

已证明的正面性质包括：

- 返回路径具有正确起点和目标；
- 连续节点正交相邻；
- 路径不重复；
- 所有节点在界内且不穿过已知阻挡；
- `allowHazard = false` 时不经过 hazard；
- monster avoid 模式下，除实现允许的起点/目标例外外，不进入 avoid 区域；
- `bfsPath_constrained_sound`：在给定 hazard/avoid 模式下，返回路径满足对应约束；
- primary/fallback 两阶段 BFS 返回的路径都满足静态路径健全性，primary 额外避怪；
- `reachableTiles` 的返回结果具有可达性 soundness；
- 如果目标确实不可达，则 BFS 返回 `none`。

#### 被证伪的两个强结论

`定理列表3.0.xlsx` 正确地把无约束 BFS 最短性和完备性标记为“证伪”。Lean 文件给出了
可执行闭合反例，而不是证明失败后简单放弃：

1. **无约束完备性反例**：走廊 `(0,0) → (1,0) → (2,0)` 在普通 `Reachable` 意义下
   可达，但把唯一中间格 `(1,0)` 放入 `avoid` 后，实际 `bfsPath` 返回 `none`。
2. **无约束最短性反例**：开放地图上存在长度 3 的直达路径，但 `avoid = [(1,0)]`
   迫使 BFS 返回长度 5 的绕行路径。

这并不说明 BFS 算法本身错误。它说明原命题把“普通无约束路径”与“Agent 实际搜索的
受约束图”混为一谈。当前形式化选择保留对 Agent 最直接的 constrained soundness，
没有继续声称相对普通 `Reachable` 的最短性或完备性。

`reachable_tiles_complete` 也没有针对当前具体实现闭合；文件只证明了满足抽象闭包搜索
规格的结果具有完备性。这是“抽象规格的完备性”，不是当前 fuel-bounded 实现的完整证明。

### 4.7 `SafetyShield.lean`：安全动作过滤

该文件把 Python `shielded(action)` 抽象为可执行 `shieldAction` 和关系式 `Shielded`。

已证明：

- 布尔危险判断与命题版定义一致；
- 回退动作总是非移动动作；
- `shieldAction_spec` 完整描述安全动作透传和危险动作替换；
- 在 `MonsterRegionSound` 下，经 Shield 发出的移动目标对真实怪物位置安全；
- 非移动回退动作没有新的移动目标，因此在该导航规格下是被动的。

这里证明的是“Shield 不把玩家移动到已建模危险区”，不是“玩家在整个游戏中绝不掉血”。
陷阱、战斗主动接近、漏检怪物和错误速度上界都在该定理范围之外。

### 4.8 `GoToTile.lean`：导航技能的局部正确性

该文件证明：

- `goto_no_approach_sound`：相邻模式无候选时确实不存在合法接近格；
- `goto_no_path_sound`：在相应搜索约束下报告无路径时，不存在满足该约束的路径；
- `goto_eventually_succeeds`：在抽象 progress 条件下，距离度量递减，导航最终成功；
- `learned_block_sound`：在 blocked feedback 的真实性假设下，碰撞学习出的格子确实阻挡；
- `planner_navigation_safe`：静态安全请求经过 Shield 后仍满足静态安全，并获得条件式怪物安全。

`goto_eventually_succeeds` 是条件活性定理，不表示动态怪物、地图变化、持续 grounding 错误
或动作未被环境执行时仍必然成功。

### 4.9 `SkillContracts.lean`：交互技能后置条件

该文件定义并证明四类成功契约：

- `OpenChestOk` / `open_chest_ok`：目标宝箱存在，结果状态等于开箱并应用 loot 的状态；
- `PressButtonOk` / `press_button_ok`：目标按钮经列表更新成为 pressed；
- `ToggleSwitchOk` / `toggle_switch_ok`：目标开关被按下并执行动态对象切换；
- `UseExitOk` / `use_exit_ok`：出口存在、条件满足，结果为 `applyExit` 的状态。

这些定理严格证明 Lean 状态转换器满足契约。它们没有直接证明 Python 的时间扩展技能
必然走到成功分支；从“目标可达”连接到“Python skill 最终返回 ok”仍通过后续组合文件的
`ReachableSkillContract` 等显式接口条件表达。

表中列出的 `kill_ok_no_tracked_monster` 当前没有对应的同名 Lean 定理；战斗结果主要在
环境语义、`WorldDSL.stepWorldSkill` 以及任务 2–5 的具体执行 witness 中体现。

### 4.10 `HighPlanner.lean`：高层优先级规格

`HighPlanner` 是一个小型抽象 planner，用于说明策略优先级：

- 无剑且有怪物威胁时选择 `flee`；
- 有剑且有怪物威胁时选择 `combat`；
- 没有更高优先级条件时选择 `idle`；
- 可达性失败且已知开关时选择 `toggle`。

最后一条不能无条件成立：如果同时存在怪物威胁，战斗/逃跑具有更高优先级。Lean 文件
因此要求“恢复时没有怪物威胁”的前提，并在文件末尾明确记录了这一限制。

这些定理验证的是抽象 `highPlanner`，不是直接解析 Python `FallbackPlanner._choose_goal`
得到的证明。二者策略意图对应，但仍需要 Python–Lean refinement 才能迁移结论。

### 4.11 `RoomBfs.lean`：房间图搜索

该文件同时保留了多种逐步演进的房间 BFS 定义，最终的主要结果来自带
`RoomRoutingContext` 的 total allowed BFS：

- 返回路线由真实房间图边组成；
- 第一跳位于一条通往目标的合法路径上；
- 没有钥匙且锁门未访问时，该边不会被当作允许边；
- total BFS 相对允许边图具有最短性；
- 若允许路径存在则能找到；
- 返回 `none` 推出允许图中不可达；
- 搜索通过有限房间集合和递减 measure 证明终止，而不只是依赖任意 fuel。

文件还证明了一个旧版无上下文 `roomBfs` 的反例：该搜索不知道锁门状态，因此会选择一条
被声明为锁定的边。这个反例说明为什么最终定理必须使用带路由上下文的
`allowedRoomBfsTotal`，而不能对所有房间搜索函数笼统声称“尊重锁门”。

### 4.12 `DSLExecution.lean`：DSL 与混合控制权语义

该文件对应 `graph.Interpreter` 和 `DSLPlanner` 的控制结构，定义：

- data/check/primitive/skill/terminal 五类节点；
- fuel-bounded 小步解释器；
- reactive guard 的顺序选择；
- main、reactive、recovery、permanent fallback 四种控制模式；
- skill 和 fallback 的抽象 total runtime。

已证明：

- 固定程序、状态和 fuel 下解释结果唯一；
- 每次调用至多输出一个七种环境动作之一；
- reactive 选择第一个为真的 guard；
- reactive 抢占期间主解释器状态保持；
- reactive 完成后恢复主解释器；
- recovery 优先于其他模式；
- permanent fallback 是吸收态；
- 在 skill/fallback total contract 下，planner step 有限返回合法动作。

表达式求值与 skill step 被当作 total function 参数，因此 `dsl_planner_step_total` 的含义是：
在这些边界组件满足总性契约时，控制器本身不会卡在无返回状态。

### 4.13 `Composition.lean`：跨层组合定理

该文件把独立证明的路线、导航、Shield 和技能契约连接起来。

主要结论包括：

- `hierarchical_navigation_sound`：房间 BFS 的第一跳、通往出口的合法 tile 路径和
  `UseExitOk` 可以组合成进入相邻目标房间的结论；
- `planner_real_safe`：静态导航安全、Tracker 区域 soundness、Shield 和真实转移模型
  对齐共同推出真实导航安全；
- 开钥匙宝箱会严格增加钥匙数；
- 有足够钥匙且 `UseExitOk` 成立时，能够穿越具体锁门；
- 按钮技能契约与地图效果契约可组合为任务条件；
- `program_eventually_acts_or_terminates`：若显式满足 `ProductiveWithin256`，解释器在
  256 次内部转移内产出动作或终止；
- `trace_success_implies_goal`：在 Python–Lean 对齐、step 保持 invariant、skill 契约和
  success 后置条件均成立时，success trace 满足任务目标。

后两条容易被过度解读：

- “最终动作或终止”把 `ProductiveWithin256` 作为前提，并没有证明任意 DSL 都无坏循环；
- “success 推出 goal”要求任务方提供 `SuccessPostcondition`，不是仅凭 terminal 标签自动
  推出任意目标。

### 4.14 `IntegratedExecution.lean`：Planner、Agent 与环境的联合执行

该文件定义 `integratedStep`：

1. DSL planner 请求动作；
2. `nsiAgentAct` 应用 blocked feedback、snapshot 和 Shield；
3. `nsiAgentEnvStep` 把实际 issued action 送入环境 `step`；
4. 同时更新 planner 和 Agent 状态。

已证明单步请求字段、环境字段与底层定义一致，并建立 `IntegratedSteps`、列表 runner、
稳定导航后交互和通用 `WorldSkillSteps` 的递归执行关系。

这些定理很重要，因为它们表明任务 witness 不是完全脱离 Agent 的环境动作脚本；但这里的
external snapshot 和 feedback 仍是输入，并没有证明它们一定等于 Python 运行时观测。

### 4.15 `WorldDSL.lean`：携带世界状态的可执行技能 DSL

该文件将抽象图控制流具体化到 Lean 世界：

- 查询任务是否完成、是否有钥匙、怪物、宝箱或是否位于指定房间；
- 调用开箱、杀怪、按钮、开关和过门技能；
- 每个技能内部使用 `agentGoToStep` 动态重算导航；
- 支持 reactive skill；
- `worldDslRuntime` 每次使用 256 的内部决策预算。

它是任务级可执行模型，不提供大量独立 theorem；其正确性主要通过底层模块和任务文件的
`native_decide` 结果体现。

### 4.16 `GenericPlanner.lean`：五关 witness 使用的通用规划器

`GenericPlanner` 根据当前世界动态选择：杀怪、开箱、按按钮、使用满足条件的出口，或者在
失败后寻找开关和恢复出口。规划器只保存当前 active skill、访问房间、完成标志和
pending toggle，不保存预先写死的动作序列。

该文件没有独立 theorem；其价值在于它是一个可执行策略，被 Task 1–5 的有限预算 runner
实际求值。它与 Python `FallbackPlanner` 的高层意图一致，但规模和细节明显更小，不能称为
Python planner 的完整形式化副本。

### 4.17 `Task1.lean`—`Task5.lean`：具体任务 witness

五个文件分别建立 task-level 房间、对象、初始 Agent、预算和最终执行状态，并证明：

| 文件 | 预算 | 已证明结果 |
|---|---:|---|
| `Task1.lean` | 40 | 打开钥匙宝箱、通过完成出口、`goalReached`、planner finished |
| `Task2.lean` | 100 | 击败怪物、打开钥匙宝箱、完成任务、planner finished |
| `Task3.lean` | 200 | 穿越多房间、击败大厅怪物、打开钥匙箱、返回并完成 |
| `Task4.lean` | 400 | 操作桥相关路线、取得资源、击败 guardian、打开最终宝箱 |
| `Task5.lean` | 700 | 完成多房间全部宝箱目标、planner finished、最终 HP 大于 0 |

`*_nonhardcoded_trace` / `*_generic_trace` 说明最终状态来自通用 runtime 的重复执行；
具体目标主要由 `native_decide` 对闭合有限模型求值证明。

这些结论的证明强度是：

- 对文件中定义的固定 tile-level 世界和初始状态成立；
- 使用状态依赖的通用 planner，而不是硬编码方向动作列表；
- 在给定预算内成立。

它们不是：

- 对所有 seed 或地图变体的量化定理；
- 对 VLM 像素输入的端到端证明；
- 对当前 `selection.json` 中 task 1–4 的具体 JSON DSL 工件逐字执行证明；
- 对 Python task 5 完整周期掉血与资源评分策略的等价证明。

### 4.18 `TaskCompletion.lean` 与 `TheoremList.lean`

`TaskCompletion.lean` 只有一个通用“已完成世界”witness，证明 `completedWorld` 满足
`goalReached`。它不是五关完成性的主体；真正的任务执行证明已经位于 `Task1`—`Task5`。

`TheoremList.lean` 是上层 import 聚合文件，使主要证明模块通过一个入口参与构建。它不定义
新的实质定理。根文件 `NesyFormalization.lean` 则聚合整个库。

## 5. 证明结果分类

为了避免把不同证明强度混在一起，可以把当前成果分为五类。

### 5.1 无额外外部假设的闭合结构定理

例如：地图邻接性质、环境纯函数局部性质、BFS 返回路径的 constrained soundness、解释器
控制流确定性、reactive/recovery 优先级。这些定理只依赖文件中定义的数据结构和函数。

### 5.2 带显式环境或感知假设的条件定理

例如：

- Tracker 球覆盖依赖真实怪物速度上界和初始同步正确；
- Shield 的真实安全依赖 `MonsterRegionSound`；
- `planner_real_safe` 依赖 `NavigationSemanticsAgree`；
- `trace_success_implies_goal` 依赖 Python–Lean 对齐、invariant 和 success postcondition；
- learned-block soundness 依赖 blocked feedback 可靠。

这些仍然是正常、有效的 Lean 定理，只是结论必须与前提一起引用。

### 5.3 抽象 contract 下的组合定理

`ReachableSkillContract`、`ReachableExitContract` 和 total `PlannerRuntime` 将尚未逐行验证的
Python skill/fallback 行为作为接口契约。Lean 证明了“若实现满足接口，则组合结论成立”。

### 5.4 有限具体模型上的计算证明

Task 1–5 使用 `native_decide` 对具体初始世界和固定预算运行可执行 planner。这是闭合证明，
但量化范围只包含该模型，不应宣传为所有地图上的普遍定理。

### 5.5 反例证明

当前有至少三组重要反例结论：

- 格子 BFS 相对普通无约束 `Reachable` 不完备；
- 格子 BFS 相对普通无约束路径不保证最短；
- 不带 lock context 的旧房间 BFS 会选择锁门边。

这些反例不是形式化工作的失败，而是对原始自然语言命题进行了规格纠正。

## 6. `定理列表3.0.xlsx` 与当前代码的差异

表格总体准确描述了证明路线，但同时包含“目标”“完成”“证伪”和“暂不证明”四种状态。
不能把表格中的每一行都理解为当前已存在的 Lean theorem。

### 已落地且与表格一致

- 地图语义、怪物危险区、Tracker 核心定理；
- BFS 路径健全性和两组反例；
- Safety Shield、GoTo 条件性质；
- skill 合同中的开箱、按钮、开关和过门；
- planner 优先级；
- 带锁门上下文的房间 total BFS；
- DSL 控制权语义；
- 组合定理和五关具体 witness。

### 表中列出但当前没有同名闭合定理

- `opened_exit_sound`；
- `kill_ok_no_tracked_monster`；
- `kill_swing_safe`；
- `fallback_step_productive`；
- `policy_act_total`；
- `hp_estimate_conservative`；
- `room_odometry_consistent`。

其中部分性质被任务 witness 或环境执行间接覆盖，但这不等价于相应的普遍同名定理。
例如 `task5_survives` 只证明具体 task 5 模型最终仍有 HP，不能替代任意运行上的
`hp_estimate_conservative`。

### 已明确不能按原强形式证明

- `bfs_shortest` 和 `bfs_complete`：相对普通无约束路径被反例证伪；
- `reachable_tiles_complete`：当前只建立抽象闭包搜索的完备性，未闭合具体实现；
- 无条件 `reachability_failure_requests_toggle`：与威胁优先级冲突，需要无怪物威胁前提；
- 无上下文房间 BFS 的 locked-exit soundness：已有反例，最终由 allowed total BFS 修正。

## 7. 关键假设与可信边界

### 7.1 Grounding 正确性

必须假设 VLM 没有漏掉影响证明的墙、hazard、出口和怪物，或者至少输出满足相应抽象关系。
当前 held-out 准确率属于实验依据，不是 Lean theorem。

### 7.2 怪物速度与观测完整性

`tracker_ball_invariant` 使用每步最大 0.5px 的上界。若环境版本改变怪物速度，或一次同步
根本没有观测到某只怪物，不确定球结论不能自动应用于该怪物。

### 7.3 Python–Lean 转移细化

`NavigationSemanticsAgree` 和 `PythonLeanAligned` 把像素世界与 tile 世界的对应保留为
接口条件。目前没有建立一个从 Python 源码或运行轨迹自动检查的 refinement theorem。

### 7.4 Reward feedback 可靠性

blocked feedback、HP 和按钮确认来自结构化 reward。若评测接口只提供标量 reward，或者
signals/weights 的语义改变，相关 soundness 前提不再成立。

### 7.5 Skill 活性

“目标静态可达”并不自动推出 Python 时间扩展技能必然返回 `ok`。当前组合定理通过
`ReachableSkillContract` 明确假设该连接；动态怪物、感知失败和 timeout 都可能使技能失败。

### 7.6 任务地图范围

Task 1–5 theorem 针对 Lean 文件中的具体模型。即使这些常量来源于课程基础图，它们也不是
对 JSON loader、任意 seed、对象 shuffle 或 topology variant 的量化证明。

## 8. 当前证明没有覆盖的结论

下面这些说法不应出现在最终答辩或报告的无条件结论中：

- “Lean 证明了 Qwen grounding 永远正确”；
- “Lean 证明了 Python Agent 在所有地图上 100% 通关”；
- “Lean 证明了所有导航路径都是无约束最短路径”；
- “Lean 证明了所有普通可达目标都一定被当前 BFS 找到”；
- “Lean 证明了 Agent 永远不会掉血”；
- “Lean 代码与 Python 像素引擎完全等价”；
- “五关 theorem 执行的就是 `selection.json` 中冻结的原始 JSON 工件”。

更准确的表述是：项目验证了从符号状态开始的关键算法与控制组合，并用具体任务模型展示
通用可执行规划器能够完成五关；真实端到端结论仍依赖感知和语义细化假设，并由实验评测补充。

## 9. 形式化工作的主要价值

1. **明确了系统可信边界**：神经感知与符号执行被清晰分开。
2. **验证了返回结果而非算法名称**：BFS 使用了 queue 不代表自动完备，Lean 发现并修正了
   avoid 约束下的错误规格。
3. **把安全论证拆成可审查前提**：速度上界、区域覆盖、Shield 和真实语义对齐分别表达。
4. **验证了混合控制器的优先级**：reactive、recovery 和 permanent fallback 的状态转换可执行。
5. **提供了系统级组合路径**：从房间路由、格子导航、技能合同到任务目标都有对应模块。
6. **任务证明不是固定动作脚本**：具体 witness 使用状态依赖的通用 planner 和每步 BFS。

## 10. 风险与后续改进

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

## 11. 构建与审阅方法

完整构建：

```bash
cd lean
lake build
```

检查是否含未完成证明：

```bash
rg -n '\b(sorry|admit|axiom)\b' lean --glob '*.lean'
```

搜索命中时还需要区分注释文本和真正语法；当前环境文件的注释中会提到这些词，但没有实际
使用相应命令。

查看某模块的公开定理：

```bash
rg -n '^(theorem|lemma) ' lean/NesyFormalization/<Module>.lean
```

## 12. 关键源码索引

| 主题 | 文件 |
|---|---|
| 环境状态与小步语义 | `lean/NesyFormalization/EnvFormalization.lean` |
| 地图基本性质 | `lean/NesyFormalization/MapSemantics.lean` |
| Agent 运行定义 | `lean/NesyFormalization/NsiAgentFormalization.lean` |
| 怪物危险区域 | `lean/NesyFormalization/MonsterDanger.lean` |
| Tracker 半像素证明 | `lean/NesyFormalization/TrackerFormalization.lean` |
| 格子 BFS | `lean/NesyFormalization/GridBfs.lean` |
| Safety Shield | `lean/NesyFormalization/SafetyShield.lean` |
| GoTo 技能 | `lean/NesyFormalization/GoToTile.lean` |
| Skill 后置条件 | `lean/NesyFormalization/SkillContracts.lean` |
| Planner 优先级 | `lean/NesyFormalization/HighPlanner.lean` |
| 房间 BFS | `lean/NesyFormalization/RoomBfs.lean` |
| DSL 控制流 | `lean/NesyFormalization/DSLExecution.lean` |
| 跨层组合 | `lean/NesyFormalization/Composition.lean` |
| 联合执行 | `lean/NesyFormalization/IntegratedExecution.lean` |
| 世界感知 DSL | `lean/NesyFormalization/WorldDSL.lean` |
| 通用任务规划器 | `lean/NesyFormalization/GenericPlanner.lean` |
| 五关证明 | `lean/NesyFormalization/Task1.lean` … `Task5.lean` |
| 目标清单 | `lean/docs/定理列表3.0.xlsx` |

## 13. 最终评价

当前 Lean 部分已经超过“为若干显然性质写几个 theorem”的规模，形成了从环境、搜索、
Tracker、Shield、skill、DSL 到任务 witness 的完整形式化链条。它最有价值的成果不是宣称
整个神经 Agent 被无条件证明，而是清晰地区分：

- 哪些符号算法已经闭合验证；
- 哪些结论依赖感知、速度和 refinement 假设；
- 哪些强规格被 Lean 反例否定并得到修正；
- 哪些任务结果只在具体 tile 模型和预算内成立；
- 哪些 Python 运行性质仍需后续形式化。

用这一边界进行陈述时，项目可以准确定位为：**神经感知负责从像素生成符号状态，Lean
验证符号 Agent 的关键执行层，并用具体任务模型验证组合后的有限执行结果。**

# NesyLink 神经符号 Agent 实验报告

**方法框架**：迁移论文 *"Lifting Traces to Logic: Programmatic Skill Induction with
Neuro-Symbolic Learning for Long-Horizon Agentic Tasks"（NSI, arXiv:2605.01293）*
**最终成绩**：提交形态端到端评测 **5/5 关全通**（纯像素 + reward + 物品栏输入）
**代码**：`nsi_agent/` · **入口**：`submission_agent.py`（`Policy` / `make_policy`）· **日期**：2026-07-04

---

## 目录

1. [系统架构总览](#1-系统架构总览)
2. [感知层 φ：稀疏关键帧 + 符号推演](#2-感知层-φ稀疏关键帧--符号推演)
3. [符号状态 Z 与跨房间记忆](#3-符号状态-z-与跨房间记忆)
4. [执行图 G 与解释器](#4-执行图-g-与解释器)
5. [原语技能层](#5-原语技能层)
6. [顶层规划 I：手写修正规划器](#6-顶层规划-i手写修正规划器)
7. [顶层规划 II：NSI 技能归纳管线](#7-顶层规划-iinsi-技能归纳管线)
8. [测评合规性](#8-测评合规性)
9. [成绩单](#9-成绩单)
10. [关键技术发现](#10-关键技术发现)
11. [Lean 形式化对接点](#11-lean-形式化对接点)
12. [复现命令](#12-复现命令)

---

## 1. 系统架构总览

### 1.1 NSI 三元组与本项目的对应

NSI 把"技能"定义为三元组 **π = (θ, φ, G)**：θ 为调用参数，φ 为神经感知
grounding（原始观测 → 符号谓词），G 为带条件分支/循环/变量绑定的一阶逻辑
**符号执行图**，按 **Perceive → Think → Act** 循环执行；顶层技能程序由"轨迹 →
逻辑"归纳获得，失败时经符号诊断反思修复。本项目将该框架完整迁移到 NesyLink：

| NSI 概念 | 本实现 | 代码位置 |
|---|---|---|
| φ 神经 grounding | Qwen2.5-VL-3B + QLoRA，像素帧 → 紧凑符号状态文本 | `grounding/vlm.py`, `grounding/train_qlora.py` |
| 符号状态 Z | `SymbolicState`（10×8 网格 + 像素级实体）+ 跨房间记忆 | `grounding/schema.py`, `memory.py` |
| Perceive–Think–Act 循环 | 关键帧调用 VLM + 帧间形式化转移模型死推演 | `tracker.py`, `agent.py` |
| 执行图 G | DataOp / CheckOp / PrimitiveOp / SkillOp / TerminalOp 图解释器 | `graph.py` |
| 原语技能 πᵢ | goto / open_chest / kill_monster / press_button / toggle_switch / use_exit / wait | `skills.py` |
| 顶层程序（手写基线） | 9 级优先级修正规划器 + 反思恢复 | `planner.py` |
| 归纳 Stage 1 | GPT-4o 逐轨迹合成局部专家程序，反例驱动迭代精化 | `induction/synthesize.py` |
| 归纳 Stage 2 | 四算子（条件分支/模块移植/变量提升/循环折叠）贪心合并 | `induction/consolidate.py` |
| 经验程序一致性 | 确定性回放：程序动作 vs 专家动作，`max Σ|R̂| − λ|π|` | `induction/consistency.py` |
| 在线/离线反思 | 运行时活锁 → 修正规划器接管；离线失败 → GPT-4o 嫁接恢复分支 | `induction/dsl.py`, `induction/reflect.py` |

### 1.2 关键环境约束（决定了整套架构）

引擎公开接口（`constants.py`，刻意与环境内部解耦复制一份）：

- **1 env.step = 1 像素**位移，单局最多约 2000 步 → 逐步调用 3B VLM 完全不可行；
- 地图为 **10×8 网格 × 16px tile = 160×128px**；玩家/怪物是 16×16 的**像素级
  精确实体**，不占格；
- 玩家 1px/步，怪物 0.5px/步，命中怪物眩晕 60 tick，玩家满血 5HP；
- 出口固定在边界格：`N:(4,0),(5,0) S:(4,7),(5,7) W:(0,3),(0,4) E:(9,3),(9,4)`；
- 动作空间 7 个：`WAIT / UP / DOWN / LEFT / RIGHT / A(交互·挥剑) / B(盾)`。

### 1.3 分层数据流

```
                    ┌────────────────────────────────────────────┐
   obs(像素帧) ───► │  φ 感知层  grounding/vlm.py (Qwen2.5-VL-3B) │
                    └───────────────┬────────────────────────────┘
                                    │ SymbolicState (一房间符号快照)
                    ┌───────────────▼────────────────────────────┐
   info[inventory]─►│  Z 状态/记忆  tracker.py + memory.py        │
   info[reward] ───►│  · 关键帧调度 · 死推演 · 不确定球 · 里程计   │
                    └───────────────┬────────────────────────────┘
                                    │ Ctx(memory, tracker, scope)
                    ┌───────────────▼────────────────────────────┐
                    │  G 顶层程序   二选一（selection.json 甄选）  │
                    │  ① DSLPlanner  (GPT-4o 归纳的 JSON 图)       │
                    │  ② FallbackPlanner (手写 9 级优先级级联)     │
                    └───────────────┬────────────────────────────┘
                                    │ 调用原语技能
                    ┌───────────────▼────────────────────────────┐
   action(int) ◄────│  πᵢ 原语技能  skills.py                     │
                    │  BFS 重规划 + 像素控制器 + 安全护盾          │
                    └─────────────────────────────────────────────┘
```

### 1.4 主控制回路（`agent.py::Policy.act`）

每个 env.step 精确执行以下逻辑（一步只产出一个动作）：

```python
def act(self, obs, info):
    self.memory.on_step(info)                 # 仅读 inventory 视图 + 步数
    if self._blocked_by_reward(info):         # reward 反馈：上一步撞墙？
        self.tracker.note_blocked_feedback()  # 回滚 1 步乐观预测

    if self.tracker.should_perceive() and backoff<=0:
        try:  state = self.backend.ground(obs)   # φ：像素 → 谓词
        except: self._ground_backoff = 3         # grounding 崩了绝不炸测评器
        if state: self.tracker.sync(state)        # 与预测对账、登记穿房

    try:  action = self.planner.step(self.ctx)    # G：符号执行
    except: action = 0                            # 最后兜底 WAIT
    self.tracker.apply_action(action)             # 形式化转移模型死推演
    return int(action)
```

三处"异常免疫"是提交形态稳健的关键：grounding 失败退避重试（下一帧通常自愈）、
规划器异常兜底 WAIT、感知解析失败在 `ground()` 内先降温采样重试一次。

---

## 2. 感知层 φ：稀疏关键帧 + 符号推演

核心思想：VLM 只在**关键帧**被调用，帧间玩家位置用与引擎一致的**确定性转移
函数**死推演（dead-reckoning），怪物位置膨胀成**不确定球**，**安全护盾**保证
稀疏感知下仍不受接触伤害。这样把每局约 2000 次潜在 VLM 调用压到几十~上百次。

### 2.1 关键帧调度（`tracker.py::should_perceive`）

在以下任一条件触发一次 grounding，否则纯靠推演：

- **显式请求** `perceive_requested`（交互/挥剑后必查；护盾停滞时；开箱前对齐时）；
- **期待穿房** `expect_transition`（UseExit 推门后必须核实是否真的过去了）；
- **周期到点**：平时 `SYNC_INTERVAL_CALM = 24` 步一次；**危险临近**
  （任一怪物切比雪夫距离 ≤ `DANGER_RADIUS_PX = 3.5×tile = 56px`）时收紧到
  `SYNC_INTERVAL_DANGER = 8` 步一次；战斗技能内部进一步收紧到每 6 步。

### 2.2 死推演转移模型（`tracker.py::apply_action / _predict_move`）

发出动作后立即前推预测位置，与引擎的**轴向钳制 AABB** 规则一致：

```
_predict_move(px, dir):
    nx, ny = clamp(px + 单位向量, [0, MAP−tile])   # 先按 1px 前移并夹在地图内
    if _rect_hits_block(nx, ny): return px          # 16×16 rect 覆盖的任一格
    return (nx, ny)                                  # 是已知阻挡则原地不动
```

`_rect_hits_block` 遍历玩家矩形覆盖的所有格（`floor` 除法 + 右下角 −1px 判边界），
查 `memory.is_blocking`。A/B 交互动作会置 `perceive_requested`（世界可能变化，
下一步必须核实）。

### 2.3 怪物不确定球 + 安全护盾（`tracker.py` + `skills.py::shielded`）

- 每一步所有怪物 `uncertainty_px += MONSTER_SPEED_PX = 0.5`：自上次感知起，怪物
  真实位置一定落在以其上次观测中心为心、半径 = 已推演步数 × 0.5px 的球内；
- `monster_clearance_px(left, top)`：玩家矩形与"膨胀后怪物矩形"的最小切比雪夫
  间隙（`reach = tile + uncertainty`），负值即重叠；
- `px_is_safe(margin = CONTACT_MARGIN_PX = 6px)` 为安全判据；
- **护盾** `shielded(action)`：任何会把玩家推入不确定球的移动都被否决，转而
  `request_perceive()`（让球坍缩回真实点）并出盾（有盾）或 WAIT。

> 这是稀疏感知能"可证安全"的核心：只要怪速上界 0.5px/步成立，球一定包住真实
> 怪物，护盾约束下就不会发生计划外接触伤害（见 §11 Lean 对接点）。

### 2.4 reward 作反馈：撞墙检测与回滚（`agent.py::_blocked_by_reward`）

作业允许把 env 的 **reward 作历史反馈信号**。撞墙步会在普通 step 惩罚之上叠加
`invalid_action` 惩罚，标量可辨识：

```
expected_blocked = weights[step] + weights[invalid_action]
scalar = Σ weights[name] × signals[name]
撞墙 ⟺ |scalar − expected_blocked| < 1e-6
```

检出后 `note_blocked_feedback()` 把上一步乐观预测的位置回滚到 `_prev_px`
（**1 步延迟**的撞墙反馈），并置 `last_move_blocked`。这条链条让我们**不必**
从"预测与观测偏差"去反推墙体——那会导致"幽灵墙自增强"（见 §10-5）。

### 2.5 关键帧对账与房间里程计（`tracker.py::sync`）

`sync(state)` 把新 grounding 快照与预测对账，核心是**判定是否发生了穿房**，
用两条独立证据抗噪：

1. **像素跳变**：`|Δx|` 或 `|Δy| > 2×tile`；
2. **网格整体替换**：新旧网格逐格不同数 `≥ 12`（穿房换了整张图）。

三种情形：

- **有 `expect_transition`（主动推门）**：跳变则 `memory.transition(dir, state)`
  按里程计更新房间坐标；否则记一次 `failed_exits[dir] += 1` 并当作同房刷新；
- **无 expect 但检测到瞬移**：引擎会在玩家"贴合出口格"的**瞬间**传送，这可能
  发生在 GoTo 的对齐阶段、早于 UseExit 置标志位。此时用"网格大换 ∨ 落点在
  移动方向**对侧**边界（进房出生点，`margin = 3×tile`）"判定这是一次穿房，用
  **最后移动方向**登记 `crossed`——否则外房关键帧会静默覆盖当前房记忆、腐蚀
  里程计（这是攻克 task_4 的竞态修复之一，见 §10-1）；
- **普通刷新**：`integrate_keyframe(state)` 就地并入当前房。

### 2.6 VLM grounding 模型（`grounding/vlm.py`）

- 基座 **Qwen2.5-VL-3B-Instruct**，4bit NF4 加载（`NSI_VLM_4BIT=1` 默认）+ 可选
  LoRA adapter（`NSI_VLM_ADAPTER`），推理 `max_new_tokens=220`、贪心解码；
- 输出即 `SymbolicState.to_text()` 的紧凑格式（约 150 token）：

  ```
  GRID
  ##########
  ..........          (8 行 × 10 字符，row0=顶)
  ...
  PLAYER 64,96 up
  MONSTERS chaser:32,32 patroller:96,80
  EXITS N:- S:normal W:locked E:-
  ```

- **解析容错**（`schema.py::from_text`）：正则抽取玩家/怪物/出口，坐标夹到合法
  范围；网格行只保留合法 tile 字符，长度漂移则按 `GRID_W` 裁剪/补齐（均匀行如
  被 LM 缩写的 `======` 用自身字符补齐）；
- **解析校验 + 采样重试**（`ground()`）：贪心结果解析失败则以 `temperature=0.3`
  再采一次——把偶发格式错误压到接近 0。

### 2.7 QLoRA 训练与数据配方（`grounding/train_qlora.py`, `grounding/prompts.py`）

**patch–tile 精确对齐**（最关键的归纳偏置）：帧用最近邻放大 `IMAGE_SCALE=3.5`
（160×128 → 560×448），使 Qwen2.5-VL 的 **28px 合并 patch 恰好覆盖 16px 游戏
tile 的 2×2**——每个 tile 对应 2×2 视觉 token，天然利于逐格分类。

**训练设置**：

| 项 | 值 |
|---|---|
| LoRA | rank 16, α 32, dropout 0.05, target = q/k/v/o/gate/up/down_proj |
| 量化 | 4bit NF4 + double-quant，compute dtype bf16 |
| 优化 | lr 1e-4 cosine，warmup 0.03，2 epoch，batch 4 × grad-accum 4，梯度检查点 |
| 监督 | **只在答案上算 loss** |

**collator 掩码 bug（v1→v2 的关键修复）**：只训练答案需把 prompt 部分掩成
`IGNORE_INDEX`，但 prompt 长度**必须在"处理后 ids"上量**——processor 会把图像
占位符展开成大量视觉 token，若用原始 tokenizer 长度会把掩码切得太早、标签严重
错位（v1 因此 24% 格式失败）。修复：对每条样本单独跑一遍
`processor(text=[prompt], images=[image])` 取真实 prompt 长度再掩码。

**数据配方（v2→v3 的质变）**：v1/v2 用约 150 张地图 × 多样本，模型学会**背布局**
（分布内 100%、未见布局整格全对 0%）；v3 改为 **3000 个"单次使用"独立布局 ×
每张仅 3 样本**（外加 1503 个深渊房样本续训成 v3b），强迫模型真正读图——未见
布局整格全对从 0% 升到 95.5%。训练标签由环境的 Oracle 后端自动生成（训练期允许
用 info）。

---

## 3. 符号状态 Z 与跨房间记忆

### 3.1 `SymbolicState`（`grounding/schema.py`）

一房间的符号快照 = **静态网格 + 像素级动态实体**：

- `grid`：8×10 字符，17 类 tile。`.`floor `#`wall；宝箱按内容物细分
  `K`钥匙 `G`金币 `H`回血 `S`道具/剑 `C`未知 `O`已开；`T`尖刺 `A`深渊 `_`gap
  `=`桥 `b/B`按钮(未压/已压) `L/l`拉杆(闲置/激活) `N`NPC；
- `player_px / facing`、`monsters(kind,px)`、`exits{dir: state}`
  （state ∈ `- / normal / locked / conditional / open`）；
- 派生谓词：`is_blocking`（`BLOCKING_TILES` = 墙/NPC/gap/所有宝箱）、`is_hazard`
  （`HAZARD_TILES` = 尖刺/深渊）、`closed_chests()`、`tiles_of(cls...)`、
  `player_tile`（中心取整归格）。这些纯函数是符号层与 Lean 的接口。

### 3.2 跨房间记忆（`memory.py`）

**房间里程计图**：起始房坐标 `(0,0)`，沿方向 d 穿门坐标偏移 `EXIT_DELTA[d]`
——**不需要地图真值，只靠 agent 自身穿房历史**。每房 `RoomMemory` 存：

- `state`：最近一次 grounding 快照；
- `learned_blocked{tile: 过期步}`：碰撞学到的隐藏墙，`TTL=300` 步过期；感知能
  分类的格由感知覆盖猜测，只保留"感知仍称 floor"的学习块（标记 grounding 错误）；
- `visited_exits / probed_dirs / failed_exits`：穿过的门 / 盲探过的方向 / 失败计数；
- `opened_chests / talked_npcs / switch_toggles`：交互进度。

`is_blocking(x,y)` 融合"未过期学习块 ∨ 感知阻挡"。`InventoryView` 只封装测评
接口显式提供的物品栏（keys/gold/items/tools/equipped + `has_sword/has_shield`
派生）。`hp_estimate` 为粗略血量：task_5 观测到**每 200 步隐藏扣 1HP**，据此计价
时间（见 §10-4）。

---

## 4. 执行图 G 与解释器（`graph.py`）

技能/程序 = 共享作用域 C（变量）与符号状态 Z 上的**类型化节点图**，节点种类严格
对齐论文：

| 节点 | 语义 |
|---|---|
| `DataOp` | 从状态绑定/更新作用域变量，`→ next` |
| `CheckOp` | 求谓词并分支 `on_true/on_false`（**循环 = 带回边的 Check**） |
| `PrimitiveOp` | 产出一个 env 动作，`→ next` |
| `SkillOp` | 调用子技能（时间扩展，运行到返回）`on_success/on_fail` |
| `TerminalOp` | 终止，带 success + **符号诊断项** diagnosis |

`Interpreter` 是**可续算**的：每次 `step` 推进图直到恰好产出一个动作或终止，给定
`(program, scope, state)` **完全确定**。防非产出循环：单步内最多推进
`MAX_TRANSITIONS_PER_STEP=256` 次转移，超出判 `nonproductive_loop` 失败。
`SkillProgram.__post_init__` 静态校验所有边指向存在的节点；`complexity()=len(nodes)`
是归纳目标里的 MDL 项 |π| 之一。这一层正是可在 Lean 中建模为小步转移语义的部分。

---

## 5. 原语技能层（`skills.py`）

所有导航技能遵循同一模式：**每步在 10×8 记忆网格上重跑 tile 级 BFS**（网格小，
重规划极廉价）→ 像素控制器驱动（1px/步）→ 安全护盾把关。

**公共构件**：

- `bfs_path(start, goals, avoid_monsters, allow_hazard)`：默认避开
  `monster_blocked_tiles`（中心落入不确定球的格），找不到路则退避为
  `avoid_monsters=False` 再试一次（护盾仍逐步把关），仍无则报符号失败 `no_path`；
- `move_toward_waypoint`：**先对齐误差较小（通常是垂直）的轴**，使 16×16 玩家
  矩形不会斜切入非路径格；
- `disambiguation_nudge`：grounded 坐标取整、引擎保留分数 → tile 归属在边界
  ±1px 内不可信。任何"依赖格归属"的交互前，先向当前格内部挪到两轴都 ≥2px 明确；
- `shielded`：见 §2.3。

**七个技能**（`SKILL_REGISTRY`）：

| 技能 | 关键机制 |
|---|---|
| `GoToTile` | 导航到目标格（或其邻格）。**停滞检测**：连续 ≥4 次移动但两次关键帧间实位未动 → 该格实为隐藏墙，`mark_blocked` 后让 BFS 绕行。**撞墙检测**：`last_move_blocked` 连续 ≥4 次同理标记 |
| `OpenChest` | 走到邻格 → `disambiguation_nudge` → **仅在刚同步的步**按 A（引擎按真实位置判邻接，在陈旧预测上按 A 会误挥剑）→ 按 A ≤4 次，验证变 `O` |
| `PressButton` | 站上按钮格（按钮按位置触发），验证变 `B` |
| `ToggleSwitch` | 走到拉杆邻格按 A 一次。杆效果常在**另一房**（旋桥），无法就地验证 → 交互后由规划器重感知受影响房并重查可达性 |
| `UseExit` | 走到出口格 → **精确像素对齐** → 向边界外推。用 `expect_transition` + `last_transition_result` 与 tracker 对账；`≥2` 次推不动判 `exit_blocked` |
| `KillMonster` | 见下 |
| `Wait` | 空转 N 步（周期重感知） |

**`KillMonster` 战术**（步数减半的关键）：

- 选最近怪（切比雪夫），按 `_swing_facing` 判断剑击窗口：垂直偏移 ≤10px 且
  水平 `gap ∈ [4,30]px` 即可朝该向挥剑——**下界 4 很小是刻意的**：引擎先结算剑、
  命中即眩晕怪 60 tick，故"贴身挥剑"安全（见 §10-6）；
- 命中后置 `_stun_left≈55`，利用眩晕窗口追击连击；未对齐且接触在即则出盾；
- 贪心逼近走进墙/箱时，**提交一段 BFS 绕行**（`_detour_left=10`），避免贪心与
  BFS 两个控制器互相抖动（一次只给一个权威）。

---

## 6. 顶层规划 I：手写修正规划器（`planner.py::FallbackPlanner`）

开发基线、归纳程序的安全网，也是 task_5 的最终选择。它是一个**9 级优先级条件
级联**（`_choose_goal`），每个 env.step 选一个 Goal 并驱动对应技能；失败的 Goal
获得**符号诊断 + 冷却**（`FAIL_COOLDOWN_STEPS=120`），相关状态变化后再重试。

```
0. 无剑且受威胁（间隙 <2 tile）→ 逃向最远安全格
1. 有剑且怪逼近（<1.9 tile）或怪挡住通往待办的所有路 → kill_monster
1.5 已提交的拨杆意图（连通性反思恢复）→ 去拨杆
2. 开最近可达的关闭宝箱
3. 持钥匙 + 锁门 → use_exit（goal key 含钥匙数，加钥匙即重试）
4. 按下未压按钮（廉价，且多数条件门的前置）
5. 在"未试过的条件签名"下试条件门（签名=钥匙数×怪数×已压按钮集）
6. unblock：本房待办不可达但存在已知拨杆 → 去拨杆（意图跨房持久化）
7. 路由：向"有待办/前沿出口"的最近房前进（房图 BFS 求首跳 `_first_hop`）
7.5 局部盲探：感知可能漏门（深渊背景）→ 向"出口格看着能走"的未试方向推一下，
    引擎权威裁决（穿房 or 挡住）
7.6 危险覆盖的边界方向可能藏被覆盖门 → 拨杆改旋桥再暴露出来探
7.7 弱待办路由：向"仍有未探方向"的房前进
8. 空转等待（周期重感知，兼冷却过期后重试）
```

**反思恢复**内嵌其中：可达性失败（`no_path/unreachable`）且已知存在拨杆
→ 置 `pending_toggle`，先去翻一个杆再重试（`MAX_TOGGLES=12` 上限）；拨杆成功后
清空冷却让"曾不可达"的目标立即重试。**战斗中断**：有剑且非战斗 Goal 时若怪间隙
< `THREAT_CLEARANCE_PX=12`，放弃当前 Goal 转战斗。方向偏好 `TASK_DIR_HINTS` 是
**纯提示**（仅影响探索顺序），逻辑本身任务无关。

---

## 7. 顶层规划 II：NSI 技能归纳管线（`induction/`）

把专家演示轨迹"提升为逻辑"：GPT-4o 写 DSL 程序，**确定性回放一致性**作接受判据，
两阶段合成 + 离线/在线反思修复。

### 7.1 DSL 与沙箱表达式（`induction/dsl.py`）

程序是 JSON：`{name, entry, reactive[], nodes[]}`。节点 4 种（data/check/skill/
terminal），循环 = 带回边的 check，`reactive` 守卫每步优先于图求值（用于战斗中断）。
表达式是**受限、无副作用的 Python 子集**，对符号状态求值：

- `_validate` 白名单 AST：只允许布尔/比较/算术/调用/下标/属性/三元；属性访问
  仅限 `inv.` / `var.`；调用只能是命名函数；
- `build_env` 暴露纯查询命名空间：`closed_chests() chests(kind) nearest(tiles)
  reachable(tile) exit_state(dir) visited(dir) threatened() buttons()
  switches() room_known(dir) hop_toward(kind) player_tile()` 等 + `inv.*`；
- **`hop_toward('locked_exit'|'chest'|'switch'|'unexplored')`**：在已知房图上
  BFS，返回通往"最近满足条件之房"的**首跳方向**——多房任务的核心查询（如
  `use_exit(hop_toward('locked_exit'))` 携钥匙回门）。加入它后 task_4 覆盖率
  从 58.5% → 87.1%；
- `eval` 在 `{"__builtins__": {}}` + 受限命名空间中执行，裸名回退到作用域变量
  （LLM 常丢 `var.` 前缀）。`complexity(spec)` = 节点/守卫计数 + 每个表达式的
  token 成本，即 MDL |π|。

### 7.2 经验程序一致性（`induction/consistency.py`）

**确定性、不含 LLM 的接受判据**。`replay(spec, trace)`：把录制的每步符号状态喂给
程序，要求它复现专家动作；`matched` 计入覆盖 |R̂|；一次发散后程序**重对齐**
（新实例）以便后段仍能得分（近似论文的"一致性区域大小"）。归纳目标：

```
max_π  Σ_traces |R̂(π)|  −  λ·|π|          (λ = LAMBDA = 0.5)
```

`score()` 返回目标值 + 每轨迹结果；发散点记录 `(step, 期望vs实际动作, 坐标,
状态文本, 出错节点)` 作为反例喂回 LLM。

### 7.3 Stage 1 逐轨迹合成（`induction/synthesize.py`）

对每条演示轨迹合成一个"局部专家"程序：`summarize_trace` 把轨迹压成**决策段落**
（技能调用序列 + 事件 + 物品栏），GPT-4o 结构化输出（`PROGRAM_JSON_SCHEMA`）；
最多 4 轮**反例驱动精化**——回放找首个未覆盖状态 → `divergence_feedback` 指出
"在节点 X 处专家做 A 而你选了 B"（含程序过早终止的提示）→ 修订；覆盖 ≥98% 且
无发散即停。`DSL_GUIDE` 系统提示详列 DSL 文法、技能签名、查询命名空间与"泛化而非
背坐标/步数"的规则。

### 7.4 Stage 2 跨轨迹合并（`induction/consolidate.py`）

贪心合并局部专家为**一个全局程序**。用覆盖最广者初始化，每轮对**最难轨迹**
（覆盖最低）用论文四算子合并：**条件分支 / 模块移植（子图搬运+重绑参数）/
变量提升（常量→状态查询）/ 循环折叠**；候选**当且仅当总覆盖严格增加且不回退
任何已覆盖轨迹**（`matched` 掉 >10 视为回退）才接受，每次合并最多 3 轮。最终全局
程序 `mathematical_logic_task_2`（7 节点 + 1 守卫）源自 task_2 局部专家的自然
泛化——**一套程序覆盖全部 5 条演示轨迹（90–99.6%）**；未被全局充分覆盖（<0.9）
的轨迹保留其专家工件。

### 7.5 DSLPlanner 运行时 + 在线反思恢复（`induction/dsl.py::DSLPlanner`）

执行归纳工件，并内建**运行时反思恢复**（论文"失败→恢复→嫁接"的在线对应）：

- **反应守卫**先于图：每步扫 `reactive`，命中即抢占为一次技能调用；
- **活锁检测**：`_progress_marker` 只取**单调进展量**（钥匙/金币/工具/已知房数/
  剩余宝箱/剩余怪/已压按钮）——房间来回振荡**不**重置活锁钟。`LIVELOCK_STEPS=150`
  步无进展判活锁；**血量吃紧（hp≤3）时收紧到 80 步**（task_5 扣血下停滞是致命的）；
- **恢复**：交给 `FallbackPlanner` 接管至多 `RECOVERY_MAX_STEPS=500` 步，有进展
  即交回程序（`MAX_RECOVERIES=1`，之后修正规划器长期持有）；
- **"程序自认为完成但 episode 未结束"** → 立即判为覆盖缺口、交修正规划器（不空转）；
- **异常免疫**：坏表达式在活 episode 中不炸，转为程序失败诊断。

### 7.6 离线反思嫁接（`induction/reflect.py`）

开发期在**真环境**跑归纳程序；失败时把终止诊断 + 尾部决策上下文交 GPT-4o，
**嫁接一条恢复分支**。补丁仅当 (a) 演示轨迹一致性覆盖不下降（`value ≥ baseline−25`）
且 (b) 原先失败的任务在**实跑（oracle 后端）中现在通关**才保留——一致性防回归、
实跑验闭环，两道关缺一不可（见 §10-2）。

### 7.7 实跑甄选（`induction/select.py` → `selection.json`）

对每关把三种候选（per-task 局部专家 / 全局程序 / 手写修正规划器）**逐一实跑**，
第一个通关者写入 `selection.json`，运行时加载器严格遵从——**上线配置即验证批准的
配置**。当前甄选结果：

| 任务 | 采用 | 工件 |
|---|---|---|
| task_1 | 局部归纳程序 | `mathematical_logic_task_1.json`（8 节点） |
| task_2 | 局部归纳程序 | `mathematical_logic_task_2.json`（7 节点，1 守卫） |
| task_3 | 局部归纳程序 | `mathematical_logic_task_3.json`（13 节点，1 守卫） |
| task_4 | 局部归纳程序 | `mathematical_logic_task_4.json`（14 节点） |
| task_5 | **手写修正规划器** | `null`（隐藏扣血预算极紧，归纳程序余量不足） |

---

## 8. 测评合规性

推理路径**仅**使用：`obs`（像素 → VLM）、`info["inventory"]`（接口显式提供）、
`info["reward"]`（reward 值反馈）、`reset(task_id)`（接口显式传入，仅影响探索
方向偏好）。**不读取** agent 坐标、地图真值、实体位置等 info 内部状态。
`OracleGrounding`（读引擎内部）仅用于训练期标注/录制/调试/甄选，`make_policy()`
显式拒绝实例化（`NSI_BACKEND=oracle` 抛错）。归纳产物是冻结的本地 JSON
（`induction/artifacts/`），**测评时不调用任何外部 API**。策略全路径异常免疫，
不会使测评器崩溃。

---

## 9. 成绩单

### 9.1 端到端评测（最终，提交形态）

`python utils/evaluate_policy.py --policy submission_agent.py`
（Qwen2.5-VL-3B QLoRA v3b + GPT-4o 归纳工件；环境对 seed 确定）

| 任务 | 成功率 | 步数 | Oracle 上界 | 备注 |
|---|---|---|---|---|
| task_1 取钥匙开门 | **100%** | 279 | 279 | **步数 = 上界最优** |
| task_2 杀怪+条件门 | **100%** | 195 | 197 | **反超上界** |
| task_3 三房任务链 | **100%** | 1449 | 582 | 盲探针开销（上限 1500） |
| task_4 旋桥+全宝箱 | **100%** | 1483 | 1229 | 不可见门三连修后攻克 |
| task_5 多房+隐藏扣血 | **100%** | 1137 | 1136 | **与上界仅差 1 步** |

Oracle 上界 = 符号层用完美感知（`OracleGrounding`）的演示步数（279/197/582/
1229/1136），也是 Stage 1 的演示轨迹长度。

### 9.2 感知精度（Qwen2.5-VL-3B QLoRA）

| 指标 | 零样本 | v2 | v3（held-out 未见布局，200 样本） |
|---|---|---|---|
| 输出格式合规 | 100% | 75% | **100%** |
| 网格 tile 精度 | 76% | 82.4% | **99.88%** |
| 整格全对率 | 0% | 0% | **95.5%** |
| 玩家/怪物/出口/朝向 | — | 100% | **100%** |
| 综合 all_ok | 0% | 0% | **95.5%** |

官方任务地图（分布内）：v2 起全指标即 100%。v2→v3 的质变来自"单次使用布局"
（杜绝布局记忆）；v3→v3b 补深渊房全类型门样本并续训。

### 9.3 NSI 归纳质量

| 任务 | Stage 1 局部专家覆盖 | Stage 2 全局程序覆盖 | 甄选采用 |
|---|---|---|---|
| task_1 | 99.6% | 99.6% | 局部归纳程序 |
| task_2 | 92.9% | 92.9% | 局部归纳程序（亦为全局基） |
| task_3 | 71.3% | 98.3% | 局部归纳程序 |
| task_4 | 87.1% | 91.4% | 局部归纳程序 |
| task_5 | 59.3% | 90.2% | 修正规划器（实跑甄选） |

Stage 2 最优全局程序源自 task_2 局部专家的自然泛化——**一套 7 节点程序覆盖全部
5 条演示轨迹（90–99.6%）**。

### 9.4 泛化验证

- 变体 task_1 地图（挪宝箱、改墙型）：归纳程序与修正规划器均 211 步通关——
  **无硬编码坐标**；
- 感知在 3000 个独立布局上训练、在完全未见布局上 95.5% 整格全对——直面
  "最终测评可能变布局"的考察点。

---

## 10. 关键技术发现（问题 → 证据 → 解法）

1. **不可见门是环境事实**：渲染器把深渊画在门之后，深渊房的门像素不可见。
   三层解法：① 感知标签对齐可见性（不可见之物不标注）；② 穿房登记竞态根治
   （贴边对齐先于"推门"标志触发引擎传送 → 计划外跳变用「网格大换 ∨ 对侧边界
   落点」证据 + 最后移动方向登记，见 §2.5）；③ 行为层知识闭环（盲探针让引擎
   裁决门的存在 → probed 记忆 → 危险覆盖方向驱动旋桥 → 强/弱 pending 分级路由
   → 钥匙增加时重探——持钥匙推不可见锁门会被引擎直接放行）。
2. **经验程序一致性必要不充分**：回放覆盖 65% 的程序实跑死循环于"取钥匙后无
   回程逻辑"——回放喂的是专家控制下的状态流，掩盖闭环控制缺陷。**live rollout
   验证 + 运行时反思恢复**（§7.5–7.6）是必要补充。
3. **布局记忆 vs 真实读图**：约 150 张地图 × 多样本训练的模型在未见布局上整格
   全对 0%（背布局）；3000 张 × 每张 3 样本 → 95.5%（§2.7）。
4. **取整观测下的边界歧义**：引擎分数像素坐标取整后，tile 归属在边界 ±1px 内
   不可信 → 交互前 `disambiguation_nudge`（向格内部挪到两轴 ≥2px 再按 A）。
5. **不要从预测偏差推断墙体**（幽灵墙自增强循环）；撞墙检测交给 reward 反馈
   （§2.4），隐藏墙只由"多步停滞/连续撞墙"经 `mark_blocked` 学习并带 TTL 过期。
6. **贴身挥剑安全**：引擎先结算剑、命中即眩晕 60 tick、眩晕怪无接触伤害 →
   挥剑窗口可放宽到 `gap∈[4,30]px`，战斗步数减半以上（§5 KillMonster）。
7. **时间即预算**：task_5 每 200 步隐藏扣 1HP → 只打 1.9 tile 内贴脸怪，活锁钟
   在 hp≤3 时从 150 收紧到 80，甄选最终选步数更省的修正规划器。

---

## 11. Lean 形式化对接点（可证层）

以下组件为纯函数/确定性小步语义，可在 Lean 中建模并证明（详见
`nsi_agent/README.md`）：

- `SymbolicState` 谓词与走格图 → 「合法移动不出界、不进墙」不变量；
- `tracker._predict_move` 转移函数 → 与引擎 AABB 钳制一致性；
- 怪物不确定球 + `px_is_safe` 护盾 → 「护盾约束下不受接触伤害」安全性定理
  （怪速 0.5px/步给出可证的最坏位移界）；
- `skills.bfs_path` → 规划器可靠性（输出路径均可走）与完备性（存在路径必找到）；
- `graph.Interpreter` + DSL 表达式语义 → 「解释器每步至多产出一个合法动作」
  「terminal 可达性」「非产出循环有界终止」；
- 归纳接受判据（覆盖单调 + MDL）→ 合并不破坏已覆盖轨迹的引理。

神经网络（VLM/GPT-4o）本身不证，证明覆盖其输出的符号层（schema 校验、action
mask、护盾、规划器、轨迹一致性检查器）。

---

## 12. 复现命令

```bash
# 训练期
python -m nsi_agent.debug_run --episodes 3                  # Oracle 调试 5 关
python -m nsi_agent.grounding.dataset --out data/g --task-episodes 3 --unique-maps 3000
python -m nsi_agent.grounding.train_qlora --data data/g --model <Qwen2.5-VL-3B> --out ckpt/lora
python -m nsi_agent.grounding.eval_grounding --data data/g --split heldout --model <...> --adapter ckpt/lora/final
python -m nsi_agent.grounding.merge_lora --model <...> --adapter ckpt/lora/final --out models/merged

# NSI 归纳（GPT-4o，需 ~/.config/nsi_agent/openai.env）
python -m nsi_agent.induction.record         # 录制 Oracle 演示轨迹
python -m nsi_agent.induction.synthesize     # Stage 1 逐轨迹合成
python -m nsi_agent.induction.consolidate    # Stage 2 贪心合并
python -m nsi_agent.induction.reflect --task mathematical_logic/task_4   # 离线反思嫁接
python -m nsi_agent.induction.select         # 实跑甄选 → selection.json

# 最终测评（提交形态）
export NSI_VLM_MODEL=<merged model dir> NSI_VLM_4BIT=0
python utils/evaluate_policy.py --policy submission_agent.py --num-envs 10
```

可视化成绩单：`report/nsi-results.html`（自包含单文件，浏览器直接打开，
支持明暗主题）。模块级技术说明另见 `nsi_agent/README.md`。

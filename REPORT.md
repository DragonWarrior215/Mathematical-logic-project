# NesyLink 神经符号 Agent 实验报告

**方法框架**：迁移论文 *"Lifting Traces to Logic: Programmatic Skill Induction with
Neuro-Symbolic Learning for Long-Horizon Agentic Tasks"（NSI, arXiv:2605.01293）*
**最终成绩**：提交形态端到端评测 **5/5 关全通**（纯像素 + reward + 物品栏输入）
**代码**：`nsi_agent/` · **入口**：`submission_agent.py` · **日期**：2026-07-04

---

## 1. 方法总览

NSI 将"技能"定义为三元组 **π = (θ, φ, G)**：θ 为调用参数，φ 为神经感知
grounding（原始观测 → 符号谓词），G 为符号执行图（带条件分支/循环/变量绑定的
一阶逻辑程序），按 **Perceive → Think → Act** 循环执行；技能程序由"轨迹 → 逻辑"
归纳获得，失败时经符号诊断反思修复。本项目将该框架完整迁移到 NesyLink：

| NSI 概念 | 本实现 | 代码位置 |
|---|---|---|
| φ 神经 grounding | Qwen2.5-VL-3B + QLoRA，像素帧 → 紧凑符号状态文本 | `grounding/vlm.py` |
| 符号状态 Z | `SymbolicState`（10×8 网格 + 像素级实体）+ 跨房间记忆 | `grounding/schema.py`, `memory.py` |
| 执行图 G | DataOp / CheckOp / SkillOp / TerminalOp 图解释器 | `graph.py` |
| Perceive-Think-Act | 关键帧调用 VLM + 帧间形式化转移模型推演 | `tracker.py`, `agent.py` |
| 原语技能 | goto / open_chest / kill_monster / press_button / toggle_switch / use_exit | `skills.py` |
| 归纳 Stage 1 | GPT-4o 逐轨迹合成局部专家程序，反例驱动迭代精化 | `induction/synthesize.py` |
| 归纳 Stage 2 | 四算子（条件分支/模块移植/变量提升/循环折叠）贪心合并 | `induction/consolidate.py` |
| 经验程序一致性 | 确定性回放：程序动作 vs 专家动作，max Σ|R̂| − λ|π| | `induction/consistency.py` |
| 反思规划 | 失败诊断 → GPT-4o 嫁接恢复分支；运行时活锁检测 → 修正规划器接管 | `induction/reflect.py`, `induction/dsl.py` |

### 1.1 感知层（φ）：关键帧调用 + 符号推演

环境 1 step = 1 像素、单局最多 2000 步，逐步调用 3B VLM 不可行。设计为：

- **关键帧触发**（进房 / 交互后 / 战斗中每 ~6 步 / 平时每 ~24 步 / 异常时）调用
  VLM，输出固定格式符号状态（80 字符网格 + 玩家/怪物像素坐标 + 出口类型）；
- **帧间推演**：玩家位置按与引擎一致的形式化转移函数推进（1px/步 + AABB 钳制），
  怪物位置放大为按 0.5px/步增长的**不确定球**，安全护盾保证不进入任何球；
- **reward 作反馈信号**（作业明确允许）：撞墙步含 invalid_action 惩罚、与正常步
  可辨识 → 1 步延迟检测撞墙并回滚预测位置。

VLM 训练：环境自动生成 (帧, 真值标签) 监督数据（训练期允许使用 info），QLoRA
微调。关键技巧：**3.5× 最近邻放大使 Qwen 的 28px 视觉 patch 与 16px 游戏 tile
精确对齐**（每 tile = 2×2 视觉 token）；**每布局只采 3 个样本 × 3000 个单次使用
布局**，使布局记忆策略失效、强迫真实读图。

### 1.2 符号规划层（G）

- 每步在 10×8 记忆网格上重规划 BFS（tile 级），像素控制器负责贴边与对齐；
- 手写修正规划器 = 8 级优先级条件级联（反应安全 → 开箱 → 过门 → 清怪 → 按钮 →
  推杆解锁 → 路由/探索 → 等待），带失败冷却与符号诊断；
- 顶层任务程序由 GPT-4o 归纳（JSON DSL，受限表达式沙箱求值），实跑甄选
  （`selection.json`）决定每关采用归纳程序或修正规划器；
- 运行时反思恢复：单调进展计数器 150 步（血量吃紧 80 步）无变化判定活锁 →
  修正规划器接管。

### 1.3 测评合规

推理路径仅使用 `obs`（像素）、`info["inventory"]`（接口显式提供）、
`info["reward"]`（reward 反馈）、`reset(task_id)`（接口显式传入）。Oracle 后端
（读引擎状态）仅用于训练期标注/录制/调试，`make_policy()` 显式拒绝。归纳产物为
冻结的本地 JSON，测评不调用任何外部 API。策略全路径异常免疫（感知失败退避重试、
规划器异常兜底），不会使测评器崩溃。

---

## 2. 成绩单

### 2.1 端到端评测（最终，提交形态）

`python utils/evaluate_policy.py --policy submission_agent.py --num-envs 2`
（Qwen2.5-VL-3B QLoRA v3b + GPT-4o 归纳工件；环境对 seed 确定）

| 任务 | 成功率 | 步数 | Oracle 上界 | 备注 |
|---|---|---|---|---|
| task_1 取钥匙开门 | **100%** | 279 | 279 | **步数 = 上界最优** |
| task_2 杀怪+条件门 | **100%** | 195 | 197 | **反超上界** |
| task_3 三房任务链 | **100%** | 1449 | 582 | 盲探针开销（上限 1500） |
| task_4 旋桥+全宝箱 | **100%** | 1483 | 1229 | 不可见门三连修后攻克 |
| task_5 多房+隐藏扣血 | **100%** | 1137 | 1136 | **与上界仅差 1 步** |

### 2.2 感知精度（Qwen2.5-VL-3B QLoRA）

| 指标 | 零样本 | v2 | v3（held-out 未见布局，200 样本） |
|---|---|---|---|
| 输出格式合规 | 100% | 75% | **100%** |
| 网格 tile 精度 | 76% | 82.4% | **99.88%** |
| 整格全对率 | 0% | 0% | **95.5%** |
| 玩家/怪物/出口/朝向 | — | 100% | **100%** |
| 综合 all_ok | 0% | 0% | **95.5%** |

官方任务地图（分布内）：v2 起全指标即 100%。v2→v3 的质变来自"单次使用布局"
（杜绝布局记忆）；v3→v3b 补深渊房全类型门样本并续训。

### 2.3 NSI 归纳质量

| 任务 | Stage 1 局部专家覆盖 | Stage 2 全局程序覆盖 | 实跑（Oracle 验证） |
|---|---|---|---|
| task_1 | 99.6% | 99.6% | ✅ 归纳程序 |
| task_2 | 92.9% | 92.9% | ✅ 归纳程序 |
| task_3 | 71.3% | 98.3% | ✅ 归纳程序 |
| task_4 | 87.1% | 91.4% | ✅ 归纳程序 |
| task_5 | 59.3% | 90.2% | 修正规划器（甄选） |

Stage 2 的最优全局程序源自 task_2 局部专家的自然泛化——**一套程序覆盖全部
5 条演示轨迹（90–99.6%）**。DSL 加入跨房路由查询 `hop_toward()` 后 task_4
覆盖率从 58.5% 提升到 87.1%。

### 2.4 泛化验证

- 变体 task_1 地图（挪宝箱、改墙型）：归纳程序与修正规划器均 211 步通关——
  无硬编码坐标；
- 感知在 3000 个独立布局上训练、在完全未见布局上 95.5% 全对——直面
  "最终测评可能变布局"的考察点。

---

## 3. 关键技术发现（问题 → 证据 → 解法）

1. **不可见门是环境事实**：渲染器把深渊画在门之后，深渊房的门像素不可见。
   解法三层：感知标签对齐可见性（不可见之物不标注）；穿房登记竞态根治
   （贴边对齐先于"推门"标志触发引擎传送 → 计划外跳变用「网格大换 ∨ 对侧边界
   落点」证据 + 最后移动方向登记）；行为层知识闭环（盲探针让引擎裁决门的存在
   → probed 记忆 → 危险覆盖方向驱动旋桥 → 强/弱 pending 分级路由 → 钥匙增加时
   重探——持钥匙推不可见锁门会被引擎直接放行）。
2. **经验程序一致性必要不充分**：回放覆盖 65% 的程序实跑死循环于"取钥匙后无
   回程逻辑"——回放喂的是专家控制下的状态流，掩盖闭环控制缺陷。live rollout
   验证 + 运行时反思恢复是必要补充。
3. **布局记忆 vs 真实读图**：150 张地图 × 多样本训练出的模型在未见布局上整格
   全对 0%（背布局）；3000 张 × 每张 3 样本 → 95.5%。
4. **取整观测下的边界歧义**：引擎分数像素坐标取整后，tile 归属在边界 ±0.5px
   内不可信 → 交互前"去歧义微调"（向 tile 内部挪 2px 再按 A）。
5. **不要从预测偏差推断墙体**（幽灵墙自增强循环）；撞墙检测交给 reward 反馈。
6. **贴身挥剑安全**：引擎先结算剑、命中即眩晕 60 tick、眩晕怪无接触伤害 →
   挥剑窗口可放宽到 gap∈[4,30]px，战斗步数减半以上。

---

## 4. Lean 形式化对接点（可证层）

以下组件为纯函数/确定性小步语义，可在 Lean 中建模并证明（详见
`nsi_agent/README.md`）：`SymbolicState` 谓词与走格图（合法移动不出界不进墙）、
`tracker` 转移函数、怪物不确定球安全护盾（护盾约束下不受接触伤害，最坏位移
0.5px/步可证界）、BFS planner（可靠性与完备性）、`graph.Interpreter` 与 DSL
表达式小步语义、归纳接受判据（覆盖单调引理）。神经网络（VLM/GPT-4o）本身不证，
证明覆盖其输出的符号层（schema 校验、action mask、护盾、轨迹一致性检查器）。

---

## 5. 复现命令

```bash
# 训练期
python -m nsi_agent.debug_run --episodes 3                  # Oracle 调试 5 关
python -m nsi_agent.grounding.dataset --out data/g --task-episodes 3 --unique-maps 3000
python -m nsi_agent.grounding.train_qlora --data data/g --model <Qwen2.5-VL-3B> --out ckpt/lora
python -m nsi_agent.grounding.eval_grounding --data data/g --split heldout --model <...> --adapter ckpt/lora/final
python -m nsi_agent.grounding.merge_lora --model <...> --adapter ckpt/lora/final --out models/merged
python -m nsi_agent.induction.record && python -m nsi_agent.induction.synthesize
python -m nsi_agent.induction.consolidate && python -m nsi_agent.induction.select

# 最终测评（提交形态）
export NSI_VLM_MODEL=<merged model dir> NSI_VLM_4BIT=0
python utils/evaluate_policy.py --policy submission_agent.py --num-envs 10
```

可视化成绩单：`report/nsi-results.html`（自包含单文件，浏览器直接打开，
支持明暗主题）。

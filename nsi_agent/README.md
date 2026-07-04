# NSI Agent — 神经符号技能归纳在 NesyLink 上的实现

本包将论文 **"Lifting Traces to Logic: Programmatic Skill Induction with
Neuro-Symbolic Learning for Long-Horizon Agentic Tasks" (NSI)** 的方法迁移到
数理逻辑大作业的 NesyLink 环境：技能 = (θ 调用参数, φ 神经感知 grounding,
G 符号执行图)，按 **Perceive → Think → Act** 循环执行；顶层任务程序由
GPT-4o 从演示轨迹**归纳**（Stage 1 逐轨迹合成 + Stage 2 贪心合并），接受判据
是确定性回放的**经验程序一致性**（max Σ|R̂| − λ|π|）。

## 论文概念 → 本实现

| NSI 概念 | 实现 | 文件 |
|---|---|---|
| φ 神经 grounding | Qwen2.5-VL-3B + QLoRA：帧 → 紧凑符号状态文本 | `grounding/vlm.py`, `grounding/schema.py` |
| 符号状态 Z | `SymbolicState`（10×8 网格 + 像素级实体）+ 跨房间记忆 | `grounding/schema.py`, `memory.py` |
| 执行图 G | DataOp/CheckOp/PrimitiveOp(SkillOp)/TerminalOp 图解释器 | `graph.py` |
| Perceive-Think-Act | 关键帧调用 VLM；帧间用形式化转移模型符号推演 | `tracker.py`, `agent.py` |
| 原语技能（≈PrimitiveOp） | goto / open_chest / kill_monster / press_button / toggle_switch / use_exit | `skills.py` |
| 技能归纳 Stage 1 | GPT-4o 逐轨迹合成局部专家，反例驱动精化 | `induction/synthesize.py` |
| 技能归纳 Stage 2 | 四算子（条件分支/模块移植/变量提升/循环折叠）贪心合并 | `induction/consolidate.py` |
| 经验程序一致性 | 确定性回放：程序动作 vs 专家动作，R̂ 覆盖 + 反例 | `induction/consistency.py` |
| 反思规划（在线演化） | 失败诊断 → GPT-4o 嫁接恢复分支 → 一致性+实跑双验证 | `induction/reflect.py` |
| 技能程序 DSL | JSON 图 + 受限表达式语言（ast 白名单沙箱求值） | `induction/dsl.py` |

## 关键帧 + 符号推演（为什么 3B 模型可行）

1 env.step = 1 像素移动，一局最多 2000 步——每步调用 VLM 不现实。本实现只在
**关键帧**（进房、交互后、战斗中每 ~6 步、平时每 ~24 步、异常时）调用 VLM；
帧间玩家位置用与引擎一致的形式化转移函数推演（1px/步 + AABB 钳制），怪物位置
放大为按 0.5px/步增长的**不确定球**，安全护盾保证不进入任何球。**撞墙由
reward 反馈检测**（作业允许 reward 作历史反馈：撞墙步含 invalid_action 惩罚，
与正常步可区分），预测 1 步内回滚。

## 测评合规性

推理路径仅使用：`obs`（像素帧 → VLM）、`info["inventory"]`（测评接口显式提供）、
`info["reward"]`（reward 值反馈）、`reset(task_id)`（接口显式传入，仅影响探索
方向偏好）。**不读取** agent 坐标、地图真值、实体位置等 `info` 内部状态。
Oracle 后端（`grounding/oracle.py`）只用于训练期标注/录制/调试，`make_policy()`
不会实例化它。归纳产物是冻结的本地 JSON（`induction/artifacts/`），**测评时
不调用任何外部 API**。

## Lean 可证层（形式化对接点）

以下组件是纯函数/确定性小步语义，适合在 Lean 中建模并证明：

- `SymbolicState` 与谓词（`is_blocking`/`is_hazard`/走格图）→ 状态/对象/目标谓词；
- `tracker._predict_move` 的转移函数 → 「合法移动不出界、不进墙」不变量；
- 怪物不确定球 + `px_is_safe` 护盾 → 「护盾约束下不受接触伤害」安全性定理
  （怪速 0.5px/步给出可证的最坏位移界）；
- `skills.bfs_path` → 规划器可靠性（输出路径均可走）与完备性（存在路径必找到）；
- `graph.Interpreter` + `induction/dsl.py` 表达式语义 → DSL 程序小步语义，
  「解释器每步至多产出一个合法动作」「terminal 可达性」等；
- 归纳接受判据（覆盖单调 + MDL）→ 合并不破坏已覆盖轨迹的引理。

若使用神经网络（VLM/GPT-4o），Lean 不证网络本身，证明覆盖其输出的符号层
（schema 校验、action mask、护盾、规划器、轨迹一致性检查器）。

## 复现命令

```bash
# 0) 符号层调试（Oracle 后端，训练期）
python -m nsi_agent.debug_run --episodes 3            # 5 关 × 3 seeds

# 1) VLM grounding（云端 GPU）
python -m nsi_agent.grounding.dataset --out data/grounding \
    --task-episodes 3 --variant-maps 60 --walk-steps 700
python -m nsi_agent.grounding.train_qlora --data data/grounding \
    --model <Qwen2.5-VL-3B-Instruct> --out ckpt/grounding_lora --epochs 2
python -m nsi_agent.grounding.eval_grounding --data data/grounding \
    --split heldout --model <...> --adapter ckpt/grounding_lora/final

# 2) NSI 归纳（GPT-4o，需 ~/.config/nsi_agent/openai.env）
python -m nsi_agent.induction.record                  # 录制演示轨迹
python -m nsi_agent.induction.synthesize              # Stage 1
python -m nsi_agent.induction.consolidate             # Stage 2
python -m nsi_agent.induction.reflect --task mathematical_logic/task_4

# 3) 最终测评（VLM 后端 + 冻结归纳工件）
export NSI_VLM_MODEL=<model dir> NSI_VLM_ADAPTER=<adapter dir>
python utils/evaluate_policy.py --policy submission_agent.py \
    --tasks mathematical_logic/task_1 ... --num-envs 10
```

## 结果（随开发更新）

- **Oracle 后端（符号层上界）**：5/5 任务成功率 100%（seeds 0-2）；
  步数 task_1 279 / task_2 197 / task_3 582 / task_4 1229 / task_5 1136。
- **NSI 归纳（GPT-4o Stage 1）**：局部专家轨迹一致性覆盖
  task_1 99.6% / task_2 92.9% / task_3 71.3% / task_4 87.1% / task_5 59.3%
  （`hop_toward` 跨房路由查询加入 DSL 后 task_4 从 58.5%→87.1%）。
- **Stage 2 合并**：task_2 的局部专家即为最优全局程序——对全部 5 条演示轨迹
  覆盖 [99.6%, 92.9%, 98.3%, 91.4%, 90.2%]（统一程序覆盖多关卡）。
- **实跑甄选（selection.json）**：task_1–4 归纳程序 live 通关 ✓；task_5 因隐藏
  扣血机制预算极紧（后备也仅 ~60 步余量），甄选采用修正规划器。
- **泛化**：变体 task_1 地图（挪宝箱/改墙型）归纳程序与后备均 211 步通关，
  无硬编码坐标。
- **方法学发现**（报告素材）：经验程序一致性（回放）对闭环控制缺陷不敏感
  ——task_3 程序回放覆盖 65% 却在实跑中卡死于"取钥匙后无回程逻辑"；
  live rollout 验证 + 运行时反思恢复（活锁检测→修正规划器接管）是必要补充。
- **VLM grounding（Qwen2.5-VL-3B QLoRA）**：
  - 零样本基线：网格 tile 76%，整体 0%（微调必要）；
  - v2（掩码修复 + 3.5× patch-tile 精确对齐 + 150 变体地图）：
    **官方任务地图全指标 100%**（120 样本，0 解析失败）；held-out 变体地图
    网格 82.4%、实体/出口/朝向 100%（网格短板 = 布局记忆）；
  - **v3（3000 个单次使用布局 + 1503 深渊房样本，train_loss 0.125）**：
    held-out 未见布局 **解析失败 0/200、网格 tile 99.88%、整格全对 95.5%、
    all_ok 95.5%**，实体/出口/朝向保持 100% —— 布局记忆根除，模型在
    完全未见的地图上真实读图。
- **端到端评测（最终，`evaluate_policy.py --policy submission_agent.py`）：
  5/5 关全部成功率 100%** ——
  - task_1 ✅ **279 步 = Oracle 最优**；task_2 ✅ **195 步（反超上界 197）**；
  - task_3 ✅ 1449 步；task_4 ✅ **1483 步**；task_5 ✅ **1137 步（≈上界 1136）**。
- **不可见门的系统性处理**（task_4 攻克的关键，报告重点素材）：
  1. 环境事实：渲染器把深渊画在门之后 → 深渊房的门**像素不可见**；
  2. 感知标签对齐像素真相（被覆盖的门标 `-`，不可见之物不该标注）；
  3. 穿房登记竞态根治：贴边对齐会先于 UseExit 的标志位触发引擎传送——
     计划外跳变用「网格大换∨对侧边界落点」证据 + 最后移动方向登记；
  4. 行为层知识闭环：盲探针（推一下让引擎裁决门的存在）→ probed 记忆 →
     危险覆盖方向驱动旋桥 → 强/弱 pending 分级路由 → 钥匙增加时重探锁门
     （持钥匙推不可见锁门会被引擎直接放行）。
- **鲁棒性**：推理路径异常免疫——感知解析失败退避重试（不炸测评器）、
  规划器异常兜底 WAIT、均匀行缩写智能补全、活锁检测→修正规划器接管。

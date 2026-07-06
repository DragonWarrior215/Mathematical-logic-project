# Agent 测试报告 v2（提交形态 + 泛化 + 技能进化）

日期：2026-07-06。代码版本：`0f659e9`（task5 阶段机、回血收敛、key 来源记录、保守全局评分器）。
模型：`grounding_merged_v3b`（AutoDL 4090，`/root/autodl-tmp/models/`）。
本轮测试全部在云端服务器完成；技能进化经 GPT-4o（yunwu.ai 中转）。

## 一、提交形态 5 任务评测（VLM grounding）

`python utils/evaluate_policy.py --policy submission_agent.py --num-envs 3`

| 任务 | 成功率 | 步数 | 奖励 | 与上一版(07-04)对比 |
|---|---:|---:|---:|---|
| task_1 | 3/3 | 279 | 127.16 | 持平（279） |
| task_2 | 3/3 | 193 | 128.02 | 略优（195） |
| task_3 | 3/3 | 668 | 199.32 | **大幅提速**（1449→668） |
| task_4 | 3/3 | 1911 | 338.79 | 变慢（1483→1911，见"已知问题"） |
| task_5 | 3/3 | 1134 | 187.31 | 略快（1137→1134），**首次由诱导 DSL 程序完成** |

**合计 15/15。** 种子扫描（oracle，4 种子 × 5 任务，20/20）确认环境对 seed 完全确定，
各种子步数逐位一致——多种子不提供额外方差信息。

## 二、泛化测试

### 2.1 Oracle 符号层（18 变体，`test_script.py`）

| Planner | 成功率 | task_5 变体 |
|---|---:|---:|
| fallback（新阶段机） | 15/18 (83.3%) | 3/6 |
| selected（进化前=fallback） | 15/18 (83.3%) | 3/6 |
| selected（进化后=诱导程序） | — | 1/6 |

- 对比上一版报告（task_5 变体 33.3%）：新阶段机 planner 把 fallback 提升到 50%。
- 三个共同失败变体全是 **key 移到西房** 的拓扑（key_in_west / key_west_center_detour /
  west_key_decoy_chests），终态均为 agent_dead：`planner.py` 中硬编码的
  key 房 `(0,1)`、回血房 `(1,0)` 假设被打破后，阶段机误判进入错误阶段。
- 诱导程序基础图更好（奖励 187 vs 174）但变体鲁棒性更差（layout_shift、east_heal_far
  在诱导程序下也失败）。

### 2.2 VLM 像素级（18 变体，`vlm_variant_eval.py`，本轮新增）

上一版报告因本地无 GPU 未做像素级泛化，本轮在 4090 上补齐：**12/18 (66.7%)**。

| 任务组 | 结果 | 结论 |
|---|---|---|
| task_1–3 全部变体 | **9/9 通过** | 感知层泛化不是瓶颈，与 oracle 完全一致 |
| task_4 | 2/3 | object_shift 在 2000 步上限截断（oracle 1375 步通过）：感知噪声叠加 planner 变慢导致超时 |
| task_5 | 1/6 | 与 oracle+诱导程序结果逐变体一致 → 失败源于符号层策略而非视觉 |

## 三、技能进化（GPT-4o 归纳管线）

流程与结果：

1. **重录轨迹**：新 planner 下 task_5 演示 1069 步（旧 1137）。
2. **Stage 1 合成**：局部专家覆盖率 0.658（第 0 轮遇中转截断自动重试）。
3. **Stage 2 合并**：与最难轨迹合并 3 轮均回归、按规则拒绝;但全局程序在新 task_5
   轨迹上覆盖率达 **0.972**。
4. **实测选择（select）**：task_5 局部专家实测 agent_dead → 全局程序实测
   world_completed → **task_5 首次从 fallback 切换到诱导程序**。现 5/5 任务
   全部运行诱导 DSL（`selection.json`）。
5. **反思进化（reflect）**：为支持变体驱动进化，`reflect.py` 新增 `--map-path`
   （接受条件：变体实测通过 + 基础图不回归 + 轨迹一致性下降 <25）。
   对 key_in_west、layout_shift 各尝试 3 轮 GPT-4o 补丁：一致性均保持
   （~3184/3187）但实测全部 agent_dead——**负结果**：现有贪心图 DSL 缺少
   表达"阶段依赖的资源管理"（HP 预算、key 优先级随拓扑变化）的原语。

## 四、已知问题与建议

1. **west-key 拓扑缺口**（fallback 与诱导程序均失败）：`planner.py` 的
   `task5_key_source_room != (0,1)` 与 `_heal_has_been_collected` 的 `(1,0)`
   硬编码需改为按房间内容（TILE_CHEST_HEAL/KEY）动态识别。
2. **task_4 步数膨胀**（1483→1911）：planner 重构把 `_locked_exit_goal`
   提到箱子之前对所有任务生效,task_4 绕路增多。距上限 2000 仅 89 步余量,
   VLM 变体 object_shift 已因此截断——建议将该优先级调整限定在 task_5。
3. **DSL 表达力**：若要诱导程序覆盖 task_5 变体,需给 DSL 增加阶段/资源
   原语（如 `hp_estimate`、`phase` 状态变量),再重跑归纳。
4. 若评分包含扰动地图,可将 `selection.json` 的 task_5 回退为 fallback
   （变体 3/6 vs 1/6);基础 5 任务两种配置都 15/15。

## 五、后续修复(2026-07-07 增补)

### 5.1 west-key 缺口修复

- **HP 记账**:`note_damage`/`note_heal` 原为死代码,hp_estimate 只记 200 步 tick;
  现接入 reward 信号 `hp_loss`/`agent_healed`(均有非零权重,合规先例同撞墙检测)。
- **去硬编码**:key 房 `(0,1)`、回血房 `(1,0)`、NEED_KEY 的 `(0,0)` 豁免全部移除,
  改为事件计数 / 全局评分 / 全房间价值过滤;新增"顺路开箱"(绕行 ≤4 格)。
- **战果**:west-key 变体 0/3→1/3(key_west_center_detour 1196 通过);
  key_in_west 从"未解锁死于 800"推进到"解锁+回血+3/4 箱,死于最后一箱"。
  剩余 3 个失败经逐段核算证明处于 1200 硬预算墙(5HP+1heal × 200 步/tick;
  执行层空转仅 14/1200 步),在"箱内容进房前不可见"约束下 south-first 与
  west-first 对称不可兼得,属环境设计的信息不可能性,非代码缺陷。
- **selection 调整**:task_5 由诱导程序改回 fallback(基础 1118<1134,变体 3/6>1/6)。

### 5.2 task_4 步数膨胀根治(1911→1581)

- **根因链**:诱导 DSL 程序 339 步 livelock(`toggle_nearest_switch`)→
  FallbackPlanner 恢复模式跑完 82% 回合;VLM 将**已开的门持续误读**为
  locked/conditional → 幻影"连通性错误"→ 拨杆乒乓循环(每圈 ~250 步 × 4+)。
- **修复**:`RoomMemory.opened_exits` 行为对账——锁门 use_exit 成功即引擎权威
  确认,此后锁门/条件门目标、pending 判定、评分路径全部跳过该方向
  (行为反馈 > 像素感知)。
- **验证**:VLM 1911→**1581**(距 2000 上限余量 89→419);oracle 代价 +160
  (1321→1481:旧高效路径依赖已开门的假 locked-pending 作回头诱饵,
  修复将该隐藏耦合显式化);纯 fallback task_4 VLM=2000 截断失败,
  证明"诱导开局+fallback 收尾"混合为最优配置,不宜翻转 selection。
- **方法论记录**:此前 5 轮失败尝试(hint 方向序恢复、失败计数、拨杆签名预算)
  均为对单条确定性轨迹的阈值调参,已全部撤销;正确流程 = 桌面推演 goal_log
  确认绑定 → 最便宜 A/B 排除路线 → 机制修复 + oracle 回归 + VLM 实测。

### 5.3 最终交付数字(v3b,提交形态)

| 任务 | 成功 | 步数 | 对比 07-06 |
|---|---|---:|---|
| task_1 | ✅ | 279 | 持平 |
| task_2 | ✅ | 193 | 持平 |
| task_3 | ✅ | 668 | 持平 |
| task_4 | ✅ | **1581** | 1911→1581 |
| task_5 | ✅ | 1118 | 1134→1118(fallback) |

task_5 六变体(oracle):3/6,与修复前构成持平且 west-key 首次有通过项。

## 六、产物位置

- 服务器：`/root/nesylink/outputs/`（eval_5task_v3b.json、generalization_eval[.v2]、
  generalization_vlm、seed_sweep.log、synthesize/consolidate/reflect 日志）
- 本地仓库已同步：新 task_5 轨迹、`local_/mathematical_logic_task_5.json`、
  `global_program.json`、`selection.json`、`reflect.py`（--map-path）、
  `vlm_variant_eval.py`（新增）、`test_script.py`（服务器路径修复）

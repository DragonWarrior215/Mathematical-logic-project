# Agent 泛化测试报告（Oracle）

## 一、测试目的


- 如果 oracle 下失败，说明问题在规划、技能、记忆或任务逻辑。
- 如果 oracle 下成功但 VLM 下失败，说明问题更可能在视觉 grounding。

本次测试的目标是：在不修改 agent 的前提下，通过改变地图布局、对象位置和房间拓扑，检查当前 agent 是否具有较强泛化能力。

## 二、测试方式

测试脚本：

`generalization_eval.py`


## 三、泛化修改类型

本次一共构造了 15 个泛化地图变体，覆盖 5 个任务。修改分为三类：

| 类型 | 含义 |
|---|---|
| `object_shift` | 移动物体位置，例如 key、chest、monster、switch、button |
| `layout_shift` | 修改房间内部地形，例如增加墙、改变绕路结构 |
| `topology_shift` | 修改房间/出口/任务链路结构，例如改变出口方向或 key 所在房间 |

这些修改都保留了原任务核心逻辑。例如 task1 仍然是 key-door，task2 仍然是 kill+key，task5 仍然是多房间综合任务。

## 四、总体结果

| Planner | 测试数量 | 成功率 | 平均步数 | 平均奖励 |
|---|---:|---:|---:|---:|
| selected | 15 | 86.7% | 781.5 | 156.05 |
| fallback | 15 | 86.7% | 744.9 | 154.01 |

结论：当前 agent 在 oracle 条件下有一定泛化能力，但不是强泛化。主要短板集中在 task5。

## 五、按任务统计

| 任务 | selected 成功率 | fallback 成功率 | 结论 |
|---|---:|---:|---|
| task1 | 100% | 100% | 稳定，通过 key/chest/door 位置变化 |
| task2 | 100% | 100% | 稳定，通过 monster/key/exit 变化 |
| task3 | 100% | 100% | 能通过，但 selected 在部分变体步数偏高 |
| task4 | 100% | 100% | 能通过，但平均步数很高 |
| task5 | 33.3% | 33.3% | 明显不稳定，是当前主要问题 |

## 六、按修改类型统计

| Planner / 类型 | 测试数量 | 成功率 | 平均步数 | 平均奖励 |
|---|---:|---:|---:|---:|
| selected: object_shift | 6 | 100% | 859.5 | 184.17 |
| selected: layout_shift | 5 | 80% | 854.2 | 143.19 |
| selected: topology_shift | 4 | 75% | 573.5 | 129.93 |
| fallback: object_shift | 6 | 100% | 833.0 | 181.44 |
| fallback: layout_shift | 5 | 80% | 777.4 | 140.36 |
| fallback: topology_shift | 4 | 75% | 572.2 | 129.93 |

结论：简单移动物体位置时表现最好；一旦涉及房间拓扑变化或复杂布局变化，成功率下降。

## 七、具体变体结果

| 变体 | 任务 | 类型 | selected 结果 | selected 步数 | 终止原因 |
|---|---|---|---|---:|---|
| task1_key_east | task1 | object_shift | 成功 | 259 | world_completed |
| task1_south_exit | task1 | topology_shift | 成功 | 387 | world_completed |
| task1_mirrored_room | task1 | layout_shift | 成功 | 279 | world_completed |
| task2_monster_far | task2 | object_shift | 成功 | 168 | world_completed |
| task2_east_exit | task2 | topology_shift | 成功 | 134 | world_completed |
| task2_wall_detour | task2 | layout_shift | 成功 | 272 | world_completed |
| task3_key_shift | task3 | object_shift | 成功 | 737 | world_completed |
| task3_hall_detour | task3 | layout_shift | 成功 | 1095 | world_completed |
| task3_east_key_chain | task3 | topology_shift | 成功 | 773 | world_completed |
| task4_object_shift | task4 | object_shift | 成功 | 1375 | world_completed |
| task4_switch_shift | task4 | layout_shift | 成功 | 1425 | world_completed |
| task4_final_chest_shift | task4 | object_shift | 成功 | 1499 | world_completed |
| task5_object_shift | task5 | object_shift | 成功 | 1119 | world_completed |
| task5_layout_shift | task5 | layout_shift | 失败 | 1200 | agent_dead |
| task5_key_in_west | task5 | topology_shift | 失败 | 1000 | agent_dead |

## 八、主要失败案例

### 1. `task5_layout_shift`

修改内容：改变中心房间的墙体布局，但保留原有出口。

结果：

- 成功：否
- 步数：1200
- 终止原因：`agent_dead`
- reward：38.85

关键事件：

- `key_collected: 1`
- `door_opened: 1`
- `chest_opened: 3`
- `monster_killed: 1`
- `room_changed: 4`
- `agent_dead: 1`

分析：agent 并不是完全不会完成子目标，它已经拿到 key、开门、开箱、击杀怪物，但在修改后的中心布局中，后续路线和任务顺序效率太低，最终死亡。这说明 task5 的 planner 对复杂地形变化不够稳。

### 2. `task5_key_in_west`

修改内容：把 key reward 从南边房间 chest 移到西边房间 chest。

结果：

- 成功：否
- 步数：1000
- 终止原因：`agent_dead`
- reward：84.85

关键事件：

- `key_collected: 1`
- `door_opened: 1`
- `chest_opened: 3`
- `monster_killed: 3`
- `room_changed: 7`
- `agent_dead: 1`

分析：这个失败更说明问题不在“拿不到 key”。agent 实际上已经拿到 key，也杀了多个怪物，但没有及时完成最终目标，说明 task5 的目标切换、完成条件判断和路线规划存在问题。

## 九、指标总结

当前最需要关注的指标：

| 指标 | 当前状态 | 问题 |
|---|---|---|
| 原始任务通过率 | oracle 下 5/5 | 原始任务没有明显问题 |
| 泛化总成功率 | 86.7% | 尚未达到强泛化 |
| task5 泛化成功率 | 33.3% | 最大短板 |
| object_shift 成功率 | 100% | 单纯物体移动泛化较好 |
| layout_shift 成功率 | 80% | 复杂地形变化仍有风险 |
| topology_shift 成功率 | 75% | 房间/出口/任务链变化较弱 |
| 死亡次数 | selected 和 fallback 各 2 次 | task5 缺少 health-aware planning |
| task4/task5 平均步数 | 偏高 | 路径效率和目标顺序仍可优化 |

## 十、结论

当前 agent 在 oracle 条件下能通过原始五关，也能通过大部分简单泛化变体，说明基础 planner 和 skills 是有效的。

但它还不能算强泛化，主要问题是：

1. task5 对复杂布局变化和 key 所在房间变化不稳定。
2. agent 会完成一些子目标，但不能稳定把子目标串成最终成功路径。
3. 在长任务中没有足够强的生命值/风险意识，容易拖到死亡。
4. selected planner 在部分任务中比 fallback 步数更多，说明当前策略选择机制还有优化空间。


# lean

## 1. 总体定位

本项目更适合走“神经感知 + 可验证符号层”的路线，而不是试图在 Lean 中证明整个神经网络对所有像素输入都正确。

也就是说：

- `obs -> SymbolicState` 由 VLM grounding 提供；
- Lean 从 `SymbolicState` 开始，形式化并证明其后的 planner / 搜索 / action mask / safety shield / 任务完成判定；
- 我们证明的是一个条件命题：
  只要 grounding 输出满足验证层的接口假设，那么经过该可验证层约束后的行为满足相应安全性与正确性规范。

这个定位与作业要求一致：

- 机器学习策略不要求证明网络本身；
- 但必须明确 Lean 覆盖的可验证层；
- 并说明模型输出与可验证层之间的关系。

---

## 2. 符号层输入

给 agent 提供的符号状态来自 [nsi_agent/grounding/schema.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/grounding/schema.py:91)：

```python
grid: tuple[str, ...]             # GRID_H strings of GRID_W chars
player_px: tuple[int, int]        # top-left pixel position
facing: str                       # one of FACINGS
monsters: tuple[Monster, ...] = ()
exits: dict[str, str] = field(default_factory=dict)  # dir -> exit state
```

例子：

```text
SymbolicState(
    grid=(
        "##########",
        "#........#",
        "#..K.....#",
        "#....b...#",
        "#........#",
        "#....T...#",
        "#........#",
        "##########",
    ),
    player_px=(64, 96),
    facing="up",
    monsters=(
        Monster(kind="chaser", px=(32, 32)),
    ),
    exits={
        "north": "-",
        "south": "normal",
        "west": "locked",
        "east": "-",
    },
)
```

其中 `grid` 中的重要 tile 类型包括：

- `.` 地板
- `#` 墙
- `K/G/H/S/C/O` 各种宝箱
- `T` 陷阱
- `A` 深渊
- `_` 缺口
- `=` 桥
- `b/B` 按钮
- `L/l` 开关
- `N` NPC

Lean 中真正证明的是：在该符号状态语义正确的前提下，后续规划与执行层满足规范。

---

## 3. 决策链条

整体决策链是：

`obs -> grounding -> SymbolicState -> planner 选 goal -> skill 产出动作 -> shield 过滤危险动作 -> tracker 预测下一状态`

对应代码位置：

- `Policy.act`：[nsi_agent/agent.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/agent.py:89)
- `FallbackPlanner.step`：[nsi_agent/planner.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/planner.py:101)
- `bfs_path` / `shielded` / skills：[nsi_agent/skills.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/skills.py:80)
- `Tracker`：[nsi_agent/tracker.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/tracker.py:45)
- `Memory`：[nsi_agent/memory.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/memory.py:70)

这个结构意味着：最适合用 Lean 覆盖的是从 `SymbolicState` 开始的“符号决策与安全约束层”。

---

## 4. Planner 与 Skill 结构

### 4.1 `planner`

主循环位于 [nsi_agent/planner.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/planner.py:101)：

- 若当前没有 goal，则 `_choose_goal(ctx)`；
- 根据 goal 构造一个 skill；
- 调用 skill 的 `step(ctx)`；
- skill 返回三类结果：
  - `("act", action)`：本次输出一个环境动作，skill 继续保留；
  - `("ok", detail)`：skill 成功结束；
  - `("fail", diagnosis)`：skill 失败结束。

goal 选择优先级位于 [nsi_agent/planner.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/planner.py:197)：

1. 没剑且怪近，先逃跑
2. 有剑且怪需要打，就打怪
3. 开最近可达宝箱
4. 有钥匙则尝试 locked exit
5. 按按钮
6. 尝试 conditional exit
7. 若目标不可达，则去找 switch 改变连通性
8. 去其他仍有待办事项的房间
9. 探测可能漏识别的门
10. 否则 wait

### 4.2 `skill`

已注册 skill 如下：

```python
SKILL_REGISTRY = {
    "goto": GoToTile,
    "open_chest": OpenChest,
    "press_button": PressButton,
    "toggle_switch": ToggleSwitch,
    "use_exit": UseExit,
    "kill_monster": KillMonster,
    "wait": Wait,
}
```

这些 skill 都是“temporally extended actions”：

- 一次 `Policy.act()` 只会输出一个环境动作；
- 但 planner 会保留当前 skill 对象；
- 因而同一个 skill 可以跨很多次 `act()` 持续执行，直到返回 `ok/fail`。

---

## 5. 应证明什么，不应证明什么

## 5.1 适合证明的内容

### A. 符号环境语义

对应 [lean/NesyFormalization/Core.lean](/home/lyh/Mathematical-logic-project-main/lean/NesyFormalization/Core.lean:1)。

可证明：

- `walkable` 的定义正确；
- `SafeState` 等安全谓词；
- `Step` 的各构造子对应合法移动、开箱、攻击、过门；
- 若一步动作满足某前置条件，则后置状态满足预期性质。

### B. 搜索与可达性

对应 [lean/NesyFormalization/Reachability.lean](/home/lyh/Mathematical-logic-project-main/lean/NesyFormalization/Reachability.lean:1) 和 [nsi_agent/skills.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/skills.py:80)。

可证明：

- 路径定义；
- 可达性定义；
- BFS soundness：
  若 `bfs_path` 返回一条路径，则该路径合法、相邻、且每步都 walkable；
- 进一步可补 BFS completeness：
  若存在合法路径，则 BFS 能找到路径。

### C. Action mask / safety shield

对应 [nsi_agent/skills.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/skills.py:52) 和 [nsi_agent/skills.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/skills.py:148)。

可证明：

- `walkable` 会排除 wall / chest / gap / hazard；
- BFS 仅在 `walkable` tile 上规划；
- 若某 move 被 `shielded` 放行，则其下一预测位置满足安全条件；
- 若某 move 会进入 monster danger region，则 `shielded` 不会原样放行该 move。

### D. Skill 的局部正确性

对应 [nsi_agent/skills.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/skills.py:189) 之后的各 skill。

可证明：

- `GoToTile.ok` 时，玩家到达目标 tile 或相邻 tile；
- `OpenChest.ok` 时，目标宝箱已经打开；
- `UseExit.ok` 时，发生合法过门；
- `ToggleSwitch.ok` 时，开关切换成功；
- 每个 skill 都有明确的 `ok/fail/timeout` 退出方式，不会无限卡死。

### E. 任务完成判定

对应 task-specific Lean 文件，如 [Task1.lean](/home/lyh/Mathematical-logic-project-main/lean/NesyFormalization/Task1.lean:1)。

可证明：

- 任务目标谓词定义正确；
- 当某终点出口成功通过时，确实满足 task goal；
- 对简单任务可给出完整参考策略证明；
- 对更复杂任务至少可证明完成判定与局部目标。

## 5.2 不适合直接证明的内容

以下命题过强，或者不符合当前项目边界：

- VLM 对所有像素输入都识别正确；
- `uncertainty_px` 单独保证永远不会被怪物碰到；
- “每个 skill 总是成功”；
- “所有任务在任意情况下都一定能完成”；
- Python 运行时实现与 Lean 模型逐字节等价。

这些应改写为“接口假设 + 在该假设下的正确性保证”。

---

## 6. 关于 `uncertainty_px` 的正确表述

`uncertainty_px` 位于 [nsi_agent/tracker.py](/home/lyh/Mathematical-logic-project-main/nsi_agent/tracker.py:36) 之后的 `TrackedMonster` / `Tracker` 机制中。

这里不应直接证明：

- “存在 uncertainty_px 机制，所以一定规避怪物碰撞”

更合适的命题是：

1. `uncertainty_px` 会随着未同步步数增长，因此 danger region 是保守扩张的。
2. 若怪物真实位置始终落在 tracker 的 uncertainty 包络内，则：
   - 任何被 `shielded` 放行的 move 都不会进入该 danger region；
   - 因而不会与该包络下的怪物发生接触。

因此，这一层证明的是“保守安全性”，而不是“怪物建模绝对正确”。

---

## 7. 关于 Skill 的正确表述

不建议直接证明：

- “每个 skill 都可行”

因为现实中存在：

- 目标不可达；
- 被怪物暂时封锁；
- 感知出错；
- 隐藏门尚未探测到；
- 超时退出。

因此更合理的证明目标是：

1. 若 skill 返回 `ok`，则满足相应后置条件；
2. 若前置条件满足且目标可达，则 skill 不会产生非法动作；
3. 若目标不可达或长期受阻，则 skill 会 `fail` 或 timeout，而不是无限卡死；
4. skill 本身可能提出危险 move，但真正交给环境的动作仍会经过 `shielded`。

这比“skill 必成功”更准确，也更符合源码实现。

---

## 8. 关于 Shield 的核心命题

`shielded` 是最值得重点证明的一层。

建议在 Lean 中对应以下命题：

1. `shield_sound`
   若某 move 被 `shielded` 放行，则下一预测位置满足安全条件。
2. `shield_blocks_dangerous_move`
   若某 move 会进入 monster danger region，则 `shielded` 不会原样放行该 move。
3. `shield_safe_fallback`
   当 move 不安全时，`shielded` 返回的是安全 fallback（如 `NOOP` 或 `ACTION_B`），而不是危险移动。

这组命题正好对应作业要求中的“输出合法、安全”。

---

## 9. 关于“每个任务都可以完成”的正确表述

这句话太强，不建议直接作为证明目标。

更稳妥的层次是：

### 第一层：完成判定正确

- 当 task goal 满足时，形式化判定能识别它；
- 当终点出口成功通过时，任务完成位被正确置真。

### 第二层：存在可行参考策略

- 对简单任务，如 task 1，证明存在一条合法路径 / 策略使任务完成；
- 对更复杂任务，可给出可解性示例，而不要求证明整个 planner 全局完备。

### 第三层：若 skill / planner 成功执行，则满足任务目标

- 即“成功时正确”，而不是“必定成功”。

---

## 10. 当前推荐的证明路线

按优先级，建议分三步推进：

### 第一步：先做最稳的公共层

- `Core.lean`：状态、动作、一步语义、安全谓词
- `Reachability.lean`：路径、可达性、BFS soundness

### 第二步：补安全约束层

- 新增 `Shield.lean`
- 形式化 monster danger region、safe move、shield correctness

### 第三步：补 skill 与 task

- 新增 `Skills.lean`
- 证明 `GoToTile` / `OpenChest` / `UseExit` 的局部正确性
- `Task1.lean` 先做一个完整任务级案例

---

## 11. 最终可向报告中表达的核心结论

本项目不试图在 Lean 中证明神经网络 grounding 对所有像素输入都正确。

相反，我们将 grounding 视为：

`obs -> SymbolicState`

的输入接口，并对其后的符号约束层进行形式化验证。具体证明内容包括：

- 搜索过程返回路径的合法性；
- action mask 与 shield 的安全性；
- 各 skill 成功时的后置条件；
- 任务完成谓词与终点判定的正确性。

因此我们得到的结论是：

> 若 grounding 输出满足验证层的接口假设，则经过 Lean 覆盖的 planner / BFS / shield / skill / task predicate 约束后的行为满足相应的合法性、安全性与成功时正确性规范。

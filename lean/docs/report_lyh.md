# Lean 形式化证明部分实验报告

## 1. EnvFormalization.lean 建模基础环境

### 代码整体结构

- `32-239`：基础环境定义部分
- `240-289`：简单辅助函数
- `291-480`：WellFormed 房间的相关定义
- `482-978`：玩家与环境交互部分定义
- `981-1087`：给出环境语义上的部分基础性质定理

### 对 Python 环境的近似处理

#### 1. 像素级格子转变为抽象格子

Python 里的怪物位置其实更精细，是“像素级”的，而且怪物本身有一个 `16×16` 的碰撞箱；但 Lean 里为了证明方便，不记录这些连续/像素细节，只把怪物看成站在某一个 tile 格子上。

例如在 Python 中怪物的坐标可能是：

```python
monster.position_px = (32.0, 48.0)
monster.size_px = 16
```

这表示怪物左上角在像素 `(32, 48)`，身体占一个 `16×16` 的矩形。判断撞到玩家时，Python 会看玩家矩形和怪物矩形有没有重叠，也就是 AABB collision。

而我们在 Lean 中的实现转换为：

```lean
pos := (2, 3)
```

此处的 `(2, 3)` 表示格子坐标，而不是像素坐标。因为每格是 $16 \times 16$ 像素，所有 Python 的 `(32, 48)` 大致对应的就是 Lean 中的 `(2, 3)`.

---

## 2. NsiAgentFormalization.lean 建模智能体

为了在 Lean 中证明 `nsi_agent` 的安全性、可达性和任务执行性质，我们在 `NsiAgentFormalization.lean` 中实现了一个 tile 层抽象版的 `nsi_agent`。抽取并形式化智能体证明中较为关键的算法原理和运行逻辑，作为后续定理证明的基础语义层。

该文件主要建模了以下内容：

- **怪物危险区域与 tracker 表示**：定义 `TrackedMonster`、不确定半径、Chebyshev 距离、危险区域和 `positionSafe` 等概念，用于描述智能体如何保守估计怪物威胁。
- **BFS 寻路机制**：实现四邻接网格搜索、可走格判断、BFS 队列节点、路径扩展和 `bfsPath`，对应 `nsi_agent` 中的 tile-level 路径规划。
- **`GoTo` 技能运行骨架**：给定目标格或目标邻接格，先通过 BFS 规划路径，再选取下一 waypoint，并将其转化为移动动作。
- **智能体 memory 框架**：建模 learned-blocked、已开启宝箱、已按按钮、已访问出口、背包信息和步数等核心记忆状态，用于表达智能体对环境的持续认知。
- **tracker 同步与死推演逻辑**：建模关键帧同步、怪物不确定性重置、帧间不确定性增长、感知请求和 grounding backoff 等机制。
- **reward feedback 修正机制**：当 invalid-action 反馈表明上一移动撞墙时，回退预测位置，并可将相关 waypoint 记录为 learned-blocked。
- **safety shield 逻辑**：在动作发出前检查目标格是否处于怪物危险区域中；若不安全，则将移动动作替换为 `wait` 或 `shieldB`。

因此，后续的 BFS、怪物危险、shield、GoTo、组合执行和任务完成等定理，都可以以 `EnvFormalization.lean` 提供的环境语义和 `NsiAgentFormalization.lean` 提供的智能体运行语义作为底层框架来展开证明。

## 0. 改进点

1. 在 `EnvFormalization.lean` 中的 291 行是硬编码的地图边界。
   - 跟 339 的 `entrySpawnCandidates` 也会有关联
   - 感觉可能还是硬编码地图大小比较好，后续部分证明也依赖了这个假设。
2. 在 `EnvFormalization.lean` 中的 1089 行到 1242 行 的测试样例也许没必要保留
3. `TaskCompletion.lean` 还没有严格证明
4. 目前缺少将 `nsi_agent` 的真实运作代码迁移到 `lean` 上，极大多数都是伪证。感觉需要将 `nsi_agent` 的核心机制也在 `lean` 中定义出来，才能严谨地证明
   - 已完成
5. lean 文件中很可能存在 大量的 “接口定理”，需要变成闭合证明。




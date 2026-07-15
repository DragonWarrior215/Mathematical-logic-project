  ## 一、符合项目的主要内容

  以下描述都能和当前代码对应：

  - task 1–4 使用 local DSL，task 5 使用 FallbackPlanner，与 nsi_agent/induction/artifacts/
    selection.json 完全一致。

  - DSL 工件节点数量准确：
      - task 1：8 节点
      - task 2：7 节点、1 个 guard
      - task 3：13 节点、1 个 guard
      - task 4：14 节点

  - 五条轨迹长度 279/197/582/1229/1069 与实际 JSON 一致。
  - 七个技能确实是：
    goto/open_chest/press_button/toggle_switch/use_exit/kill_monster/wait。

  - Tracker 的参数准确：
      - 普通感知间隔 24 步
      - 危险状态 8 步
      - 怪物不确定性每步扩大 0.5px
      - 玩家移动每步 1px

  - DSL 解释器确实有每步最多 256 次内部转移的限制。
  - MAX_RECOVERIES = 1 当前确实意味着第一次恢复后，FallbackPlanner 永久接管。
  - task 5 确实存在 NEED_KEY → HAVE_KEY → NEED_HEAL → CLEANUP 阶段机。
  - Memory 确实有 300 步 TTL 的临时阻挡记忆。
  - 报告对“轨迹一致性不能保证闭环成功”的判断是准确的。
  - Lean 模块映射总体准确；我前面实际执行过 lake build，26 个目标全部成功。

  ## 二、最需要修改的问题

  ### 1. Agent 输入契约存在代码注释和实际实现不一致

  报告指出：

  > 当前实现依赖结构化 reward 明细，不只是标量 reward。

  这个判断是正确的，而且是非常重要的问题。

  实际代码读取：

  info["reward"]["reward_signals"]
  info["reward"]["reward_weights"]

  用于：

  - 判断撞墙；
  - 估计 HP 损失；
  - 确认回血；
  - 确认按钮按下。

  但 nsi_agent/agent.py:1 顶部却写着：

  > Nothing else in info is read

  并且 _blocked_by_reward 的 docstring 说：

  > reward value alone

  这两句话都不准确。报告已经识别出这个问题，建议进一步明确写成：

  > 在线推理读取 obs、info["inventory"] 以及 info["reward"] 中的结构化 reward_signals/reward_weights。
  > 它不读取 agent 坐标、房间 ID、地图或对象真值。

  同时，报告 2.1 表格中的：

  > 最终策略只能使用像素、reward 历史和显式物品栏

  最好改为：

  > 最终策略使用像素、结构化 reward 历史和显式物品栏。

  否则容易让人误以为只使用了标量奖励。

  ### 2. “确定性运动模型”表述稍强

  报告将 Tracker 描述为：

  > 用确定性运动模型推演玩家位置

  更严谨的说法应该是：

  > 用基于当前符号地图的确定性预测模型进行 dead-reckoning，并利用 reward 反馈修正未知碰撞造成的预测误
  > 差。

  因为 Tracker 不知道所有真实碰撞面。对于 VLM 漏检的墙，它会先乐观移动，下一步收到 invalid_action 后才
  回滚。因此它是确定性预测函数，但不代表对真实环境始终精确。

  ### 3. “与引擎相同的 AABB 模型”需要保留抽象边界

  报告说：

  > Tracker 使用像素坐标和 AABB 阻挡模型

  这没有问题。但若写成“与引擎一致”或“相同语义”，就有些过强。

  Tracker 的 _rect_hits_block 是依据符号网格判断 16×16 矩形覆盖格，而引擎还可能涉及：

  - 动态对象状态；
  - 未被感知的阻挡物；
  - 出口瞬时传送；
  - 具体碰撞处理顺序；
  - 像素渲染与状态不同步。

  建议统一称为：

  > 对引擎轴向像素移动与矩形占用规则的符号近似模型。

  ### 4. Safety Shield 不能直接称为“保证安全”

  报告 4.4.3 已经加了条件：

  > grounding 给出的怪物集合完整、0.5px/步上界成立、Tracker 未漏掉房间跳变。

  这部分写得比较严谨。但报告前面还有一些无条件语气，例如：

  > 用安全护盾拦截危险移动

  可以保留；如果出现“保证不受伤”“可证不会接触怪物”，则应统一改为：

  > 在怪物观测完整、速度上界成立且 Tracker 危险区域覆盖真实怪物位置的条件下，Safety Shield 保证所放行
  > 的移动不进入符号危险区域。

  Lean 中的 lean/NesyFormalization/SafetyShield.lean:73 也确实依赖 MonsterRegionSound 一类连接假设，并
  不是无条件证明视觉环境安全。

  ### 5. BFS 的“完备性”不能不加限制

  报告第 8 节已经写成“带约束完备性前提”，这比简单声称 BFS 完备更准确。

  原因是 Lean 和 Python 实现包含具体搜索限制；Lean 的 bfsPath 使用固定 fuel 80。虽然地图恰好只有 80 个
  格子，但当前形式化中的 seen/queue 实现及约束条件仍需要仔细区分：

  - 路径 soundness：返回的路径一定合法；
  - 不重复、避障、避 hazard：有相应定理；
  - 完备性：只能在形式化给出的搜索闭包、fuel 和约束前提下声称；
  - 最短路：目前主要是具体反例/实例级证明，不能概括为完整的普遍最短路定理。

  因此建议把表格里的“soundness、无重复、避障/避 hazard；带约束完备性前提”保留，不要在摘要中进一步简化
  成“Lean 已证明 BFS 完备且最优”。

  ## 三、报告中几处值得调整的小问题

  ### “当前交付”与“审阅基线”

  报告注明基线 commit 99dcf31，但当前工作区可能已经不是完全相同的提交状态。建议将其改为：

  > 本报告以 commit 99dcf31 为主要审阅基线；文中工件和 Lean 构建状态另按 2026-07-15 工作区核对。

  否则后面项目继续修改时，报告会显得像在描述固定提交，实际却混入了更新后的内容。

  ### “11 个非 selection JSON 工件”

  当前 artifacts 目录确实有 12 个 JSON，其中排除 selection.json 后为 11 个。这句话目前正确，但建议改成
  更自然的：

  > artifacts/ 中除 selection.json 外的 11 个程序工件均能通过当前 DSL 编译器加载。

  ### “当前环境缺少 pytest 和 gymnasium”

  这是一次审阅时的环境状态，不是项目设计事实。建议移到“审阅限制”小节，或者注明：

  > 在生成本报告的审阅环境中未安装……

  不要让读者误以为仓库本身不能安装它们。特别是 gymnasium 已经在 pyproject.toml 的正式依赖中。

  ### “静默吞掉异常”

  这个说法基本正确，但不同异常后的行为不完全相同：

  - grounding 异常：退避 3 步；
  - planner 顶层异常：当前步返回 WAIT；
  - DSL 表达式异常：保存 runtime_error diagnosis 后返回 WAIT；
  - artifact 加载异常：是否能安全 fallback 取决于异常发生的位置，并非全部加载错误都会自动回退。

  所以报告中“工件加载、VLM、规划器异常都可回退”稍微过宽。建议改成：

  > VLM 推理和在线规划异常具有降级路径；部分工件解析或配置错误仍可能在初始化/reset 阶段直接暴露。

  ## 四、Lean 部分的准确评价

  报告的 Lean 部分总体符合项目，而且比 lean/README.md 中“主要形式化环境层”的旧描述更接近当前状态。

  当前 Lean 实际已经覆盖：

  环境语义
    ↓
  Tracker 与怪物危险区域
    ↓
  BFS / GoTo / Safety Shield
    ↓
  技能契约与组合
    ↓
  DSL / Planner / Integrated Execution
    ↓
  Task 1–5 的抽象执行 witness

  但需要强调：Task 1–5 的 theorem 是在 Lean 中重新建立的抽象世界、抽象 planner 和预算执行 witness，不
  是把 Python Agent 代码自动提取进 Lean 后证明，也不是证明 Python 像素策略面对所有地图都必定通关。

  报告第 8 节已经列出三个关键假设，这一段应当保留，甚至可以突出：

  1. grounding 与真实视觉状态的对应；
  2. Tracker 危险区域覆盖真实怪物；
  3. Lean tile 模型对 Python 像素语义的 refinement。

  ## 总体评价

  我会给这份报告大约“90% 符合当前项目”的评价。主体结构、代码参数、工件状态和 Lean 模块对应都比较准确，
  主要问题不是“写了不存在的功能”，而是少数地方容易把：

  - 预测模型写成真实模型；
  - 条件安全写成无条件安全；
  - 结构化 reward 写成单一 reward 值；
  - Lean 抽象执行写成 Python 端到端证明。
# 设计:oracle agent 行为观察器(`utils/agent_play.py`)

日期:2026-07-09
状态:已确认(brainstorming 定稿)

## 目的

调试 planner 行为:以人类玩家视角(`utils/human_play.py` 同款 pygame 窗口)实时观看
oracle 模式 agent 跑关,叠加其内部决策状态,支持暂停/单步/调速。

不在范围内:视频录制、HTML 回放器、怪物禁行区叠加(本轮明确不做)。

## 架构

新文件 `utils/agent_play.py`,与 `human_play.py` 并列;agent 构造复用
`nsi_agent/debug_run.py` 的模式。对 agent 代码的唯一侵入见「代码改动」节。

### CLI

```
python utils/agent_play.py --task mathematical_logic/task_1 [--seed 0]
                           [--backend oracle|vlm] [--fallback]
                           [--speed 1] [--smoke N]
```

- `--task` / `--seed`:同 human_play/debug_run。
- `--backend`:默认 `oracle`(`OracleGrounding(env)`);`vlm` 用 `VLMGrounding()`。
- `--fallback`:`prefer_induced=False`,强制手写 planner,同 debug_run。
- `--speed`:初始速度倍率,取值 0.25/0.5/1/2/4/8/16。
- `--smoke N`:跑 N 步后自动退出并打印摘要;配合 `SDL_VIDEODRIVER=dummy`
  可无显示冒烟。

### 环境与 agent 构造

```python
env = make_env(task_id=..., observation_mode="pixels", render_mode="rgb_array")
grounding = OracleGrounding(env)  # 或 VLMGrounding()
policy = Policy(backend=grounding, prefer_induced=not fallback)
policy.reset(seed=seed, task_id=task_id)
```

## 窗口布局

总窗口 = 左侧游戏画面 + 右侧信息面板(`PANEL_WIDTH = 320`)。

- **游戏画面**:`WINDOW_WIDTH × WINDOW_HEIGHT`(640×640,`WINDOW_SCALE=4`),
  与 human_play 相同:`env.render()` → surfarray → scale → blit。
- **信息面板(上:状态块)**:task、step、HP、keys、当前 `Goal`
  (key / skill / args)、task5 阶段(`planner.task5_phase`,仅 task_5)、
  当前速度与 PAUSED 状态。
- **信息面板(下:事件流)**:`planner.goal_log` 增量滚动显示
  (step, kind, key),保留最近 30 条;`planner.diagnoses` 新条目以
  另一颜色插入同一流。

## 画面叠加层

坐标换算:HUD 在画面底部,地图自 (0,0) 起,故
`tile (tx,ty) → 窗口像素 (tx*TILE_SIZE*WINDOW_SCALE, ty*TILE_SIZE*WINDOW_SCALE)`,
无偏移。

- **规划路径**:当前活跃 GoToTile 的 `_path`,按 tile 中心连半透明折线。
- **waypoint**:`_waypoint` 格子描边高亮。
- **路径来源**:工具函数 `extract_nav(skill)` —— 活跃技能
  `planner._skill` 本身是 GoToTile 则直接用;否则取其 `_nav` 属性
  (OpenChest 等嵌套导航技能);都没有则不画。

## 交互与主循环

键位:`Space` 暂停/继续;`N` 单步(暂停态执行一步);`+`/`-` 调速
(0.25×–16× 档位表);`R` 重置 episode(同 seed);`Tab` 倾倒最近
obs/info 历史(复用 human_play 的 dump 逻辑);`Esc` 退出。

主循环 `clock.tick(TARGET_FPS)`;速度用步数累加器实现:每帧累加
`speed`,累加值每满 1 执行一步(speed<1 时自然隔帧执行)。每步:

```python
action = policy.act(obs, info)
obs, reward, terminated, truncated, info = env.step(action)
```

`terminated/truncated` 后冻结画面,居中显示 VICTORY / GAME OVER,
等待 `R` 或 `Esc`。对 planner/tracker/skill 状态的访问全部只读。

## 代码改动(agent 侧)

仅 `nsi_agent/skills.py` 的 `GoToTile`:

- `step()` 中把规划出的局部变量 `path` 存为 `self._path`;
- `reset()` 中置 `self._path = None`。

其余零改动。

## 错误处理

- pygame 显示初始化失败:报错退出,提示需要 WSLg/X server,
  或用 `SDL_VIDEODRIVER=dummy --smoke N` 无显示运行。
- episode 结束后不再调用 `policy.act`。
- VLM backend 的网络重试沿用 Policy 已有 backoff,不额外处理。

## 验证

- 冒烟:`SDL_VIDEODRIVER=dummy python utils/agent_play.py --task
  mathematical_logic/task_1 --smoke 200` 正常退出、摘要含步数与事件。
- 手动验收:task_1 oracle 全程观看;暂停/单步/调速/日志滚动正常;
  task_5 显示阶段;路径线与实际走位一致。

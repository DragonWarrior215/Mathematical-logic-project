# Oracle Agent 行为观察器实现计划

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 新建 `utils/agent_play.py`:human_play 同款 pygame 窗口,由 oracle/vlm 模式的 `Policy.act()` 驱动,叠加规划路径与 goal_log,支持暂停/单步/调速。

**Architecture:** 单文件观察器脚本(镜像 `utils/human_play.py` 的结构),纯逻辑助手(调速档位、路径提取、日志流)放模块顶部供 pytest 直测;`AgentSession` 封装 env+policy 的 rollout 状态;渲染分 `draw_game`/`draw_overlay`/`draw_panel` 三个函数。对 agent 代码唯一侵入:`GoToTile` 增加 `_path` 字段。

**Tech Stack:** Python 3.12(`.venv/bin/python`)、pygame(已有依赖)、pytest(`python -m pytest`)。

**Spec:** `docs/superpowers/specs/2026-07-09-oracle-agent-viz-design.md`

## Global Constraints

- 解释器一律用 `.venv/bin/python`,在项目根 `/home/bruce/nesylink` 下运行。
- 不新增任何第三方依赖。
- 对 `nsi_agent/` 的改动仅限 Task 1 的 `GoToTile._path`(2 处赋值 + 1 个字段);观察器对 planner/tracker/skill 的其余访问全部只读。
- 不得改动 `nsi_agent/agent.py` 的 `make_policy`(oracle 拒绝逻辑是评测约束)。
- 面板宽 `PANEL_WIDTH = 320`;速度档位 `SPEED_LADDER = [0.25, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0]`;日志保留 30 条。
- 坐标换算:tile `(tx, ty)` → 窗口像素 `(tx*TILE_SIZE*WINDOW_SCALE, ty*TILE_SIZE*WINDOW_SCALE)`,无偏移(HUD 在画面底部)。
- goal_log 条目为 `(step, kind, key)`;FallbackPlanner 的 kind ∈ {"start", "ok", "fail"},DSLPlanner 另有 "node"/"restart"/"recovery_start"/"recovery_end"/"guard:*"/"terminal_fail" 等;染色规则采用 `"fail" in kind or kind == "diag"`。diagnoses 条目为 `(key, payload)`。

---

### Task 1: `GoToTile` 暴露规划路径 `_path`

**Files:**
- Modify: `nsi_agent/skills.py`(GoToTile,约 192-298 行)
- Test: `tests/test_agent_play.py`(新建)

**Interfaces:**
- Consumes: 无
- Produces: `GoToTile._path: list[tuple[int,int]] | None` — 最近一次 `step()` 规划出的完整 BFS 路径(含起点终点);`reset()` 后为 `None`。Task 2 的 `extract_nav` 与 Task 4 的 `draw_overlay` 依赖它。

- [ ] **Step 1: 写失败测试**

新建 `tests/test_agent_play.py`:

```python
"""Tests for utils/agent_play.py helpers and the GoToTile._path hook."""
from nsi_agent.skills import GoToTile


def test_gototile_path_defaults_none():
    nav = GoToTile()
    assert nav._path is None


def test_gototile_reset_clears_path():
    nav = GoToTile()
    nav._path = [(1, 1), (1, 2)]
    nav.reset(None, target=(3, 4))
    assert nav._path is None
```

(`GoToTile.reset` 不使用 ctx 参数,传 `None` 安全。)

- [ ] **Step 2: 运行确认失败**

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 2 FAIL,`AttributeError: 'GoToTile' object has no attribute '_path'`

- [ ] **Step 3: 最小实现**

`nsi_agent/skills.py` 三处修改:

字段(`_waypoint` 之后,约 210 行):

```python
    _waypoint: Tile | None = None
    _path: list[Tile] | None = None
    _bump_streak: int = 0
```

`reset()` 末尾(约 224 行,`self._waypoint = None` 之后):

```python
        self._waypoint = None
        self._path = None
        self._bump_streak = 0
```

`step()` 中路径规划成功后(约 284-292 行,在 `waypoint = path[1] ...` 之前):

```python
        path = bfs_path(ctx, here, goals, avoid=self.avoid)
        if path is None:
            # Retry ignoring monster balls once (shield still guards moves);
            # a truly disconnected target is a symbolic failure.
            path = bfs_path(ctx, here, goals, avoid_monsters=False,
                            avoid=self.avoid)
            if path is None:
                return ("fail", ("no_path", self.target))
        self._path = path
        waypoint = path[1] if len(path) > 1 else path[0]
```

- [ ] **Step 4: 运行测试通过**

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 2 PASS

- [ ] **Step 5: 回归验证 agent 行为未变**

Run: `.venv/bin/python -m nsi_agent.debug_run --tasks mathematical_logic/task_1 --episodes 1`
Expected: 输出 JSON 中 `"success": true`,与改动前一致。

- [ ] **Step 6: Commit**

```bash
git add tests/test_agent_play.py nsi_agent/skills.py
git commit -m "GoToTile 暴露 _path 供观察器叠加渲染"
```

---

### Task 2: agent_play 纯逻辑助手(调速 / 路径提取 / 格式化)

**Files:**
- Create: `utils/agent_play.py`
- Test: `tests/test_agent_play.py`(追加)

**Interfaces:**
- Consumes: `GoToTile`(`nsi_agent.skills`)、`Goal`(`nsi_agent.planner`,字段 `key/skill/args`)、Task 1 的 `_path`
- Produces(Task 3/4/5 依赖,签名如下):
  - `SPEED_LADDER: list[float]`
  - `class StepPacer: __init__(speed: float = 1.0); steps_this_frame() -> int; faster() -> None; slower() -> None; speed: float`
  - `extract_nav(skill) -> GoToTile | None`
  - `format_goal(goal) -> str`

- [ ] **Step 1: 写失败测试**

`tests/test_agent_play.py` 追加:

```python
from nsi_agent.planner import Goal
from utils.agent_play import SPEED_LADDER, StepPacer, extract_nav, format_goal


def test_pacer_accumulates_fractional_speed():
    pacer = StepPacer(0.5)
    steps = [pacer.steps_this_frame() for _ in range(4)]
    assert sum(steps) == 2          # 0.5x:每 2 帧走 1 步
    pacer = StepPacer(4.0)
    assert pacer.steps_this_frame() == 4


def test_pacer_ladder_bounds():
    pacer = StepPacer(16.0)
    pacer.faster()
    assert pacer.speed == 16.0      # 顶格不越界
    pacer = StepPacer(0.25)
    pacer.slower()
    assert pacer.speed == 0.25      # 底格不越界
    pacer = StepPacer(1.0)
    pacer.faster()
    assert pacer.speed == 2.0


def test_extract_nav_direct_and_nested():
    nav = GoToTile()
    assert extract_nav(nav) is nav

    class FakeChestSkill:
        def __init__(self):
            self._nav = GoToTile()

    holder = FakeChestSkill()
    assert extract_nav(holder) is holder._nav
    assert extract_nav(None) is None
    assert extract_nav(object()) is None


def test_format_goal():
    assert format_goal(None) == "(idle)"
    goal = Goal(("chest", (0, 0), (3, 4)), "open_chest", {"target": (3, 4)})
    text = format_goal(goal)
    assert "open_chest" in text and "(3, 4)" in text
```

- [ ] **Step 2: 运行确认失败**

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 新增 4 个测试 FAIL(`ModuleNotFoundError: No module named 'utils.agent_play'`),Task 1 的 2 个仍 PASS

- [ ] **Step 3: 创建 `utils/agent_play.py`(仅助手部分)**

```python
"""Agent-play observer: watch the NSI agent play like a human player.

Usage:
    python utils/agent_play.py --task mathematical_logic/task_1 [--seed 0]
                               [--backend oracle|vlm] [--fallback]
                               [--speed 1] [--smoke N]

Keys: Space=pause/resume, N=single-step, +/-=speed, R=reset episode,
      Tab=dump obs/info history, Esc=quit
"""

from __future__ import annotations

import sys
from pathlib import Path

# Ensure project root is on sys.path so imports work when running directly.
_project_root = str(Path(__file__).resolve().parent.parent)
if _project_root not in sys.path:
    sys.path.insert(0, _project_root)

from nsi_agent.skills import GoToTile

PANEL_WIDTH = 320
HISTORY_SIZE = 5
LOG_KEEP = 30
SPEED_LADDER = [0.25, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0]


class StepPacer:
    """Fractional-speed step accumulator: each frame accrues `speed` and
    yields the integer part as the number of env steps to run."""

    def __init__(self, speed: float = 1.0) -> None:
        self.speed = speed if speed in SPEED_LADDER else 1.0
        self._acc = 0.0

    def steps_this_frame(self) -> int:
        self._acc += self.speed
        n = int(self._acc)
        self._acc -= n
        return n

    def faster(self) -> None:
        idx = SPEED_LADDER.index(self.speed)
        self.speed = SPEED_LADDER[min(idx + 1, len(SPEED_LADDER) - 1)]

    def slower(self) -> None:
        idx = SPEED_LADDER.index(self.speed)
        self.speed = SPEED_LADDER[max(idx - 1, 0)]


def extract_nav(skill) -> GoToTile | None:
    """The active skill's navigation core: the skill itself (GoToTile) or
    its embedded `_nav` (OpenChest and friends); None when neither."""
    if isinstance(skill, GoToTile):
        return skill
    nav = getattr(skill, "_nav", None)
    return nav if isinstance(nav, GoToTile) else None


def format_goal(goal) -> str:
    if goal is None:
        return "(idle)"
    args = ", ".join(f"{k}={v}" for k, v in goal.args.items())
    return f"{goal.skill}({args})  key={goal.key}"
```

- [ ] **Step 4: 运行测试通过**

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 6 PASS

- [ ] **Step 5: Commit**

```bash
git add tests/test_agent_play.py utils/agent_play.py
git commit -m "agent_play 助手:调速档位、导航提取、目标格式化"
```

---

### Task 3: `AgentSession` + `LogStream` + 无头 smoke 主干

**Files:**
- Modify: `utils/agent_play.py`(追加)
- Test: 命令行冒烟(见 Step 3)

**Interfaces:**
- Consumes: `Policy` / `OracleGrounding` / `VLMGrounding`(`nsi_agent.agent`)、`nesylink.make_env`、Task 2 助手
- Produces(Task 4/5 依赖):
  - `class LogStream: entries: deque[tuple[int|None, str, str]]; poll(planner) -> None`
  - `class AgentSession: __init__(task_id, seed, backend, prefer_induced); reset(); step(); done: bool; success: bool; obs; info; steps: int; total_reward: float; history: deque; policy; env; summary() -> dict; close()`
  - `main()` 与 argparse CLI(`--task --seed --backend --fallback --speed --smoke`)

- [ ] **Step 1: 追加 session 与日志流实现**

在 `utils/agent_play.py` 顶部 import 区(`from nsi_agent.skills import GoToTile` 上方)追加:

```python
import argparse
import json
import os
from collections import Counter, deque

import numpy as np

import nesylink
from nsi_agent.agent import OracleGrounding, Policy
```

在 `format_goal` 之后追加:

```python
class LogStream:
    """Incremental reader over planner.goal_log / planner.diagnoses.

    The planner instance is replaced on policy.reset(), so track its id and
    restart the cursors when it changes."""

    def __init__(self) -> None:
        self._planner_id: int | None = None
        self._n_goals = 0
        self._n_diag = 0
        self.entries: deque = deque(maxlen=LOG_KEEP)

    def poll(self, planner) -> None:
        if id(planner) != self._planner_id:
            self._planner_id = id(planner)
            self._n_goals = 0
            self._n_diag = 0
        goal_log = getattr(planner, "goal_log", [])
        for step, kind, key in goal_log[self._n_goals:]:
            self.entries.append((step, f"{kind} {key}", kind))
        self._n_goals = len(goal_log)
        diagnoses = getattr(planner, "diagnoses", [])
        for key, payload in diagnoses[self._n_diag:]:
            self.entries.append((None, f"diag {key}: {payload!r}", "diag"))
        self._n_diag = len(diagnoses)


class AgentSession:
    """Env + policy rollout state for the observer window."""

    def __init__(self, task_id: str, seed: int, backend: str,
                 prefer_induced: bool) -> None:
        self.task_id = task_id
        self.seed = seed
        self.env = nesylink.make_env(
            task_id=task_id, api="gym",
            observation_mode="pixels", render_mode="rgb_array",
        )
        if backend == "oracle":
            grounding = OracleGrounding(self.env)
        else:
            from nsi_agent.agent import VLMGrounding
            grounding = VLMGrounding()
        self.policy = Policy(backend=grounding, prefer_induced=prefer_induced)
        self.events: Counter = Counter()
        self.history: deque = deque(maxlen=HISTORY_SIZE)
        self.reset()

    def reset(self) -> None:
        self.policy.reset(seed=self.seed, task_id=self.task_id)
        self.obs, self.info = self.env.reset(seed=self.seed)
        self.events.clear()
        self.history.clear()
        self.steps = 0
        self.total_reward = 0.0
        self.terminated = False
        self.truncated = False

    @property
    def done(self) -> bool:
        return self.terminated or self.truncated

    @property
    def success(self) -> bool:
        return bool(
            self.info.get("game", {}).get("world_completed")
            or self.info.get("terminal_reason") == "world_completed"
        )

    def step(self) -> None:
        if self.done:
            return
        action = self.policy.act(self.obs, self.info)
        step_count = self.info.get("episode", {}).get("step_count", self.steps)
        (self.obs, reward, self.terminated,
         self.truncated, self.info) = self.env.step(action)
        self.steps += 1
        self.total_reward += float(reward)
        self.history.append((step_count, action, self.obs, self.info))
        for record in self.info.get("events", {}).get("records", []):
            name = record.get("name")
            if name:
                self.events[name] += 1

    def summary(self) -> dict:
        return {
            "task_id": self.task_id,
            "seed": self.seed,
            "steps": self.steps,
            "reward": round(self.total_reward, 3),
            "success": self.success,
            "terminal_reason": self.info.get("terminal_reason"),
            "events": dict(sorted(self.events.items())),
        }

    def close(self) -> None:
        self.env.close()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Watch the NSI agent play with a human-play style window"
    )
    parser.add_argument("--task", type=str,
                        default="mathematical_logic/task_1")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--backend", choices=["oracle", "vlm"],
                        default="oracle")
    parser.add_argument("--fallback", action="store_true",
                        help="force the hand-written planner")
    parser.add_argument("--speed", type=float, default=1.0,
                        choices=SPEED_LADDER)
    parser.add_argument("--smoke", type=int, default=0, metavar="N",
                        help="headless-friendly: run N steps then exit "
                             "with a JSON summary")
    return parser.parse_args()
```

- [ ] **Step 2: 追加最小 `main()`(先只有 smoke 路径,渲染下个任务补)**

```python
def main() -> None:
    args = parse_args()
    if args.smoke:
        os.environ.setdefault("SDL_VIDEODRIVER", "dummy")
    session = AgentSession(args.task, args.seed, args.backend,
                           prefer_induced=not args.fallback)
    stream = LogStream()
    while not session.done and (not args.smoke or session.steps < args.smoke):
        session.step()
        stream.poll(session.policy.planner)
        if not args.smoke:
            break   # 交互渲染循环在 Task 4/5 中实现
    summary = session.summary()
    summary["log_entries"] = len(stream.entries)
    print(json.dumps(summary, ensure_ascii=False))
    session.close()


if __name__ == "__main__":
    main()
```

- [ ] **Step 3: 冒烟验证**

Run: `.venv/bin/python utils/agent_play.py --task mathematical_logic/task_1 --smoke 200`
Expected: 退出码 0;输出 JSON 含 `"steps": 200`(或提前终局的更小值)、`"log_entries"` > 0

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 6 PASS(无回归)

- [ ] **Step 4: Commit**

```bash
git add utils/agent_play.py
git commit -m "agent_play:AgentSession/LogStream 与无头 smoke 主干"
```

---

### Task 4: pygame 窗口、信息面板与路径叠加层

**Files:**
- Modify: `utils/agent_play.py`(追加渲染函数,重写 `main()`)

**Interfaces:**
- Consumes: Task 1 `_path`/`_waypoint`、Task 2 `extract_nav`/`format_goal`/`StepPacer`、Task 3 `AgentSession`/`LogStream`;常量 `TILE_SIZE=16, WINDOW_SCALE=4, WINDOW_WIDTH=640, WINDOW_HEIGHT=640, TARGET_FPS=60`
- Produces(Task 5 依赖):`draw_game(display, frame)`、`draw_overlay(display, skill) -> bool`、`draw_panel(display, fonts, session, stream, pacer, paused)`;`main()` 含完整渲染循环与 `overlay_frames` 计数

- [ ] **Step 1: 追加渲染函数**

在 `utils/agent_play.py` 顶部 import 区追加:

```python
import pygame

from nesylink.core.constants import (
    TARGET_FPS,
    TILE_SIZE,
    WINDOW_HEIGHT,
    WINDOW_SCALE,
    WINDOW_WIDTH,
)
```

在 `AgentSession` 之后追加:

```python
CELL = TILE_SIZE * WINDOW_SCALE
PATH_COLOR = (80, 200, 255, 160)
WAYPOINT_COLOR = (255, 220, 80, 200)
PANEL_BG = (24, 24, 32)
TEXT_COLOR = (230, 230, 230)
LOG_OK_COLOR = (170, 220, 170)
LOG_FAIL_COLOR = (255, 120, 120)


def tile_center_px(tile) -> tuple[int, int]:
    tx, ty = tile
    return (tx * CELL + CELL // 2, ty * CELL + CELL // 2)


def draw_game(display: "pygame.Surface", frame: np.ndarray) -> None:
    surface = pygame.surfarray.make_surface(np.transpose(frame, (1, 0, 2)))
    display.blit(
        pygame.transform.scale(surface, (WINDOW_WIDTH, WINDOW_HEIGHT)), (0, 0)
    )


def draw_overlay(display: "pygame.Surface", skill) -> bool:
    """Planned path + next waypoint over the game view. True if drawn."""
    nav = extract_nav(skill)
    if nav is None or not nav._path:
        return False
    layer = pygame.Surface((WINDOW_WIDTH, WINDOW_HEIGHT), pygame.SRCALPHA)
    points = [tile_center_px(t) for t in nav._path]
    if len(points) >= 2:
        pygame.draw.lines(layer, PATH_COLOR, False, points, 3)
    if nav._waypoint is not None:
        wx, wy = nav._waypoint
        pygame.draw.rect(layer, WAYPOINT_COLOR,
                         (wx * CELL, wy * CELL, CELL, CELL), 3)
    display.blit(layer, (0, 0))
    return True


def draw_panel(display: "pygame.Surface", fonts, session: AgentSession,
               stream: LogStream, pacer: StepPacer, paused: bool) -> None:
    font, small = fonts
    x = WINDOW_WIDTH + 10
    pygame.draw.rect(display, PANEL_BG,
                     (WINDOW_WIDTH, 0, PANEL_WIDTH, WINDOW_HEIGHT))
    info = session.info
    planner = session.policy.planner
    lines = [
        f"task: {session.task_id}",
        f"seed: {session.seed}   step: "
        f"{info.get('episode', {}).get('step_count', '?')}",
        f"hp: {info.get('agent', {}).get('hp', '?')}   "
        f"keys: {info.get('inventory', {}).get('keys', '?')}   "
        f"room: {info.get('env', {}).get('room_id', '?')}",
        f"reward: {session.total_reward:.1f}   speed: {pacer.speed}x"
        + ("   [PAUSED]" if paused else ""),
        "",
        "goal: " + format_goal(getattr(planner, "current", None)),
    ]
    if session.task_id.endswith("task_5"):
        lines.append(f"phase: {getattr(planner, 'task5_phase', '-')}")
    lines += ["", "-- goal log --"]
    y = 8
    for text in lines:
        display.blit(font.render(text, True, TEXT_COLOR), (x, y))
        y += 20
    for step, text, kind in list(stream.entries):
        color = LOG_FAIL_COLOR if kind in ("fail", "diag") else LOG_OK_COLOR
        prefix = f"{step} " if step is not None else "    "
        display.blit(small.render((prefix + text)[:44], True, color), (x, y))
        y += 15
        if y > WINDOW_HEIGHT - 15:
            break
```

- [ ] **Step 2: 重写 `main()` 为渲染循环(交互键位 Task 5 再加)**

```python
def main() -> None:
    args = parse_args()
    if args.smoke:
        os.environ.setdefault("SDL_VIDEODRIVER", "dummy")
    session = AgentSession(args.task, args.seed, args.backend,
                           prefer_induced=not args.fallback)
    pygame.init()
    display = pygame.display.set_mode(
        (WINDOW_WIDTH + PANEL_WIDTH, WINDOW_HEIGHT))
    pygame.display.set_caption(
        f"NesyLink Agent Observer — {args.task} [{args.backend}]")
    clock = pygame.time.Clock()
    fonts = (pygame.font.SysFont(None, 22), pygame.font.SysFont(None, 17))
    pacer = StepPacer(args.speed)
    stream = LogStream()
    paused = False
    overlay_frames = 0
    running = True

    while running:
        if not args.smoke:
            clock.tick(TARGET_FPS)
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
        if not session.done:
            n = 16 if args.smoke else (0 if paused
                                       else pacer.steps_this_frame())
            for _ in range(n):
                session.step()
                if session.done:
                    break
        stream.poll(session.policy.planner)

        draw_game(display, session.env.render())
        if draw_overlay(display, session.policy.planner._skill):
            overlay_frames += 1
        draw_panel(display, fonts, session, stream, pacer, paused)
        pygame.display.flip()

        if args.smoke and (session.steps >= args.smoke or session.done):
            running = False

    summary = session.summary()
    summary["overlay_frames"] = overlay_frames
    summary["log_entries"] = len(stream.entries)
    print(json.dumps(summary, ensure_ascii=False))
    session.close()
    pygame.quit()
```

(Task 3 `main()` 中的临时 while 循环被本版整体替换。)

- [ ] **Step 3: 冒烟验证渲染路径**

Run: `.venv/bin/python utils/agent_play.py --task mathematical_logic/task_1 --smoke 200`
Expected: 退出码 0;JSON 含 `"overlay_frames"` > 0(agent 大部分时间在导航)且 `"log_entries"` > 0

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 6 PASS

- [ ] **Step 4: 有显示环境手动查看(WSLg)**

Run: `.venv/bin/python utils/agent_play.py --task mathematical_logic/task_1`
Expected: 窗口弹出,agent 自动跑,路径蓝线 + waypoint 黄框随移动更新,右侧面板显示 goal 与滚动日志。(此步无显示环境可跳过,留给 Task 5 验收。)

- [ ] **Step 5: Commit**

```bash
git add utils/agent_play.py
git commit -m "agent_play:pygame 窗口、信息面板与路径叠加层"
```

---

### Task 5: 交互键位、终局画面与显示错误处理

**Files:**
- Modify: `utils/agent_play.py`(完善 `main()`)

**Interfaces:**
- Consumes: Task 4 的渲染循环、`utils.human_play.dump_history`
- Produces: 最终 CLI 工具;键位 Space/N/+/-/R/Tab/Esc;显示初始化失败的友好报错

- [ ] **Step 1: 键位、终局与错误处理**

`main()` 中三处修改。(a) `set_mode` 包上错误处理:

```python
    pygame.init()
    try:
        display = pygame.display.set_mode(
            (WINDOW_WIDTH + PANEL_WIDTH, WINDOW_HEIGHT))
    except pygame.error as exc:
        print(f"[display unavailable: {exc}]")
        print("需要 WSLg/X server;或无显示运行:"
              "SDL_VIDEODRIVER=dummy python utils/agent_play.py --smoke N")
        session.close()
        pygame.quit()
        sys.exit(1)
```

(b) 事件循环替换为完整键位处理(`single_step` 初始化于 while 顶部):

```python
        single_step = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    running = False
                elif event.key == pygame.K_SPACE:
                    paused = not paused
                elif event.key == pygame.K_n:
                    single_step = True
                elif event.key in (pygame.K_PLUS, pygame.K_EQUALS,
                                   pygame.K_KP_PLUS):
                    pacer.faster()
                elif event.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                    pacer.slower()
                elif event.key == pygame.K_r:
                    session.reset()
                    stream = LogStream()
                    paused = False
                elif event.key == pygame.K_TAB:
                    from utils.human_play import dump_history
                    dump_history(session.history)
```

步进逻辑改为:

```python
        if not session.done:
            if args.smoke:
                n = 16
            elif paused:
                n = 1 if single_step else 0
            else:
                n = pacer.steps_this_frame()
            for _ in range(n):
                session.step()
                if session.done:
                    break
```

(c) `pygame.display.flip()` 之前加终局横幅:

```python
        if session.done and not args.smoke:
            banner = ("VICTORY - R to restart" if session.success
                      else "GAME OVER - R to restart")
            text_surface = fonts[0].render(banner, True, (255, 255, 255))
            rect = text_surface.get_rect(
                center=(WINDOW_WIDTH // 2, WINDOW_HEIGHT // 2))
            display.blit(text_surface, rect)
```

- [ ] **Step 2: 完整冒烟(跑到终局)**

Run: `.venv/bin/python utils/agent_play.py --task mathematical_logic/task_1 --smoke 3000`
Expected: `"success": true`、`"terminal_reason": "world_completed"`、`"overlay_frames"` > 0

Run: `.venv/bin/python -m pytest tests/test_agent_play.py -v`
Expected: 6 PASS

- [ ] **Step 3: 手动验收清单(WSLg 窗口)**

Run: `.venv/bin/python utils/agent_play.py --task mathematical_logic/task_5`
逐项确认:

1. Space 暂停后画面冻结,面板显示 [PAUSED];再按恢复。
2. 暂停态按 N,agent 恰好走一步。
3. `+`/`-` 在 0.25x–16x 间调速,面板速度值同步变化。
4. 面板显示 `phase: need_key` 等 task5 阶段并随进度切换。
5. 路径蓝线与实际走位一致;waypoint 黄框在 agent 前方。
6. goal_log 滚动,fail/diag 红色,start/ok 绿色。
7. R 重置后从头开跑,日志清空。
8. Tab 在终端倾倒最近 5 步 obs/info。
9. Esc 退出,终端打印 JSON 摘要。

- [ ] **Step 4: Commit**

```bash
git add utils/agent_play.py
git commit -m "agent_play:交互键位、终局画面与显示错误处理"
```

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

import argparse
import json
import os
from collections import Counter, deque

import numpy as np
import pygame

import nesylink
from nesylink.core.constants import (
    TARGET_FPS,
    TILE_SIZE,
    WINDOW_HEIGHT,
    WINDOW_SCALE,
    WINDOW_WIDTH,
)
from nsi_agent.agent import OracleGrounding, Policy
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
        # DSLPlanner uses 'override', FallbackPlanner uses '_skill'
        skill = (getattr(session.policy.planner, '_skill', None) or
                 getattr(session.policy.planner, 'override', None))
        if draw_overlay(display, skill):
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


if __name__ == "__main__":
    main()

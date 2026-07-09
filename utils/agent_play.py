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

"""Tests for utils/agent_play.py helpers and the GoToTile._path hook."""
from nsi_agent.skills import GoToTile
from nsi_agent.planner import Goal
from utils.agent_play import SPEED_LADDER, StepPacer, extract_nav, format_goal


def test_gototile_path_defaults_none():
    nav = GoToTile()
    assert nav._path is None


def test_gototile_reset_clears_path():
    nav = GoToTile()
    nav._path = [(1, 1), (1, 2)]
    nav.reset(None, target=(3, 4))
    assert nav._path is None


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

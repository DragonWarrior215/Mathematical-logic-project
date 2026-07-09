"""Tests for utils/agent_play.py helpers and the GoToTile._path hook."""
from nsi_agent.skills import GoToTile
from nsi_agent.planner import Goal
from utils.agent_play import (
    SPEED_LADDER, StepPacer, active_skill, describe_goal, extract_nav,
    format_goal,
)


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


def test_active_skill_fallback_planner():
    nav = GoToTile()

    class FakeFallback:
        _skill = None

    planner = FakeFallback()
    assert active_skill(planner) is None
    planner._skill = nav
    assert active_skill(planner) is nav


def test_active_skill_dsl_planner_layers():
    nav = GoToTile()

    class FakeInterp:
        active_skill = None

    class FakeDSL:
        override = None
        _recovery = None
        interp = FakeInterp()

    planner = FakeDSL()
    assert active_skill(planner) is None          # idle interpreter
    planner.interp.active_skill = nav
    assert active_skill(planner) is nav           # program execution
    override = GoToTile()
    planner.override = override
    assert active_skill(planner) is override      # guard preempts program

    class FakeRecovery:
        _skill = None

    recovery = FakeRecovery()
    recovery._skill = nav
    planner._recovery = recovery
    assert active_skill(planner) is nav           # recovery preempts all


def test_describe_goal_across_planners():
    from nsi_agent.planner import FallbackPlanner

    fp = FallbackPlanner()
    assert describe_goal(fp) == "(idle)"
    fp.current = Goal(("k",), "goto", {"target": (1, 2)})
    assert "goto" in describe_goal(fp)

    class FakeInterp:
        pc = "n3"
        active_skill = None

    class FakeDSL:
        override = None
        _recovery = None
        interp = FakeInterp()

    planner = FakeDSL()
    assert describe_goal(planner) == "node: n3"
    planner.override = GoToTile()
    assert describe_goal(planner) == "guard: GoToTile"

    class FakeRecovery:
        current = None

    planner._recovery = FakeRecovery()
    assert describe_goal(planner) == "recovery: (idle)"


def test_observer_attribute_contract():
    """Pin the private attribute names the observer reads, so a rename in
    the agent code fails here instead of silently killing the overlay."""
    import inspect
    import re

    from nsi_agent.graph import Interpreter
    from nsi_agent.induction.dsl import DSLPlanner
    from nsi_agent.planner import FallbackPlanner

    fp = FallbackPlanner()
    for attr in ("_skill", "current", "goal_log", "diagnoses"):
        assert hasattr(fp, attr)
    dsl_src = inspect.getsource(DSLPlanner.__init__)
    for attr in ("override", "goal_log", "diagnoses", "_recovery", "interp"):
        assert re.search(rf"self\.{attr}\s*[:=]", dsl_src), attr
    assert re.search(r"self\.active_skill\s*[:=]",
                     inspect.getsource(Interpreter.__init__))

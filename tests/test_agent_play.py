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

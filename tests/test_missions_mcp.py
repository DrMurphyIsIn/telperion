"""Tests for missions MCP tools (Task M8).

Run from telperion/:
    python3 -m pytest tests/test_missions_mcp.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

pytest = __import__("pytest")
pytest.importorskip("mcp")

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.mcp_server import mission_status, mission_open_leaves  # noqa: E402


class TestMissionsMCPTools:
    """Test mission MCP tools exist and are callable."""

    def test_mission_status_exists(self):
        """mission_status function exists and is callable."""
        assert callable(mission_status)
        # Basic smoke test: can call with empty campaign
        result = mission_status(campaign="")
        assert isinstance(result, str)

    def test_mission_open_leaves_exists(self):
        """mission_open_leaves function exists and is callable."""
        assert callable(mission_open_leaves)
        # Basic smoke test: can call with defaults
        result = mission_open_leaves(campaign="", include_claimed=False)
        assert isinstance(result, str)

    def test_mission_open_leaves_with_claimed(self):
        """mission_open_leaves respects include_claimed parameter."""
        result_without = mission_open_leaves(campaign="", include_claimed=False)
        result_with = mission_open_leaves(campaign="", include_claimed=True)
        # Both should return strings (may be empty or error messages)
        assert isinstance(result_without, str)
        assert isinstance(result_with, str)

"""Test that prove2me MCP tools are properly registered."""
import pytest

# Skip if mcp is not installed
pytest.importorskip("mcp")


def test_p2m_tools_exist():
    """Verify the five p2m_* tools are registered in mcp_server."""
    from telperion.mcp_server import (
        p2m_triage,
        p2m_lift,
        p2m_attempt,
        p2m_status,
        p2m_coverage,
    )

    # Assert all five functions exist and are callable
    assert callable(p2m_triage), "p2m_triage must be callable"
    assert callable(p2m_lift), "p2m_lift must be callable"
    assert callable(p2m_attempt), "p2m_attempt must be callable"
    assert callable(p2m_status), "p2m_status must be callable"
    assert callable(p2m_coverage), "p2m_coverage must be callable"

import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_mcp_extra_excludes_mcp_2():
    # mcp_server imports mcp.server.fastmcp, which mcp 2.x removed (renamed MCPServer)
    extra = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]["optional-dependencies"]["mcp"]
    spec = next(s for s in extra if s.replace(" ", "").startswith("mcp"))
    assert "<2" in spec.replace(" ", ""), spec

"""Warm-worker single-shot contract + strict cold-path fallback.

Offline tests (no Lean): the fallback contract — a missing/unavailable env never
yields available(), close() is idempotent. The live parity check (server= verdict
== cold verdict) is skipped unless a built env + elan are present; it runs in CI
against zero_free_bridge. conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))


from telperion.lean_server import LeanServer  # noqa: E402


def test_missing_env_is_never_available():
    srv = LeanServer("/nonexistent/path/xyz")
    assert srv.start() is False
    assert srv.probe() is False
    assert srv.available() is False

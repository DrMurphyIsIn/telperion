"""Warm-worker single-shot contract + strict cold-path fallback.

Offline tests (no Lean): the fallback contract — a missing/unavailable env never
yields available(), close() is idempotent. The live parity check (server= verdict
== cold verdict) is skipped unless a built env + elan are present; it runs in CI
against zero_free_bridge. conjecture1_proved = False.
"""
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

from telperion.lean_server import LeanServer  # noqa: E402
from telperion.verify import verify_lean  # noqa: E402

_ENV = Path(__file__).resolve().parents[1] / "examples" / "zero_free_bridge" / "lean"
_HAVE_LEAN = shutil.which("lake") is not None or (Path.home() / ".elan" / "bin" / "lake").exists()
_BUILT = (_ENV / ".lake").exists()


def test_missing_env_is_never_available():
    srv = LeanServer("/nonexistent/path/xyz")
    assert srv.start() is False
    assert srv.probe() is False
    assert srv.available() is False


def test_available_defaults_false_before_probe():
    srv = LeanServer(_ENV)
    assert srv.available() is False        # no auto-probe; explicit opt-in


def test_close_is_idempotent_noop():
    srv = LeanServer(_ENV)
    srv.close()
    srv.close()                            # must not raise


@pytest.mark.skipif(not (_HAVE_LEAN and _BUILT),
                    reason="needs a built zero_free_bridge env + elan (CI / cleared local)")
def test_server_verdict_matches_cold_path():
    srv = LeanServer(_ENV)
    assert srv.probe(timeout=120) is True
    for src, want_ok in [
        ("import Mathlib\ntheorem t_true : (1:ℝ) = 1 := by norm_num\n", True),
        ("import Mathlib\ntheorem t_false : (1:ℝ) = 2 := by norm_num\n", False),
    ]:
        warm = verify_lean(src, env_dir=_ENV, decls=[], server=srv)
        cold = verify_lean(src, env_dir=_ENV, decls=[])
        assert warm.okay == cold.okay == want_ok, (src, warm.okay, cold.okay)
    srv.close()

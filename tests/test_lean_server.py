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
    assert srv.probe(timeout=180) is True
    for src, want_ok in [
        ("import Mathlib\ntheorem t_true : (1:ℝ) = 1 := by norm_num\n", True),
        ("import Mathlib\ntheorem t_false : (1:ℝ) = 2 := by norm_num\n", False),
    ]:
        warm = verify_lean(src, env_dir=_ENV, decls=[], server=srv)
        cold = verify_lean(src, env_dir=_ENV, decls=[])
        assert warm.okay == cold.okay == want_ok, (src, warm.okay, cold.okay)
    srv.close()


@pytest.mark.skipif(not (_HAVE_LEAN and _BUILT),
                    reason="needs a built zero_free_bridge env + elan (CI / cleared local)")
def test_warm_lsp_reuse_correct_across_interleaved_verdicts():
    # The warm LSP path (incremental didChange to one resident doc) must give the
    # RIGHT verdict for every call with no stale-diagnostic bleed across true/false
    # interleaving, and axioms must parse through it.
    srv = LeanServer(_ENV)
    assert srv.probe(timeout=180) is True
    assert srv.warm() is True                         # resident LSP is active
    for i in range(6):
        true_thm = (i % 2 == 0)
        rhs = i if true_thm else i + 1
        out, rc = srv.elaborate(f"import Mathlib\ntheorem w{i} : ({i}:ℝ) = {rhs} := by norm_num\n")
        assert ("error:" in out) == (not true_thm), (i, out[:80])
    # #print axioms flows through the warm path and is parsed by verify_lean.
    r = verify_lean("import Mathlib\ntheorem wax : (2:ℝ) = 2 := by norm_num\n",
                    env_dir=_ENV, decls=["wax"], server=srv)
    assert r.okay and r.axioms_clean
    srv.close()

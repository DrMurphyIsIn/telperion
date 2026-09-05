"""Signature / statement-match gate — the positive half of the trust boundary.

`verify` certifies a proof compiles + is axiom-clean; `negative_control` certifies a
FALSE instance is rejected; neither certifies the TRUE instance states the INTENDED
proposition.  These tests pin that `statement_match_check` catches a WEAKENED theorem
(the AXLE `verify_proof` signature check, `use_def_eq=False`) and accepts an exact
match, and that `def_identity_check` catches a def whose body diverges from intent.
Kernel-backed (needs a built env); guarded to skip cleanly when no env is present.
conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from telperion.statement_match import (  # noqa: E402
    statement_match_check, def_identity_check,
)
from lean_env import lean_env_ready  # noqa: E402

_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"
# A checked-in lake-manifest.json is NOT proof the env is usable: the runner also
# needs `lake` on PATH and a built Mathlib cache. `lean_env_ready` checks both, so
# this suite skips cleanly on the no-toolchain unit job (and never rebuilds).
_HAS_ENV = lean_env_ready(_ENV)
pytestmark = pytest.mark.skipif(not _HAS_ENV, reason="needs a built Lean env (lake + Mathlib)")


def test_signature_gate_catches_weakening():
    # foo proves `0 ≤ x²+1`; bar proves `0 ≤ x²`.
    prelude = ("theorem foo (x : ℝ) : 0 ≤ x^2 + 1 := by positivity\n"
               "theorem bar (x : ℝ) : 0 ≤ x^2 := by positivity")
    res = statement_match_check(
        intended={
            "foo": "∀ (x : ℝ), 0 ≤ x^2 + x + 1",   # STRONGER than foo proves -> MISMATCH
            "bar": "∀ (x : ℝ), 0 ≤ x^2",            # exactly what bar proves -> MATCH
        },
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude,
    )
    assert not res.all_match
    assert res.matched == ["bar"]
    assert "foo" in res.mismatched


def test_signature_gate_accepts_exact():
    prelude = "theorem exact_thm (x : ℝ) : 0 ≤ x^2 + 1 := by positivity"
    res = statement_match_check(
        intended={"exact_thm": "∀ (x : ℝ), 0 ≤ x^2 + 1"},
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude,
    )
    assert res.all_match and res.matched == ["exact_thm"]


def test_batch_fast_path_all_match():
    # two exact matches -> the batched path (one Mathlib load) returns all_match.
    prelude = ("theorem a1 (x : ℝ) : 0 ≤ x^2 := by positivity\n"
               "theorem a2 (x : ℝ) : 0 ≤ x^2 + 1 := by positivity")
    res = statement_match_check(
        intended={"a1": "∀ (x : ℝ), 0 ≤ x^2", "a2": "∀ (x : ℝ), 0 ≤ x^2 + 1"},
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude, batch=True)
    assert res.all_match and set(res.matched) == {"a1", "a2"}


def test_def_identity_catches_divergence():
    prelude = "def myprop (x : ℝ) : Prop := 0 ≤ x^2 + 1"
    # correct body -> MATCH
    ok, _ = def_identity_check(
        "myprop", "(x : ℝ)", "0 ≤ x^2 + 1",
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude)
    assert ok
    # wrong body -> MISMATCH
    bad, _ = def_identity_check(
        "myprop", "(x : ℝ)", "0 ≤ x^2",
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude)
    assert not bad

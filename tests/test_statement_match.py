"""Signature / statement-match gate — the positive half of the trust boundary.

`verify` certifies a proof compiles + is axiom-clean; `negative_control` certifies a
FALSE instance is rejected; neither certifies the TRUE instance states the INTENDED
proposition.  These tests pin that `statement_match_check` catches a WEAKENED theorem
(the AXLE `verify_proof` signature check, `use_def_eq=False`) and accepts an exact
match, and that `def_identity_check` catches a def whose body diverges from intent.
Kernel-backed (needs a built env); guarded to skip cleanly when no env is present.
conjecture1_proved = False.

Also tests `statement_match_example` -- a text-generation utility that emits a
kernel-enforced `example : <type> := <theorem_name>` snippet.  The type ascription
must be defeq to the theorem's type or the Lean build fails; this is the statement-drift
guard wired into BoxRobustEmitter.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.statement_match import (  # noqa: E402
    statement_match_check, def_identity_check, statement_match_example,
)

_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"
_HAS_ENV = (_ENV / "lake-manifest.json").exists()
_needs_env = pytest.mark.skipif(not _HAS_ENV, reason="needs a built Lean env")


# ---------------------------------------------------------------------------
# Pure Python tests for statement_match_example (no Lean env required)
# ---------------------------------------------------------------------------

def test_gate_text_shape():
    g = statement_match_example("my_thm", "forall x : R, 0 <= x^2")
    assert g.strip() == "example : forall x : R, 0 <= x^2 := my_thm"


def test_gate_uses_exact_type():
    # the ascribed type must be exactly what is passed (no truncation/normalization)
    t = "(A -> B -> C)"
    assert t in statement_match_example("t", t)


# ---------------------------------------------------------------------------
# Kernel-backed tests (require a built Lean env)
# ---------------------------------------------------------------------------

@_needs_env
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


@_needs_env
def test_signature_gate_accepts_exact():
    prelude = "theorem exact_thm (x : ℝ) : 0 ≤ x^2 + 1 := by positivity"
    res = statement_match_check(
        intended={"exact_thm": "∀ (x : ℝ), 0 ≤ x^2 + 1"},
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude,
    )
    assert res.all_match and res.matched == ["exact_thm"]


@_needs_env
def test_batch_fast_path_all_match():
    # two exact matches -> the batched path (one Mathlib load) returns all_match.
    prelude = ("theorem a1 (x : ℝ) : 0 ≤ x^2 := by positivity\n"
               "theorem a2 (x : ℝ) : 0 ≤ x^2 + 1 := by positivity")
    res = statement_match_check(
        intended={"a1": "∀ (x : ℝ), 0 ≤ x^2", "a2": "∀ (x : ℝ), 0 ≤ x^2 + 1"},
        env_dir=str(_ENV), imports=("import Mathlib",), prelude=prelude, batch=True)
    assert res.all_match and set(res.matched) == {"a1", "a2"}


@_needs_env
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

"""Tests for the mechanical, verify-guarded proof minimizer (``telperion.simplify``).

Two layers, mirroring ``test_repair.py`` / ``test_verify.py``:

  * OFFLINE unit tests (no Lean invoked) for the pure text machinery -- named
    ``have`` detection, block-extent computation, the conservative word-boundary
    reference check, and the unused-candidate selection.  These are the safety
    core: a wrong reference check would delete a still-used ``have``.
  * A GUARDED Lean end-to-end test (skipped unless ``lean_env_ready`` says the
    ``examples/log_combination/lean`` Mathlib env is built) that feeds a proof
    carrying a genuinely-unused ``have`` to :func:`simplify_proof` and asserts the
    ``have`` is removed AND the result still verifies (kernel-green, axioms-clean),
    plus the rollback guarantee: a proof whose ``have`` LOOKS unused but is needed
    from context is returned UNCHANGED.

conjecture1_proved = False.
"""
from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # noqa: E402
from lean_env import lean_env_ready  # noqa: E402

# This test drives `simplify_proof`, which shells out to `lake env lean` to decide
# verifiability — it needs the `lake` binary (but NOT a built Mathlib, since it runs
# against an empty tmp env). Skip cleanly when no toolchain is present.
_HAVE_LAKE = shutil.which("lake") is not None or (Path.home() / ".elan" / "bin" / "lake").exists()

from telperion.simplify import (  # noqa: E402
    HaveStep,
    SimplifyResult,
    SimplifyStep,
    find_have_steps,
    remove_unused_haves,
    simplify_proof,
    unused_have_steps,
)
from telperion.simplify import _referenced, _delete_step, _leading_width  # noqa: E402


EXAMPLE_ENV = (Path(__file__).resolve().parents[1]
               / "examples" / "log_combination" / "lean")


# --------------------------------------------------------------------------- #
# Reference check (the safety core).                                          #
# --------------------------------------------------------------------------- #

def test_referenced_whole_token():
    assert _referenced("key", "linarith [key]") is True
    assert _referenced("key", "exact key.mp h") is True


def test_referenced_not_substring_of_longer_ident():
    # `h` must NOT match inside `h2`, `hpos`, etc.
    assert _referenced("h", "rw [h2] at hpos") is False
    # `e1` must NOT match inside `e10`.
    assert _referenced("e1", "rw [e10] at hle") is False


def test_referenced_ignores_trailing_prime():
    # Lean identifiers may carry a trailing prime; `hpos` != `hpos'`.
    assert _referenced("hpos", "have hpos' := foo") is False
    assert _referenced("hpos", "exact hpos'") is False


def test_referenced_absent():
    assert _referenced("ghost", "linarith") is False


# --------------------------------------------------------------------------- #
# have detection + block extent.                                             #
# --------------------------------------------------------------------------- #

def test_find_single_flat_have():
    proof = (
        "theorem foo : (2:Nat) = 2 := by\n"
        "  have dead : (1:Nat) = 1 := rfl\n"
        "  rfl\n"
    )
    steps = find_have_steps(proof)
    assert len(steps) == 1
    st = steps[0]
    assert st.name == "dead"
    assert st.start_line == 1
    assert st.end_line == 2       # single-line step: [1, 2)
    assert st.indent == 2


def test_find_multiline_by_block_have_extent():
    # A `have h : T := by <block>` spans the header + the deeper-indented block,
    # and ends at the next sibling tactic at the SAME indent.
    proof = (
        "theorem foo : True := by\n"
        "  have key : True := by\n"
        "    trivial\n"
        "  trivial\n"
    )
    steps = find_have_steps(proof)
    assert len(steps) == 1
    st = steps[0]
    assert st.name == "key"
    assert st.start_line == 1
    assert st.end_line == 3       # header (1) + block body (2) -> [1, 3)


def test_find_multiline_type_signature_have():
    # A `have` whose TYPE wraps onto a continuation line (deeper indent) is one step.
    proof = (
        "theorem foo : True := by\n"
        "  have hsplit : a\n"
        "      = b := by\n"
        "    trivial\n"
        "  trivial\n"
    )
    steps = find_have_steps(proof)
    assert len(steps) == 1
    assert steps[0].name == "hsplit"
    assert steps[0].start_line == 1
    assert steps[0].end_line == 4  # lines 1,2,3 belong; line 4 is the sibling


def test_anonymous_have_is_not_detected():
    # `have : T := ...` (no name) is deliberately never a candidate.
    proof = (
        "theorem foo : True := by\n"
        "  have : True := trivial\n"
        "  exact this\n"
    )
    assert find_have_steps(proof) == []


def test_nested_have_is_covered_by_outer_block():
    # The top-level scan treats the outer `have key` block as one unit; the inner
    # e1/e2 haves live inside it and are not surfaced as separate top-level steps.
    proof = (
        "theorem foo : True := by\n"
        "  have key : True := by\n"
        "    have e1 : True := trivial\n"
        "    exact e1\n"
        "  exact key\n"
    )
    steps = find_have_steps(proof)
    assert [s.name for s in steps] == ["key"]
    assert steps[0].end_line == 4  # covers the nested e1 line


# --------------------------------------------------------------------------- #
# unused-candidate selection.                                                 #
# --------------------------------------------------------------------------- #

def test_unused_have_when_name_never_referenced_later():
    proof = (
        "theorem foo : (2:Nat) = 2 := by\n"
        "  have dead : (1:Nat) = 1 := rfl\n"
        "  rfl\n"
    )
    assert [s.name for s in unused_have_steps(proof)] == ["dead"]


def test_used_have_is_not_a_candidate():
    proof = (
        "theorem foo : (2:Nat) = 2 := by\n"
        "  have live : (2:Nat) = 2 := rfl\n"
        "  exact live\n"
    )
    assert unused_have_steps(proof) == []


def test_reference_only_before_step_does_not_count():
    # A textual occurrence BEFORE the step's own binding is not a use of it (have
    # binds forward); the later region is what determines use.
    proof = (
        "theorem foo : True := by\n"
        "  have hx : True := trivial\n"       # binds hx
        "  have hy : True := trivial\n"       # hy never used later -> candidate
        "  exact hx\n"
    )
    names = [s.name for s in unused_have_steps(proof)]
    assert "hy" in names
    assert "hx" not in names   # hx IS used later


def test_delete_step_removes_exact_range():
    proof = (
        "theorem foo : True := by\n"
        "  have dead : True := trivial\n"
        "  trivial\n"
    )
    lines = proof.splitlines()
    step = unused_have_steps(proof)[0]
    out = "\n".join(_delete_step(lines, step))
    assert "dead" not in out
    assert out == "theorem foo : True := by\n  trivial"


def test_leading_width():
    assert _leading_width("    x") == 4
    assert _leading_width("x") == 0
    assert _leading_width("\t x") == 2


# --------------------------------------------------------------------------- #
# offline behaviour of simplify_proof / remove_unused_haves without a build.  #
# (verify_lean will fail against a bare tmp env, so the guard returns input    #
#  unchanged -- this exercises the "input does not verify -> no-op" branch.)   #
# --------------------------------------------------------------------------- #

@pytest.mark.skipif(not _HAVE_LAKE, reason="needs the lake toolchain to run the verifier")
def test_simplify_returns_input_unchanged_when_not_verifiable(tmp_path):
    # Content that does NOT verify (an unknown identifier) must be a strict no-op:
    # the minimizer never attempts a deletion on a proof it cannot first confirm
    # passing, so it can never return a version that does not verify.
    proof = (
        "theorem foo : True := by\n"
        "  have dead : True := this_identifier_does_not_exist\n"
        "  trivial\n"
    )
    res = simplify_proof(proof, env_dir=tmp_path, decls=["foo"])
    assert isinstance(res, SimplifyResult)
    assert res.applied == []
    assert res.content == proof
    assert res.changed is False
    assert res.result is not None and res.result.okay is False


# --------------------------------------------------------------------------- #
# Guarded Lean end-to-end.                                                     #
# --------------------------------------------------------------------------- #

def _skip_unless_env():
    if not lean_env_ready(EXAMPLE_ENV):
        pytest.skip("log_combination Mathlib env not built (guard prevents rebuild)")


def test_e2e_removes_genuinely_unused_have_and_still_verifies():
    _skip_unless_env()
    # A true theorem with a genuinely-DEAD `have` (dead_fact used nowhere): the
    # minimizer must delete it and the result must still verify axioms-clean.
    src = (
        "import Mathlib\n"
        "theorem simp_probe : (1 : Real) = 1 := by\n"
        "  have dead_fact : (2 : Real) = 2 := by norm_num\n"
        "  norm_num\n"
    )
    res = simplify_proof(src, env_dir=EXAMPLE_ENV, decls=["simp_probe"])
    assert res.changed is True, res.summary()
    assert [s.name for s in res.applied] == ["dead_fact"]
    assert "dead_fact" not in res.content
    assert res.result is not None
    assert res.result.okay and res.result.axioms_clean, res.result.summary()


def test_e2e_keeps_context_used_have_via_rollback():
    _skip_unless_env()
    # `hkey` LOOKS unused textually (name not referenced by the final `linarith`),
    # but `linarith` consumes it from context -- deleting it BREAKS the proof (the
    # bound `x < 2` is derived from the NON-linear `hsq : x^2 = 1, hpos : 0 < x`
    # that linarith alone cannot use), so the verify-guard must ROLL BACK and
    # return the proof unchanged.
    src = (
        "import Mathlib\n"
        "theorem simp_ctx (x : Real) (hpos : 0 < x) (hsq : x ^ 2 = 1) : x < 3 := by\n"
        "  have hkey : x < 2 := by nlinarith [hsq, hpos]\n"
        "  linarith\n"
    )
    res = simplify_proof(src, env_dir=EXAMPLE_ENV, decls=["simp_ctx"])
    assert res.applied == [], res.summary()
    assert "hkey" in res.content
    assert res.result is not None
    assert res.result.okay and res.result.axioms_clean, res.result.summary()


def test_e2e_noop_on_already_minimal_proof():
    _skip_unless_env()
    src = (
        "import Mathlib\n"
        "theorem simp_min : (1 : Real) = 1 := by norm_num\n"
    )
    res = simplify_proof(src, env_dir=EXAMPLE_ENV, decls=["simp_min"])
    assert res.applied == []
    assert res.result is not None and res.result.okay and res.result.axioms_clean


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))

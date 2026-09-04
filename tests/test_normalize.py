"""Canonical-form + proof-blanking utilities (the AXLE ``normalize`` +
``theorem2sorry`` lesson).

Pure-text tests, no Lean build needed:

* :func:`normalize_lean` collapses blank-line runs, strips trailing whitespace,
  and ends the file with exactly one newline -- and is idempotent.
* :func:`canonical_statement` maps cosmetically-different-but-equal statements to
  the same key, and a genuinely different statement to a different key.
* :func:`theorem2sorry` blanks a named proof to ``:= by sorry`` (term mode ->
  ``:= sorry``), leaves non-named theorems untouched, and round-trips with
  ``gap_fill.extract_gaps``.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.normalize import (  # noqa: E402
    normalize_lean, canonical_statement, theorem2sorry,
)


def test_normalize_lean_whitespace_and_blank_lines():
    raw = (
        "theorem foo : T := by\n"
        "    norm_num   \n"      # trailing whitespace
        "\n"
        "\n"
        "\n"                       # triple blank run
        "theorem bar : U := by rfl\t\n"  # trailing tab
    )
    out = normalize_lean(raw)
    lines = out.split("\n")
    # No trailing whitespace on any line.
    assert all(ln == ln.rstrip() for ln in lines)
    # Blank runs collapsed to at most one blank line.
    assert "\n\n\n" not in out
    assert "\n\n" in out  # the single surviving blank line
    # Exactly one final newline.
    assert out.endswith("\n") and not out.endswith("\n\n")


def test_normalize_lean_is_idempotent():
    raw = "  a  \n\n\n\n  b  \n\n\n"
    once = normalize_lean(raw)
    assert normalize_lean(once) == once


def test_normalize_lean_preserves_token_content():
    # Interior tokens (the `(7/4 : ℝ)` ascription) must be untouched.
    raw = "theorem t : Real.log (7/4 : ℝ) ≤ 4 * FSTAR := by sorry\n"
    assert normalize_lean(raw) == "theorem t : Real.log (7/4 : ℝ) ≤ 4 * FSTAR := by sorry\n"


def test_canonical_statement_equates_cosmetic_variants():
    a = canonical_statement("Real.log (7/4 : ℝ)  ≤  4 * FSTAR")
    b = canonical_statement("Real.log (7/4) ≤ 4*FSTAR")
    assert a == b, (a, b)


def test_canonical_statement_distinguishes_different_statements():
    a = canonical_statement("Real.log (7/4 : ℝ) ≤ 4 * FSTAR")
    c = canonical_statement("Real.log (5/4 : ℝ) ≤ 4 * FSTAR")
    assert a != c


def test_theorem2sorry_blanks_named_tactic_proof():
    x = "theorem foo : (1:ℝ)=1 := by norm_num\n"
    out = theorem2sorry(x, names=["foo"])
    assert out == "theorem foo : (1:ℝ)=1 := by sorry\n", repr(out)


def test_theorem2sorry_leaves_unnamed_theorems_untouched():
    content = (
        "theorem foo : (1:ℝ)=1 := by norm_num\n"
        "theorem bar : (2:ℝ)=2 := by norm_num\n"
    )
    out = theorem2sorry(content, names=["foo"])
    assert "theorem foo : (1:ℝ)=1 := by sorry" in out
    # bar is untouched.
    assert "theorem bar : (2:ℝ)=2 := by norm_num" in out
    assert out.count("sorry") == 1


def test_theorem2sorry_term_mode():
    x = "theorem foo : Nat := 3\n"
    out = theorem2sorry(x, names=["foo"])
    assert out == "theorem foo : Nat := sorry\n", repr(out)


def test_theorem2sorry_round_trips_with_extract_gaps():
    from telperion.gap_fill import extract_gaps
    x = "theorem log74_le_4fstar : Real.log (7/4 : ℝ) ≤ 4 * FSTAR := by monotone_tac\n"
    blanked = theorem2sorry(x, names=["log74_le_4fstar"])
    gaps = extract_gaps(blanked)
    assert {g.name for g in gaps} == {"log74_le_4fstar"}, gaps

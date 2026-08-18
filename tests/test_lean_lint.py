"""Tests for the soundness/honesty Lean lint (complements test_lint.py)."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.lean_lint import (  # noqa: E402
    LeanLintError,
    LeanLintIssue,
    check_lean_text,
    lint_lean_file,
    lint_lean_text,
)

HEADER = "/- telperion 0.1.3 | test -/\nimport Mathlib\n\n"


def codes(issues):
    return {i.code for i in issues}


def test_clean_theorem_passes():
    text = HEADER + "theorem good : (2 : ℤ) = 2 := by norm_num\n"
    issues = lint_lean_text(text)
    assert issues == []
    check_lean_text(text)  # no raise


def test_sorry_body_is_error():
    text = HEADER + "theorem bad : 1 = 1 := by sorry\n"
    issues = lint_lean_text(text)
    assert "SORRY" in codes(issues)
    assert any(i.severity == "error" for i in issues if i.code == "SORRY")


def test_admit_is_error():
    text = HEADER + "theorem bad : 1 = 1 := by admit\n"
    assert "SORRY" in codes(lint_lean_text(text))


def test_axiom_is_error():
    text = HEADER + "axiom cheat : 1 = 2\n"
    issues = lint_lean_text(text)
    assert "AXIOM" in codes(issues)
    assert all(i.severity == "error" for i in issues if i.code == "AXIOM")


def test_trivial_stub_is_warn():
    text = HEADER + "theorem foo : True := trivial\n"
    issues = lint_lean_text(text)
    stubs = [i for i in issues if i.code == "TRIVIAL_STUB"]
    assert stubs and stubs[0].severity == "warn"


def test_prop_placeholder_is_warn():
    text = HEADER + "theorem placeholder : Prop := by trivial\n"
    assert "TRIVIAL_STUB" in codes(lint_lean_text(text))


def test_sorry_in_line_comment_not_flagged():
    text = HEADER + "-- this proof avoids sorry entirely\ntheorem ok : 1 = 1 := rfl\n"
    assert "SORRY" not in codes(lint_lean_text(text))


def test_sorry_in_block_comment_not_flagged():
    text = HEADER + "/- earlier we had a sorry here -/\ntheorem ok : 1 = 1 := rfl\n"
    assert "SORRY" not in codes(lint_lean_text(text))


def test_missing_ascription_is_error():
    text = HEADER + "theorem noty := (5 : ℤ)\n"
    issues = lint_lean_text(text)
    assert "NO_ASCRIPTION" in codes(issues)
    assert all(i.severity == "error" for i in issues if i.code == "NO_ASCRIPTION")


def test_ascription_with_binder_colon_not_confused():
    # colon inside binder parens is NOT a top-level ascription -> flagged
    text = HEADER + "theorem b (n : Nat) := n\n"
    assert "NO_ASCRIPTION" in codes(lint_lean_text(text))
    # but with a real ascription it passes the ascription check
    text2 = HEADER + "theorem b (n : Nat) : n = n := rfl\n"
    assert "NO_ASCRIPTION" not in codes(lint_lean_text(text2))


def test_empty_tactic_is_error():
    text = HEADER + "theorem empty : 1 = 1 := by\n"
    issues = lint_lean_text(text)
    assert "EMPTY_TACTIC" in codes(issues)


def test_check_raises_on_error():
    text = HEADER + "theorem bad : 1 = 1 := by sorry\n"
    with pytest.raises(LeanLintError):
        check_lean_text(text)


def test_check_does_not_raise_on_warn_by_default():
    text = HEADER + "theorem foo : True := trivial\n"
    check_lean_text(text)  # warn only -> no raise


def test_check_raises_on_warn_when_strict():
    text = HEADER + "theorem foo : True := trivial\n"
    with pytest.raises(LeanLintError):
        check_lean_text(text, strict=True)


def test_issue_dataclass_frozen():
    i = LeanLintIssue(line=1, code="SORRY", severity="error", message="x")
    with pytest.raises(Exception):
        i.line = 2  # type: ignore[misc]


def test_lint_lean_file(tmp_path):
    p = tmp_path / "Bad.lean"
    p.write_text(HEADER + "theorem bad : 1 = 1 := by sorry\n", encoding="utf-8")
    issues = lint_lean_file(p)
    assert "SORRY" in codes(issues)

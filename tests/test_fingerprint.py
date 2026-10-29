import os
from pathlib import Path
import pytest
from telperion.checks.fingerprint import parse_fingerprints, render_fingerprint_script


def test_parse():
    out = "noise\nFP-BEGIN foo\n∀ (_ : Nat), ...\nFP-END foo\nFP-BEGIN bar\nX\nFP-END bar\n"
    fp = parse_fingerprints(out)
    assert set(fp) == {"foo", "bar"} and len(fp["foo"]) == 64 and fp["foo"] != fp["bar"]


def test_parse_missing_target_raises():
    with pytest.raises(ValueError, match="baz"):
        parse_fingerprints("FP-MISSING baz\n")


def test_render_mentions_targets_and_roots():
    s = render_fingerprint_script(["Mathlib"], ["foo"])
    assert "`foo" in s and "deltaExpand" in s and "`Mathlib" in s


LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set")


def _fp(tmp_text: str, target: str) -> str:
    from telperion.checks.fingerprint import run_fingerprint_on_text
    return run_fingerprint_on_text(Path(LEAN_ENV), tmp_text, target)


@lean
def test_shadowed_definition_changes_hash():                 # MUST-FAIL control
    a = "import Mathlib\ndef bound : ℕ := 5\ntheorem t : ∀ n : ℕ, n < bound → n < 10 := by intro n h; unfold bound at h; omega\n"
    b = a.replace(":= 5", ":= 6")
    assert _fp(a, "t") != _fp(b, "t")


@lean
def test_binder_rename_same_hash():                          # MUST-PASS control
    a = "import Mathlib\ntheorem t : ∀ n : ℕ, n < 3 → n < 10 := by omega\n"
    b = a.replace("∀ n : ℕ, n < 3 → n < 10", "∀ m : ℕ, m < 3 → m < 10")
    assert _fp(a, "t") == _fp(b, "t")


@lean
def test_argument_swap_changes_hash():                       # MUST-FAIL control
    # erased binders are re-freshened by the delaborator (`_`, `__1`); distinct bound variables must stay distinct
    a = "import Mathlib\ntheorem t : ∀ a b : ℕ, a ≤ a + b := by omega\n"
    b = a.replace("a ≤ a + b", "b ≤ a + b")
    assert _fp(a, "t") != _fp(b, "t")


# Beyond the brief: pp.all does not lift pp.maxSteps, so an elided `⋯` must never be hashed.
def test_parse_elided_statement_raises():
    with pytest.raises(ValueError, match="elided"):
        parse_fingerprints("FP-BEGIN foo\n∀ (_ : Nat), ⋯\nFP-END foo\n")


def test_parse_unterminated_block_raises():
    with pytest.raises(ValueError, match="foo"):
        parse_fingerprints("FP-BEGIN foo\nX\n")


def test_render_lifts_max_steps_and_places_body():
    s = render_fingerprint_script(["Mathlib"], ["t"], body="def bound : ℕ := 5")
    assert "pp.maxSteps" in s
    assert s.index("import Mathlib") < s.index("import Lean") < s.index("def bound") < s.index("#eval")


def test_cli_prints_hashes_and_exits_2_on_missing(monkeypatch, capsys):
    from telperion import cli
    from telperion.checks import fingerprint as fp_
    monkeypatch.setattr(fp_, "run_fingerprint", lambda project, imports, targets, wrapper=None, timeout=0:
                        {t: "a" * 64 for t in targets})
    assert cli.main(["fingerprint", "--project", ".", "--import", "Mathlib", "--target", "foo", "--target", "bar"]) == 0
    assert capsys.readouterr().out == f"foo {'a' * 64}\nbar {'a' * 64}\n"

    def missing(project, imports, targets, wrapper=None, timeout=0):
        raise ValueError("target not found: baz")
    monkeypatch.setattr(fp_, "run_fingerprint", missing)
    assert cli.main(["fingerprint", "--project", ".", "--import", "Mathlib", "--target", "baz"]) == 2
    assert "baz" in capsys.readouterr().out

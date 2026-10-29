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


# Fix round 1 (Ruling 6): structural serialization; refuse what deltaExpand cannot unfold.
def test_parse_refused_raises():
    with pytest.raises(ValueError, match="refused.*t Good inductive"):
        parse_fingerprints("FP-REFUSED t Good inductive\n")


def test_parse_empty_serialization_raises():
    with pytest.raises(ValueError, match="empty"):
        parse_fingerprints("FP-BEGIN foo\n\nFP-END foo\n")


def test_parse_hashes_ellipsis_in_string_literal():
    # the old ⋯ guard is gone: a structural serialization never elides, and `⋯` may sit in a string literal
    assert len(parse_fingerprints('FP-BEGIN foo\n(str "⋯")\nFP-END foo\n')["foo"]) == 64


def test_parse_unterminated_block_raises():
    with pytest.raises(ValueError, match="foo"):
        parse_fingerprints("FP-BEGIN foo\nX\n")


def test_render_is_structural_and_places_body():
    s = render_fingerprint_script(["Mathlib"], ["t"], body="def bound : ℕ := 5")
    assert "ppExpr" not in s and "pp.all" not in s and "tpSer" in s and "FP-REFUSED" in s
    assert s.index("import Mathlib") < s.index("import Lean") < s.index("def bound") < s.index("#eval")


@pytest.mark.parametrize("spoof", ["Mathlib/Foo.lean", "src/Lean/Bar.lean", "Std.lean"])
def test_library_root_spoof_refused(tmp_path, spoof):
    from telperion.checks.fingerprint import run_fingerprint, run_fingerprint_on_text
    f = tmp_path / spoof
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text("def bound : Nat := 5\n", encoding="utf-8")
    root = spoof.replace(".lean", "").split("/")[-2 if "/" in spoof else 0]
    with pytest.raises(ValueError, match=f"library root.*{root}"):
        run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=["false"])
    with pytest.raises(ValueError, match=f"library root.*{root}"):
        run_fingerprint_on_text(tmp_path, "import Mathlib\ntheorem t : True := trivial\n", "t", wrapper=["false"])
    assert not (tmp_path / ".telperion_fingerprint").exists()


def test_spoof_check_ignores_lake_packages(tmp_path):
    from telperion.checks.fingerprint import run_fingerprint
    (tmp_path / ".lake/packages/mathlib/Mathlib").mkdir(parents=True)
    (tmp_path / ".lake/packages/mathlib/Mathlib/Foo.lean").write_text("", encoding="utf-8")
    with pytest.raises(ValueError, match="lean exited"):        # passes the spoof check, then `false` fails
        run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=["false"])


def test_escaped_target_key_is_found(monkeypatch, tmp_path):
    # Lean prints `«my thm»`; the caller passes `my thm`
    from telperion.checks import fingerprint as fp_
    out = "FP-BEGIN «my thm»\n(c _.\"True\" [])\nFP-END «my thm»\n"

    class P:
        returncode, stdout, stderr = 0, out, ""
    monkeypatch.setattr(fp_.subprocess, "run", lambda *a, **k: P)
    assert len(fp_.run_fingerprint(tmp_path, ["Mathlib"], ["my thm"], wrapper=[])["my thm"]) == 64


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


# Fix round 1 Lean controls. MUST-FAIL: non-def local constants are refused, never hashed by name.
def _refused(text: str, what: str):
    with pytest.raises(ValueError, match=f"refused.*{what}"):
        _fp(text, "t")


@lean
def test_local_inductive_refused():                          # MUST-FAIL control
    _refused("import Mathlib\ninductive Good : ℕ → Prop\n  | mk : Good 5\ntheorem t : Good 5 := .mk\n", "Good inductive")


@lean
def test_local_structure_refused():                          # MUST-FAIL control
    _refused("import Mathlib\nstructure Box where\n  val : ℕ\ntheorem t : ∀ b : Box, b.val = b.val := fun _ => rfl\n",
             "Box inductive")


@lean
def test_irreducible_def_refused():                          # MUST-FAIL control
    _refused("import Mathlib\nirreducible_def ibound : ℕ := 5\ntheorem t : ∀ n : ℕ, n < ibound → n < ibound := fun _ h => h\n",
             "ibound")


@lean
def test_nat_vs_int_differ_under_pp_explicit_false():        # MUST-FAIL control
    a = "import Mathlib\nset_option pp.explicit false\nset_option pp.all false\ntheorem t : (2 : ℕ) = 2 := rfl\n"
    assert _fp(a, "t") != _fp(a.replace("ℕ", "ℤ"), "t")


@lean
def test_universe_param_rename_same_hash():                  # MUST-PASS control
    a = "import Mathlib\ntheorem t.{u} {α : Sort u} (a : α) : a = a := rfl\n"
    b = a.replace(".{u}", ".{v}").replace("Sort u", "Sort v")
    assert _fp(a, "t") == _fp(b, "t")


@lean
def test_quoted_target_name():                               # MUST-PASS control
    assert len(_fp("import Mathlib\ntheorem «my thm» : True := trivial\n", "my thm")) == 64

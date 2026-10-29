import os
import re
import subprocess
import time
from pathlib import Path
import pytest
from telperion.checks.fingerprint import parse_fingerprints, render_fingerprint_script

N = "0123456789abcdef" * 2      # a fixed nonce for the pure parser tests


def test_parse():
    out = (f"noise\nFP-BEGIN {N} foo\n∀ (_ : Nat), ...\nFP-END {N} foo\nFP-BEGIN {N} bar\nX\nFP-END {N} bar\n"
           f"FP-DONE {N}\n")
    fp = parse_fingerprints(out, N)
    assert set(fp) == {"foo", "bar"} and len(fp["foo"]) == 64 and fp["foo"] != fp["bar"]


def test_parse_missing_target_raises():
    with pytest.raises(ValueError, match="baz"):
        parse_fingerprints(f"FP-MISSING {N} baz\nFP-DONE {N}\n", N)


def test_render_mentions_targets_and_roots():
    s = render_fingerprint_script(["Mathlib"], ["foo"])
    assert "`foo" in s and "deltaExpand" in s and "`Mathlib" in s


LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set")


def _fp(tmp_text: str, target: str, **kw) -> str:
    from telperion.checks.fingerprint import run_fingerprint_on_text
    return run_fingerprint_on_text(Path(LEAN_ENV), tmp_text, target, **kw)


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
    a = "import Mathlib\ntheorem t : ∀ a b : ℕ, a ≤ a + b := by omega\n"
    b = a.replace("a ≤ a + b", "b ≤ a + b")
    assert _fp(a, "t") != _fp(b, "t")


# Fix round 1 (Ruling 6): structural serialization; refuse what deltaExpand cannot unfold.
def test_parse_refused_raises():
    with pytest.raises(ValueError, match="refused.*t Good inductive"):
        parse_fingerprints(f"FP-REFUSED {N} t Good inductive\nFP-DONE {N}\n", N)


def test_parse_empty_serialization_raises():
    with pytest.raises(ValueError, match="empty"):
        parse_fingerprints(f"FP-BEGIN {N} foo\n\nFP-END {N} foo\nFP-DONE {N}\n", N)


def test_parse_hashes_ellipsis_in_string_literal():
    assert len(parse_fingerprints(f'FP-BEGIN {N} foo\n(str "⋯")\nFP-END {N} foo\nFP-DONE {N}\n', N)["foo"]) == 64


def test_parse_unterminated_block_raises():
    with pytest.raises(ValueError, match="foo"):
        parse_fingerprints(f"FP-BEGIN {N} foo\nX\nFP-DONE {N}\n", N)


# Fix round 2 (C1): every marker carries the run's nonce; one result per target; a final FP-DONE.
def test_parse_wrong_nonce_raises():
    other = "f" * 32
    with pytest.raises(ValueError, match="nonce"):
        parse_fingerprints(f"FP-BEGIN {other} t\nX\nFP-END {other} t\nFP-BEGIN {N} t\nY\nFP-END {N} t\nFP-DONE {N}\n", N)


def test_parse_marker_without_nonce_raises():
    with pytest.raises(ValueError, match="nonce"):
        parse_fingerprints(f"FP-BEGIN t\nX\nFP-END t\nFP-DONE {N}\n", N)


def test_parse_duplicate_block_raises():
    with pytest.raises(ValueError, match="duplicate.*t"):
        parse_fingerprints(f"FP-BEGIN {N} t\nX\nFP-END {N} t\nFP-BEGIN {N} t\nY\nFP-END {N} t\nFP-DONE {N}\n", N)


def test_parse_missing_done_raises():
    with pytest.raises(ValueError, match="FP-DONE"):
        parse_fingerprints(f"FP-BEGIN {N} t\nX\nFP-END {N} t\n", N)


def test_parse_marker_after_done_raises():
    with pytest.raises(ValueError, match="FP-DONE"):
        parse_fingerprints(f"FP-DONE {N}\nFP-BEGIN {N} t\nX\nFP-END {N} t\nFP-DONE {N}\n", N)


def test_render_is_structural_and_imports_programmatically():
    s = render_fingerprint_script(["Mathlib"], ["t"], nonce=N, trusted=["/opt/lib/lean"], search=["/x/build"])
    assert "ppExpr" not in s and "pp.all" not in s and "tpSer" in s and "FP-REFUSED" in s
    assert s.splitlines()[0] == "import Lean" and "\nimport Mathlib" not in s     # imports are loaded in the #eval
    assert "importModules" in s and "loadExts := false" in s
    assert N in s and '"/opt/lib/lean"' in s and '"/x/build"' in s and "too-large" in s and "sorry" in s


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


def test_symlinked_dir_refused(tmp_path):
    from telperion.checks.fingerprint import run_fingerprint
    outside = tmp_path / "outside"
    (outside / "Mathlib").mkdir(parents=True)
    (outside / "Mathlib/Evil.lean").write_text("def bound : Nat := 5\n", encoding="utf-8")
    proj = tmp_path / "proj"
    proj.mkdir()
    (proj / "vendor").symlink_to(outside, target_is_directory=True)
    with pytest.raises(ValueError, match="symlink.*vendor"):
        run_fingerprint(proj, ["Mathlib"], ["t"], wrapper=["false"])


def test_spoof_check_ignores_lake_packages(tmp_path):
    from telperion.checks.fingerprint import run_fingerprint
    (tmp_path / ".lake/packages/mathlib/Mathlib").mkdir(parents=True)
    (tmp_path / ".lake/packages/mathlib/Mathlib/Foo.lean").write_text("", encoding="utf-8")
    with pytest.raises(ValueError) as exc:                       # passes the spoof check, then `false` fails
        run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=["false"])
    assert "library root" not in str(exc.value) and "symlink" not in str(exc.value)


def _fake_lean(monkeypatch, body_for):
    """Replace run_lean: --print-libdir answers a fixed dir; the script run answers body_for(nonce)."""
    from telperion.checks import fingerprint as fp_

    def fake(cmd, cwd, timeout, input=None):
        if "--print-libdir" in cmd:
            return 0, "/opt/lean/lib/lean\n"
        nonce = re.search(r'tpNonce : String := "([0-9a-f]{32})"', input).group(1)
        return 0, body_for(nonce)
    monkeypatch.setattr(fp_, "run_lean", fake)
    return fp_


def test_escaped_target_key_is_found(monkeypatch, tmp_path):
    # Lean prints `«my thm»`; the caller passes `my thm`
    fp_ = _fake_lean(monkeypatch, lambda n: f'FP-BEGIN {n} «my thm»\n(c _."True" [])\nFP-END {n} «my thm»\nFP-DONE {n}\n')
    assert len(fp_.run_fingerprint(tmp_path, ["Mathlib"], ["my thm"], wrapper=[])["my thm"]) == 64


def test_nonce_is_fresh_per_run(monkeypatch, tmp_path):
    seen = []
    fp_ = _fake_lean(monkeypatch, lambda n: seen.append(n) or f"FP-BEGIN {n} t\nX\nFP-END {n} t\nFP-DONE {n}\n")
    fp_.run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=[])
    fp_.run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=[])
    assert len(seen) == 2 and seen[0] != seen[1] and all(re.fullmatch(r"[0-9a-f]{32}", n) for n in seen)


def test_trusted_prefixes_from_manifest(tmp_path):
    import json
    from telperion.checks.fingerprint import _trusted_prefixes
    (tmp_path / ".lake/packages/mathlib").mkdir(parents=True)
    (tmp_path / "lake-manifest.json").write_text(json.dumps(
        {"packagesDir": ".lake/packages", "packages": [{"name": "mathlib", "type": "git"}]}), encoding="utf-8")
    got = _trusted_prefixes(tmp_path, ["sh", "-c", "echo /opt/lean/lib/lean", "--"], timeout=10)
    assert got == [os.path.realpath("/opt/lean/lib/lean"), os.path.realpath(tmp_path / ".lake/packages/mathlib")]


# Fix round 2 (I2): the process-group runner.
def test_run_lean_output_and_stdin(tmp_path):
    from telperion.checks.lean_run import run_lean
    assert run_lean(["sh", "-c", "cat; echo err >&2; exit 3"], tmp_path, 10, input="hi\n") == (3, "hi\nerr\n")


def test_run_lean_timeout_kills_grandchild(tmp_path):
    from telperion.checks.lean_run import run_lean
    pidf = tmp_path / "pid"
    with pytest.raises(subprocess.TimeoutExpired):
        run_lean(["sh", "-c", f"sleep 60 & echo $! > {pidf}; wait"], tmp_path, 1)
    pid = int(pidf.read_text())
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.1)
    pytest.fail(f"grandchild {pid} outlived the timeout")


# Fix round 1 Lean controls. MUST-FAIL: non-def local constants are refused, never hashed by name.
def _refused(text: str, what: str, **kw):
    with pytest.raises(ValueError, match=f"refused.*{what}"):
        _fp(text, "t", **kw)


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


# Fix round 2 Lean controls.
FAKE_TRUE = '(c _.\\"True\\" [])'


@lean
@pytest.mark.parametrize("trick", [
    # the reviewer's spoof: a fake block for `True`, then #exit before anything else is checked
    'theorem t : False := sorry\n#eval IO.println "FP-BEGIN {n} t\\n{fake}\\nFP-END {n} t\\nFP-DONE {n}"\n#exit\n',
    'theorem t : False := sorry\n#eval (do IO.println "FP-BEGIN {n} t\\n{fake}\\nFP-END {n} t\\nFP-DONE {n}"; '
    'IO.Process.exit 0 : IO Unit)\n',
    'theorem t : False := sorry\ninitialize IO.println "FP-BEGIN {n} t\\n{fake}\\nFP-END {n} t\\nFP-DONE {n}"\n',
])
def test_body_cannot_spoof_markers(trick):                   # MUST-FAIL control (C1)
    body = "import Mathlib\n" + trick.format(n=N, fake=FAKE_TRUE)
    true_hash = _fp("import Mathlib\ntheorem t : True := trivial\n", "t")
    false_hash = _fp("import Mathlib\ntheorem t : False := sorry\n", "t")
    try:
        got = _fp(body, "t")
    except ValueError:
        return                                              # refused: fine
    assert got == false_hash != true_hash


@lean
def test_doubling_definitions_too_large_fast():              # MUST-FAIL control (I1)
    defs = "def a0 : ℕ := 1\n" + "".join(f"def a{k + 1} : ℕ := a{k} + a{k}\n" for k in range(20))
    start = time.monotonic()
    _refused("import Mathlib\n" + defs + "theorem t : a20 = a20 := rfl\n", "too-large", timeout=60)
    assert time.monotonic() - start < 60


@lean
def test_local_axiom_refused():                              # MUST-FAIL control
    _refused("import Mathlib\naxiom ax : ℕ\ntheorem t : ax = ax := rfl\n", "ax axiom")


@lean
def test_local_opaque_refused():                             # MUST-FAIL control
    _refused("import Mathlib\nopaque op : ℕ\ntheorem t : op = op := rfl\n", "op opaque")


@lean
def test_sorry_in_statement_refused():                       # MUST-FAIL control (M3)
    _refused("import Mathlib\ntheorem t : (sorry : ℕ) = 0 := sorry\n", "sorry")


@lean
def test_local_universe_polymorphic_def_unfolds():           # MUST-PASS control
    a = ("import Mathlib\ndef idf.{w} (α : Sort w) (x : α) : α := x\n"
         "theorem t.{u} {α : Sort u} (a : α) : idf α a = a := rfl\n")
    b = a.replace(".{w}", ".{z}").replace("Sort w", "Sort z").replace(".{u}", ".{v}").replace("Sort u", "Sort v")
    direct = "import Mathlib\ntheorem t.{u} {α : Sort u} (a : α) : a = a := rfl\n"
    assert _fp(a, "t") == _fp(b, "t") == _fp(direct, "t")


@lean
def test_untrusted_library_module_refused():                 # MUST-FAIL control (I3)
    # with no trusted prefixes, every Mathlib/Init module's olean is untrusted: the Lean-side check must fire
    from telperion.checks.fingerprint import _fingerprint
    with pytest.raises(ValueError, match="untrusted-library-module"):
        _fingerprint(Path(LEAN_ENV), [], ["t"], None, 600,
                     body="import Mathlib\ntheorem t : True := trivial\n", trusted=[])


@lean
def test_serializer_injectivity_cases():                     # serializer unit cases (Lean only, no Mathlib)
    from telperion.checks.fingerprint import HELPERS, ROOTS_DEF
    from telperion.checks.lean_run import run_lean
    from telperion.checks.negation_probe import default_wrapper
    script = "import Lean\nopen Lean Meta\n" + ROOTS_DEF.replace("__ROOTS__", "[`Init]") + HELPERS + r'''
def ser (e : Expr) : String := match (tpSer [] e).run "" with
  | .ok ((), s) => s
  | .error m => "ERR " ++ m
def nat : Expr := .const ``Nat []
#eval do
  let cases : List (String × Expr × Expr) := [
    ("binderInfo", .forallE `n nat (.bvar 0) .implicit, .forallE `n nat (.bvar 0) .default),
    ("instImplicit", .forallE `n nat (.bvar 0) .instImplicit, .forallE `n nat (.bvar 0) .strictImplicit),
    ("letE nonDep", .letE `x nat (.lit (.natVal 1)) (.bvar 0) true, .letE `x nat (.lit (.natVal 1)) (.bvar 0) false),
    ("quote in name", .const (.str .anonymous "a\"b") [], .const (.str (.str .anonymous "a") "b") []),
    ("» in name", .const (.str .anonymous "a.b»") [], .const (.str (.str .anonymous "a") "b»") []),
    ("str lit", .lit (.strVal "a\" b"), .lit (.strVal "a\\\" b")),
    ("binder name ignored", .lam `x nat (.bvar 0) .default, .lam `y nat (.bvar 0) .default)]
  for (label, x, y) in cases do
    IO.println s!"CASE {label} | {ser x == ser y} | {ser x} | {ser y}"
  IO.println s!"TOSTRING-COLLIDES {(Name.str .anonymous "a.b»").toString == (Name.str (.str .anonymous "a") "b»").toString}"
'''
    rc, out = run_lean([*default_wrapper(), "lake", "env", "lean", "--stdin"], Path(LEAN_ENV), 600, input=script)
    assert rc == 0, out
    eq = {m.group(1): m.group(2) == "true" for m in re.finditer(r"^CASE (.+?) \| (true|false) \|", out, re.M)}
    assert eq == {"binderInfo": False, "instImplicit": False, "letE nonDep": False, "quote in name": False,
                  "» in name": False, "str lit": False, "binder name ignored": True}, out
    assert "TOSTRING-COLLIDES true" in out          # why tpSerName does not use Name.toString

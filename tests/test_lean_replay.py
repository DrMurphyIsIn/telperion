"""lean_replay: an untrusted module's constants reach a check by kernel replay, and none of its code runs."""
from __future__ import annotations

import os
import secrets
import shutil
import subprocess
from pathlib import Path

import pytest

from telperion.checks import lean_replay
from telperion.checks.lean_replay import (parse_replay_output, render_replay_script, run_replay, split_search_path,
                                          under_prefix)

NONCE = "TR" + "ab" * 16
CB = "def TelperionReplay.callback : Lean.Elab.Term.TermElabM Unit := TelperionReplay.line \"CB hi\"\n"


# ---------------------------------------------------------------------------------------------------------------
# Pure: the trusted/untrusted split.
def test_under_prefix_is_a_path_boundary_not_a_string_prefix(tmp_path):
    lib = tmp_path / "lib"
    (lib / "Mathlib").mkdir(parents=True)
    (tmp_path / "lib-evil").mkdir()
    assert under_prefix(lib, [lib]) and under_prefix(lib / "Mathlib", [lib]) and under_prefix(lib / "Mathlib", [f"{lib}/"])
    assert not under_prefix(tmp_path / "lib-evil", [lib])
    assert not under_prefix(tmp_path, [lib])


def test_under_prefix_resolves_symlinks_both_ways(tmp_path):
    lib, elsewhere = tmp_path / "lib", tmp_path / "elsewhere"
    lib.mkdir()
    elsewhere.mkdir()
    (tmp_path / "into_lib").symlink_to(lib)
    (lib / "out").symlink_to(elsewhere)        # a link inside the trusted dir that points out of it
    assert under_prefix(tmp_path / "into_lib", [lib])
    assert not under_prefix(lib / "out", [lib])
    assert under_prefix(lib, [tmp_path / "into_lib"])


def test_split_search_path_keeps_order_and_drops_empties(tmp_path):
    a, b, u1, u2 = (tmp_path / n for n in ("a", "b", "u1", "u2"))
    for d in (a, b, u1, u2):
        d.mkdir()
    t, u = split_search_path([str(u1), str(a), "", str(u2), str(b)], [a, b])
    assert t == [str(a), str(b)] and u == [str(u1), str(u2)]


# ---------------------------------------------------------------------------------------------------------------
# Pure: the rendered script.
def test_render_imports_only_trusted_modules_and_never_the_target(tmp_path):
    src = render_replay_script(["Mathlib", "Plausible"], "Foo.Bar", [tmp_path], CB, NONCE, ["/x", str(tmp_path)])
    imports = [ln for ln in src.splitlines() if ln.startswith("import ")]
    assert imports == ["import Mathlib", "import Plausible", "import Lean"]
    assert "def targetModule : Name := `Foo.Bar" in src
    assert f'def tag : String := "{NONCE}"' in src
    assert f'def trustedPrefixes : List String := ["{os.path.realpath(tmp_path)}"]' in src
    assert f'(["/x", "{tmp_path}"] : List String)' in src          # the search path is data, not LEAN_PATH
    assert CB in src and "Kernel" not in CB
    assert "TelperionReplay.Replay.replay c.consts env" in src and "(← get).env.addDeclCore 0 0 d none" in src
    assert "setEnv env'" in src and "setEnv (Environment.ofKernelEnv" not in src


def test_render_escapes_paths_and_refuses_bad_names_and_nonces(tmp_path):
    src = render_replay_script(["Mathlib"], "Foo", ["/"], CB, NONCE, ['/we"ird\\path'])
    assert '["/we\\"ird\\\\path"]' in src and 'def trustedPrefixes : List String := ["/"]' in src
    for bad in ("Foo Bar", "Foo\nimport Evil", "Foo.«bar»", "", "Foo..Bar", "1Foo"):
        with pytest.raises(ValueError):
            render_replay_script(["Mathlib"], bad, ["/"], CB, NONCE)
        with pytest.raises(ValueError):
            render_replay_script([bad], "Foo", ["/"], CB, NONCE)
    for nonce in ("TR-x", "TR x", "", 'TR"'):
        with pytest.raises(ValueError):
            render_replay_script(["Mathlib"], "Foo", ["/"], CB, nonce)


# ---------------------------------------------------------------------------------------------------------------
# Pure: the protocol.
def _out(*lines: str, tag: str = NONCE) -> str:
    return "".join(f"{tag}-{ln}\n" for ln in lines)


def test_parse_ok_failed_needs():
    out = "noise\n" + _out("REPLAY OK modules=[Foo] constants=3", "CB a", "CB b", "DONE")
    assert parse_replay_output(out, NONCE) == ("OK", "modules=[Foo] constants=3", ["CB a", "CB b"], [])
    assert parse_replay_output(_out("REPLAY FAILED (kernel) bad", "DONE"), NONCE)[:2] == ("FAILED", "(kernel) bad")
    assert parse_replay_output(_out("REPLAY NEEDS A.B C", "DONE"), NONCE) == ("NEEDS", "A.B C", [], ["A.B", "C"])


def test_parse_ignores_other_tags_and_refuses_broken_protocols():
    forged = _out("REPLAY OK modules=[] constants=0", "CB forged", "DONE", tag="TR" + "cd" * 16)
    ok = _out("REPLAY FAILED x", "DONE")
    assert parse_replay_output(forged + ok, NONCE)[0] == "FAILED"
    broken = {
        "no replay line": _out("CB a", "DONE"),
        "two replay lines": _out("REPLAY OK m", "REPLAY OK m", "DONE"),
        "no done": _out("REPLAY OK m", "CB a"),
        "done not last": _out("REPLAY OK m", "DONE", "CB a"),
        "two dones": _out("REPLAY OK m", "DONE", "DONE"),
        "line before replay": _out("CB a", "REPLAY OK m", "DONE"),
        "lines after failed": _out("REPLAY FAILED x", "CB a", "DONE"),
        "lines after needs": _out("REPLAY NEEDS A", "CB a", "DONE"),
    }
    for why, out in broken.items():
        assert parse_replay_output(out, NONCE)[0] == "ERROR", why
    assert parse_replay_output(_out("REPLAY OK m", "DONE"), NONCE, rc=1)[0] == "ERROR"
    st, detail, lines, _ = parse_replay_output(_out("REPLAY OK m", "CB a", "CALLBACK FAILED boom", "DONE"), NONCE)
    assert (st, detail, lines) == ("ERROR", "the callback failed: boom", ["CB a", "CALLBACK FAILED boom"])


def test_run_replay_reruns_once_with_needed_trusted_modules(tmp_path, monkeypatch):
    trusted, untrusted = tmp_path / "trusted", tmp_path / "untrusted"
    trusted.mkdir()
    untrusted.mkdir()
    monkeypatch.setattr(lean_replay, "project_search_path", lambda project, extra="": [str(untrusted), str(trusted)])
    log = tmp_path / "log"
    # The fake Lean: $2 is LEAN_PATH=..., $4 the script. It echoes NEEDS until the script imports Foo.Bar.
    fake = ('echo "$2" >> {log}; t=$(sed -n \'s/^def tag : String := "\\(.*\\)"$/\\1/p\' "$4"); '
            'if grep -q "^import Foo.Bar$" "$4"; then printf "%s-REPLAY OK m\\n%s-CB x\\n%s-DONE\\n" $t $t $t; '
            'else printf "%s-REPLAY NEEDS Foo.Bar\\n%s-DONE\\n" $t $t; fi').format(log=log)
    r = run_replay(tmp_path, "Foo", CB, wrapper=["sh", "-c", fake, "sh"], prefixes=[str(trusted)])
    assert (r.status, r.lines) == ("OK", ["CB x"]), r
    assert log.read_text().splitlines() == [f"LEAN_PATH={trusted}"] * 2      # never the untrusted dir
    assert not list(tmp_path.glob(lean_replay.REPLAY_DIR_PREFIX + "*"))
    always = ('t=$(sed -n \'s/^def tag : String := "\\(.*\\)"$/\\1/p\' "$4"); '
              'printf "%s-REPLAY NEEDS Foo.Bar\\n%s-DONE\\n" $t $t')
    r = run_replay(tmp_path, "Foo", CB, wrapper=["sh", "-c", always, "sh"], prefixes=[str(trusted)])
    assert r.status == "ERROR" and "after importing them" in r.detail


def test_run_replay_timeout_is_error(tmp_path, monkeypatch):
    monkeypatch.setattr(lean_replay, "project_search_path", lambda project, extra="": [])
    r = run_replay(tmp_path, "Foo", CB, wrapper=["sh", "-c", "sleep 60", "sh"], prefixes=[], timeout=1)
    assert r.status == "ERROR" and "did not finish" in r.detail
    assert not list(tmp_path.glob(lean_replay.REPLAY_DIR_PREFIX + "*"))


# ---------------------------------------------------------------------------------------------------------------
# Lean tests. Each module is compiled into its OWN dir `<env>/.tp_replay_<hex>/` (put on LEAN_PATH only by the runs
# that test it); nothing in the env's shared `.lake/build` is written or removed.
LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")

HONEST = r'''import Mathlib
namespace TpHonest
inductive Color | red | green | blue
  deriving DecidableEq
structure Pt where
  x : ℕ
  y : ℕ
def Color.toNat : Color → ℕ
  | .red => 0 | .green => 1 | .blue => 2
def sq (n : ℕ) : ℕ := n * n
theorem sq_le {α : Type*} [Nonempty α] (n : ℕ) (p : Pt) (h : p.x < n) : p.x ≤ sq n ∧ Color.toNat .blue = 2 :=
  ⟨le_trans h.le (Nat.le_mul_self n), rfl⟩
end TpHonest
'''

# The reviewer's three attack shapes. Each prints a marker if it ever runs.
EVIL = r'''import Lean
open Lean Elab Command Tactic
initialize IO.println "TPEVIL-INIT"
@[command_elab Lean.Parser.Command.eval] def tpEvilEval : CommandElab := fun _ => IO.println "TPEVIL-EVAL"
@[tactic Lean.Parser.Tactic.omega] def tpEvilOmega : Tactic := fun _ => do
  IO.println "TPEVIL-TACTIC"
  for g in ← getGoals do g.admit
theorem TpEvil.t : 2 + 2 = 4 := rfl
'''

# A false lemma that only the elaborator saw: the kernel check is skipped while compiling the module.
BOGUS = r'''import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM do
  let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 4) (mkNatLit 5)
  let value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 4)
  addDecl (.thmDecl { name := `TpBogus.bogus, levelParams := [], type, value })
theorem TpBogus.target : False := absurd TpBogus.bogus (by decide)
'''

MATHLIB_EVIL = r'''import Lean
initialize IO.println "TPEVIL-INIT"
theorem Mathlib.Evil.t : 1 + 1 = 2 := rfl
'''

TYPE_CB = r'''open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  for n in [`TpHonest.sq_le, `TpHonest.Color.toNat, `TpHonest.Pt.x, `TpHonest.Color.rec] do
    let ci ← getConstInfo n
    TelperionReplay.line s!"TYPE {n} {ci.type.hash} {(toString (repr ci.type)).replace "\n" " "}"
'''

EVIL_CB = r'''open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  let ci ← getConstInfo `TpEvil.t
  TelperionReplay.line s!"CB-FOUND {ci.name}"
  TelperionReplay.line s!"CB-EVALATTR {(← getEnv).contains `tpEvilEval}"
  let ty ← elabTerm (← `(∀ x : Nat, x < 3 → x < 5)) none
  let g ← mkFreshExprMVar ty
  let rest ← Tactic.run g.mvarId! (Tactic.evalTactic (← `(tactic| intro x h; omega)))
  let pf ← instantiateMVars g
  TelperionReplay.line s!"CB-OMEGA goals={rest.length} sorry={pf.hasSorry}"
'''

FOUND_CB = r'''open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  for n in [`TpBogus.target, `Mathlib.Evil.t] do
    TelperionReplay.line s!"CB-HAS {n} {(← getEnv).contains n}"
'''


def _wrapper(lib: Path | None = None) -> list[str]:
    return (["env", f"LEAN_PATH={lib}"] if lib else []) + lean_replay.default_wrapper()


@pytest.fixture
def lib():
    d = Path(LEAN_ENV) / f".tp_replay_{secrets.token_hex(8)}"
    d.mkdir()
    yield d
    shutil.rmtree(d, ignore_errors=True)


def _build(lib: Path, module: str, body: str) -> None:
    """Compile `body` as module `module` into `lib` (sources under `lib/src`, removed afterwards)."""
    rel = Path(*module.split("."))
    src = lib / "src" / rel.with_suffix(".lean")
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_text(body, encoding="utf-8")
    out = (lib / rel).with_suffix(".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    p = subprocess.run([*_wrapper(), "lake", "env", "lean", "-R", str(lib / "src"), "-o", str(out), str(src)],
                       cwd=LEAN_ENV, capture_output=True, text=True, timeout=3600)
    shutil.rmtree(lib / "src")
    assert p.returncode == 0, p.stdout + p.stderr


def _import_normally(lib: Path, body: str) -> str:
    """Output of a `lake env lean` file that IMPORTS the module the usual way (the control for what replay avoids)."""
    f = lib / "Control.lean"
    f.write_text(body, encoding="utf-8")
    p = subprocess.run([*_wrapper(lib), "lake", "env", "lean", str(f)], cwd=LEAN_ENV, capture_output=True,
                       text=True, timeout=3600)
    f.unlink()
    return p.stdout + p.stderr


@lean
def test_a_replayed_types_are_identical_to_imported_ones(lib):
    _build(lib, "TpHonest", HONEST)
    r = run_replay(Path(LEAN_ENV), "TpHonest", TYPE_CB, extra_lean_path=str(lib))
    assert r.status == "OK" and "modules=[TpHonest]" in r.detail, (r.status, r.detail, r.output[-3000:])
    replayed = [ln for ln in r.lines if ln.startswith("TYPE ")]
    assert len(replayed) == 4
    # The same types through a normal import. `repr` of an Expr is its whole tree (binder names and infos, levels,
    # mdata), so equal strings mean Expr.equal types.
    ctl = _import_normally(lib, "import Mathlib\nimport TpHonest\n" + TYPE_CB.replace("TelperionReplay.line", "IO.println")
                           + "#eval TelperionReplay.callback\n")
    imported = [ln for ln in ctl.splitlines() if ln.startswith("TYPE ")]
    assert imported == replayed, ctl[-3000:]


@lean
def test_b_evil_module_runs_nothing(lib):
    _build(lib, "TpEvil", EVIL)
    # Control: imported the usual way, all three shapes fire (the initializer, the `#eval` override, the tactic).
    ctl = _import_normally(lib, "import TpEvil\nexample : ∀ x : Nat, x < 3 → x < 5 := by intro x h; omega\n"
                                "#eval IO.println \"CONTROL-EVAL-RAN\"\n")
    assert all(m in ctl for m in ("TPEVIL-INIT", "TPEVIL-TACTIC", "TPEVIL-EVAL")), ctl[-3000:]
    assert "CONTROL-EVAL-RAN" not in ctl
    # Replayed: none of them runs, and the callback's own values are reported.
    r = run_replay(Path(LEAN_ENV), "TpEvil", EVIL_CB, trusted_imports=("Lean",), extra_lean_path=str(lib))
    assert "TPEVIL" not in r.output, r.output[-3000:]
    assert r.status == "OK" and "modules=[TpEvil]" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.lines == ["CB-FOUND TpEvil.t", "CB-EVALATTR true", "CB-OMEGA goals=0 sorry=false"]


@lean
def test_c_kernel_invalid_module_is_rejected(lib):
    _build(lib, "TpBogus", BOGUS)
    r = run_replay(Path(LEAN_ENV), "TpBogus", FOUND_CB, trusted_imports=("Lean",), extra_lean_path=str(lib))
    assert r.status == "FAILED" and "(kernel)" in r.detail and "TpBogus.bogus" in r.detail, (r.status, r.detail)
    assert r.lines == []


@lean
def test_d_mathlib_named_module_outside_the_prefixes_is_untrusted(lib):
    _build(lib, "Mathlib.Evil", MATHLIB_EVIL)
    r = run_replay(Path(LEAN_ENV), "Mathlib.Evil", FOUND_CB, extra_lean_path=str(lib))
    assert "TPEVIL" not in r.output
    assert r.status == "OK" and "modules=[Mathlib.Evil]" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.lines == ["CB-HAS TpBogus.target false", "CB-HAS Mathlib.Evil.t true"]


@lean
def test_e_trusted_target_and_missing_target_are_refused(lib):
    r = run_replay(Path(LEAN_ENV), "Mathlib.Order.Basic", FOUND_CB, trusted_imports=("Mathlib.Order.Basic",))
    assert r.status == "FAILED" and "resolves to the trusted" in r.detail, (r.status, r.detail)
    r = run_replay(Path(LEAN_ENV), "TpNeverBuilt", FOUND_CB, trusted_imports=("Lean",), extra_lean_path=str(lib))
    assert r.status == "FAILED" and "build it first" in r.detail, (r.status, r.detail)


@lean
def test_f_needed_trusted_module_is_added(lib):
    _build(lib, "TpHonest", HONEST)
    r = run_replay(Path(LEAN_ENV), "TpHonest", TYPE_CB, trusted_imports=("Lean",), extra_lean_path=str(lib))
    assert r.status == "OK" and len(r.lines) == 4, (r.status, r.detail, r.output[-3000:])


MODULE_FILE = r"""module
public theorem TpMod.t : 1 + 1 = 2 := by decide
def TpMod.hidden : Nat := 3
"""

MODULE_CB = r"""open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  -- `TpMod.hidden` is not public, so its constant has a private (mangled) name; find it by its user name.
  let hidden := (← getEnv).constants.foldStage2 (fun acc n _ =>
    if privateToUserName n == `TpMod.hidden && n != `TpMod.hidden then n :: acc else acc) []
  for n in `TpMod.t :: hidden do
    let kind := match (← getEnv).find? n with
      | some (.thmInfo _) => "theorem" | some (.defnInfo _) => "def" | some _ => "other" | none => "absent"
    TelperionReplay.line s!"CB-KIND {privateToUserName n} {kind}"
"""

BUSY_CB = r"""open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  TelperionReplay.line "CB start"
  for _ in [0:1000000] do
    let _ ← mkFreshExprMVar none
    Core.checkMaxHeartbeats "telperion"
  TelperionReplay.line "CB unreachable"
"""


@lean
def test_g_module_system_file_is_read_in_full(lib):
    # A `module` file's exported part holds a theorem as an AXIOM, and its private data (here a non-public def) is
    # in `.olean.private`; all parts are read, so the theorem comes back with its proof.
    _build(lib, "TpMod", MODULE_FILE)
    r = run_replay(Path(LEAN_ENV), "TpMod", MODULE_CB, trusted_imports=("Lean",), extra_lean_path=str(lib))
    assert r.status == "OK", (r.status, r.detail, r.output[-3000:])
    assert r.lines == ["CB-KIND TpMod.t theorem", "CB-KIND TpMod.hidden def"]


@lean
def test_h_callback_heartbeat_timeout_is_reported_and_done_still_printed(lib):
    _build(lib, "Mathlib.Evil", MATHLIB_EVIL)
    r = run_replay(Path(LEAN_ENV), "Mathlib.Evil", BUSY_CB, trusted_imports=("Lean",), extra_lean_path=str(lib),
                   heartbeats=1)
    assert r.status == "ERROR" and "heartbeats" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.lines[0] == "CB start" and "CB unreachable" not in r.lines

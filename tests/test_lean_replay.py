"""lean_replay: an untrusted module's constants reach a check by kernel replay, and none of its code runs."""
from __future__ import annotations

import json
import os
import re
import secrets
import shutil
import subprocess
from pathlib import Path

import pytest

from telperion.checks import lean_replay
from telperion.checks.lean_replay import (build_trusted_manifest, closure_digest, default_manifest_path, parse_axioms,
                                          parse_declared, parse_replay_output, pinned_env, render_replay_script,
                                          resolve_olean, run_replay, split_search_path, under_prefix,
                                          verify_trusted_manifest)
from telperion.checks.lean_run import run_lean

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))  # shared lean_env helpers

NONCE = "TR" + "ab" * 16
CB = "def TelperionReplay.callback : Lean.Elab.Term.TermElabM Unit := TelperionReplay.line \"CB hi\"\n"
TOOLCHAIN = "leanprover/lean4:v4.35.0"


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
# Pure: the pinned env and its manifest, on a fake env and elan home.
def _fake_env(tmp_path: Path) -> tuple[Path, Path]:
    """(env, elan_home): a toolchain with a `lean` and `Init.olean`, an env with mathlib and its own build dir."""
    elan = tmp_path / "elan"
    tdir = elan / "toolchains" / "leanprover--lean4---v4.35.0"
    (tdir / "bin").mkdir(parents=True)
    (tdir / "bin" / "lean").write_text("#!/bin/sh\n")
    (tdir / "bin" / "lean").chmod(0o755)
    (tdir / "lib" / "lean").mkdir(parents=True)
    (tdir / "lib" / "lean" / "Init.olean").write_bytes(b"init")
    (tdir / "lib" / "lean" / "libleanshared.dylib").write_bytes(b"so")
    env = tmp_path / "env"
    ml = env / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    (ml / "Mathlib").mkdir(parents=True)
    (ml / "Mathlib.olean").write_bytes(b"ml")
    (ml / "Mathlib" / "Basic.olean").write_bytes(b"basic")
    (ml / "Mathlib" / "Basic.ilean").write_bytes(b"ilean")
    (env / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
    (env / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    return env, elan


def test_pinned_env_comes_from_the_env_and_its_toolchain(tmp_path, monkeypatch):
    env, elan = _fake_env(tmp_path)
    p = pinned_env(env, elan)
    tdir = os.path.realpath(elan / "toolchains" / "leanprover--lean4---v4.35.0")
    assert p.lean == f"{tdir}/bin/lean" and p.libdir == f"{tdir}/lib/lean" and p.toolchain == TOOLCHAIN
    real = os.path.realpath(env)
    assert p.entries == (f"{real}/.lake/packages/mathlib/.lake/build/lib/lean", f"{real}/.lake/build/lib/lean")
    assert p.prefixes == (p.libdir, *p.entries)
    monkeypatch.setenv("TELPERION_LEAN_ENV", str(env))
    assert pinned_env(None, elan) == p
    monkeypatch.delenv("TELPERION_LEAN_ENV")
    with pytest.raises(ValueError, match="no trusted env"):
        pinned_env(None, elan)
    (env / "lean-toolchain").write_text("leanprover/lean4:v4.99.0\n")
    with pytest.raises(ValueError, match="not installed"):
        pinned_env(env, elan)
    (env / "lean-toolchain").write_text("../../etc\n")
    with pytest.raises(ValueError, match="unexpected lean-toolchain"):
        pinned_env(env, elan)


def test_manifest_detects_changed_added_and_removed_trusted_files(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    p = pinned_env(env, elan)
    verify_trusted_manifest(p, m)
    files = json.loads(m.read_text())["files"]
    assert p.lean in files and any(f.endswith("libleanshared.dylib") for f in files)
    assert not any(f.endswith(".ilean") for f in files)
    ml = env / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    (ml / "Mathlib" / "Basic.ilean").write_bytes(b"not loaded by lean")           # ignored
    verify_trusted_manifest(p, m)
    (ml / "Mathlib" / "Basic.olean").write_bytes(b"tampered")
    with pytest.raises(ValueError, match="1 differ"):
        verify_trusted_manifest(p, m)
    (ml / "Mathlib" / "Basic.olean").write_bytes(b"basic")
    (ml / "Mathlib" / "Evil.olean").write_bytes(b"planted")                         # would be trusted
    with pytest.raises(ValueError, match="1 added"):
        verify_trusted_manifest(p, m)
    (ml / "Mathlib" / "Evil.olean").unlink()
    (ml / "Mathlib.olean").unlink()
    with pytest.raises(ValueError, match="1 removed"):
        verify_trusted_manifest(p, m)
    (ml / "Mathlib.olean").write_bytes(b"ml")
    Path(p.lean).write_text("#!/bin/sh\necho evil\n")
    with pytest.raises(ValueError, match="1 differ"):
        verify_trusted_manifest(p, m)
    Path(p.lean).write_text("#!/bin/sh\n")
    verify_trusted_manifest(p, m)
    (env / ".lake" / "packages" / "evilpkg" / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
    with pytest.raises(ValueError, match="prefixes"):
        verify_trusted_manifest(pinned_env(env, elan), m)
    with pytest.raises(ValueError, match="no readable trusted manifest"):
        verify_trusted_manifest(p, tmp_path / "absent.json")


FAKE_LEAN = Path(__file__).resolve().parent / "fake_lean_cli.py"


def _fake_lean(log: Path, mode: str = "ok") -> list[str]:
    """A wrapper standing in for Lean (tests/fake_lean_cli.py): it logs each call and answers the list and replay
    runs as lean_env.fake_replay_output does for `mode`."""
    import sys
    return [sys.executable, str(FAKE_LEAN), str(log), mode]


def _calls(log: Path) -> list[list[str]]:
    return [ln.split("|") for ln in log.read_text().splitlines()]


def _submission(tmp_path: Path) -> Path:
    sub = tmp_path / "submission"
    sub.mkdir()
    (sub / "Foo.olean").write_bytes(b"foo")
    return sub


def test_run_replay_uses_only_pinned_anchors_and_a_private_cwd(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    p = pinned_env(env, elan)
    sub = _submission(tmp_path)
    log = tmp_path / "log"
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan,
                   wrapper=_fake_lean(log))
    assert (r.status, r.lines, r.axioms) == ("OK", ["CB x"], ["propext"]), r
    import hashlib
    closure = [["Foo", "olean", hashlib.sha256(b"foo").hexdigest()]]
    assert r.olean_closure == closure and r.olean_sha256 == closure_digest(closure)
    calls = _calls(log)
    assert [c[5] for c in calls] == ["list", "replay"]                 # a list run, then the replay run
    for lean_path, binary, cwd, mode, mem, _kind in calls:
        assert lean_path == "LEAN_PATH=" + os.pathsep.join(p.entries) and binary == p.lean
        assert mode == "700" and not under_prefix(cwd, [tmp_path]) and not os.path.exists(cwd)
        assert mem == "--memory=8192"


def test_run_replay_reads_only_private_copies_and_binds_the_closure(tmp_path, monkeypatch):
    from telperion.checks import lean_replay
    from lean_env import fake_replay_output
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    sub = _submission(tmp_path)
    seen = {}

    def fake(cmd, cwd, timeout, input=None, env=None, read=None):
        script = Path(cmd[-1]).read_text(encoding="utf-8")
        out = fake_replay_output(script, "<TAG>-CB x\n")
        if "def listOnly : Bool := true" not in script:
            seen["search"] = re.search(r"def searchPath .* := \((\[.*\]) : List String\)", script).group(1)
            seen["expect"] = re.search(r"def expectOleans .* := (\[.*\])", script).group(1)
            if read is not None:                             # report a file beyond the copies
                tag = re.search(r'def tag : String := "(TR[0-9a-f]+)"', script).group(1)
                out = f"{tag}-READ {read}\n" + out
        return 0, out
    monkeypatch.setattr(lean_replay, "run_lean", fake)
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan, wrapper=[])
    assert r.status == "OK", r
    # the replay searched the copies dir, not the submission dir, and expected the copy
    assert str(sub) not in seen["search"] and "/telperion_replay_" in seen["search"]
    assert re.fullmatch(r'\[\(`Foo, ".*/telperion_replay_[^/"]+/olean/Foo\.olean"\)\]', seen["expect"])
    # a READ outside the copies is an ERROR
    monkeypatch.setattr(lean_replay, "run_lean", lambda *a, **k: fake(*a, **k, read=str(sub / "Foo.olean")))
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan, wrapper=[])
    assert r.status == "ERROR" and "beyond the copies" in r.detail, r.detail


def test_listed_file_vanishing_before_the_copy_is_error(tmp_path, monkeypatch):
    from telperion.checks import lean_replay
    from lean_env import fake_replay_output
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    sub = _submission(tmp_path)

    def fake(cmd, cwd, timeout, input=None, env=None):
        out = fake_replay_output(Path(cmd[-1]).read_text(encoding="utf-8"))
        (sub / "Foo.olean").unlink()                      # listed, then gone before the copy
        return 0, out
    monkeypatch.setattr(lean_replay, "run_lean", fake)
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan, wrapper=[])
    assert r.status == "ERROR" and "cannot copy or hash a listed untrusted file" in r.detail, r


def test_memory_flag_plumbing(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    sub = _submission(tmp_path)
    for mem, flag in ((2048, "--memory=2048"), (None, "")):
        log = tmp_path / f"log{mem}"
        r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan,
                       wrapper=_fake_lean(log), memory_mb=mem)
        assert r.status == "OK" and [c[4] for c in _calls(log)] == [flag, flag], r


def test_run_replay_reruns_once_with_needed_trusted_modules(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    log = tmp_path / "log"
    sub = _submission(tmp_path)
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan,
                   wrapper=_fake_lean(log, "needs"))
    assert (r.status, r.lines) == ("OK", ["CB x"]), r
    assert [c[5] for c in _calls(log)] == ["list", "replay", "replay"]
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan,
                   wrapper=_fake_lean(log, "always-needs"))
    assert r.status == "ERROR" and "after importing them" in r.detail


def test_run_replay_refuses_before_running_lean(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    log = tmp_path / "log"
    ran = _fake_lean(log)
    ml = env / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    cases = {
        "lies under a trusted prefix": dict(untrusted_paths=[ml / "Mathlib"]),
        "contains a trusted prefix": dict(untrusted_paths=[env]),
        "no readable trusted manifest": dict(manifest=tmp_path / "absent.json"),
    }
    for why, kw in cases.items():
        kw = {"trusted_env": env, "manifest": m, "elan_home": elan, **kw}
        r = run_replay("Foo", CB, wrapper=ran, **kw)
        assert r.status == "ERROR" and why.strip() in r.detail, (why, r.detail)
    # the env as the project adds no submission dir (its own build dir is trusted): nothing to replay Foo from
    r = run_replay("Foo", CB, project=env, trusted_env=env, manifest=m, elan_home=elan, wrapper=ran)
    assert r.status == "ERROR" and "did not list the target olean" in r.detail and log.exists(), r.detail
    log.unlink()
    (ml / "Mathlib" / "Basic.olean").write_bytes(b"tampered")
    r = run_replay("Foo", CB, trusted_env=env, manifest=m, elan_home=elan, wrapper=ran)
    assert r.status == "ERROR" and "differ" in r.detail
    assert not log.exists()


def test_run_replay_timeout_is_error(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    sub = _submission(tmp_path)
    r = run_replay("Foo", CB, untrusted_paths=[sub], trusted_env=env, manifest=m, elan_home=elan,
                   wrapper=_fake_lean(tmp_path / "log", "sleep"), timeout=1)
    assert r.status == "ERROR" and "did not finish" in r.detail


def test_build_trusted_manifest_refuses_to_overwrite_without_force(tmp_path):
    env, elan = _fake_env(tmp_path)
    m = build_trusted_manifest(env, tmp_path / "manifest.json", elan)
    with pytest.raises(ValueError, match="already exists"):
        build_trusted_manifest(env, m, elan)
    assert build_trusted_manifest(env, m, elan, force=True) == m


def test_run_reaps_the_process_group_after_a_normal_exit(tmp_path):
    pidfile = tmp_path / "daemon.pid"
    rc, out = run_lean(["sh", "-c", f"sleep 60 & echo $! > {pidfile}; echo hi"], tmp_path, 30)
    assert (rc, out) == (0, "hi\n")
    pid = int(pidfile.read_text())
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


# ---------------------------------------------------------------------------------------------------------------
# Pure: the rendered script.
def test_render_imports_only_trusted_modules_and_never_the_target(tmp_path):
    src = render_replay_script(["Mathlib", "Plausible"], "Foo.Bar", [tmp_path], CB, NONCE, ["/x", str(tmp_path)])
    imports = [ln for ln in src.splitlines() if ln.startswith("import ")]
    assert imports == ["import Mathlib", "import Plausible", "import Lean"]
    assert "def targetModules : List Name := [`Foo.Bar]" in src
    assert 'def expectOleans : List (Name × String) := [(`Foo.Bar, "")]' in src
    assert "def allowAxioms : Bool := false" in src and "def allowSorry : Bool := false" in src
    assert f'def tag : String := "{NONCE}"' in src
    assert f'def trustedPrefixes : List String := ["{os.path.realpath(tmp_path)}"]' in src
    assert f'(["/x", "{tmp_path}"] : List String)' in src          # the search path is data, not LEAN_PATH
    assert CB in src and "Kernel" not in CB
    assert "TelperionReplay.Replay.replay c.consts env" in src and "(← get).env.addDeclCore 0 0 d none" in src
    assert "setEnv env'" in src and "setEnv (Environment.ofKernelEnv" not in src
    assert "SearchPath.findWithExt searchPath" in src and "TelperionReplay.fidelity env env' c.consts" in src
    port = src[src.index("namespace Replay"):src.index("end Replay")]
    assert "]!" not in port and "unreachable!" not in port and "inductiveVal!" not in port


def test_render_targets_expectations_and_flags(tmp_path):
    # allow_axioms=True here is a test-only control of the flag's rendering; no check passes it (Ruling 10)
    src = render_replay_script(["Lean"], ["A", "B.C"], ["/"], CB, NONCE, expect_oleans={"A": "/x/A.olean"},
                               allow_axioms=True, allow_sorry=True)
    assert "def targetModules : List Name := [`A, `B.C]" in src
    assert 'def expectOleans : List (Name × String) := [(`A, "/x/A.olean"), (`B.C, "")]' in src
    assert "def allowAxioms : Bool := true" in src and "def allowSorry : Bool := true" in src


def test_resolve_olean_follows_import_resolution_and_the_closure_digest_is_canonical(tmp_path):
    a, b = tmp_path / "a", tmp_path / "b"
    (a / "Mathlib").mkdir(parents=True)
    (b / "Mathlib").mkdir(parents=True)
    (b / "Mathlib" / "Evil.olean").write_bytes(b"e")
    (b / "Solo.olean").write_bytes(b"s")
    # the first entry holding the root `Mathlib` wins, as in `SearchPath.findWithExt`: no Mathlib.Evil there
    assert resolve_olean([str(a), str(b)], "Mathlib.Evil") is None
    assert resolve_olean([str(b), str(a)], "Mathlib.Evil") == os.path.realpath(b / "Mathlib" / "Evil.olean")
    assert resolve_olean([str(a), str(b)], "Solo") == os.path.realpath(b / "Solo.olean")
    assert resolve_olean([str(a)], "Nope") is None
    x, y = ["M", "olean", "1" * 64], ["N", "olean.private", "2" * 64]
    assert closure_digest([x, y]) == closure_digest([y, x]) != closure_digest([x])
    assert closure_digest([x]) != closure_digest([["M", "olean", "3" * 64]])


def test_default_manifest_path_is_outside_the_env_and_tracks_its_pins(tmp_path, monkeypatch):
    monkeypatch.delenv("TELPERION_TRUSTED_MANIFEST", raising=False)
    env, _elan = _fake_env(tmp_path)
    p1 = default_manifest_path(env)
    assert p1.parent == Path(os.path.expanduser("~/telperion-tools/trusted-manifests")) and not under_prefix(p1, [env])
    (env / "lake-manifest.json").write_text('{"packages": []}')
    p2 = default_manifest_path(env)
    assert p2 != p1 and p2.parent == p1.parent
    monkeypatch.setenv("TELPERION_TRUSTED_MANIFEST", str(tmp_path / "m.json"))
    assert default_manifest_path(env) == tmp_path / "m.json"


def test_missing_default_manifest_names_the_build_command(tmp_path, monkeypatch):
    env, elan = _fake_env(tmp_path)
    monkeypatch.setenv("TELPERION_TRUSTED_MANIFEST", str(tmp_path / "absent.json"))
    r = run_replay("Foo", CB, trusted_env=env, elan_home=elan, wrapper=["false"])
    assert r.status == "ERROR" and f"telperion trusted-manifest build --env {os.path.realpath(env)}" in r.detail


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
    out = "noise\n" + _out("REPLAY OK modules=[Foo] constants=3 declared=[Foo.ax] axioms=[propext, Quot.sound]",
                           "CB a", "CB b", "DONE")
    st, detail, lines, needs = parse_replay_output(out, NONCE)
    assert (st, lines, needs) == ("OK", ["CB a", "CB b"], []) and parse_axioms(detail) == ["propext", "Quot.sound"]
    assert parse_declared(detail) == ["Foo.ax"] and parse_declared("axioms=[]") == []
    assert parse_axioms("modules=[Foo] constants=0 axioms=[]") == []
    assert parse_replay_output(_out("REPLAY FAILED (kernel) bad", "DONE"), NONCE)[:2] == ("FAILED", "(kernel) bad")
    assert parse_replay_output(_out("REPLAY NEEDS A.B C", "DONE"), NONCE) == ("NEEDS", "A.B C", [], ["A.B", "C"])


def test_parse_ignores_other_tags_and_refuses_broken_protocols():
    forged = _out("REPLAY OK modules=[] constants=0 axioms=[]", "CB forged", "DONE", tag="TR" + "cd" * 16)
    ok = _out("REPLAY FAILED x", "DONE")
    assert parse_replay_output(forged + ok, NONCE)[0] == "FAILED"
    broken = {
        "no replay line": _out("CB a", "DONE"),
        "two replay lines": _out("REPLAY OK axioms=[]", "REPLAY OK axioms=[]", "DONE"),
        "no done": _out("REPLAY OK axioms=[]", "CB a"),
        "done not last": _out("REPLAY OK axioms=[]", "DONE", "CB a"),
        "two dones": _out("REPLAY OK axioms=[]", "DONE", "DONE"),
        "line before replay": _out("CB a", "REPLAY OK axioms=[]", "DONE"),
        "lines after failed": _out("REPLAY FAILED x", "CB a", "DONE"),
        "lines after needs": _out("REPLAY NEEDS A", "CB a", "DONE"),
        "ok without axioms": _out("REPLAY OK modules=[] constants=0", "DONE"),
    }
    for why, out in broken.items():
        assert parse_replay_output(out, NONCE)[0] == "ERROR", why
    assert parse_replay_output(_out("REPLAY OK axioms=[]", "DONE"), NONCE, rc=1)[0] == "ERROR"
    st, detail, lines, _ = parse_replay_output(_out("REPLAY OK axioms=[]", "CB a", "CALLBACK FAILED boom", "DONE"),
                                               NONCE)
    assert (st, detail, lines) == ("ERROR", "the callback failed: boom", ["CB a", "CALLBACK FAILED boom"])


# ---------------------------------------------------------------------------------------------------------------
# Lean tests. Each module is compiled into its OWN dir `<env>/.tp_replay_<hex>/` (an untrusted path for the runs that
# test it); nothing in the env's shared `.lake/build` is written or removed. The manifest is built once per session in
# a temp dir.
LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")
CLEAN = {"propext", "Classical.choice", "Quot.sound"}

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

TINY = "theorem TpTiny.t : 1 + 1 = 2 := rfl\n"
AXIOM = "axiom TpAx.bad : False\ntheorem TpAx.t : 1 = 2 := TpAx.bad.elim\n"
SORRY = "theorem TpSorry.t : 1 = 2 := sorry\n"

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

# I1 as a unit test of the script's own comparison, on crafted ConstantInfos against the live environment.
FIDELITY_CB = r"""open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  let env ← getEnv
  let add ← getConstInfo ``Nat.add
  let .defnInfo v := add | throwError "Nat.add is not a definition"
  let comm ← getConstInfo ``Nat.add_comm
  let .thmInfo tv := comm | throwError "Nat.add_comm is not a theorem"
  let implicit := match v.type with
    | .forallE n t b _ => Expr.forallE n t b .implicit
    | e => e
  let cases : List (String × Name × ConstantInfo) := [
    ("same", ``Nat.add, add),
    ("value", ``Nat.add, .defnInfo { v with value := mkConst ``Nat.zero }),
    ("binder", ``Nat.add, .defnInfo { v with type := implicit }),
    ("dedup", ``Nat.add_comm, .thmInfo { tv with value := mkConst ``True.intro }),
    ("missing", `TpNoSuch.thm, .thmInfo { tv with name := `TpNoSuch.thm })]
  for (label, n, ci) in cases do
    let r := match TelperionReplay.fidelity env env (Std.HashMap.ofList [(n, ci)]) with
      | .ok _ => "ok" | .error _ => "refused"
    TelperionReplay.line s!"CB-FID {label} {r}"
"""


def _wrapper(lib: Path | None = None) -> list[str]:
    return (["env", f"LEAN_PATH={lib}"] if lib else []) + lean_replay.default_wrapper()


@pytest.fixture(scope="session")
def manifest(tmp_path_factory):
    return build_trusted_manifest(LEAN_ENV, tmp_path_factory.mktemp("manifest") / "trusted.json")


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
    p = subprocess.run([*_wrapper(lib), "lake", "env", "lean", "-R", str(lib / "src"), "-o", str(out), str(src)],
                       cwd=LEAN_ENV, capture_output=True, text=True, timeout=3600)
    shutil.rmtree(lib / "src")
    assert p.returncode == 0, p.stdout + p.stderr


def _sha(path: Path) -> str:
    import hashlib
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _import_normally(lib: Path, body: str) -> str:
    """Output of a `lake env lean` file that IMPORTS the module the usual way (the control for what replay avoids)."""
    f = lib / "Control.lean"
    f.write_text(body, encoding="utf-8")
    p = subprocess.run([*_wrapper(lib), "lake", "env", "lean", str(f)], cwd=LEAN_ENV, capture_output=True,
                       text=True, timeout=3600)
    f.unlink()
    return p.stdout + p.stderr


def _replay(lib: Path, manifest: Path, target: str, cb: str, **kw):
    return run_replay(target, cb, untrusted_paths=[lib], trusted_env=LEAN_ENV, manifest=manifest, **kw)


@lean
def test_a_replayed_types_are_identical_to_imported_ones(lib, manifest):
    _build(lib, "TpHonest", HONEST)
    r = _replay(lib, manifest, "TpHonest", TYPE_CB)
    assert r.status == "OK" and "modules=[TpHonest]" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.axioms is not None and set(r.axioms) <= CLEAN, r.axioms
    closure = [["TpHonest", "olean", _sha(lib / "TpHonest.olean")]]
    assert r.olean_closure == closure and r.olean_sha256 == closure_digest(closure)
    replayed = [ln for ln in r.lines if ln.startswith("TYPE ")]
    assert len(replayed) == 4
    # The same types through a normal import. `repr` of an Expr is its whole tree (binder names and infos, levels,
    # mdata), so equal strings mean Expr.equal types.
    ctl = _import_normally(lib, "import Mathlib\nimport TpHonest\n" + TYPE_CB.replace("TelperionReplay.line", "IO.println")
                           + "#eval TelperionReplay.callback\n")
    imported = [ln for ln in ctl.splitlines() if ln.startswith("TYPE ")]
    assert imported == replayed, ctl[-3000:]


@lean
def test_b_evil_module_runs_nothing(lib, manifest):
    _build(lib, "TpEvil", EVIL)
    # Control: imported the usual way, all three shapes fire (the initializer, the `#eval` override, the tactic).
    ctl = _import_normally(lib, "import TpEvil\nexample : ∀ x : Nat, x < 3 → x < 5 := by intro x h; omega\n"
                                "#eval IO.println \"CONTROL-EVAL-RAN\"\n")
    assert all(m in ctl for m in ("TPEVIL-INIT", "TPEVIL-TACTIC", "TPEVIL-EVAL")), ctl[-3000:]
    assert "CONTROL-EVAL-RAN" not in ctl
    # Replayed: none of them runs, and the callback's own values are reported.
    r = _replay(lib, manifest, "TpEvil", EVIL_CB, trusted_imports=("Lean",))
    assert "TPEVIL" not in r.output, r.output[-3000:]
    assert r.status == "OK" and "modules=[TpEvil]" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.lines == ["CB-FOUND TpEvil.t", "CB-EVALATTR true", "CB-OMEGA goals=0 sorry=false"]
    assert "sorryAx" not in r.axioms


@lean
def test_c_kernel_invalid_module_is_rejected(lib, manifest):
    _build(lib, "TpBogus", BOGUS)
    r = _replay(lib, manifest, "TpBogus", FOUND_CB, trusted_imports=("Lean",))
    assert r.status == "FAILED" and "(kernel)" in r.detail and "TpBogus.bogus" in r.detail, (r.status, r.detail)
    assert r.lines == []


@lean
def test_d_mathlib_named_module_outside_the_prefixes_is_never_trusted(lib, manifest):
    # An import resolves `Mathlib.Evil` under the Mathlib package (the first entry holding the root `Mathlib`), where
    # no such .olean exists; the one in the submission dir is refused, not read and not trusted.
    _build(lib, "Mathlib.Evil", MATHLIB_EVIL)
    r = _replay(lib, manifest, "Mathlib.Evil", FOUND_CB)
    assert "TPEVIL" not in r.output
    assert r.status == "FAILED" and "an import would not find" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.lines == []


@lean
def test_e_trusted_target_and_missing_target_are_refused(lib, manifest):
    r = _replay(lib, manifest, "Mathlib.Order.Basic", FOUND_CB, trusted_imports=("Mathlib.Order.Basic",))
    assert r.status == "FAILED" and "resolves to the trusted" in r.detail, (r.status, r.detail)
    r = _replay(lib, manifest, "TpNeverBuilt", FOUND_CB, trusted_imports=("Lean",))
    assert r.status == "FAILED" and "build it first" in r.detail, (r.status, r.detail)


@lean
def test_f_needed_trusted_module_is_added(lib, manifest):
    _build(lib, "TpHonest", HONEST)
    r = _replay(lib, manifest, "TpHonest", TYPE_CB, trusted_imports=("Lean",))
    assert r.status == "OK" and len(r.lines) == 4, (r.status, r.detail, r.output[-3000:])


@lean
def test_g_module_system_file_is_read_in_full(lib, manifest):
    # A `module` file's exported part holds a theorem as an AXIOM, and its private data (here a non-public def) is
    # in `.olean.private`; all parts are read (and checked against each other), so the theorem comes back with its
    # proof.
    _build(lib, "TpMod", MODULE_FILE)
    r = _replay(lib, manifest, "TpMod", MODULE_CB, trusted_imports=("Lean",))
    assert r.status == "OK", (r.status, r.detail, r.output[-3000:])
    assert r.lines == ["CB-KIND TpMod.t theorem", "CB-KIND TpMod.hidden def"]


@lean
def test_h_callback_heartbeat_timeout_is_reported_and_done_still_printed(lib, manifest):
    _build(lib, "TpTiny", TINY)
    r = _replay(lib, manifest, "TpTiny", BUSY_CB, trusted_imports=("Lean",), heartbeats=1)
    assert r.status == "ERROR" and "heartbeats" in r.detail, (r.status, r.detail, r.output[-3000:])
    assert r.lines[0] == "CB start" and "CB unreachable" not in r.lines


@lean
def test_i_untrusted_axiom_is_refused(lib, manifest):
    _build(lib, "TpAx", AXIOM)
    r = _replay(lib, manifest, "TpAx", FOUND_CB, trusted_imports=("Lean",))
    assert r.status == "FAILED" and "declares the axiom TpAx.bad" in r.detail, (r.status, r.detail)
    assert r.lines == []
    # test-only control: the flag works when set; no check sets it (Ruling 10: untrusted axioms are refused)
    r = _replay(lib, manifest, "TpAx", FOUND_CB, trusted_imports=("Lean",), allow_axioms=True)
    assert r.status == "OK" and r.declared == ["TpAx.bad"] and "TpAx.bad" in r.axioms, (r.status, r.detail)


@lean
def test_j_sorry_in_the_target_is_refused(lib, manifest):
    _build(lib, "TpSorry", SORRY)
    r = _replay(lib, manifest, "TpSorry", FOUND_CB, trusted_imports=("Lean",))
    assert r.status == "FAILED" and "uses sorryAx" in r.detail, (r.status, r.detail)
    assert r.lines == []
    r = _replay(lib, manifest, "TpSorry", FOUND_CB, trusted_imports=("Lean",), allow_sorry=True)
    assert r.status == "OK" and "sorryAx" in r.axioms, (r.status, r.detail)


@lean
def test_k_fidelity_comparison(lib, manifest):
    _build(lib, "TpTiny", TINY)
    r = _replay(lib, manifest, "TpTiny", FIDELITY_CB, trusted_imports=("Lean",))
    assert r.status == "OK", (r.status, r.detail, r.output[-3000:])
    assert r.axioms == []
    assert r.lines == ["CB-FID same ok", "CB-FID value refused", "CB-FID binder refused", "CB-FID dedup ok",
                       "CB-FID missing refused"]


@lean
def test_l_target_olean_binding_and_several_targets(lib, manifest):
    _build(lib, "TpTiny", TINY)
    _build(lib, "TpSorry", SORRY)
    r = _replay(lib, manifest, "TpTiny", FOUND_CB, trusted_imports=("Lean",), expect_oleans={"TpTiny": "/nowhere.olean"})
    assert r.status == "FAILED" and "olean-mismatch TpTiny" in r.detail, (r.status, r.detail)
    r = _replay(lib, manifest, ["TpTiny", "TpSorry"], FOUND_CB, trusted_imports=("Lean",), allow_sorry=True)
    assert r.status == "OK" and "modules=[TpTiny, TpSorry]" in r.detail, (r.status, r.detail)
    closure = sorted([m, "olean", _sha(lib / f"{m}.olean")] for m in ("TpTiny", "TpSorry"))
    assert r.olean_closure == closure and r.olean_sha256 == closure_digest(closure)


@lean
def test_m_changing_an_untrusted_dependency_changes_the_binding(lib, manifest):
    # R2-I2: M imports the untrusted N; rebuilding N with a different statement must change olean_sha256 although
    # M's own olean is unchanged
    _build(lib, "TpN", "theorem TpN.a : 1 = 1 := rfl\n")
    _build(lib, "TpM", "import TpN\ntheorem TpM.t : True := trivial\n")
    r1 = _replay(lib, manifest, "TpM", FOUND_CB, trusted_imports=("Lean",))
    assert r1.status == "OK" and "TpN" in r1.detail, (r1.status, r1.detail)
    assert sorted(e[0] for e in r1.olean_closure) == ["TpM", "TpN"]
    m_before = _sha(lib / "TpM.olean")
    _build(lib, "TpN", "theorem TpN.a : 2 = 2 := rfl\n")
    assert _sha(lib / "TpM.olean") == m_before
    r2 = _replay(lib, manifest, "TpM", FOUND_CB, trusted_imports=("Lean",))
    assert r2.status == "OK", (r2.status, r2.detail)
    assert r2.olean_sha256 != r1.olean_sha256
    m1 = [e for e in r1.olean_closure if e[0] == "TpM"]
    assert m1 == [e for e in r2.olean_closure if e[0] == "TpM"] and m1[0][2] == m_before

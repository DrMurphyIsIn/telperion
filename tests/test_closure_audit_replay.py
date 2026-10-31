"""The closure audit as a kernel-replay callback (step 5 Task 7): `audit-closure` no longer imports the submission.

The legacy audit (`run_closure_audit`) runs `lake env lean` on a script that IMPORTS the submission, so the
submission's lakefile, initializers and elaborators run in the audit process and can forge its PASS. The replayed
audit (`run_closure_audit_replayed`) runs the same closure walk as a `TelperionReplay.callback` (checks/lean_replay.py):
trusted imports only, the untrusted closure read as data from private copies and kernel-replayed, untrusted axioms
refused, the result bound to the replayed oleans by `olean_sha256`, and no lake.

Pure tests: rendering (every name is string DATA, never syntax), the mapping from a replay result to an AuditResult,
the import split, and the CLI. Lean tests (TELPERION_LEAN_ENV set): parity with the legacy audit on a clean module,
the step-4 evil module, a module whose legacy PASS is forged, `sorryAx`, an untrusted axiom and a re-declared name.
"""
from __future__ import annotations

import json
import os
import re
import secrets
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))  # shared lean_env helpers

from telperion import closure_audit  # noqa: E402
from telperion.checks import lean_replay  # noqa: E402
from telperion.checks.lean_replay import ReplayResult, closure_digest, render_replay_script  # noqa: E402
from telperion.closure_audit import (  # noqa: E402
    PROTOCOL_VERSION,
    AuditResult,
    AuditSpec,
    parse_audit_output,
    render_audit_callback,
    replayed_audit_result,
    run_closure_audit,
    run_closure_audit_replayed,
)
from telperion.comparator import CLEAN_AXIOMS  # noqa: E402

NONCE = "N" + "ab" * 8


def _spec(**kw) -> AuditSpec:
    base = dict(imports=("Foo.Bar",), targets=("Foo.main",))
    base.update(kw)
    return AuditSpec(**base)


def _string_literals(text: str) -> list[str]:
    """The Lean string literals in `text` (enough of Lean's lexer for what the renderer emits)."""
    return re.findall(r'"(?:[^"\\]|\\.)*"', text)


def _outside_strings(text: str) -> str:
    return re.sub(r'"(?:[^"\\]|\\.)*"', '""', text)


# ---------------------------------------------------------------------------------------------------------------
# Pure: rendering the callback.
def test_callback_renders_every_name_as_string_data():
    """Targets, library roots, absent constants, absent module prefixes and allowed axioms reach Lean as lists of
    string components fed to `Name.mkStr`, never as name literals or other syntax."""
    spec = _spec(targets=("Foo.main", "Foo.aux'"), absent_module_prefixes=("NegControls",),
                 absent_constants=("sorryAx", "Lean.ofReduceBool"), scan_patterns=("heegner",))
    text = render_audit_callback(spec, NONCE)
    code = _outside_strings(text)
    for name in ("Foo", "main", "aux'", "NegControls", "ofReduceBool", "heegner", "Classical", "choice"):
        assert f'"{name}"' in text, name
    assert "Foo.main" not in code and "NegControls" not in code and "heegner" not in code
    assert "`" not in code.replace("``", ""), [ln for ln in code.splitlines() if "`" in ln]
    assert "Name.mkStr" in text
    assert "def TelperionReplay.callback (c : TelperionReplay.Closure)" in text
    assert not re.search(r"(?m)^\s*(import|#eval)\b", code) and "#eval" not in code


@pytest.mark.parametrize("field", ["targets", "absent_constants", "absent_module_prefixes", "allowed_axioms",
                                   "library_roots", "scan_patterns"])
def test_callback_injection_attempts_stay_inside_string_literals(field):
    """The step-5 Task 2 injection class: a name with a quote, a newline and a Lean command in it must stay data."""
    evil = 'Evil"\n#eval IO.println "pwned"\nimport Foo -- »]'
    spec = _spec(**{field: (evil,) if field != "targets" else ("Foo.main", evil)})
    text = render_audit_callback(spec, NONCE)
    code = _outside_strings(text)
    assert "pwned" not in code and "#eval" not in code and not re.search(r"(?m)^\s*import\b", code)
    assert not any(ln.lstrip().startswith(("#eval", "import")) for ln in text.splitlines())
    assert any("pwned" in s for s in _string_literals(text))


def test_callback_placeholders_are_substituted_once():
    """A value that spells another placeholder is not substituted again (a sequential replace would let a target
    named `__SCAN_PATTERNS__` pull the scan list's source into its own literal)."""
    spec = _spec(targets=("Foo.__SCAN_PATTERNS__",), scan_patterns=("__targets__",))
    text = render_audit_callback(spec, NONCE)
    assert '"__SCAN_PATTERNS__"' in text and '"__targets__"' in text
    assert not re.search(r"__[A-Z_]+__", _outside_strings(text))


def test_callback_walk_matches_the_legacy_script():
    """The same closure walk (`.rec` per inductive, or the reviewer's getUsedConstantsAsSet), both axiom checks and
    the consistency cross-check; the module of a replayed constant comes from the replay's closure."""
    text = render_audit_callback(_spec(), NONCE)
    for piece in ("ci.getUsedConstantsAsSet.toArray", 'Name.mkStr n "rec"',
                  "some (.axiomInfo _) => axiomAcc := axiomAcc.push n", "collectAxioms t",
                  "inconsistent environment", "c.moduleOf", "c.modules", PROTOCOL_VERSION):
        assert piece in text, piece
    assert f'"{NONCE}"' in text
    assert "def includeRecursors : Bool := true" in text
    assert "def includeRecursors : Bool := false" in render_audit_callback(_spec(include_recursors=False), NONCE)
    assert "def closureOut : Option String := none" in text
    out = render_audit_callback(_spec(closure_out='/tmp/a "b"\n.txt'), NONCE)
    assert 'def closureOut : Option String := some "/tmp/a \\"b\\"\\n.txt"' in out


def test_callback_rejects_bad_nonce_and_empty_components():
    with pytest.raises(ValueError):
        render_audit_callback(_spec(), 'x"y')
    with pytest.raises(ValueError):
        render_audit_callback(_spec(targets=("Foo..bar",)), NONCE)


def test_replay_script_passes_the_closure_to_a_closure_callback():
    """lean_replay calls `TelperionReplay.callback c` (c: the replayed closure, which records each constant's module)
    only when asked; the probe's and the fingerprint's `callback : TermElabM Unit` contract is unchanged."""
    args = (["Lean"], "Foo", ["/t"], "def TelperionReplay.callback := 0\n", "TR" + "0" * 32)
    default = render_replay_script(*args)
    closure = render_replay_script(*args, callback_takes_closure=True)
    assert "tryCatchRuntimeEx (TelperionReplay.callback) fun ex" in default
    assert "tryCatchRuntimeEx (TelperionReplay.callback c) fun ex" in closure
    assert "moduleOf : Std.HashMap Name Name" in default
    assert "moduleOf := out.moduleOf.insert c.name m" in default


def test_callback_numeric_components_are_name_num():
    """Cleanup M5: a bare-digit component is a `Name.num`, as Lean's own `Name.toString` prints one (a STRING
    component "0" prints as `«0»`). So a private constant `_private.Foo.0.Foo.bar` can be named in absent_constants,
    absent_module_prefixes and targets; with string components it could never match (vacuously "absent")."""
    text = render_audit_callback(_spec(targets=("_private.Foo.0.Foo.bar",), absent_constants=("_private.Foo.0.x",),
                                       absent_module_prefixes=("A.12",)), NONCE)
    assert '[.str "_private", .str "Foo", .num 0, .str "Foo", .str "bar"]' in text
    assert '[.str "_private", .str "Foo", .num 0, .str "x"]' in text and '[.str "A", .num 12]' in text
    assert '.str "0x"' in render_audit_callback(_spec(targets=("A.0x",)), NONCE)
    for odd in ("A.007", "A.00"):
        with pytest.raises(ValueError, match="leading zero"):
            render_audit_callback(_spec(targets=(odd,)), NONCE)


def test_callback_emit_flattens_tabs_in_fields():
    """Cleanup M3: a field (an untrusted constant or module name) cannot split a protocol line into more fields."""
    text = render_audit_callback(_spec(), NONCE)
    assert '(fields.map (fun f => "\\t" ++ f.replace "\\t" " "))' in text


def test_replay_render_is_single_pass_and_refuses_placeholder_modules():
    """Cleanup M1: a value (a search-path entry, an expected olean path) that spells a placeholder is not rescanned,
    and a module component that spells one is refused before anything is rendered."""
    cb = "def TelperionReplay.callback : Lean.Elab.Term.TermElabM Unit := pure () -- CB-MARK\n"
    text = render_replay_script(["Lean"], "Foo", ["/t"], cb, "TR" + "0" * 32,
                                search_path=["/tmp/__CALLBACK__/x", "/tmp/__HEARTBEATS__"],
                                expect_oleans={"Foo": "/tmp/__ALLOW_SORRY__.olean"})
    assert text.count("CB-MARK") == 1
    assert '"/tmp/__CALLBACK__/x"' in text and '"/tmp/__HEARTBEATS__"' in text
    assert '"/tmp/__ALLOW_SORRY__.olean"' in text
    for bad in ("Evil.__CALLBACK__", "__TARGETS__", "Evil.__ALLOW_SORRY__.X"):
        with pytest.raises(ValueError):
            lean_replay._module(bad)
        with pytest.raises(ValueError):
            render_replay_script(["Lean"], bad, ["/t"], cb, "TR" + "0" * 32)
        with pytest.raises(ValueError):
            render_replay_script([bad], "Foo", ["/t"], cb, "TR" + "0" * 32)
    lean_replay._module("Evil.__init")          # an ordinary dunder-ish name is still fine


# ---------------------------------------------------------------------------------------------------------------
# Pure: a replay result as an AuditResult.
def _lines(nonce: str, *rows) -> list[str]:
    return ["@@" + nonce + "\t" + "\t".join(r) for r in rows]


def _ok_lines(nonce: str, verdict: str = "PASS", failures=()) -> list[str]:
    rows = [("protocol", PROTOCOL_VERSION), ("lean_version", "4.35.0"), ("include_recursors", "true"),
            ("target", "Foo.main", "theorem", "1 + 1 = 2"), ("closure_size", "3"), ("per_root", "Foo", "1"),
            ("per_root", "Init", "2"), ("nonlib_module", "Foo.Bar", "1"), ("nonlib_const", "Foo.Bar", "Foo.main"),
            ("absent_const", "sorryAx", "false"), ("closure_axioms", "propext"),
            ("axioms", "Foo.main", "propext"), ("axioms_consistent", "true")]
    rows += [("failure", f) for f in failures]
    rows.append(("verdict", verdict))
    return _lines(nonce, *rows)


CLOSURE = [["Foo.Bar", "olean", "f" * 64]]


def _ok(lines) -> ReplayResult:
    return ReplayResult("OK", "modules=[Foo.Bar] constants=3 declared=[] axioms=[propext]", lines, "the output",
                        ["propext"], [], closure_digest(CLOSURE), CLOSURE)


def test_replay_ok_maps_to_an_isolated_audit_result():
    res = replayed_audit_result(_ok(_ok_lines(NONCE)), NONCE)
    assert res.verdict == "PASS" and res.ok and res.lean_exit_code == 0
    assert res.isolated is True
    assert res.olean_sha256 == closure_digest(CLOSURE) and res.olean_closure == CLOSURE
    assert res.closure_size == 3 and res.nonlib_modules == {"Foo.Bar": ["Foo.main"]}
    assert res.targets[0].axioms == ["propext"] and res.closure_axioms == ["propext"]
    fail = replayed_audit_result(_ok(_ok_lines(NONCE, "FAIL", ["forbidden constant sorryAx is in the closure"])),
                                 NONCE)
    assert fail.verdict == "FAIL" and not fail.ok and fail.isolated and fail.olean_sha256


@pytest.mark.parametrize("mutate, why", [
    (lambda ls: ls[:-1] + ["something else"] + ls[-1:], "outside the audit protocol"),
    (lambda ls: ls + _lines("OTHER", ("verdict", "PASS")), "outside the audit protocol"),
    (lambda ls: ls[:-1] + ls[-1:] + ls[3:4], "not the last"),
    (lambda ls: ls + ls[-1:], "2 verdict lines"),
])
def test_replay_callback_lines_outside_the_protocol_fail_integrity(mutate, why):
    res = replayed_audit_result(_ok(mutate(_ok_lines(NONCE))), NONCE)
    assert res.verdict == "FAIL" and not res.ok, res
    assert any(f.startswith("integrity:") and why in f for f in res.failures), res.failures


def test_replay_ok_without_a_verdict_is_no_verdict():
    res = replayed_audit_result(_ok(_ok_lines(NONCE)[:-1]), NONCE)
    assert res.verdict == "" and not res.ok and any("no verdict" in f for f in res.failures)


def test_replay_ok_with_a_malformed_protocol_line_is_no_verdict():
    """Cleanup M3: a malformed line (e.g. an untrusted module name with a TAB shifting a count) is a no-verdict
    result, never an exception out of `replayed_audit_result` (which the library promises)."""
    lines = _ok_lines(NONCE)
    lines.insert(5, "@@" + NONCE + "\tper_root\tEvil\tnot-a-number")
    res = replayed_audit_result(_ok(lines), NONCE)
    assert res.verdict == "" and not res.ok and res.isolated
    assert any("malformed" in f for f in res.failures), res.failures


@pytest.mark.parametrize("status, detail, verdict, why", [
    ("FAILED", "the untrusted module Foo.Bar declares the axiom Foo.bad; refusing", "FAIL", "Foo.bad"),
    ("FAILED", "while replaying declaration 'Foo.bogus': (kernel) declaration type mismatch", "FAIL", "(kernel)"),
    ("FAILED", "the target module uses sorryAx (axioms=[sorryAx])", "FAIL", "sorryAx"),
    ("FAILED", "module Foo.Bar has no .olean in the search path (build it first)", "", "build it first"),
    ("ERROR", "lean exited 137: 'killed'", "", "lean exited 137"),
    ("ERROR", "the callback failed: maximum recursion depth", "", "the callback failed"),
])
def test_replay_refusals_map_to_fail_or_no_verdict(status, detail, verdict, why):
    """Ruling 10: an untrusted axiom is refused by replay itself; the audit is a FAIL naming it, not a crash. A
    kernel rejection is a FAIL. An unbuilt module or a broken run gives no verdict (exit 2)."""
    res = replayed_audit_result(ReplayResult(status, detail, [], "out"), NONCE)
    assert res.verdict == verdict and not res.ok
    assert res.isolated is True and res.olean_sha256 is None
    assert any(why in f for f in res.failures), res.failures
    if "declares the axiom" in detail:
        assert any("untrusted axiom Foo.bad" in f and "Ruling 10" in f for f in res.failures), res.failures


def test_audit_result_json_carries_isolation_fields():
    """Backward compatible: every legacy key is still there; the legacy path says isolated false."""
    legacy = parse_audit_output("@@N\tprotocol\tx\n@@N\tverdict\tPASS\n", nonce="N")
    d = json.loads(legacy.to_json())
    assert d["isolated"] is False and d["olean_sha256"] is None and d["olean_closure"] == []
    for key in ("protocol", "targets", "closure_size", "closure_axioms", "axioms_consistent", "verdict", "ok"):
        assert key in d
    rep = json.loads(replayed_audit_result(_ok(_ok_lines(NONCE)), NONCE).to_json())
    assert rep["isolated"] is True and rep["olean_sha256"] == closure_digest(CLOSURE)
    assert rep["olean_closure"] == CLOSURE and rep["verdict"] == "PASS" and rep["ok"] is True
    assert "NOT ISOLATED" in legacy.render() and "kernel replay" in replayed_audit_result(
        _ok(_ok_lines(NONCE)), NONCE).render()


def test_run_replayed_splits_trusted_and_untrusted_imports(tmp_path, monkeypatch):
    """An import that resolves to a trusted .olean is imported; every other one is a replay target. The callback
    takes the closure, untrusted axioms stay refused, and the result is bound to the replay's olean digest."""
    from lean_env import fake_trusted_env
    env, elan, manifest = fake_trusted_env(tmp_path)
    proj = tmp_path / "proj"
    (proj / ".lake" / "build" / "lib" / "lean" / "Demo").mkdir(parents=True)
    (proj / ".lake" / "build" / "lib" / "lean" / "Demo" / "Proof.olean").write_bytes(b"x")
    seen = {}

    def fake(targets, callback, **kw):
        seen.update(kw, targets=targets, callback=callback)
        nonce = re.search(r'def nonce : String := "([0-9a-f]+)"', callback).group(1)
        return _ok(_ok_lines(nonce))

    monkeypatch.setattr(lean_replay, "run_replay", fake)
    res = run_closure_audit_replayed(_spec(imports=("Mathlib", "Demo.Proof"), closure_out="rel/out.txt"), proj,
                                     trusted_env=env, manifest=manifest, elan_home=elan, wrapper=[])
    assert res.ok and res.isolated and res.olean_sha256 == closure_digest(CLOSURE)
    assert seen["targets"] == ["Demo.Proof"] and seen["trusted_imports"] == ["Mathlib"]
    assert seen["callback_takes_closure"] is True and seen["allow_sorry"] is True
    assert not seen.get("allow_axioms") and seen["manifest"] == manifest
    assert seen["untrusted_paths"] == [os.path.realpath(proj / ".lake" / "build" / "lib" / "lean")]
    # a relative closure file is the caller's, not the private run dir's (which is removed)
    assert f'some "{os.path.abspath("rel/out.txt")}"' in seen["callback"]


def test_run_replayed_without_a_trusted_env_is_no_verdict(tmp_path, monkeypatch):
    monkeypatch.delenv("TELPERION_LEAN_ENV", raising=False)
    res = run_closure_audit_replayed(_spec(), tmp_path)
    assert res.verdict == "" and not res.ok and any("trusted env" in f for f in res.failures), res.failures


# ---------------------------------------------------------------------------------------------------------------
# Pure: the CLI.
def test_cli_audit_closure_replays_by_default(tmp_path, monkeypatch, capsys):
    from telperion.cli import main
    calls = []

    def fake(spec, project, **kw):
        calls.append((spec, project, kw))
        return replayed_audit_result(_ok(_ok_lines(NONCE)), NONCE)

    monkeypatch.setattr(closure_audit, "run_closure_audit_replayed", fake)
    monkeypatch.setattr(closure_audit, "run_closure_audit",
                        lambda *a, **k: pytest.fail("the legacy import path ran without --legacy-import"))
    js = tmp_path / "c.json"
    rc = main(["audit-closure", "--project", str(tmp_path), "--import", "Foo.Bar", "--target", "Foo.main",
               "--trusted-env", str(tmp_path / "env"), "--memory-mb", "0", "--wrapper", "", "--json", str(js)])
    assert rc == 0 and len(calls) == 1
    _spec_, project, kw = calls[0]
    assert Path(project) == tmp_path and kw["trusted_env"] == tmp_path / "env"
    assert kw["memory_mb"] is None and kw["wrapper"] == []
    d = json.loads(js.read_text())
    assert d["isolated"] is True and d["olean_sha256"] == closure_digest(CLOSURE)
    assert "NOT ISOLATED" not in capsys.readouterr().err


def test_cli_legacy_import_warns_not_isolated(tmp_path, monkeypatch, capsys):
    from telperion.cli import main
    monkeypatch.setattr(closure_audit, "run_closure_audit_replayed",
                        lambda *a, **k: pytest.fail("the replayed path ran under --legacy-import"))
    monkeypatch.setattr(closure_audit, "run_closure_audit",
                        lambda spec, project, **kw: parse_audit_output("@@N\tprotocol\tx\n@@N\tverdict\tPASS\n",
                                                                       nonce="N"))
    js = tmp_path / "c.json"
    assert main(["audit-closure", "--legacy-import", "--project", str(tmp_path), "--import", "Foo.Bar",
                 "--target", "Foo.main", "--json", str(js)]) == 0
    err = capsys.readouterr().err
    assert "NOT ISOLATED" in err and "checks-record" in err
    assert json.loads(js.read_text())["isolated"] is False


def test_cli_script_path_needs_legacy_import(tmp_path, capsys):
    from telperion.cli import main
    assert main(["audit-closure", "--project", str(tmp_path), "--import", "A", "--target", "A.t",
                 "--script-path", str(tmp_path / "Audit.lean")]) == 2
    assert "--legacy-import" in capsys.readouterr().out


def test_cli_render_only_writes_the_callback(tmp_path):
    from telperion.cli import main
    out = tmp_path / "cb.lean"
    assert main(["audit-closure", "--project", str(tmp_path), "--import", "A.B", "--target", "A.t",
                 "--render-only", str(out)]) == 0
    text = out.read_text()
    assert "def TelperionReplay.callback (c : TelperionReplay.Closure)" in text and '.str "A", .str "t"' in text
    assert "import A.B" not in text


# ---------------------------------------------------------------------------------------------------------------
# Lean tests. Modules are compiled into their own dir `<env>/.tp_audit_<hex>/` (an untrusted path), as the replay
# tests do; nothing in the env's shared `.lake/build` is written. The legacy audit runs `lake env lean` in the env with
# that dir on LEAN_PATH, exactly as test_lean_replay's import control does.
LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")

from test_lean_replay import AXIOM, EVIL, HONEST, SORRY  # noqa: E402

# The legacy audit's hole, made concrete: under a normal import this replaces `#eval`, reads the audit's per-run nonce
# out of the audit script's own definitions, and prints a forged PASS for a theorem proved by `sorry`.
FORGE = r'''import Lean
open Lean Elab Command
@[command_elab Lean.Parser.Command.eval] def tpForgeEval : CommandElab := fun _ => do
  if let some (.defnInfo v) := (← getEnv).find? `TelperionClosureAudit.nonce then
    if let .lit (.strVal n) := v.value.consumeMData then
      IO.println s!"@@{n}\tprotocol\ttelperion-closure-audit/1"
      IO.println s!"@@{n}\tverdict\tPASS"
theorem TpForge.t : 1 = 2 := sorry
'''

DUP_A = "theorem TpDup.t : 1 = 1 := rfl\n"
DUP_B = "theorem TpDup.t : 1 = 1 := Eq.refl 1\n"


@pytest.fixture(scope="module")
def manifest():
    from lean_env import session_trusted_manifest
    return session_trusted_manifest(LEAN_ENV)


@pytest.fixture
def lib():
    d = Path(LEAN_ENV) / f".tp_audit_{secrets.token_hex(8)}"
    d.mkdir()
    yield d
    shutil.rmtree(d, ignore_errors=True)


def _build(lib: Path, module: str, body: str) -> None:
    from test_lean_replay import _build as build
    build(lib, module, body)


def _replayed(lib: Path, manifest: Path, spec: AuditSpec) -> AuditResult:
    return run_closure_audit_replayed(spec, None, untrusted_paths=[lib], trusted_env=LEAN_ENV, manifest=manifest)


def _legacy(lib: Path, spec: AuditSpec) -> AuditResult:
    from test_lean_replay import _wrapper
    return run_closure_audit(spec, LEAN_ENV, wrapper=_wrapper(lib), script_path=lib / "LegacyAudit.lean")


def _sha(path: Path) -> str:
    import hashlib
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


@lean
@pytest.mark.parametrize("recursors", [True, False])
def test_lean_parity_with_the_legacy_audit_on_a_clean_module(lib, manifest, recursors):
    """On a clean module the replayed audit computes what the legacy (import) audit does: the same closure, census,
    non-library listing, scan hits, absences, axioms and statements, in both walk modes."""
    _build(lib, "TpHonest", HONEST)
    spec = dict(imports=("TpHonest",), targets=("TpHonest.sq_le", "TpHonest.Color.toNat"),
                scan_patterns=("color", "nat.le_mul"), absent_module_prefixes=("TpNeg", "Mathlib.Tactic.Linarith"),
                include_recursors=recursors)
    old = _legacy(lib, AuditSpec(**spec, closure_out=str(lib / "legacy.txt")))
    new = _replayed(lib, manifest, AuditSpec(**spec, closure_out=str(lib / "replayed.txt")))
    assert old.verdict == "PASS" and old.ok and not old.isolated, (old.failures, old.raw_tail)
    assert new.verdict == "PASS" and new.ok and new.isolated, (new.failures, new.raw_tail)
    closure = [["TpHonest", "olean", _sha(lib / "TpHonest.olean")]]
    assert new.olean_closure == closure and new.olean_sha256 == closure_digest(closure)
    assert (lib / "replayed.txt").read_text() == (lib / "legacy.txt").read_text()
    assert new.closure_size == old.closure_size > 100
    for f in ("lean_version", "include_recursors", "per_root", "closure_axioms", "axioms_consistent",
              "absent_constants", "absent_modules", "env_modules_per_root", "failures"):
        assert getattr(new, f) == getattr(old, f), f
    assert [(t.name, t.kind, t.axioms, t.statement) for t in new.targets] == \
        [(t.name, t.kind, t.axioms, t.statement) for t in old.targets]
    assert {m: sorted(cs) for m, cs in new.nonlib_modules.items()} == \
        {m: sorted(cs) for m, cs in old.nonlib_modules.items()} != {}
    key = lambda h: (h["module"], h["constant"])  # noqa: E731
    assert sorted(new.scan_hits, key=key) == sorted(old.scan_hits, key=key) != []
    assert sorted(new.scan_module_hits) == sorted(old.scan_module_hits)
    assert sorted(new.unused_nonlib_modules) == sorted(old.unused_nonlib_modules)
    assert set(new.closure_axioms) <= set(CLEAN_AXIOMS)


# Cleanup M6: what HONEST lacks. A private def (a mangled `_private.<Module>.0.<name>` constant), an `opaque`, and a
# `module`-system file, whose private part holds the non-public def.
PRIV = """namespace TpPriv
private def hidden (n : Nat) : Nat := n + n
opaque secret : Nat
theorem t : hidden 2 = 4 ∧ secret = secret := ⟨rfl, rfl⟩
end TpPriv
"""
MODULE_SYSTEM = """module
def TpModP.hidden : Nat := 3
public theorem TpModP.t : True := let _ := TpModP.hidden; trivial
"""


@lean
@pytest.mark.parametrize("module, body, target", [("TpPriv", PRIV, "TpPriv.t"),
                                                  ("TpModP", MODULE_SYSTEM, "TpModP.t")])
def test_lean_parity_private_opaque_and_module_file(lib, manifest, module, body, target):
    _build(lib, module, body)
    spec = dict(imports=(module,), targets=(target,))
    old = _legacy(lib, AuditSpec(**spec, closure_out=str(lib / "legacy.txt")))
    new = _replayed(lib, manifest, AuditSpec(**spec, closure_out=str(lib / "replayed.txt")))
    assert old.verdict == new.verdict == "PASS", (old.failures, new.failures, new.raw_tail)
    assert (lib / "replayed.txt").read_text() == (lib / "legacy.txt").read_text()
    for f in ("closure_size", "per_root", "closure_axioms", "axioms_consistent", "absent_constants",
              "env_modules_per_root"):
        assert getattr(new, f) == getattr(old, f), f
    assert {m: sorted(cs) for m, cs in new.nonlib_modules.items()} == \
        {m: sorted(cs) for m, cs in old.nonlib_modules.items()}
    private = f"_private.{module}.0.{module}.hidden"
    assert private in new.nonlib_modules[module], new.nonlib_modules
    if module == "TpPriv":
        assert "TpPriv.secret" in new.nonlib_modules[module]


@lean
def test_lean_private_constant_is_matched_by_its_numeric_component(lib, manifest):
    """Cleanup M5: `_private.TpPriv.0.TpPriv.hidden` (a `Name.num` 0) is found as a target and as a forbidden
    constant; with string components the absence check passed vacuously."""
    _build(lib, "TpPriv", PRIV)
    private = "_private.TpPriv.0.TpPriv.hidden"
    r = _replayed(lib, manifest, AuditSpec(imports=("TpPriv",), targets=("TpPriv.t",), absent_constants=(private,)))
    assert r.verdict == "FAIL" and r.absent_constants == {private: True}, (r.failures, r.raw_tail)
    assert f"forbidden constant {private} is in the closure" in r.failures
    r = _replayed(lib, manifest, AuditSpec(imports=("TpPriv",), targets=(private,)))
    assert r.verdict == "PASS" and [(t.name, t.kind) for t in r.targets] == [(private, "definition")], r.failures


@lean
def test_lean_evil_module_cannot_change_the_replayed_verdict(lib, manifest):
    """The step-4 evil module (an initializer, a `#eval` command_elab override, an `omega` tactic override): imported,
    it swallows the legacy audit's `#eval`, so there is no verdict; replayed, none of it runs and the audit PASSes."""
    _build(lib, "TpEvil", EVIL)
    spec = AuditSpec(imports=("TpEvil",), targets=("TpEvil.t",))
    old = _legacy(lib, spec)
    assert "TPEVIL-INIT" in old.raw_tail and "TPEVIL-EVAL" in old.raw_tail and old.verdict == "", old.raw_tail
    outputs = []
    real = lean_replay.run_replay

    def capture(*a, **kw):
        r = real(*a, **kw)
        outputs.append(r.output)
        return r

    lean_replay.run_replay = capture
    try:
        new = _replayed(lib, manifest, spec)
    finally:
        lean_replay.run_replay = real
    assert new.verdict == "PASS" and new.ok and new.isolated, (new.failures, new.raw_tail)
    assert len(outputs) == 1 and "TPEVIL" not in outputs[0], outputs
    assert [t.kind for t in new.targets] == ["theorem"] and new.nonlib_modules["TpEvil"] == ["TpEvil.t"]


@lean
def test_lean_forged_legacy_pass_is_caught_by_replay(lib, manifest):
    """A theorem proved by `sorry` whose module forges the legacy audit's PASS: the replayed audit FAILs it."""
    _build(lib, "TpForge", FORGE)
    spec = AuditSpec(imports=("TpForge",), targets=("TpForge.t",))
    old = _legacy(lib, spec)
    assert old.verdict == "PASS" and old.ok and old.targets == [], (old.failures, old.raw_tail)   # the forgery
    new = _replayed(lib, manifest, spec)
    assert new.verdict == "FAIL" and not new.ok and new.isolated, (new.failures, new.raw_tail)
    assert new.absent_constants == {"sorryAx": True} and "sorryAx" in new.closure_axioms
    assert "forbidden constant sorryAx is in the closure" in new.failures


@lean
def test_lean_sorry_and_untrusted_axiom_are_refused(lib, manifest):
    _build(lib, "TpSorry", SORRY)
    _build(lib, "TpAx", AXIOM)
    s = _replayed(lib, manifest, AuditSpec(imports=("TpSorry",), targets=("TpSorry.t",)))
    assert s.verdict == "FAIL" and s.absent_constants == {"sorryAx": True}, (s.failures, s.raw_tail)
    assert "sorryAx" in s.targets[0].axioms
    a = _replayed(lib, manifest, AuditSpec(imports=("TpAx",), targets=("TpAx.t",)))
    assert a.verdict == "FAIL" and not a.ok and a.isolated, (a.failures, a.raw_tail)
    assert any("untrusted axiom TpAx.bad" in f for f in a.failures), a.failures


@lean
def test_lean_redeclared_constant_is_refused(lib, manifest):
    """Two untrusted modules declaring one name (the legacy audit's re-declaration hazard) are refused by replay."""
    _build(lib, "TpDupA", DUP_A)
    _build(lib, "TpDupB", DUP_B)
    r = _replayed(lib, manifest, AuditSpec(imports=("TpDupA", "TpDupB"), targets=("TpDup.t",)))
    assert r.verdict == "FAIL" and not r.ok, (r.failures, r.raw_tail)
    assert any("declared twice" in f for f in r.failures), r.failures

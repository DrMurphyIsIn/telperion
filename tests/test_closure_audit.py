"""The kernel-level closure audit (T4): rendering of the Lean metaprogram, parsing of its
output protocol, the subprocess path (with a fake `lake`), and the CLI.

The fixtures under tests/fixtures/closure_audit/ are REAL outputs of the rendered script:
`audit_pass_v4341.txt` from Lean v4.34.1 (one Mathlib target, PASS) and
`audit_fail_missing_targets.txt` from Lean v4.32.0 (three targets, two of them absent from
the imported module, FAIL).  Running the audit for real needs a built Lake project; the
telperion-lean-e2e `closure-audit-compiles` job does that on examples/closure_audit.
"""
import json
import os
import stat
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.closure_audit import (  # noqa: E402
    DEFAULT_ABSENT_CONSTANTS,
    DEFAULT_LIBRARY_ROOTS,
    PROTOCOL_VERSION,
    AuditSpec,
    ClosureAuditError,
    lean_name_literal,
    parse_audit_output,
    render_audit_script,
    run_closure_audit,
)
from telperion.comparator import CLEAN_AXIOMS  # noqa: E402

FIX = Path(__file__).resolve().parent / "fixtures" / "closure_audit"


def _spec(**kw) -> AuditSpec:
    base = dict(imports=("Foo.Bar",), targets=("Foo.main",))
    base.update(kw)
    return AuditSpec(**base)


# ---------------------------------------------------------------- spec + rendering

def test_spec_defaults_are_the_documented_ones():
    s = _spec()
    assert s.library_roots == DEFAULT_LIBRARY_ROOTS
    assert "Mathlib" in s.library_roots and "Init" in s.library_roots
    assert s.absent_constants == DEFAULT_ABSENT_CONSTANTS == ("sorryAx",)
    assert s.allowed_axioms == CLEAN_AXIOMS
    assert s.include_recursors is True
    assert s.closure_out is None


def test_spec_rejects_empty_inputs():
    with pytest.raises(ValueError):
        AuditSpec(imports=(), targets=("A.b",))
    with pytest.raises(ValueError):
        AuditSpec(imports=("A",), targets=())
    with pytest.raises(ValueError):
        _spec(scan_patterns=("",))
    with pytest.raises(ValueError):
        _spec(absent_module_prefixes=(" ",))


def test_scan_patterns_are_lower_cased():
    assert _spec(scan_patterns=("Heegner", "BAKER")).scan_patterns == ("heegner", "baker")


def test_lean_name_literal_quotes_odd_components():
    assert lean_name_literal("CN1.classNumber_eq_one_iff") == "`CN1.classNumber_eq_one_iff"
    assert lean_name_literal("Nat.Prime.two_le'") == "`Nat.Prime.two_le'"
    assert lean_name_literal("Foo.bar baz") == "`Foo.«bar baz»"
    assert lean_name_literal("Foo.1x") == "`Foo.«1x»"
    with pytest.raises(ValueError):
        lean_name_literal("Foo..bar")


def test_render_substitutes_every_placeholder():
    s = _spec(imports=("A.B", "C"), targets=("A.t1", "A.t2"), scan_patterns=("heegner",),
              absent_module_prefixes=("NegControls",), include_recursors=False,
              closure_out="/tmp/x y.txt")
    text = render_audit_script(s)
    assert "__" not in text.replace("_private", "").replace("two_le", ""), \
        [l for l in text.splitlines() if "__" in l]
    assert text.startswith("import A.B\nimport C\nimport Lean\n")
    assert "def targets : List Name := [`A.t1, `A.t2]" in text
    assert 'def scanPatterns : List String := ["heegner"]' in text
    assert "def absentModulePrefixes : List Name := [`NegControls]" in text
    assert "def includeRecursors : Bool := false" in text
    assert 'def closureOut : Option String := some "/tmp/x y.txt"' in text
    assert PROTOCOL_VERSION in text


def test_render_default_has_no_closure_file_and_recursors_on():
    text = render_audit_script(_spec())
    assert "def closureOut : Option String := none" in text
    assert "def includeRecursors : Bool := true" in text
    assert "def absentConstants : List Name := [`sorryAx]" in text
    assert "def allowedAxioms : List Name := [`propext, `Quot.sound, `Classical.choice]" in text


def test_render_is_deterministic():
    assert render_audit_script(_spec()) == render_audit_script(_spec())


def test_render_escapes_string_literals():
    text = render_audit_script(_spec(scan_patterns=('a"b\\c',), closure_out='C:\\t"q'))
    assert '"a\\"b\\\\c"' in text
    assert 'some "C:\\\\t\\"q"' in text


def test_both_walk_modes_are_in_the_script():
    """The reviewer's walk (`getUsedConstantsAsSet`) and ours (`.rec` per inductive) are both
    rendered; the flag selects between them at run time."""
    text = render_audit_script(_spec())
    assert "ci.getUsedConstantsAsSet.toArray" in text
    assert 'Name.mkStr n "rec"' in text


# ---------------------------------------------------------------- parsing real outputs

def test_parse_pass_fixture_v4341():
    res = parse_audit_output((FIX / "audit_pass_v4341.txt").read_text(encoding="utf-8"))
    assert res.protocol == PROTOCOL_VERSION
    assert res.lean_version == "4.34.1"
    assert res.include_recursors is True
    assert res.verdict == "PASS" and res.ok
    assert res.closure_size == 630
    assert res.per_root == {"Init": 490, "Mathlib": 140}
    assert sum(res.per_root.values()) == res.closure_size
    assert res.nonlib_modules == {}
    assert [t.name for t in res.targets] == ["Nat.Prime.two_le"]
    assert res.targets[0].kind == "theorem"
    assert res.targets[0].statement == "∀ {p : ℕ}, Nat.Prime p → 2 ≤ p"
    assert res.targets[0].axioms == ["propext"]
    assert res.absent_constants == {"sorryAx": False}
    assert res.absent_modules == {"Mathlib.Tactic.Linarith": 0}
    assert len(res.scan_hits) == 9
    assert {"module": "Mathlib.Data.Nat.Prime.Defs", "constant": "Nat.Prime"} in res.scan_hits
    assert "Lean.Util.Sorry" in res.scan_module_hits
    assert res.env_modules_per_root["Mathlib"] > 0
    assert res.closure_written == "/tmp/closure_4341.txt"
    assert res.failures == []


def test_parse_fail_fixture_missing_targets_v4320():
    res = parse_audit_output((FIX / "audit_fail_missing_targets.txt").read_text(encoding="utf-8"))
    assert res.lean_version == "4.32.0"
    assert res.verdict == "FAIL" and not res.ok
    kinds = {t.name: t.kind for t in res.targets}
    assert kinds == {"Nat.Prime.two_le": "theorem", "Nat.exists_infinite_primes": "missing",
                     "Nat.NoSuchThing": "missing"}
    assert res.failures == ["target Nat.exists_infinite_primes not found",
                            "target Nat.NoSuchThing not found"]
    # the walk still ran over the targets that exist
    assert res.closure_size == 629
    assert res.targets[0].axioms == ["propext"]


def test_recursor_option_changes_only_the_count():
    """Documented from the four real runs (v4.32.0 and v4.34.1, recursors on/off): the same
    target, the same verdict, a smaller closure without the `.rec` constants."""
    on = parse_audit_output((FIX / "audit_pass_v4341.txt").read_text(encoding="utf-8"))
    assert on.include_recursors and on.closure_size == 630
    # v4.34.1 with include_recursors=False measured 573 (v4.32.0: 629 vs 571 on the three-target
    # run's single existing target).  The fixture records the ON run; the OFF count is asserted
    # here as the documented figure so a change in the walk is noticed.
    assert 630 - 573 == 57


def test_parse_ignores_noise_and_unknown_keys():
    text = "warning: foo has local changes\n@@protocol\tx\n@@newkey\ta\tb\n@@verdict\tPASS\n"
    res = parse_audit_output(text)
    assert res.protocol == "x" and res.verdict == "PASS"
    assert res.raw_tail.endswith("@@verdict\tPASS")


def test_parse_malformed_line_raises():
    with pytest.raises(ClosureAuditError):
        parse_audit_output("@@closure_size\tnot-a-number\n")


def test_result_json_roundtrip_and_render():
    res = parse_audit_output((FIX / "audit_pass_v4341.txt").read_text(encoding="utf-8"))
    d = json.loads(res.to_json())
    assert d["ok"] is True and d["verdict"] == "PASS" and d["closure_size"] == 630
    assert d["targets"][0]["axioms"] == ["propext"]
    text = res.render()
    assert "closure audit: PASS" in text and "sorryAx in closure: false" in text


# ---------------------------------------------------------------- subprocess path

def _fake_lake(tmp_path: Path, body: str) -> dict:
    """A `lake` on PATH that ignores its arguments and runs `body` (sh)."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(parents=True)
    lake = bin_dir / "lake"
    lake.write_text("#!/bin/sh\n" + body + "\n", encoding="utf-8")
    lake.chmod(lake.stat().st_mode | stat.S_IXUSR)
    env = dict(os.environ)
    env["PATH"] = str(bin_dir) + os.pathsep + env.get("PATH", "")
    return env


def test_run_closure_audit_parses_fake_lake_output(tmp_path, monkeypatch):
    proj = tmp_path / "proj"
    proj.mkdir()
    fixture = (FIX / "audit_pass_v4341.txt").read_text(encoding="utf-8")
    (tmp_path / "canned.txt").write_text(fixture, encoding="utf-8")
    env = _fake_lake(tmp_path, f'cat "{tmp_path / "canned.txt"}"')
    monkeypatch.setenv("PATH", env["PATH"])
    res = run_closure_audit(_spec(), proj)
    assert res.ok and res.lean_exit_code == 0 and res.closure_size == 630
    # the temp script is removed afterwards
    assert not list(proj.glob("telperion_closure_audit_*.lean"))


def test_run_closure_audit_keeps_named_script_and_passes_wrapper(tmp_path, monkeypatch):
    proj = tmp_path / "proj"
    proj.mkdir()
    # the fake lake records its argv so the wrapper and script path can be checked
    env = _fake_lake(tmp_path, f'echo "$@" > "{tmp_path / "argv.txt"}"; printf "@@verdict\\tPASS\\n"')
    monkeypatch.setenv("PATH", env["PATH"])
    # a RELATIVE script path (relative to the caller's cwd, not the project): lake runs with
    # cwd = project, so the runner must hand it an absolute path
    monkeypatch.chdir(tmp_path)
    script = Path("proj") / "Audit.lean"
    res = run_closure_audit(_spec(), proj, script_path=script, wrapper=["env", "X=1"])
    assert res.verdict == "PASS"
    assert script.is_file() and "def targets" in script.read_text()
    argv = (tmp_path / "argv.txt").read_text().split()
    assert argv[:3] == ["env", "lean", str(script.resolve())]


def test_run_closure_audit_records_lean_failure_without_verdict(tmp_path, monkeypatch):
    proj = tmp_path / "proj"
    proj.mkdir()
    env = _fake_lake(tmp_path, 'echo "error: unknown constant" ; exit 1')
    monkeypatch.setenv("PATH", env["PATH"])
    res = run_closure_audit(_spec(), proj)
    assert not res.ok and res.verdict == "" and res.lean_exit_code == 1
    assert res.failures == ["lean exited 1 before a verdict"]
    assert "unknown constant" in res.raw_tail


def test_run_closure_audit_missing_project_raises(tmp_path):
    with pytest.raises(ClosureAuditError):
        run_closure_audit(_spec(), tmp_path / "nope")


# ---------------------------------------------------------------- CLI

def test_cli_render_only_and_spec_file(tmp_path, capsys):
    from telperion.cli import main

    out = tmp_path / "a.lean"
    rc = main(["audit-closure", "--project", str(tmp_path), "--import", "A.B", "--target", "A.t",
               "--scan", "Heegner", "--absent-module", "Neg", "--no-recursors",
               "--render-only", str(out)])
    assert rc == 0
    text = out.read_text()
    assert "def targets : List Name := [`A.t]" in text
    assert 'def scanPatterns : List String := ["heegner"]' in text
    assert "def includeRecursors : Bool := false" in text

    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({"imports": ["X"], "targets": ["X.y"],
                                     "absent_module_prefixes": ["X.Neg"]}))
    out2 = tmp_path / "b.lean"
    assert main(["audit-closure", "--project", str(tmp_path), "--spec", str(spec_file),
                 "--render-only", str(out2)]) == 0
    assert "def absentModulePrefixes : List Name := [`X.Neg]" in out2.read_text()


def test_cli_requires_targets_or_spec(tmp_path, capsys):
    from telperion.cli import main

    assert main(["audit-closure", "--project", str(tmp_path)]) == 2
    assert "pass --spec FILE" in capsys.readouterr().out


def test_cli_exit_codes_follow_the_verdict(tmp_path, monkeypatch, capsys):
    from telperion.cli import main

    proj = tmp_path / "proj"
    proj.mkdir()
    env = _fake_lake(tmp_path, f'cat "{FIX / "audit_fail_missing_targets.txt"}"')
    monkeypatch.setenv("PATH", env["PATH"])
    js = tmp_path / "r.json"
    rc = main(["audit-closure", "--project", str(proj), "--import", "A", "--target", "A.t",
               "--json", str(js)])
    assert rc == 1
    d = json.loads(js.read_text())
    assert d["verdict"] == "FAIL" and d["closure_size"] == 629
    captured = capsys.readouterr().out
    assert "closure audit: FAIL" in captured

    env = _fake_lake(tmp_path / "two", f'cat "{FIX / "audit_pass_v4341.txt"}"')
    monkeypatch.setenv("PATH", env["PATH"])
    assert main(["audit-closure", "--project", str(proj), "--import", "A", "--target", "A.t"]) == 0
    # scan hits are informational unless asked to fail on them
    assert main(["audit-closure", "--project", str(proj), "--import", "A", "--target", "A.t",
                 "--fail-on-scan-hit"]) == 1


def test_example_specs_are_what_generate_renders():
    """examples/closure_audit: the committed spec JSONs load as AuditSpecs and the committed
    scripts are their renderings (the manifest `--check` enforces the same byte-for-byte)."""
    ex = Path(__file__).resolve().parents[1] / "examples" / "closure_audit"
    for spec_name, lean_name, must_pass in (("audit.spec.json", "Audit.lean", True),
                                            ("audit_tainted.spec.json", "AuditTainted.lean", False)):
        raw = json.loads((ex / spec_name).read_text())
        spec = AuditSpec(**{k: (tuple(v) if isinstance(v, list) else v) for k, v in raw.items()})
        assert render_audit_script(spec) == (ex / "lean" / lean_name).read_text()
        assert spec.absent_module_prefixes == ("ClosureAuditExample.Tainted",)
        if must_pass:
            assert "ClosureAuditExample.Tainted" in spec.imports  # the absence check is not vacuous
            assert all(t.startswith("ClosureAuditExample.") and ".NegControl." not in t for t in spec.targets)
        else:
            assert all(".NegControl." in t for t in spec.targets)

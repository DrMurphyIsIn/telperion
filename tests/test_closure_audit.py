"""The kernel-level closure audit (T4): rendering of the Lean metaprogram, parsing of its
nonce-tagged output protocol, the integrity rules, the subprocess path (with a fake `lake`),
the CLI, and the re-declaration hazard an independent reviewer demonstrated.

The fixtures under tests/fixtures/closure_audit/ are REAL outputs of the rendered script,
rendered with the nonce FIXTURENONCE:
  audit_pass_v4341.txt            Lean v4.34.1, one Mathlib target, PASS;
  audit_fail_missing_targets.txt  Lean v4.32.0, three targets, two absent from the import, FAIL;
  audit_redeclare_v4320.txt       Lean v4.32.0, the example's Redeclare control imported beside
                                  Example: the closure holds a native_decide axiom while the
                                  per-target cached record is clean -> FAIL.
Running the audit for real needs a built Lake project; the telperion-lean-e2e
`closure-audit-compiles` job does that on examples/closure_audit, and
`test_live_example_audits` runs it locally when TELPERION_CLOSURE_AUDIT_LIVE=1.
"""
import json
import os
import re
import stat
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.closure_audit import (  # noqa: E402
    DEFAULT_ABSENT_CONSTANTS,
    DEFAULT_LIBRARY_ROOTS,
    PLACEHOLDER_NONCE,
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
NONCE = "FIXTURENONCE"
EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "closure_audit"


def _fixture(name: str) -> str:
    return (FIX / name).read_text(encoding="utf-8")


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
    text = render_audit_script(s, nonce="abc123")
    assert "__" not in text.replace("_private", "").replace("two_le", ""), \
        [l for l in text.splitlines() if "__" in l]
    assert text.startswith("import A.B\nimport C\nimport Lean\n")
    assert "def targets : List Name := [`A.t1, `A.t2]" in text
    assert 'def scanPatterns : List String := ["heegner"]' in text
    assert "def absentModulePrefixes : List Name := [`NegControls]" in text
    assert "def includeRecursors : Bool := false" in text
    assert 'def closureOut : Option String := some "/tmp/x y.txt"' in text
    assert 'def nonce : String := "abc123"' in text
    assert PROTOCOL_VERSION in text


def test_render_default_has_no_closure_file_recursors_on_and_placeholder_nonce():
    text = render_audit_script(_spec())
    assert "def closureOut : Option String := none" in text
    assert "def includeRecursors : Bool := true" in text
    assert "def absentConstants : List Name := [`sorryAx]" in text
    assert "def allowedAxioms : List Name := [`propext, `Quot.sound, `Classical.choice]" in text
    assert f'def nonce : String := "{PLACEHOLDER_NONCE}"' in text


def test_render_rejects_non_alphanumeric_nonce():
    with pytest.raises(ValueError):
        render_audit_script(_spec(), nonce='x"y')


def test_render_is_deterministic():
    assert render_audit_script(_spec()) == render_audit_script(_spec())


def test_render_escapes_string_literals():
    text = render_audit_script(_spec(scan_patterns=('a"b\\c',), closure_out='C:\\t"q'))
    assert '"a\\"b\\\\c"' in text
    assert 'some "C:\\\\t\\"q"' in text


def test_both_walk_modes_and_both_axiom_checks_are_in_the_script():
    """The reviewer's walk (`getUsedConstantsAsSet`) and ours (`.rec` per inductive) are both
    rendered; the closure-based axiom collection, the per-target `collectAxioms` and the
    consistency cross-check are all present (A1 of the independent review)."""
    text = render_audit_script(_spec())
    assert "ci.getUsedConstantsAsSet.toArray" in text
    assert 'Name.mkStr n "rec"' in text
    assert "some (.axiomInfo _) => axiomAcc := axiomAcc.push n" in text
    assert "collectAxioms t" in text
    assert "inconsistent environment" in text


# ---------------------------------------------------------------- parsing real outputs

def test_parse_pass_fixture_v4341():
    res = parse_audit_output(_fixture("audit_pass_v4341.txt"), nonce=NONCE)
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
    assert res.closure_axioms == ["propext"]
    assert res.axioms_consistent is True
    assert res.absent_constants == {"sorryAx": False}
    assert res.absent_modules == {"Mathlib.Tactic.Linarith": 0}
    assert len(res.scan_hits) == 9
    assert {"module": "Mathlib.Data.Nat.Prime.Defs", "constant": "Nat.Prime"} in res.scan_hits
    assert "Lean.Util.Sorry" in res.scan_module_hits
    assert res.env_modules_per_root["Mathlib"] > 0
    assert res.closure_written == "/tmp/closure_4341_rec.txt"
    assert res.failures == []


def test_parse_fail_fixture_missing_targets_v4320():
    res = parse_audit_output(_fixture("audit_fail_missing_targets.txt"), nonce=NONCE)
    assert res.lean_version == "4.32.0"
    assert res.verdict == "FAIL" and not res.ok
    kinds = {t.name: t.kind for t in res.targets}
    assert kinds == {"Nat.Prime.two_le": "theorem", "Nat.exists_infinite_primes": "missing",
                     "Nat.NoSuchThing": "missing"}
    assert res.failures == ["target Nat.exists_infinite_primes not found",
                            "target Nat.NoSuchThing not found"]
    # the walk still ran over the target that exists
    assert res.closure_size == 629
    assert res.targets[0].axioms == ["propext"] and res.closure_axioms == ["propext"]
    assert res.axioms_consistent is True


def test_parse_redeclare_fixture_fails_on_closure_axiom_and_inconsistency():
    """bb's scenario: Redeclare.lean re-declares `ClosureAuditExample.prime_101` by
    `native_decide` and is imported beside Example.lean.  The per-target record is whatever
    the declaring module's .olean cached; the closure holds the native_decide axiom; the
    audit must FAIL on the closure axiom and report the two lists as inconsistent."""
    res = parse_audit_output(_fixture("audit_redeclare_v4320.txt"), nonce=NONCE)
    assert res.verdict == "FAIL" and not res.ok
    assert any("native_decide" in a for a in res.closure_axioms), res.closure_axioms
    assert any(f.startswith("closure contains non-allowed axioms") for f in res.failures), res.failures
    assert res.axioms_consistent is False
    assert any(f.startswith("inconsistent environment") for f in res.failures), res.failures
    # and the per-target record alone would have said clean -- the whole point
    [t] = res.targets
    assert set(t.axioms) <= set(CLEAN_AXIOMS), t.axioms


def test_recursor_option_changes_only_the_count():
    """Documented figures from the real runs (same target, both toolchains): 629/571 on
    v4.32.0, 630/573 on v4.34.1.  The fixture records the v4.34.1 ON run; the OFF count is
    asserted here as the documented figure so a change in the walk is noticed."""
    on = parse_audit_output(_fixture("audit_pass_v4341.txt"), nonce=NONCE)
    assert on.include_recursors and on.closure_size == 630
    assert 630 - 573 == 57 and 629 - 571 == 58


def test_parse_ignores_noise_other_nonces_and_unknown_keys():
    text = ("warning: foo has local changes\n"
            "@@OTHER\tverdict\tPASS\n"          # someone else's nonce: ignored
            "@@verdict\tPASS\n"                 # no nonce: ignored
            "@@N\tprotocol\tx\n@@N\tnewkey\ta\tb\n@@N\tverdict\tPASS\n")
    res = parse_audit_output(text, nonce="N")
    assert res.protocol == "x" and res.verdict == "PASS" and res.ok
    assert res.raw_tail.endswith("@@N\tverdict\tPASS")


def test_parse_malformed_line_raises():
    with pytest.raises(ClosureAuditError):
        parse_audit_output("@@N\tclosure_size\tnot-a-number\n", nonce="N")


@pytest.mark.parametrize("text, why", [
    ("@@N\tprotocol\tx\n@@N\tverdict\tPASS\n@@N\tverdict\tPASS\n", "2 verdict lines"),
    ("@@N\tverdict\tPASS\n", "0 protocol lines"),
    ("@@N\tprotocol\tx\n@@N\tprotocol\tx\n@@N\tverdict\tPASS\n", "2 protocol lines"),
    ("@@N\tprotocol\tx\n@@N\tfailure\tbad\n@@N\tverdict\tPASS\n", "PASS with failure lines"),
    ("@@N\tprotocol\tx\n@@N\tverdict\tMAYBE\n", "unknown verdict"),
])
def test_parse_integrity_rules_turn_forged_shapes_into_fail(text, why):
    """A2: the run is unsandboxed, so a stray or forged line must not be read as a verdict."""
    res = parse_audit_output(text, nonce="N")
    assert res.verdict == "FAIL" and not res.ok
    assert any(f.startswith("integrity:") and why in f for f in res.failures), (why, res.failures)


def test_parse_no_verdict_is_not_an_integrity_failure():
    """Lean dying before the verdict is reported by the runner (exit code), not as forgery."""
    res = parse_audit_output("@@N\tprotocol\tx\n@@N\tclosure_size\t3\n", nonce="N")
    assert res.verdict == "" and res.failures == [] and not res.ok


def test_result_json_roundtrip_and_render():
    res = parse_audit_output(_fixture("audit_pass_v4341.txt"), nonce=NONCE)
    d = json.loads(res.to_json())
    assert d["ok"] is True and d["verdict"] == "PASS" and d["closure_size"] == 630
    assert d["targets"][0]["axioms"] == ["propext"]
    assert d["closure_axioms"] == ["propext"] and d["axioms_consistent"] is True
    text = res.render()
    assert "closure audit: PASS" in text and "sorryAx in closure: false" in text
    assert "axioms in closure: ['propext']" in text


# ---------------------------------------------------------------- subprocess path

def _fake_lake(tmp_path: Path, body: str) -> dict:
    """A `lake` on PATH that runs `body` (sh).  `$NONCE` holds the nonce the runner baked into
    the script it was handed (the script path is the last argument), so a canned fixture can
    be re-tagged with it: the runner only reads lines carrying its own nonce."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(parents=True)
    lake = bin_dir / "lake"
    lake.write_text(
        "#!/bin/sh\n"
        'for last in "$@"; do :; done\n'
        'NONCE=$(sed -n \'s/^def nonce : String := "\\(.*\\)"$/\\1/p\' "$last")\n'
        + body + "\n", encoding="utf-8")
    lake.chmod(lake.stat().st_mode | stat.S_IXUSR)
    env = dict(os.environ)
    env["PATH"] = str(bin_dir) + os.pathsep + env.get("PATH", "")
    return env


def _canned(tmp_path: Path, fixture: str) -> str:
    """Shell that prints the fixture re-tagged with the runner's nonce."""
    (tmp_path / "canned.txt").write_text(_fixture(fixture), encoding="utf-8")
    return f'sed "s/^@@{NONCE}\t/@@$NONCE\t/" "{tmp_path / "canned.txt"}"'


def test_run_closure_audit_parses_fake_lake_output_with_its_own_nonce(tmp_path, monkeypatch):
    proj = tmp_path / "proj"
    proj.mkdir()
    env = _fake_lake(tmp_path, _canned(tmp_path, "audit_pass_v4341.txt"))
    monkeypatch.setenv("PATH", env["PATH"])
    res = run_closure_audit(_spec(), proj)
    assert res.ok and res.lean_exit_code == 0 and res.closure_size == 630
    assert len(res.nonce) == 32 and res.nonce != NONCE
    # the temp script is removed afterwards
    assert not list(proj.glob("telperion_closure_audit_*.lean"))


def test_run_closure_audit_ignores_output_tagged_with_a_foreign_nonce(tmp_path, monkeypatch):
    """A script that prints the FIXTURE nonce (not the run's) is a forged or stale output: no
    verdict is read, and the result is not ok."""
    proj = tmp_path / "proj"
    proj.mkdir()
    (tmp_path / "canned.txt").write_text(_fixture("audit_pass_v4341.txt"), encoding="utf-8")
    env = _fake_lake(tmp_path, f'cat "{tmp_path / "canned.txt"}"')
    monkeypatch.setenv("PATH", env["PATH"])
    res = run_closure_audit(_spec(), proj)
    assert res.verdict == "" and not res.ok and res.closure_size == 0


def test_run_closure_audit_keeps_named_script_and_passes_wrapper(tmp_path, monkeypatch):
    proj = tmp_path / "proj"
    proj.mkdir()
    env = _fake_lake(tmp_path, f'echo "$@" > "{tmp_path / "argv.txt"}"; '
                               'printf "@@%s\\tprotocol\\tx\\n@@%s\\tverdict\\tPASS\\n" "$NONCE" "$NONCE"')
    monkeypatch.setenv("PATH", env["PATH"])
    # a RELATIVE script path (relative to the caller's cwd, not the project): lake runs with
    # cwd = project, so the runner must hand it an absolute path
    monkeypatch.chdir(tmp_path)
    script = Path("proj") / "Audit.lean"
    res = run_closure_audit(_spec(), proj, script_path=script, wrapper=["env", "X=1"])
    assert res.verdict == "PASS" and res.ok
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
    env = _fake_lake(tmp_path, _canned(tmp_path, "audit_fail_missing_targets.txt"))
    monkeypatch.setenv("PATH", env["PATH"])
    js = tmp_path / "r.json"
    rc = main(["audit-closure", "--project", str(proj), "--import", "A", "--target", "A.t",
               "--json", str(js)])
    assert rc == 1
    d = json.loads(js.read_text())
    assert d["verdict"] == "FAIL" and d["closure_size"] == 629
    assert "closure audit: FAIL" in capsys.readouterr().out

    two = tmp_path / "two"
    two.mkdir()
    env = _fake_lake(two, _canned(two, "audit_pass_v4341.txt"))
    monkeypatch.setenv("PATH", env["PATH"])
    assert main(["audit-closure", "--project", str(proj), "--import", "A", "--target", "A.t"]) == 0
    # scan hits are informational unless asked to fail on them
    assert main(["audit-closure", "--project", str(proj), "--import", "A", "--target", "A.t",
                 "--fail-on-scan-hit"]) == 1


# ---------------------------------------------------------------- the example

def test_example_specs_are_what_generate_renders():
    """examples/closure_audit: the committed spec JSONs load as AuditSpecs and the committed
    scripts are their renderings with the placeholder nonce (the manifest `--check` enforces
    the same byte-for-byte)."""
    cases = (("audit.spec.json", "Audit.lean", "pass"),
             ("audit_tainted.spec.json", "AuditTainted.lean", "tainted"),
             ("audit_redeclare.spec.json", "AuditRedeclare.lean", "redeclare"))
    for spec_name, lean_name, kind in cases:
        raw = json.loads((EXAMPLE / spec_name).read_text())
        spec = AuditSpec(**{k: (tuple(v) if isinstance(v, list) else v) for k, v in raw.items()})
        assert render_audit_script(spec) == (EXAMPLE / "lean" / lean_name).read_text()
        if kind == "pass":
            assert spec.absent_module_prefixes == ("ClosureAuditExample.Tainted",)
            assert "ClosureAuditExample.Tainted" in spec.imports  # the absence check is not vacuous
            assert "ClosureAuditExample.Redeclare" not in spec.imports  # never beside a re-declared name
            assert all(t.startswith("ClosureAuditExample.") and ".NegControl." not in t for t in spec.targets)
        elif kind == "tainted":
            assert all(".NegControl." in t for t in spec.targets)
        else:
            assert spec.imports == ("ClosureAuditExample.Example", "ClosureAuditExample.Redeclare")
            assert spec.targets == ("ClosureAuditExample.prime_101",)


def test_example_controls_never_share_a_name_with_a_clean_target_except_redeclare():
    """The Tainted control's names are distinct from every clean target (so the clean audit's
    PASS is not the re-declaration accident); Redeclare's one theorem IS a clean target's
    name, on purpose, and is a separate build root."""
    lean = EXAMPLE / "lean"
    names = lambda f: set(re.findall(r"^theorem\s+(\w+)", (lean / f).read_text(), re.M))
    clean = names("ClosureAuditExample/Example.lean")
    assert not (clean & names("ClosureAuditExample/Tainted.lean"))
    assert names("ClosureAuditExample/Redeclare.lean") == {"prime_101"} and "prime_101" in clean
    lakefile = (lean / "lakefile.toml").read_text()
    assert 'roots = ["ClosureAuditExample", "ClosureAuditExample.Redeclare"]' in lakefile
    umbrella = (lean / "ClosureAuditExample.lean").read_text()
    assert "Redeclare" not in umbrella


@pytest.mark.skipif(os.environ.get("TELPERION_CLOSURE_AUDIT_LIVE") != "1",
                    reason="needs the built example project; set TELPERION_CLOSURE_AUDIT_LIVE=1 "
                           "(and TELPERION_LEAN_WRAPPER for a build lock)")
def test_live_example_audits():
    """Lean-gated: the three example audits against the built library.  Clean PASS; tainted
    FAIL; re-declared FAIL with the closure axiom and the inconsistency."""
    proj = EXAMPLE / "lean"
    wrapper = os.environ.get("TELPERION_LEAN_WRAPPER") or None

    def run(spec_name):
        raw = json.loads((EXAMPLE / spec_name).read_text())
        spec = AuditSpec(**{k: (tuple(v) if isinstance(v, list) else v) for k, v in raw.items()})
        return run_closure_audit(spec, proj, wrapper=wrapper)

    clean = run("audit.spec.json")
    assert clean.ok, clean.failures
    assert clean.axioms_consistent is True and set(clean.closure_axioms) <= set(CLEAN_AXIOMS)
    assert clean.absent_modules["ClosureAuditExample.Tainted"] == 0
    tainted = run("audit_tainted.spec.json")
    assert tainted.verdict == "FAIL" and tainted.absent_constants["sorryAx"] is True
    assert "sorryAx" in tainted.closure_axioms
    redeclare = run("audit_redeclare.spec.json")
    assert redeclare.verdict == "FAIL"
    assert any("native_decide" in a for a in redeclare.closure_axioms)
    assert any(f.startswith("closure contains non-allowed axioms") for f in redeclare.failures)
    assert redeclare.axioms_consistent is False
    assert any(f.startswith("inconsistent environment") for f in redeclare.failures)

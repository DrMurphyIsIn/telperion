import os
from pathlib import Path
import pytest
from telperion.checks.negation_probe import classify, render_probes

# Fix round 2: a compiled `false`/`witness` probe counts only with its `#print axioms` line, clean axioms only.
OK = (0, "'_tp_false' does not depend on any axioms\n'_tp_witness' depends on axioms: [propext]\n")


def test_false_compiled_is_vacuous():
    assert classify({"false": OK, "negation": (1, "error: plausible gave up")}).verdict == "VACUOUS"


def test_counterexample_is_refuted():
    out = (1, "error: \n===================\nFound a counter-example!\nx := 3\n")
    assert classify({"false": (1, "error: linarith failed"), "negation": out}).verdict == "REFUTED"


def test_plausible_gave_up():
    r = classify({"false": (1, "error: linarith failed"), "negation": (1, "error: Gave up after 200 tests")})
    assert r.verdict == "PROBE_ONLY"


def test_probe_error_is_not_vacuous():
    r = classify({"false": (1, "error: unknown identifier 'Foo'"), "negation": (1, "error: unknown identifier 'Foo'")})
    assert r.verdict == "ERROR"


def test_witness():
    r = classify({"false": (1, "error: linarith failed"), "negation": (1, "error: Gave up"), "witness": OK})
    assert r.verdict == "WITNESSED"


def test_render_contains_parts():
    src = render_probes(["Mathlib"], "", "(x : ℕ) (h : x < 3)", "x < 5", None)
    assert "theorem _tp_false (x : ℕ) (h : x < 3) : False" in src["false"]
    assert "plausible" in src["negation"] and "witness" not in src


LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")


@lean
def test_lean_contradictory_hypotheses_vacuous():          # MUST-FAIL control
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ) (h1 : x < 2) (h2 : 5 < x)", "x = 7", None), Path(LEAN_ENV))
    assert r.verdict == "VACUOUS", r.detail


@lean
def test_lean_false_claim_refuted():                        # MUST-FAIL control
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ)", "x * x ≠ 16", None), Path(LEAN_ENV))
    assert r.verdict == "REFUTED", r.detail


@lean
def test_lean_true_claim_probe_only():                      # MUST-PASS control
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ) (h : x < 3)", "x < 5", None), Path(LEAN_ENV))
    assert r.verdict == "PROBE_ONLY", r.detail


# Real v4.35.0 outputs: `first` reports only aesop's failure; plausible's no-Testable error; a sorry'd witness.
AESOP = (1, "f.lean:4:83: error: Tactic `aesop` failed, made no progress\nInitial goal:\n  x : ℕ\n  ⊢ False\n")
UNABLE = (0, "Unable to find a counter-example\nf.lean:3:0: warning: declaration uses `sorry`\n")


def test_aesop_failure_is_purpose_error():
    assert classify({"false": AESOP, "negation": UNABLE}).verdict == "PROBE_ONLY"


def test_no_testable_instance_is_probe_only():
    neg = (1, "f.lean:3:37: error: Failed to create a `testable` instance for `∀ (x : ℝ), x * x ≥ 0`.\n")
    assert classify({"false": AESOP, "negation": neg}).verdict == "PROBE_ONLY"


def test_sorry_witness_is_not_witnessed():
    w = (0, "f.lean:3:0: warning: declaration uses `sorry`\n")
    assert classify({"false": AESOP, "negation": UNABLE, "witness": w}).verdict == "PROBE_ONLY"


def test_failed_witness_is_error():
    w = (1, "f.lean:4:2: error: type mismatch\n  trivial\n")
    assert classify({"false": AESOP, "negation": UNABLE, "witness": w}).verdict == "ERROR"


def test_nonzero_rc_without_message_is_error():
    assert classify({"false": (1, "lake: something broke\n"), "negation": UNABLE}).verdict == "ERROR"


def test_render_autoimplicit_off_and_witness_binders():
    src = render_probes(["Mathlib"], "open Nat", "{n : ℕ} [Fact (1 < n)] (h : n < 3)", "n = 2", "⟨2, ⟨by norm_num⟩, by norm_num, trivial⟩")
    for s in src.values():
        assert "set_option autoImplicit false in" in s and "open Nat" in s
    assert "theorem _tp_witness : ∃ (n : ℕ) (_ : Fact (1 < n)) (h : n < 3), True :=" in src["witness"]


def test_read_signature_and_cli_json(tmp_path, monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import negation_probe as np_
    from telperion.checks.negation_probe import ProbeResult, read_signature
    f = tmp_path / "T.lean"
    f.write_text("import Mathlib\n\nnamespace Foo\nopen Real\n\n-- a comment\ntheorem bar (x : ℕ) (h : x < 3) :\n"
                 "    x < 5 := by\n  have h2 : x < 4 := by omega\n  omega\n\nend Foo\n", encoding="utf-8")
    imps, prelude, binders, concl = read_signature(f.read_text(encoding="utf-8"), "Foo.bar")
    assert (imps, prelude, binders, concl) == (["Mathlib"], "namespace Foo\nopen Real", "(x : ℕ) (h : x < 3)", "x < 5")
    seen = {}
    monkeypatch.setattr(np_, "run_probe", lambda spec, project, wrapper=None, timeout=0:
                        seen.setdefault("r", ProbeResult("REFUTED", "x := 4")))
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--file", str(f), "--theorem", "Foo.bar", "--json"])
    assert rc == 1 and json.loads(capsys.readouterr().out) == {"verdict": "REFUTED", "detail": "x := 4"}
    assert cli.main(["probe-negation", "--project", str(tmp_path), "--file", str(f), "--theorem", "Foo.nope"]) == 2


def test_coded_error_header_is_parsed():
    # v4.35.0: an unknown identifier in a binder is `error(lean.unknownIdentifier):`, beside aesop's purpose error.
    coded = (1, "p/false.lean:5:25: error(lean.unknownIdentifier): Unknown identifier `Foo`\n\n"
                "Note: It is not possible to treat `Foo` as an implicitly bound variable here\n" + AESOP[1])
    r = classify({"false": coded, "negation": UNABLE})
    assert r.verdict == "ERROR" and "unknownIdentifier" in r.detail


# Fix round 1. Real v4.35.0 timeout text; `first` does not catch it, so it ends the `false` battery.
TIMEOUT = (1, "f.lean:5:29: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has "
              "been reached\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\n")
REFUTE = (1, "f.lean:3:38: error: \n===================\nFound a counter-example!\nx := 4\n-------------------\n")


def test_false_timeout_is_inconclusive():
    r = classify({"false": TIMEOUT, "negation": UNABLE})
    assert r.verdict == "PROBE_ONLY" and "probe 'false' timed out at maxHeartbeats 200000 (inconclusive)" in r.detail


def test_negation_timeout_is_inconclusive():
    r = classify({"false": AESOP, "negation": TIMEOUT})
    assert r.verdict == "PROBE_ONLY" and "probe 'negation' timed out at maxHeartbeats 200000 (inconclusive)" in r.detail


def test_timeout_plus_counterexample_elsewhere_is_refuted():
    assert classify({"false": TIMEOUT, "negation": REFUTE}).verdict == "REFUTED"


def test_timeout_never_gives_positive_verdict():
    # a timed-out probe is never read as compiled or as a counterexample, even with rc 0 or the line in its output
    assert classify({"false": (0, TIMEOUT[1]), "negation": UNABLE}).verdict == "PROBE_ONLY"
    assert classify({"false": AESOP, "negation": (1, REFUTE[1] + TIMEOUT[1])}).verdict == "PROBE_ONLY"
    r = classify({"false": AESOP, "negation": UNABLE, "witness": TIMEOUT})
    assert r.verdict == "PROBE_ONLY" and "probe 'witness' timed out" in r.detail


def test_no_testable_detail_says_search_never_ran():
    neg = (1, "f.lean:3:37: error: Failed to create a `testable` instance for `∀ (x : ℝ), x * x ≥ 0`.\n")
    r = classify({"false": AESOP, "negation": neg})
    assert "negation probe did not run: no testable instance (e.g. ℝ)" in r.detail


def test_autoimplicit_error_detail():
    coded = (1, "p/false.lean:5:25: error(lean.unknownIdentifier): Unknown identifier `Foo`\n\nNote: It is not "
                "possible to treat `Foo` as an implicitly bound variable here because the `autoImplicit` option is "
                "set to `false`.\n")
    r = classify({"false": coded, "negation": coded})
    assert r.verdict == "ERROR" and "statement relies on autoImplicit; make binders explicit" in r.detail


def test_leftover_probe_dir_detail(tmp_path):
    from telperion.checks.negation_probe import ProbeSpec, run_probe
    (tmp_path / ".telperion_probe").mkdir()
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ)", "x = x", None), tmp_path, wrapper=["false"])
    assert r.verdict == "ERROR" and str(tmp_path / ".telperion_probe") in r.detail
    assert "remove it if no other probe is running" in r.detail
    assert (tmp_path / ".telperion_probe").is_dir()


def test_cli_help_documents_local_definitions(capsys):
    from telperion import cli
    with pytest.raises(SystemExit):
        cli.main(["probe-negation", "--help"])
    assert "local" in capsys.readouterr().out


# Fix round 2. (1) local/shadowing declarations; the reviewer's example: in the real file `factorial` is
# `Foo.factorial` (current namespace beats `open Nat`), in a probe without it it would be `Nat.factorial`.
SHADOW = ("import Mathlib\n\nnamespace Foo\nopen Nat\n\ndef factorial (n : ℕ) : ℕ := n\n\n"
          "theorem t (n : ℕ) : factorial n ≤ n := le_refl _\n\nend Foo\n")


def test_scanner_refuses_def_without_import():
    from telperion.checks.negation_probe import local_command_problems
    bad = local_command_problems(SHADOW, imported=False)
    assert bad and "line 6" in bad and "def" in bad
    assert "local declarations can change name resolution; pass --import <module>" in bad
    assert local_command_problems(SHADOW, imported=True) is None


def test_scanner_always_refuses_local_scoped_private_variable():
    from telperion.checks.negation_probe import local_command_problems
    for cmd in ("local notation \"‖\" x \"‖\" => x + 1", "scoped infix:50 \" ≺ \" => LT.lt",
                "attribute [local simp] Nat.add_comm", "@[local simp] theorem s : 1 = 1 := rfl",
                "private def factorial (n : ℕ) : ℕ := n", "variable [inst : Inhabited ℕ]",
                "local instance : Inhabited ℕ := ⟨3⟩"):
        text = f"import Mathlib\n\nnamespace Foo\n{cmd}\n\ntheorem t (n : ℕ) : n ≤ n := le_refl _\n"
        bad = local_command_problems(text, imported=True)
        assert bad and "line 4" in bad, cmd


def test_scanner_allows_theorems_opens_options_comments():
    from telperion.checks.negation_probe import local_command_problems
    text = ("import Mathlib\n/- def hidden : ℕ := 0\n-/\nuniverse u\nset_option maxHeartbeats 400000\n"
            "open scoped BigOperators\nnamespace Foo\n-- def also_hidden := 1\nnoncomputable section\n"
            "theorem a (n : ℕ) : n ≤ n := le_refl _\nlemma b (n : ℕ) : n ≤ n + 1 := by\n  omega\nend\nend Foo\n")
    assert local_command_problems(text, imported=False) is None


def test_cli_shadowing_is_error(tmp_path, capsys):
    import json
    from telperion import cli
    f = tmp_path / "S.lean"
    f.write_text(SHADOW, encoding="utf-8")
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--file", str(f), "--theorem", "Foo.t", "--json"])
    out = json.loads(capsys.readouterr().out)
    assert rc == 2 and out["verdict"] == "ERROR" and "line 6" in out["detail"]


# (2) REFUTED only on plausible's banner, not on the phrase anywhere in the output.
def test_counterexample_phrase_outside_banner_is_not_refuted():
    neg = (0, "Unable to find a counter-example\nf.lean:3:0: warning: unused `s = \"Found a counter-example!\"`\n"
              "f.lean:3:0: warning: declaration uses `sorry`\n")
    assert classify({"false": AESOP, "negation": neg}).verdict == "PROBE_ONLY"
    neg2 = (1, "f.lean:3:8: error: type mismatch \"Found a counter-example!\"\n")
    assert classify({"false": AESOP, "negation": neg2}).verdict == "ERROR"


# (3) any unexpected exception is ERROR, exit 2, JSON shape kept.
def test_cli_unexpected_exception_is_error(tmp_path, monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import negation_probe as np_
    f = tmp_path / "T.lean"
    f.write_text("import Mathlib\n\ntheorem t (n : ℕ) : n ≤ n := le_refl _\n", encoding="utf-8")

    def boom(*a, **k):
        raise RuntimeError("kaboom")
    monkeypatch.setattr(np_, "run_probe", boom)
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--file", str(f), "--theorem", "t", "--json"])
    out = json.loads(capsys.readouterr().out)
    assert rc == 2 and out["verdict"] == "ERROR" and "kaboom" in out["detail"]


# (4) the wall-clock timeout kills the whole process group, grandchildren included.
def test_wallclock_timeout_kills_process_group(tmp_path):
    import time
    from telperion.checks.negation_probe import ProbeSpec, run_probe
    pidfile = tmp_path / "child.pid"
    wrapper = ["sh", "-c", f"sleep 60 & echo $! > {pidfile}; wait", "sh"]
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ)", "x = x", None), tmp_path, wrapper=wrapper, timeout=1)
    assert r.verdict == "ERROR" and "did not finish" in r.detail
    pid = int(pidfile.read_text().strip())
    for _ in range(50):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            break
        time.sleep(0.1)
    else:
        pytest.fail(f"grandchild {pid} outlived the timeout")
    assert not (tmp_path / ".telperion_probe").exists()


# (6) axiom audit of the verdict-producing probes.
def test_false_probe_with_nonstandard_axiom_not_counted():
    r = classify({"false": (0, "'Foo._tp_false' depends on axioms: [bad]\n"), "negation": UNABLE})
    assert r.verdict == "PROBE_ONLY" and "probe 'false' used non-standard axioms ['bad']; not counted" in r.detail


def test_compiled_probe_without_axiom_line_not_counted():
    r = classify({"false": (0, ""), "negation": UNABLE, "witness": (0, "")})
    assert r.verdict == "PROBE_ONLY" and "probe 'false'" in r.detail and "probe 'witness'" in r.detail


def test_witness_with_sorryax_not_counted_and_namespaced_clean_counts():
    w = (0, "'Foo._tp_witness' depends on axioms: [propext,\n sorryAx]\n")
    r = classify({"false": AESOP, "negation": UNABLE, "witness": w})
    assert r.verdict == "PROBE_ONLY" and "sorryAx" in r.detail
    f = (0, "'Foo._tp_false' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
    assert classify({"false": f, "negation": UNABLE}).verdict == "VACUOUS"


@lean
def test_lean_bad_axiom_is_not_vacuous():
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    prelude = "namespace TpBad\n@[aesop safe apply] axiom bad : False"
    r = run_probe(ProbeSpec(["Mathlib"], prelude, "(x : ℕ) (h : x < 3)", "x < 5", None), Path(LEAN_ENV))
    assert r.verdict == "PROBE_ONLY" and "non-standard axioms ['bad']" in r.detail, r.detail


@lean
def test_lean_shadowing_example():
    # the hazard: the spec as a probe without the local def reads `factorial` as `Nat.factorial` and is REFUTED ...
    from telperion.checks.negation_probe import run_probe, ProbeSpec, read_signature
    imps, prelude, binders, concl = read_signature(SHADOW, "Foo.t")
    assert run_probe(ProbeSpec(imps, prelude, binders, concl, None), Path(LEAN_ENV)).verdict == "REFUTED"
    # ... so the CLI refuses the file before any Lean runs
    import tempfile
    from telperion import cli
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "S.lean"
        f.write_text(SHADOW, encoding="utf-8")
        assert cli.main(["probe-negation", "--project", LEAN_ENV, "--file", str(f), "--theorem", "Foo.t"]) == 2

import os
from pathlib import Path
import pytest
from telperion.checks.negation_probe import classify, render_probes

OK = (0, "")


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
    assert "example (x : ℕ) (h : x < 3) : False" in src["false"]
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
    assert "example : ∃ (n : ℕ) (_ : Fact (1 < n)) (h : n < 3), True :=" in src["witness"]


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

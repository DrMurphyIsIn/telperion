import os
import secrets
import shutil
import subprocess
from pathlib import Path
import pytest
from telperion.checks.negation_probe import classify, render_probes

# Fix round 3 (Ruling 7): the probes run on the ELABORATED CONSTANT. The `false` and `witness` metaprograms print
# protocol lines `<tag>-FALSE ...` / `<tag>-WITNESS ...`, then a final `<tag>-DONE`; classify's default tag is "TP".
OK = (0, "TP-PREMISES 2\nTP-FALSE PROVED axioms=[]\nTP-WITNESS PROVED axioms=[propext]\nTP-DONE\n")
NOT_FALSE = (0, "TP-PREMISES 2\nTP-FALSE FAILED linarith failed\nTP-DONE\n")


def test_false_compiled_is_vacuous():
    assert classify({"false": OK, "negation": (1, "error: plausible gave up")}).verdict == "VACUOUS"


def test_counterexample_is_refuted():
    out = (1, "error: \n===================\nFound a counter-example!\nx := 3\n")
    assert classify({"false": NOT_FALSE, "negation": out}).verdict == "REFUTED"


def test_plausible_gave_up():
    r = classify({"false": NOT_FALSE, "negation": (1, "error: Gave up after 200 tests")})
    assert r.verdict == "PROBE_ONLY"


def test_probe_error_is_not_vacuous():
    r = classify({"false": (1, "error: unknown identifier 'Foo'"), "negation": (1, "error: unknown identifier 'Foo'")})
    assert r.verdict == "ERROR"


def test_witness():
    r = classify({"false": NOT_FALSE, "negation": (1, "error: Gave up"), "witness": OK})
    assert r.verdict == "WITNESSED"


def test_render_contains_parts():
    src = render_probes("Foo.Bar", "Foo.t", None)
    assert "import Foo.Bar" in src["false"] and "import Mathlib" in src["false"]
    assert "getConstInfo `«Foo».«t»" in src["false"] and "forallBoundedTelescope" in src["false"]
    assert "example : type_of% @«Foo».«t» := by plausible" in src["negation"] and "witness" not in src
    w = render_probes("Foo.Bar", "Foo.t", 'by exact ⟨2, "a\\"b"⟩', tag="TPx")["witness"]
    assert '"by exact ⟨2, \\"a\\\\\\"b\\"⟩"' in w and "TPx-WITNESS PROVED" in w and 'IO.println "TPx-DONE"' in w
    assert 'IO.println "TP-DONE"' in src["false"]


# Real v4.35.0 outputs: plausible's no-counterexample and no-Testable reports; a caught tactic failure.
AESOP = (0, "TP-PREMISES 1\nTP-FALSE FAILED Tactic `aesop` failed, made no progress Initial goal: x : ℕ ⊢ False\n"
            "TP-DONE\n")
UNABLE = (0, "Unable to find a counter-example\nf.lean:3:0: warning: declaration uses `sorry`\n")


def test_aesop_failure_is_purpose_error():
    assert classify({"false": AESOP, "negation": UNABLE}).verdict == "PROBE_ONLY"


def test_no_testable_instance_is_probe_only():
    neg = (1, "f.lean:3:37: error: Failed to create a `testable` instance for `∀ (x : ℝ), x * x ≥ 0`.\n")
    r = classify({"false": AESOP, "negation": neg})
    assert r.verdict == "PROBE_ONLY" and "negation probe did not run: no testable instance (e.g. ℝ)" in r.detail


def test_incomplete_witness_is_not_witnessed():
    w = (0, "TP-WITNESS INCOMPLETE mvars=false sorry=true\nTP-DONE\n")
    r = classify({"false": AESOP, "negation": UNABLE, "witness": w})
    assert r.verdict == "PROBE_ONLY" and "probe 'witness'" in r.detail


def test_failed_witness_is_error():
    w = (0, "TP-WITNESS FAILED type mismatch trivial\nTP-DONE\n")
    assert classify({"false": AESOP, "negation": UNABLE, "witness": w}).verdict == "ERROR"


def test_nonzero_rc_without_message_is_error():
    assert classify({"false": (1, "lake: something broke\n"), "negation": UNABLE}).verdict == "ERROR"


def test_coded_error_header_is_parsed():
    coded = (1, "p/false.lean:5:25: error(lean.unknownConstant): Unknown constant `Foo.nope`\n")
    r = classify({"false": coded, "negation": UNABLE})
    assert r.verdict == "ERROR" and "unknownConstant" in r.detail


def test_missing_protocol_line_is_error():
    r = classify({"false": (0, "TP-PREMISES 1\nTP-DONE\n"), "negation": UNABLE})
    assert r.verdict == "ERROR" and "no TP-FALSE result line" in r.detail


def test_protocol_tag_done_and_duplicates():
    # a line with another tag (an imported module printing at `initialize`, say) is ignored
    assert classify({"false": OK, "negation": UNABLE}, tag="TPab12").verdict == "ERROR"
    # exactly one result line per probe, then exactly one DONE, nothing tagged after it
    for out in ("TP-FALSE PROVED axioms=[]\nTP-FALSE FAILED later\nTP-DONE\n",
                "TP-FALSE FAILED earlier\nTP-FALSE PROVED axioms=[]\nTP-DONE\n",
                "TP-FALSE PROVED axioms=[]\n",
                "TP-FALSE PROVED axioms=[]\nTP-DONE\nTP-DONE\n",
                "TP-DONE\nTP-FALSE PROVED axioms=[]\n"):
        r = classify({"false": (0, out), "negation": UNABLE})
        assert r.verdict == "ERROR", out
    assert classify({"false": (0, "TP-FALSE PROVED axioms=[]\nTP-DONE\n"), "negation": UNABLE}).verdict == "VACUOUS"


def test_run_probe_nonce_is_128_bit(tmp_path):
    import re
    from telperion.checks.negation_probe import ProbeSpec, run_probe
    # the wrapper prints the probe source instead of running Lean: no protocol line, so ERROR naming the tag
    r = run_probe(ProbeSpec("Foo", "Foo.t"), tmp_path, wrapper=["sh", "-c", 'cat "$4"', "sh"])
    m = re.search(r"no (TP[0-9a-f]+)-FALSE result line", r.detail)
    assert r.verdict == "ERROR" and m and len(m.group(1)) == 2 + 32, r.detail


def test_unbuilt_module_is_error():
    out = (1, "p/false.lean:1:0: error: unknown module prefix 'Foo'\n\nNo directory 'Foo' or file 'Foo.olean' in the "
              "search path entries:\n/x/.lake/build/lib/lean\n")
    r = classify({"false": out, "negation": out}, module="Foo.Bar")
    assert r.verdict == "ERROR" and "build Foo.Bar first (lake build Foo.Bar)" in r.detail


# Fix round 1: timeouts are inconclusive.
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
    assert classify({"false": (1, OK[1] + TIMEOUT[1]), "negation": UNABLE}).verdict == "PROBE_ONLY"
    assert classify({"false": AESOP, "negation": (1, REFUTE[1] + TIMEOUT[1])}).verdict == "PROBE_ONLY"
    r = classify({"false": AESOP, "negation": UNABLE, "witness": TIMEOUT})
    assert r.verdict == "PROBE_ONLY" and "probe 'witness' timed out" in r.detail


def test_leftover_probe_dir_detail(tmp_path):
    from telperion.checks.negation_probe import ProbeSpec, run_probe
    (tmp_path / ".telperion_probe").mkdir()
    r = run_probe(ProbeSpec("Foo", "Foo.t"), tmp_path, wrapper=["false"])
    assert r.verdict == "ERROR" and str(tmp_path / ".telperion_probe") in r.detail
    assert "remove it if no other probe is running" in r.detail
    assert (tmp_path / ".telperion_probe").is_dir()


def test_cli_help_documents_built_module(capsys):
    from telperion import cli
    with pytest.raises(SystemExit):
        cli.main(["probe-negation", "--help"])
    out = capsys.readouterr().out
    assert "--module" in out and "built" in out and "elaborated" in out


# Fix round 2: anchored banner, CLI exceptions, process-group timeout, axiom audit.
def test_counterexample_phrase_outside_banner_is_not_refuted():
    neg = (0, "Unable to find a counter-example\nf.lean:3:0: warning: unused `s = \"Found a counter-example!\"`\n"
              "f.lean:3:0: warning: declaration uses `sorry`\n")
    assert classify({"false": AESOP, "negation": neg}).verdict == "PROBE_ONLY"
    neg2 = (1, "f.lean:3:8: error: type mismatch \"Found a counter-example!\"\n")
    assert classify({"false": AESOP, "negation": neg2}).verdict == "ERROR"


def test_cli_json_and_theorem_qualified_from_file(tmp_path, monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import negation_probe as np_
    from telperion.checks.negation_probe import ProbeResult
    f = tmp_path / "T.lean"
    f.write_text("import Mathlib\n\nnamespace Foo\nopen Nat\n\ntheorem bar (x : ℕ) : x ≤ x := le_refl _\n\nend Foo\n",
                 encoding="utf-8")
    seen = {}

    def fake(spec, project, wrapper=None, timeout=0):
        seen["spec"] = spec
        return ProbeResult("REFUTED", "x := 4")
    monkeypatch.setattr(np_, "run_probe", fake)
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--module", "T", "--file", str(f),
                   "--theorem", "bar", "--json"])
    assert rc == 1 and json.loads(capsys.readouterr().out) == {"verdict": "REFUTED", "detail": "x := 4"}
    assert (seen["spec"].module, seen["spec"].theorem) == ("T", "Foo.bar")
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--module", "T", "--theorem", "Foo.bar"])
    assert rc == 1 and seen["spec"].theorem == "Foo.bar"


def test_cli_unexpected_exception_is_error(tmp_path, monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import negation_probe as np_

    def boom(*a, **k):
        raise RuntimeError("kaboom")
    monkeypatch.setattr(np_, "run_probe", boom)
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--module", "T", "--theorem", "t", "--json"])
    out = json.loads(capsys.readouterr().out)
    assert rc == 2 and out["verdict"] == "ERROR" and "kaboom" in out["detail"]


def test_wallclock_timeout_kills_process_group(tmp_path):
    import time
    from telperion.checks.negation_probe import ProbeSpec, run_probe
    pidfile = tmp_path / "child.pid"
    wrapper = ["sh", "-c", f"sleep 60 & echo $! > {pidfile}; wait", "sh"]
    r = run_probe(ProbeSpec("Foo", "Foo.t"), tmp_path, wrapper=wrapper, timeout=1)
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


def test_false_probe_with_nonstandard_axiom_not_counted():
    r = classify({"false": (0, "TP-FALSE PROVED axioms=[TpBad.bad]\nTP-DONE\n"), "negation": UNABLE})
    assert r.verdict == "PROBE_ONLY" and "probe 'false' used non-standard axioms ['TpBad.bad']; not counted" in r.detail


def test_witness_with_sorryax_not_counted_and_clean_counts():
    w = (0, "TP-WITNESS PROVED axioms=[propext, sorryAx]\nTP-DONE\n")
    r = classify({"false": AESOP, "negation": UNABLE, "witness": w})
    assert r.verdict == "PROBE_ONLY" and "sorryAx" in r.detail
    f = (0, "TP-FALSE PROVED axioms=[propext, Classical.choice, Quot.sound]\nTP-DONE\n")
    assert classify({"false": f, "negation": UNABLE}).verdict == "VACUOUS"


# ---------------------------------------------------------------------------------------------------------------
# Lean tests: modules are compiled into the env's own build dir under unique names and removed afterwards.
LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")

# Each case is TRUE as the file states it (the proofs compile), and each re-rendered as text in the old probe would
# read `factorial` as `Nat.factorial` (or `default` with the erased instance back), giving a wrong REFUTED. The
# re-review's Lean-confirmed scanner misses are among them (rereview_scan_harness.py).
CASES = r'''
namespace Controls
theorem vac (x : ℕ) (h1 : x < 2) (h2 : 5 < x) : x = 7 := by omega
theorem ref (x : ℕ) : x * x ≠ 16 := sorry
theorem tru (x : ℕ) (h : x < 3) : x < 5 := by omega
theorem ne_t (x : ℕ) : x + 1 ≠ 0 := by omega
theorem imp_t (x : ℕ) (h : x < 3) : x < 0 → False := by omega
end Controls

namespace S0
open Nat
def factorial (n : ℕ) : ℕ := n
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S0

namespace S1
open Nat
public def factorial (n : ℕ) : ℕ := n
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S1

namespace S2
open Nat
meta def factorial (n : ℕ) : ℕ := n
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S2

namespace S3
open Nat
theorem t0 : True := trivial def factorial (n : ℕ) : ℕ := n
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S3

with_weak_namespace S4 def factorial (n : ℕ) : ℕ := n
namespace S4
open Nat
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S4

namespace S5
open Nat
theorem c0 : '"'.toNat = 34 := rfl
def factorial (n : ℕ) : ℕ := n
-- "
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S5

namespace S6
open Nat
set_option hygiene false in
run_cmd Lean.Elab.Command.elabCommand (← `(def factorial (n : ℕ) : ℕ := n))
theorem t (n : ℕ) : factorial n ≤ n := le_refl _
end S6

namespace S7
instance (priority := high) inh7 : Inhabited ℕ := ⟨7⟩
attribute [-instance] inh7
theorem t : (default : ℕ) = 0 := rfl
end S7
'''
BAD = "namespace TpBad\n@[aesop safe apply] axiom bad : False\ntheorem tb (x : ℕ) (h : x < 3) : x < 5 := by omega\nend TpBad\n"


def _build_module(env: Path, body: str, must_build: bool = True) -> str | None:
    """Compile `import Mathlib` + body as a fresh module in env/.lake/build/lib/lean (on env's LEAN_PATH). With
    must_build=False a failed build returns None instead of failing the test."""
    from telperion.checks.negation_probe import default_wrapper
    name = f"TpTmp{secrets.token_hex(4)}"
    src = env / f".{name}_src"
    src.mkdir()
    (src / f"{name}.lean").write_text("import Mathlib\n" + body, encoding="utf-8")
    lib = env / ".lake" / "build" / "lib" / "lean"
    lib.mkdir(parents=True, exist_ok=True)
    p = subprocess.run([*default_wrapper(), "lake", "env", "lean", "-R", str(src), "-o", str(lib / f"{name}.olean"),
                        "-i", str(lib / f"{name}.ilean"), str(src / f"{name}.lean")], cwd=env,
                       capture_output=True, text=True, timeout=1800)
    shutil.rmtree(src)
    if p.returncode != 0:
        _remove_module(env, name)
        if must_build:
            pytest.fail(p.stdout + p.stderr)
        return None
    return name


def _remove_module(env: Path, name: str) -> None:
    lib = env / ".lake" / "build" / "lib" / "lean"
    for ext in (".olean", ".ilean"):
        (lib / f"{name}{ext}").unlink(missing_ok=True)
    for d in (lib, lib.parent, lib.parent.parent):
        try:
            d.rmdir()                       # only if now empty: never remove anything else's build output
        except OSError:
            break


@pytest.fixture(scope="module")
def cases_module():
    env = Path(LEAN_ENV)
    name = _build_module(env, CASES)
    yield name
    _remove_module(env, name)


@pytest.fixture(scope="module")
def bad_module():
    env = Path(LEAN_ENV)
    name = _build_module(env, BAD)
    yield name
    _remove_module(env, name)


def _probe(module, theorem, witness=None):
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    return run_probe(ProbeSpec(module, theorem, witness), Path(LEAN_ENV))


@lean
def test_lean_contradictory_hypotheses_vacuous(cases_module):          # MUST-FAIL control
    r = _probe(cases_module, "Controls.vac")
    assert r.verdict == "VACUOUS", r.detail


@lean
def test_lean_false_claim_refuted(cases_module):                        # MUST-FAIL control
    r = _probe(cases_module, "Controls.ref")
    assert r.verdict == "REFUTED", r.detail


@lean
def test_lean_true_claim_probe_only(cases_module):                      # MUST-PASS control
    r = _probe(cases_module, "Controls.tru")
    assert r.verdict == "PROBE_ONLY", r.detail
    r = _probe(cases_module, "Controls.tru", "⟨2, by norm_num, trivial⟩")
    assert r.verdict == "WITNESSED", r.detail


@lean
@pytest.mark.parametrize("theorem", ["Controls.ne_t", "Controls.imp_t"])
def test_lean_conclusion_arrows_are_not_premises(cases_module, theorem):  # MUST-PASS: `≠`, `→ False` conclusions
    r = _probe(cases_module, theorem)
    assert r.verdict == "PROBE_ONLY", r.detail


@lean
@pytest.mark.parametrize("ns", ["S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7"])
def test_lean_local_declarations_cannot_change_the_statement(cases_module, ns):   # MUST-PASS: true theorems
    r = _probe(cases_module, f"{ns}.t")
    assert r.verdict == "PROBE_ONLY", r.detail


@lean
def test_lean_bad_axiom_is_not_vacuous(bad_module):
    r = _probe(bad_module, "TpBad.tb")
    assert r.verdict == "PROBE_ONLY" and "non-standard axioms ['TpBad.bad']" in r.detail, r.detail


@lean
def test_lean_unbuilt_module_is_error():
    r = _probe("TpTmpNeverBuilt", "X.t")
    assert r.verdict == "ERROR" and "build TpTmpNeverBuilt first (lake build TpTmpNeverBuilt)" in r.detail, r.detail


@lean
def test_lean_unknown_constant_is_error(cases_module):
    r = _probe(cases_module, "Controls.nope")
    assert r.verdict == "ERROR", r.detail


# The re-reviewer's Lean-confirmed regression files (.superpowers/sdd/2026-10-27-step4-checks/rereview_lean_cases/,
# git-excluded, so copied here verbatim). Each compiles, so each `Foo.t` is TRUE as stated: `factorial` is the local
# identity, which a text re-render under `open Nat` read as `Nat.factorial` (a wrong REFUTED).
REREVIEW = {
    "charlit": "namespace Foo\ntheorem c0 : '\"'.toNat = 34 := rfl\ndef factorial (n : Nat) : Nat := n\n-- \"\nopen Nat\n"
               "theorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
    "meta": "namespace Foo\nmeta def factorial (n : Nat) : Nat := n\nopen Nat\n"
            "theorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
    "public": "namespace Foo\npublic def factorial (n : Nat) : Nat := n\nopen Nat\n"
              "theorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
    "runcmd": "import Lean\nnamespace Foo\nrun_cmd Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `factorial) "
              "(n : Nat) : Nat := n))\nopen Nat\ntheorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
    "sameend": "namespace Foo\nsection S end S def factorial (n : Nat) : Nat := n\nopen Nat\n"
               "theorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
    "sameline": "namespace Foo\ntheorem t0 : True := trivial def factorial (n : Nat) : Nat := n\nopen Nat\n"
                "theorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
    "weakns": "with_weak_namespace Foo def factorial (n : Nat) : Nat := n\nnamespace Foo\nopen Nat\n"
              "theorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n",
}
# control.lean: no local def, so `factorial` IS `Nat.factorial` and the proof does not compile (the shadowing above is
# real). Its sorry'd form is a FALSE statement and must be REFUTED.
REREVIEW_CONTROL = "namespace Foo\nopen Nat\ntheorem t (n : Nat) : factorial n ≤ n := Nat.le_refl _\nend Foo\n"
# instthm.lean: an `@[instance] theorem`; no premises, nothing to refute.
REREVIEW_INSTTHM = "namespace Foo\n@[instance] theorem fi : Fact (1 < 2) := ⟨by decide⟩\nend Foo\n"
# mod/A.lean: `attribute [-instance] hi` makes `K.v` mean `lo`'s 2 in A; it does not carry over to an importer (mod/B.lean,
# `theorem inB : K.v = 2 := rfl`, does not compile), so a text re-render outside A would read `hi`'s 1.
REREVIEW_MOD_A = ("class K where v : Nat\ninstance hi : K := ⟨1⟩\ninstance (priority := low) lo : K := ⟨2⟩\n"
                  "attribute [-instance] hi\ntheorem inA : K.v = 2 := rfl\n")


@pytest.fixture(scope="module")
def rereview_modules():
    env = Path(LEAN_ENV)
    mods = {k: _build_module(env, body) for k, body in REREVIEW.items()}
    mods["instthm"] = _build_module(env, REREVIEW_INSTTHM)
    mods["mod_a"] = _build_module(env, REREVIEW_MOD_A)
    mods["control_sorry"] = _build_module(env, REREVIEW_CONTROL.replace("Nat.le_refl _", "sorry"))
    yield mods
    for name in mods.values():
        _remove_module(env, name)


@lean
@pytest.mark.parametrize("case", sorted(REREVIEW))
def test_lean_rereview_cases_probe_the_real_statement(rereview_modules, case):   # MUST-PASS: true theorems
    r = _probe(rereview_modules[case], "Foo.t")
    assert r.verdict == "PROBE_ONLY", r.detail


@lean
def test_lean_rereview_control_is_really_false(rereview_modules):
    assert _build_module(Path(LEAN_ENV), REREVIEW_CONTROL, must_build=False) is None
    r = _probe(rereview_modules["control_sorry"], "Foo.t")
    assert r.verdict == "REFUTED", r.detail


@lean
def test_lean_rereview_instthm_and_erased_instance(rereview_modules):
    r = _probe(rereview_modules["instthm"], "Foo.fi")
    assert r.verdict == "PROBE_ONLY", r.detail
    r = _probe(rereview_modules["mod_a"], "inA")
    assert r.verdict == "PROBE_ONLY", r.detail

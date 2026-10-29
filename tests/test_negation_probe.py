import os
import secrets
import shutil
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple
import pytest
from telperion.checks.lean_replay import ReplayResult
from telperion.checks.negation_probe import ProbeSpec, classify, classify_replay, render_callback

sys.path.insert(0, str(Path(__file__).resolve().parent))  # shared lean_env helpers
from lean_env import fake_trusted_env, session_trusted_manifest  # noqa: E402

# Phase 2 (replay isolation): the probes run as ONE callback on the module's kernel replay and report through the
# replay's nonce'd lines (tag stripped here): `PREMISES n`, then one `FALSE`, `NEGATION` and (with a witness)
# `WITNESS` result line. The inputs below are those lines; the expected verdicts are the ones the text-based probe had.
OK = ["PREMISES 2", "FALSE PROVED axioms=[]", "WITNESS PROVED axioms=[propext]"]
NOT_FALSE = ["PREMISES 2", "FALSE FAILED linarith failed"]
GAVE_UP = ["NEGATION GAVEUP 200"]


def test_false_compiled_is_vacuous():
    assert classify(OK[:2] + GAVE_UP).verdict == "VACUOUS"


def test_counterexample_is_refuted():
    # REFUTED is plausible's `TestResult.failure` value (the callback prints its counterexample), not banner text
    assert classify(NOT_FALSE + ["NEGATION FAILURE x := 3"]).verdict == "REFUTED"


def test_plausible_gave_up():
    r = classify(NOT_FALSE + GAVE_UP)
    assert r.verdict == "PROBE_ONLY"


def test_probe_error_is_not_vacuous():
    r = classify_replay(ReplayResult("ERROR", "lean exited 1: error: unknown identifier 'Foo'"), ProbeSpec("M", "t"))
    assert r.verdict == "ERROR"


def test_witness():
    r = classify(NOT_FALSE + GAVE_UP + OK[2:], witness=True)
    assert r.verdict == "WITNESSED"


def test_render_contains_parts():
    src = render_callback("Foo.t", None)
    assert not any(ln.startswith("import") for ln in src.splitlines())   # the callback never imports the module
    assert "find? `«Foo».«t»" in src and "forallBoundedTelescope" in src
    assert "Plausible.Testable.checkIO" in src and "evalExpr (IO TelperionProbe.Outcome)" in src
    assert "| .failure _ xs _ => .failure xs" in src and '"NEGATION FAILURE' in src and "WITNESS" not in src
    w = render_callback("Foo.t", 'by exact ⟨2, "a\\"b"⟩')
    assert '"by exact ⟨2, \\"a\\\\\\"b\\"⟩"' in w and "WITNESS PROVED" in w
    # round 4: the witness ranges over the FULL non-reducing telescope; the premise split checks the exact marker
    assert "forallTelescope info.type" in w
    assert "v.ctx == `_internal && v.imported.isAnonymous" in src


# Real v4.35.0 shapes: a caught tactic failure, plausible finding nothing.
AESOP = ["PREMISES 1", "FALSE FAILED Tactic `aesop` failed, made no progress Initial goal: x : ℕ ⊢ False"]
UNABLE = ["NEGATION SUCCESS"]


def test_aesop_failure_is_purpose_error():
    assert classify(AESOP + UNABLE).verdict == "PROBE_ONLY"


def test_no_testable_instance_is_probe_only():
    r = classify(AESOP + ["NEGATION NO_TESTABLE"])
    assert r.verdict == "PROBE_ONLY" and "negation probe did not run: no testable instance (e.g. ℝ)" in r.detail


def test_incomplete_witness_is_not_witnessed():
    w = ["WITNESS INCOMPLETE mvars=false sorry=true"]
    r = classify(AESOP + UNABLE + w, witness=True)
    assert r.verdict == "PROBE_ONLY" and "probe 'witness'" in r.detail


def test_failed_witness_is_error():
    w = ["WITNESS FAILED type mismatch trivial"]
    assert classify(AESOP + UNABLE + w, witness=True).verdict == "ERROR"


def test_nonzero_rc_without_message_is_error():
    r = classify_replay(ReplayResult("ERROR", "lean exited 1: 'lake: something broke'"), ProbeSpec("M", "t"))
    assert r.verdict == "ERROR"


def test_coded_error_header_is_parsed():
    coded = ReplayResult("ERROR", "lean exited 1: p/R.lean:5:25: error(lean.unknownConstant): Unknown constant `Foo.nope`")
    r = classify_replay(coded, ProbeSpec("M", "t"))
    assert r.verdict == "ERROR" and "unknownConstant" in r.detail


def test_missing_protocol_line_is_error():
    r = classify(["PREMISES 1"] + UNABLE)
    assert r.verdict == "ERROR" and "no FALSE result line" in r.detail      # R2-M6: no per-probe tag any more


def test_protocol_tag_done_and_duplicates():
    from telperion.checks.lean_replay import parse_replay_output
    tag = "TR" + "ab" * 16
    out = "".join(f"TR{'cd' * 16}-{ln}\n" for ln in ["REPLAY OK axioms=[]", *OK, "DONE"])
    # a line with another tag (any other process printing protocol lines, say) is ignored
    assert parse_replay_output(out, tag)[0] == "ERROR"
    # exactly one result line per probe
    for lines in (["FALSE PROVED axioms=[]", "FALSE FAILED later"], ["FALSE FAILED earlier", "FALSE PROVED axioms=[]"]):
        r = classify(lines + UNABLE)
        assert r.verdict == "ERROR", lines
    # exactly one final DONE, nothing tagged after it (lean_replay's protocol around the callback lines)
    for body in (["REPLAY OK axioms=[]", "FALSE PROVED axioms=[]"], ["REPLAY OK axioms=[]", "DONE", "DONE"],
                 ["REPLAY OK axioms=[]", "DONE", "FALSE PROVED axioms=[]"]):
        out = "".join(f"{tag}-{ln}\n" for ln in body)
        assert parse_replay_output(out, tag)[0] == "ERROR", body
    assert classify(["FALSE PROVED axioms=[]"] + UNABLE).verdict == "VACUOUS"


def test_run_probe_nonce_is_128_bit(tmp_path):
    import re
    from telperion.checks.negation_probe import run_probe
    env, elan, manifest = fake_trusted_env(tmp_path / "trusted")
    sub = tmp_path / "sub"
    sub.mkdir()
    (sub / "Foo.olean").write_bytes(b"foo")
    # the wrapper prints the replay script instead of running Lean: no protocol line, so ERROR
    seen = tmp_path / "seen.txt"
    r = run_probe(ProbeSpec("Foo", "Foo.t"), tmp_path, wrapper=["sh", "-c", f'for a; do s=$a; done; cat "$s" >> {seen}', "sh"],
                  untrusted_paths=[sub], trusted_env=env, manifest=manifest, elan_home=elan)
    assert r.verdict == "ERROR", r.detail
    m = re.search(r'def tag : String := "(TR[0-9a-f]+)"', seen.read_text())
    assert m and len(m.group(1)) == 2 + 32
    # the script lives in a private temp dir: nothing is written to the project
    assert sorted(p.name for p in tmp_path.iterdir()) == ["seen.txt", "sub", "trusted"]


def test_unbuilt_module_is_error():
    r = classify_replay(ReplayResult("FAILED", "module Foo.Bar has no .olean in the search path (build it first)"),
                        ProbeSpec("Foo.Bar", "t"))
    assert r.verdict == "ERROR" and "build Foo.Bar first (lake build Foo.Bar)" in r.detail


# Fix round 1: timeouts are inconclusive.
TIMEOUT = "TIMEOUT (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached"
REFUTE = ["NEGATION FAILURE x := 4"]


def test_false_timeout_is_inconclusive():
    r = classify(["FALSE " + TIMEOUT] + UNABLE)
    assert r.verdict == "PROBE_ONLY" and "probe 'false' timed out at maxHeartbeats 200000 (inconclusive)" in r.detail


def test_negation_timeout_is_inconclusive():
    r = classify(AESOP + ["NEGATION " + TIMEOUT])
    assert r.verdict == "PROBE_ONLY" and "probe 'negation' timed out at maxHeartbeats 200000 (inconclusive)" in r.detail


def test_timeout_plus_counterexample_elsewhere_is_refuted():
    assert classify(["FALSE " + TIMEOUT] + REFUTE).verdict == "REFUTED"


def test_timeout_never_gives_positive_verdict():
    assert classify(OK[:2] + ["FALSE " + TIMEOUT] + UNABLE).verdict == "PROBE_ONLY"
    assert classify(AESOP + REFUTE + ["NEGATION " + TIMEOUT]).verdict == "PROBE_ONLY"
    r = classify(AESOP + UNABLE + ["WITNESS " + TIMEOUT], witness=True)
    assert r.verdict == "PROBE_ONLY" and "probe 'witness' timed out" in r.detail


def test_stale_probe_dirs_do_not_wedge_later_probes(tmp_path):
    # round 4: a SIGKILLed run's dir never blocks a later one; phase 2: probes write nothing to the project at all
    from telperion.checks.negation_probe import run_probe
    env, elan, manifest = fake_trusted_env(tmp_path / "trusted")
    for stale in (".telperion_probe", ".telperion_probe_deadbeef"):
        (tmp_path / stale).mkdir()
        (tmp_path / stale / "false.lean").write_text("stale", encoding="utf-8")
    r = run_probe(ProbeSpec("Foo", "Foo.t"), tmp_path, wrapper=["false"], trusted_env=env, manifest=manifest,
                  elan_home=elan)
    assert r.verdict == "ERROR" and "probe dir" not in r.detail and "exited 1" in r.detail
    assert sorted(p.name for p in tmp_path.glob(".telperion_probe*")) == [".telperion_probe", ".telperion_probe_deadbeef"]
    assert (tmp_path / ".telperion_probe_deadbeef" / "false.lean").read_text(encoding="utf-8") == "stale"


def test_cli_help_documents_built_module(capsys):
    from telperion import cli
    with pytest.raises(SystemExit):
        cli.main(["probe-negation", "--help"])
    out = capsys.readouterr().out
    assert "--module" in out and "built" in out and "elaborated" in out


# Fix round 2: anchored banner, CLI exceptions, process-group timeout, axiom audit.
def test_counterexample_phrase_outside_banner_is_not_refuted():
    # no text is scanned at all: a statement or message mentioning the phrase cannot produce REFUTED
    neg = AESOP + ['PREMISES 1 "Found a counter-example!"', "NEGATION SUCCESS"]
    assert classify(neg).verdict == "PROBE_ONLY"
    neg2 = ReplayResult("ERROR", 'lean exited 1: f.lean:3:8: error: type mismatch "Found a counter-example!"')
    assert classify_replay(neg2, ProbeSpec("M", "t")).verdict == "ERROR"


def test_cli_json_and_theorem_qualified_from_file(tmp_path, monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import negation_probe as np_
    from telperion.checks.negation_probe import ProbeResult
    f = tmp_path / "T.lean"
    f.write_text("import Mathlib\n\nnamespace Foo\nopen Nat\n\ntheorem bar (x : ℕ) : x ≤ x := le_refl _\n\nend Foo\n",
                 encoding="utf-8")
    seen = {}

    def fake(spec, project, wrapper=None, timeout=0, **kw):
        seen["spec"] = spec
        return ProbeResult("REFUTED", "x := 4")
    monkeypatch.setattr(np_, "run_probe", fake)
    rc = cli.main(["probe-negation", "--project", str(tmp_path), "--module", "T", "--file", str(f),
                   "--theorem", "bar", "--json"])
    import hashlib
    assert rc == 1 and json.loads(capsys.readouterr().out) == {
        "verdict": "REFUTED", "detail": "x := 4", "module": "T", "theorem": "Foo.bar",
        "source_sha256": hashlib.sha256(f.read_bytes()).hexdigest()}
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
    from telperion.checks.negation_probe import run_probe
    env, elan, manifest = fake_trusted_env(tmp_path / "trusted")
    pidfile = tmp_path / "child.pid"
    wrapper = ["sh", "-c", f"sleep 60 & echo $! > {pidfile}; wait", "sh"]
    r = run_probe(ProbeSpec("Foo", "Foo.t"), tmp_path, wrapper=wrapper, timeout=1, trusted_env=env,
                  manifest=manifest, elan_home=elan)
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
    r = classify(["FALSE PROVED axioms=[TpBad.bad]"] + UNABLE)
    assert r.verdict == "PROBE_ONLY" and "probe 'false' used non-standard axioms ['TpBad.bad']; not counted" in r.detail


def test_witness_with_sorryax_not_counted_and_clean_counts():
    w = ["WITNESS PROVED axioms=[propext, sorryAx]"]
    r = classify(AESOP + UNABLE + w, witness=True)
    assert r.verdict == "PROBE_ONLY" and "sorryAx" in r.detail
    f = ["FALSE PROVED axioms=[propext, Classical.choice, Quot.sound]"]
    assert classify(f + UNABLE).verdict == "VACUOUS"


# Phase 2: the value-based negation statuses, the declared-axiom note, and the olean binding.
def test_unavailable_negation_is_a_probe_only_note_and_untrusted_axioms_are_error():
    r = classify(AESOP + ["NEGATION UNAVAILABLE Failed to find LCNF signature for S0.factorial"])
    assert r.verdict == "PROBE_ONLY" and "could not evaluate the statement" in r.detail
    refused = ReplayResult("FAILED", "the untrusted module M declares the axiom M.ax; refusing")
    r = classify_replay(refused, ProbeSpec("M", "t"))
    assert (r.verdict, r.detail) == ("ERROR", "module declares axiom M.ax; untrusted axioms are refused by replay")
    assert classify(AESOP + ["NEGATION BOGUS"]).verdict == "ERROR"
    assert classify(["MISSING"]).verdict == "ERROR"


def test_replay_result_binds_the_olean():
    closure = [["M", "olean", "cd" * 32]]
    ok = ReplayResult("OK", "modules=[M] constants=1 declared=[] axioms=[]", OK[:2] + GAVE_UP,
                      olean_sha256="ab" * 32, olean_closure=closure)
    r = classify_replay(ok, ProbeSpec("M", "t"))
    assert r.verdict == "VACUOUS" and r.olean_sha256 == "ab" * 32
    assert r.to_json()["olean_sha256"] == "ab" * 32 and r.to_json()["olean_closure"] == closure
    r = classify_replay(ReplayResult("FAILED", "(kernel) declaration type mismatch"), ProbeSpec("M", "t"))
    assert r.verdict == "ERROR" and "replay refused" in r.detail and "olean_sha256" not in r.to_json()


# ---------------------------------------------------------------------------------------------------------------
# Lean tests: modules are compiled into their own dirs `<env>/.tp_mod_<hex>/` and replayed from there (an untrusted
# path); the trusted manifest of the env is built once per process in a temp dir.
LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")


@pytest.fixture(autouse=True)
def _trusted_manifest(request):
    if LEAN_ENV and request.node.get_closest_marker("skipif") is not None:
        session_trusted_manifest(LEAN_ENV)

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

namespace C2
-- round 4, the re-reviewer's C2 cases: an arrow conclusion, and macro-generated binders `a✝`/`h✝` (macro scopes of
-- THIS module, not the elaborator's `_internal` arrow marker)
theorem arrow (n : ℕ) : n < 0 → n = 7 := by omega
macro "tp_mk_hyg" : command => `(theorem $(Lean.mkIdent `hyg) (a : ℕ) (h : a < 0) : a = 7 := by omega)
tp_mk_hyg
end C2

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


class Built(NamedTuple):
    name: str
    lib: Path                         # this module's own dir, an untrusted olean dir for the replay


def _lean_path_wrapper(lib: Path | None) -> list[str]:
    from telperion.checks.negation_probe import default_wrapper
    return (["env", f"LEAN_PATH={lib}"] if lib else []) + default_wrapper()


def _build_module(env: Path, body: str, must_build: bool = True) -> Built | None:
    """Compile `import Mathlib` + body as a fresh module into its OWN dir `<env>/.tp_mod_<hex>/`, which only the
    probes of this module put on LEAN_PATH. Nothing shared (the env's `.lake/build`) is created or removed, so a
    concurrent compile cannot race the cleanup. With must_build=False a failed build returns None."""
    hexid = secrets.token_hex(8)
    built = Built(f"TpTmp{hexid}", env / f".tp_mod_{hexid}")
    src = built.lib / "src"
    src.mkdir(parents=True)
    (src / f"{built.name}.lean").write_text("import Mathlib\n" + body, encoding="utf-8")
    p = subprocess.run([*_lean_path_wrapper(None), "lake", "env", "lean", "-R", str(src),
                        "-o", str(built.lib / f"{built.name}.olean"), "-i", str(built.lib / f"{built.name}.ilean"),
                        str(src / f"{built.name}.lean")], cwd=env, capture_output=True, text=True, timeout=1800)
    shutil.rmtree(src)
    if p.returncode != 0:
        _remove_module(built)
        if must_build:
            pytest.fail(p.stdout + p.stderr)
        return None
    return built


def _remove_module(built: Built) -> None:
    shutil.rmtree(built.lib, ignore_errors=True)


@pytest.fixture(scope="module")
def cases_module():
    built = _build_module(Path(LEAN_ENV), CASES)
    yield built
    _remove_module(built)


@pytest.fixture(scope="module")
def bad_module():
    built = _build_module(Path(LEAN_ENV), BAD)
    yield built
    _remove_module(built)


def _probe(module: Built | str, theorem, witness=None):
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    if isinstance(module, Built):
        return run_probe(ProbeSpec(module.name, theorem, witness), untrusted_paths=[module.lib])
    return run_probe(ProbeSpec(module, theorem, witness))


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
    # Ruling 10: never VACUOUS through an untrusted axiom; the replay refuses the axiom outright (was: PROBE_ONLY with
    # "non-standard axioms ['TpBad.bad']" when the module was imported and aesop used the axiom)
    r = _probe(bad_module, "TpBad.tb")
    assert r.verdict == "ERROR" and r.detail == ("module declares axiom TpBad.bad; untrusted axioms are refused by "
                                                 "replay"), r.detail


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
    for built in mods.values():
        _remove_module(built)


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


@lean
def test_lean_witness_ranges_over_the_full_telescope(cases_module):   # C2: the premise split is author-controlled
    # `n < 0 → n = 7`: the arrow is not a premise for VACUOUS, but the witness must also satisfy it
    assert _probe(cases_module, "C2.arrow").verdict == "PROBE_ONLY"
    r = _probe(cases_module, "C2.arrow", "⟨0, trivial⟩")
    assert r.verdict != "WITNESSED", r.detail
    # macro-scoped user binders are premises (exact `_internal` marker), so `a < 0` is seen, and is contradictory
    r = _probe(cases_module, "C2.hyg")
    assert r.verdict == "VACUOUS" and "the 2 premise(s)" in r.detail, r.detail
    r = _probe(cases_module, "C2.hyg", "trivial")
    assert r.verdict != "WITNESSED", r.detail


# Phase 2 MUST-FAIL controls: the reviewer's evil module. Imported, it forges verdicts (an `initialize` that reads the
# check's script for the nonce and prints forged result lines, a `#eval` override, `omega`/`plausible` overrides, a
# compile-time forging `#eval`); replayed, none of it runs, so the probe gives the TRUE verdicts.
EVIL = r'''open Lean Elab Command Tactic
#eval IO.println "TP0000-NEGATION FAILURE x := 0"
initialize do
  IO.println "TPEVIL-INIT"
  for e in ← System.FilePath.readDir "." do
    if let .ok s ← (IO.FS.readFile e.path).toBaseIO then
      for l in s.splitOn "\n" do
        if l.startsWith "def tag : String := " then
          if let _ :: t :: _ := l.splitOn "\"" then
            IO.println s!"{t}-WITNESS PROVED axioms=[]"
            IO.println s!"{t}-NEGATION FAILURE x := 0"
@[command_elab Lean.Parser.Command.eval] def tpEvilEval : CommandElab := fun _ => IO.println "TPEVIL-EVAL"
@[tactic Lean.Parser.Tactic.omega] def tpEvilOmega : Tactic := fun _ => do
  IO.println "TPEVIL-TACTIC"
  for g in ← getGoals do g.admit
@[tactic plausibleSyntax] def tpEvilPlausible : Tactic := fun _ => do
  IO.println "TPEVIL-PLAUSIBLE"
  throwError "\n===================\nFound a counter-example!\nx := 0\n-------------------"
namespace TpEvil
theorem vac (x : ℕ) (h : x < 0) : x = 7 := absurd h (Nat.not_lt_zero x)
theorem tru (x : ℕ) (h : x < 3) : x < 5 := Nat.lt_trans h (by decide)
end TpEvil
'''


@pytest.fixture(scope="module")
def evil_module():
    built = _build_module(Path(LEAN_ENV), EVIL)
    yield built
    _remove_module(built)


@lean
def test_lean_evil_module_cannot_forge_verdicts(evil_module):          # MUST-FAIL control (phase 2)
    # control: imported the usual way, the shapes fire (the old probe's `plausible` and `#eval` are hijacked)
    f = evil_module.lib / "Control.lean"
    f.write_text(f"import Mathlib\nimport {evil_module.name}\nexample : type_of% @TpEvil.tru := by plausible\n"
                 "#eval IO.println \"CONTROL-EVAL-RAN\"\n", encoding="utf-8")
    p = subprocess.run([*_lean_path_wrapper(evil_module.lib), "lake", "env", "lean", str(f)], cwd=LEAN_ENV,
                       capture_output=True, text=True, timeout=1800)
    ctl = p.stdout + p.stderr
    assert all(m in ctl for m in ("TPEVIL-INIT", "TPEVIL-PLAUSIBLE", "TPEVIL-EVAL")), ctl[-3000:]
    assert "CONTROL-EVAL-RAN" not in ctl
    # replayed: the true verdicts. A forged WITNESSED for the vacuous theorem, or REFUTED for the true one, is a FAIL.
    r = _probe(evil_module, "TpEvil.vac", "⟨0, sorry, trivial⟩")
    assert r.verdict == "VACUOUS" and "TPEVIL" not in r.detail, r.detail
    r = _probe(evil_module, "TpEvil.tru")
    assert r.verdict == "PROBE_ONLY" and "TPEVIL" not in r.detail, r.detail
    assert r.olean_sha256 and len(r.olean_sha256) == 64

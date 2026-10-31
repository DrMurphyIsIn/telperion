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
# `WITNESS` and `REDUCED` result line. The inputs below are those lines; the expected verdicts are the ones the
# text-based probe had.
OK = ["PREMISES 2", "FALSE PROVED axioms=[]", "WITNESS PROVED axioms=[propext]", "REDUCED PROVED axioms=[propext]",
      "ALLOW OK"]
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
    # final review C1: the target name reaches Lean as DATA (string literals fed to Name.mkStr), never as syntax
    assert '(["Foo", "t"] : List String).foldl Lean.Name.mkStr Lean.Name.anonymous' in src
    assert "find? TelperionProbe.target" in src and "forallBoundedTelescope" in src
    assert "Plausible.Testable.checkIO" in src and "evalExpr (IO TelperionProbe.Outcome)" in src
    assert "| .failure _ xs _ => .failure xs" in src and '"NEGATION FAILURE' in src and "WITNESS" not in src
    w = render_callback("Foo.t", 'by exact ⟨2, "a\\"b"⟩')
    assert '"by exact ⟨2, \\"a\\\\\\"b\\"⟩"' in w and "WITNESS PROVED" in w
    # round 4: the witness ranges over the FULL non-reducing telescope; the premise split checks the exact marker
    assert "forallTelescope ty" in w           # final review C2: `ty` is the type with non-library heads unfolded
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


# Final review C1: untrusted artifact text never reaches the callback's Lean source as syntax.
PAYLOAD_ARTIFACT = ('def s : String := r#"\nnamespace X»<|>(←(TelperionReplay.line("x")*>IO.Process.exit(0)))<|>`«Y\n"#\n'
                    'theorem foo : 1 + 1 = 2 := rfl\n')


def test_c1_payload_in_a_string_never_reaches_the_callback():
    from telperion.checks.negation_probe import qualify
    name = qualify(PAYLOAD_ARTIFACT, "foo")
    assert name == "foo"                                         # the namespace line is inside a raw string
    src = render_callback(name, None)
    assert "IO.Process.exit" not in src and "<|>" not in src and "X»" not in src
    # a namespace line that is real code but not a plain identifier is refused, never spliced
    with pytest.raises(ValueError, match="not a plain Lean name"):
        qualify("namespace X»<|>(e)<|>`«Y\ntheorem foo : True := trivial\nend X\n", "foo")


@pytest.mark.parametrize("bad", ["X»<|>(←(IO.Process.exit 0))<|>`«Y.foo", "«a b».t", "a..b", "1a", "Foo.t\n#eval 1",
                                 'a"b', "λx"])
def test_c1_names_are_validated_identifiers(bad):
    from telperion.checks.negation_probe import run_probe
    with pytest.raises(ValueError, match="not a plain Lean name"):
        render_callback(bad, None)
    r = run_probe(ProbeSpec("M", bad), wrapper=["false"])        # refused before anything runs
    assert r.verdict == "ERROR" and "not a plain Lean name" in r.detail


def test_c1_comments_and_char_literals_are_not_commands():
    from telperion.checks.negation_probe import qualify
    text = ("namespace A.B\n-- namespace Z\n/- namespace W -/\ntheorem c : ('\"').toNat = 34 := rfl\n"
            's := "\nnamespace Q\n"\ntheorem foo : True := trivial\nend A.B\n')
    assert qualify(text, "foo") == "A.B.foo"


# Final review C2 and M1: the statement's non-library heads are unfolded, only a theorem is probed, a witness needs
# a Prop-typed antecedent, and the auxiliary theorems are kernel-checked before PROVED is printed.
def test_c2_m1_render():
    src = render_callback("Foo.t", "trivial")
    assert "TelperionProbe.unfoldHeads (← getEnv) 1000 info.type" in src and "forallBoundedTelescope ty" in src
    assert "forallTelescope ty" in src and "Plausible.Decorations.addDecorations ty" in src
    assert "unless info matches .thmInfo _ do" in src and '"NOTTHEOREM' in src and '"WITNESS NOANTECEDENT"' in src
    # step 6 Task 0 adds the third site: the reduced witness check is kernel-checked synchronously too
    assert src.count("withOptions (fun o => Elab.async.set o false) do\n") == 3
    assert src.count("withOptions (fun o => Elab.async.set o false) do\n          addDecl") == 2     # witness, reduced
    assert src.count("withOptions (fun o => Elab.async.set o false) do\n            addDecl") == 1   # false
    assert "`Mathlib" in src and "`Init" in src                  # the library roots: the fingerprint's


def test_c2_classify_not_a_theorem_and_no_antecedent():
    r = classify(["NOTTHEOREM def"])
    assert r.verdict == "ERROR" and "not a theorem" in r.detail
    r = classify(AESOP + UNABLE + ["WITNESS NOANTECEDENT"], witness=True)
    assert r.verdict == "PROBE_ONLY" and "nothing to witness" in r.detail


def test_n1_witness_string_uses_only_lean_escapes():
    from telperion.checks.negation_probe import _lean_string
    assert _lean_string('a"b\\c\nd\te\rf') == '"a\\"b\\\\c\\nd\\te\\rf"'
    assert _lean_string("\b\f\x01\x7f") == '"\\x08\\x0c\\x01\\x7f"'          # never JSON's \b or \f
    assert _lean_string("⟨2, trivial⟩") == '"⟨2, trivial⟩"'


def test_n2_unfold_fuel_exhausted_is_error():
    assert "let some ty := TelperionProbe.unfoldHeads (← getEnv) 1000 info.type" in render_callback("Foo.t", None)
    r = classify(["UNFOLD_EXHAUSTED"])
    assert r.verdict == "ERROR" and "did not unfold within 1000 steps" in r.detail


# Step 6 Task 0 (C2 residual): WITNESSED also needs the same witness to close the ∃-closure over the REDUCING
# telescope (the `REDUCED` line). That check only ever downgrades WITNESSED to PROBE_ONLY.
WITNESS_OK = ["WITNESS PROVED axioms=[propext]"]
SURVIVE = "witness does not survive reduction"


def test_c2r_render():
    src = render_callback("Foo.t", "trivial")
    assert "partial def reducedClosure" in src and "forallTelescopeReducing e fun xs body" in src
    # fix round 3 (R3): the closure is built from the SAME expanded term the allowlist walks
    assert "let e ← TelperionProbe.expandLocal ty" in src and "expanded.set (some e)" in src
    assert "withTransparency .default (TelperionProbe.reducedClosure e)" in src
    assert "(``And, #[a, b])" in src and "(``Iff, #[a, b])" in src
    assert 'TelperionProbe.budget "REDUCED" "FAILED" do' in src and "`_telperion_probe_reduced" in src
    # the same witness, parsed from the same data literal, and kernel-checked synchronously like the first one
    assert src.count('`term "trivial"') == 2
    sync_add = "withOptions (fun o => Elab.async.set o false) do\n          addDecl (.thmDecl { name := `"
    assert src.count(sync_add + "_telperion_probe_reduced") == 1
    assert "REDUCED" not in render_callback("Foo.t", None)


@pytest.mark.parametrize("reduced", [[], ["REDUCED FAILED type mismatch ⟨0, rfl, trivial⟩"],
                                     ["REDUCED " + "TIMEOUT (deterministic) timeout at `whnf`, maximum number of "
                                      "heartbeats (200000) has been reached"],
                                     ["REDUCED INCOMPLETE mvars=false sorry=true"],
                                     ["REDUCED PROVED axioms=[propext, sorryAx]"],
                                     ["REDUCED PROVED"]])
def test_c2r_witness_that_does_not_survive_reduction_is_probe_only(reduced):
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + reduced, witness=True)
    assert r.verdict == "PROBE_ONLY" and SURVIVE in r.detail, r.detail


def test_c2r_reduction_timeout_note():
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + ["REDUCED " + TIMEOUT], witness=True)
    assert r.verdict == "PROBE_ONLY" and SURVIVE in r.detail and "timed out at maxHeartbeats 200000" in r.detail


def test_c2r_reduction_never_upgrades():
    red = ["REDUCED PROVED axioms=[propext]", "ALLOW OK"]
    assert classify(NOT_FALSE + GAVE_UP + WITNESS_OK + red, witness=True).verdict == "WITNESSED"
    # every non-WITNESSED witness outcome stays what it was with a clean REDUCED line
    for w, verdict in ((["WITNESS NOANTECEDENT"], "PROBE_ONLY"), (["WITNESS INCOMPLETE mvars=true sorry=false"],
                       "PROBE_ONLY"), (["WITNESS PROVED axioms=[sorryAx]"], "PROBE_ONLY"),
                       (["WITNESS " + TIMEOUT], "PROBE_ONLY"), (["WITNESS FAILED type mismatch"], "ERROR")):
        assert classify(AESOP + UNABLE + w + red, witness=True).verdict == verdict, w
    assert classify(OK[:2] + GAVE_UP + WITNESS_OK + red, witness=True).verdict == "VACUOUS"
    assert classify(NOT_FALSE + REFUTE + WITNESS_OK + red, witness=True).verdict == "REFUTED"
    # without a witness a REDUCED line means nothing (the callback prints none)
    assert classify(NOT_FALSE + GAVE_UP + red).verdict == "PROBE_ONLY"


def test_c2r_reduced_protocol_is_strict():
    two = ["REDUCED PROVED axioms=[]", "REDUCED FAILED later"]
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + two, witness=True)
    assert r.verdict == "ERROR" and "2 REDUCED result lines" in r.detail
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + ["REDUCED BOGUS"], witness=True)
    assert r.verdict == "ERROR" and "unknown status 'BOGUS'" in r.detail


# Fix rounds 1-2 (Rulings 3, 4): WITNESSED needs the statement inside an ALLOWLIST of shapes (`REDUCED OUTSIDE`
# otherwise), checked once the witness has closed the reduced closure; anything else is PROBE_ONLY, whatever the
# witness.
ALLOW = "outside the WITNESSED allowlist"


def test_c2r_unopened_render():
    src = render_callback("Foo.t", "trivial")
    assert "def unopened" not in src                                        # Ruling 3's denylist is gone
    # fix round 3 (Ruling 5, M5): `Ne` is gone from the heads (it reduces to `→ False` before any leaf)
    heads = "[``Eq, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``True, ``Nat.le, ``Dvd.dvd]"
    assert f"def okHeads : List Name := {heads}" in src
    assert "partial def dataProblem (e : Expr) : MetaM (Option String)" in src and "isPropFormerType ty" in src
    assert "deltaExpand ty fun n => !isLib env n" in src                   # local definitions cannot hide data
    # the walk has its own budget and line (M7), on the term the REDUCED check expanded (R3)
    assert 'TelperionProbe.budget "ALLOW" "FAILED" do' in src
    assert "match ← TelperionProbe.allowlistProblem e with" in src
    assert 'TelperionReplay.line s!"ALLOW OUTSIDE {why}"' in src and 'TelperionReplay.line "ALLOW OK"' in src
    assert src.count("allowlistProblem e") == 1 and "REDUCED OUTSIDE" not in src
    assert "ALLOW" not in render_callback("Foo.t", None)


def test_c2r_unopened_is_probe_only():
    red = ["REDUCED PROVED axioms=[propext]"]
    out = ["ALLOW OUTSIDE a hypothesis `x = 0 ↔ V` is not an atom"]
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + red + out, witness=True)
    assert r.verdict == "PROBE_ONLY" and ALLOW in r.detail and "a hypothesis `x = 0 ↔ V`" in r.detail, r.detail
    # never an upgrade: with a failed first witness it is still ERROR, with no antecedent still PROBE_ONLY
    assert classify(AESOP + UNABLE + ["WITNESS FAILED x"] + red + out, witness=True).verdict == "ERROR"
    r = classify(AESOP + UNABLE + ["WITNESS NOANTECEDENT"] + red + out, witness=True)
    assert r.verdict == "PROBE_ONLY" and "nothing to witness" in r.detail
    assert classify(NOT_FALSE + GAVE_UP + WITNESS_OK + ["REDUCED UNOPENED x"], witness=True).verdict == "ERROR"
    assert classify(NOT_FALSE + GAVE_UP + WITNESS_OK + ["REDUCED OUTSIDE x"], witness=True).verdict == "ERROR"


# Fix round 3 (Ruling 5, M7): the ALLOW line, its own budget and note. Missing, failed or timed out: not WITNESSED.
@pytest.mark.parametrize("allow,note", [
    ([], "allowlist check failed: no ALLOW result line"),
    (["ALLOW FAILED unknown constant"], "allowlist check failed: unknown constant"),
    (["ALLOW " + TIMEOUT], "allowlist check failed: it timed out at maxHeartbeats")])
def test_c2r_allow_failure_is_probe_only(allow, note):
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + ["REDUCED PROVED axioms=[]"] + allow, witness=True)
    assert r.verdict == "PROBE_ONLY" and note in r.detail and "does not survive" not in r.detail, r.detail


def test_c2r_allow_protocol_is_strict():
    red = ["REDUCED PROVED axioms=[]"]
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + red + ["ALLOW OK", "ALLOW OK"], witness=True)
    assert r.verdict == "ERROR" and "2 ALLOW result lines" in r.detail
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + red + ["ALLOW MAYBE"], witness=True)
    assert r.verdict == "ERROR" and "unknown status 'MAYBE'" in r.detail
    # the reduced-witness reason comes first; ALLOW OK never rescues it
    r = classify(NOT_FALSE + GAVE_UP + WITNESS_OK + ["REDUCED FAILED x", "ALLOW OK"], witness=True)
    assert r.verdict == "PROBE_ONLY" and "does not survive" in r.detail


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


# Final review C1 (Lean): the reviewer's payload artifact compiles, and the probe gives a normal verdict on `foo`.
@lean
def test_lean_c1_payload_artifact_gives_a_normal_verdict():
    from telperion.checks.negation_probe import qualify
    built = _build_module(Path(LEAN_ENV), PAYLOAD_ARTIFACT)
    try:
        name = qualify(PAYLOAD_ARTIFACT, "foo")
        assert name == "foo"
        r = _probe(built, name)
        assert r.verdict == "PROBE_ONLY", r.detail
    finally:
        _remove_module(built)


# Final review C2 (Lean): def-wrapped vacuous statements, a def as the target, and statements with no antecedent.
C2_DEFS = """
def TpVac : Prop := ∀ n : ℕ, n < 0 → n = 7
theorem TpVac.foo : TpVac := fun n h => absurd h (Nat.not_lt_zero n)
theorem TpVac.triv : True := trivial
theorem TpVac.conj : 1 = 1 ∧ 2 = 2 := ⟨rfl, rfl⟩
theorem TpVac.pad (m : ℕ) (h : m = m) : TpVac := fun n hn => absurd hn (Nat.not_lt_zero n)
"""


@pytest.fixture(scope="module")
def c2_module():
    built = _build_module(Path(LEAN_ENV), C2_DEFS)
    yield built
    _remove_module(built)


@lean
def test_lean_c2_def_wrapped_vacuous_is_never_witnessed(c2_module):     # MUST-FAIL control
    r = _probe(c2_module, "TpVac.foo")
    assert r.verdict in ("VACUOUS", "PROBE_ONLY"), r.detail
    print(f"C2 def-wrapped, no witness: {r.verdict} -- {r.detail}")
    r = _probe(c2_module, "TpVac.foo", "trivial")
    assert r.verdict != "WITNESSED", r.detail
    print(f"C2 def-wrapped, witness trivial: {r.verdict} -- {r.detail}")


@lean
def test_lean_c2_target_must_be_a_theorem(c2_module):                   # MUST-FAIL control
    r = _probe(c2_module, "TpVac", "trivial")
    assert r.verdict == "ERROR" and "not a theorem" in r.detail, r.detail


@lean
@pytest.mark.parametrize("theorem", ["TpVac.triv", "TpVac.conj"])
def test_lean_c2_no_antecedent_is_never_witnessed(c2_module, theorem):   # MUST-FAIL control
    r = _probe(c2_module, theorem, "trivial")
    assert r.verdict == "PROBE_ONLY" and "nothing to witness" in r.detail, r.detail


# Final review M1 (Lean): a witness whose proof term the kernel rejects (assigned ill-typed by a tactic) is no
# WITNESSED: the auxiliary theorem is kernel-checked synchronously, before WITNESS PROVED could be printed.
@lean
def test_lean_m1_kernel_rejected_witness_is_error(cases_module):          # MUST-FAIL control
    w = "by run_tac do let g ← Lean.Elab.Tactic.getMainGoal; g.assign (Lean.mkNatLit 0)"
    r = _probe(cases_module, "Controls.tru", w)
    assert r.verdict == "ERROR", r.detail
    print(f"M1 kernel-rejected witness: {r.verdict} -- {r.detail}")


@lean
def test_lean_n3_padded_def_wrapped_vacuous_is_never_witnessed(c2_module):   # MUST-FAIL control (re-review N3)
    # without unfoldHeads the telescope would stop at `TpVac` after the satisfiable pad (m, h : m = m), and
    # ⟨0, rfl, trivial⟩ would witness it; unfolded, the witness must also cover `n < 0`, so it does not check
    r = _probe(c2_module, "TpVac.pad", "⟨0, rfl, trivial⟩")
    assert r.verdict != "WITNESSED", r.detail
    print(f"N3 padded def-wrapped: {r.verdict} -- {r.detail}")


# Step 6 Task 0 (C2 residual, Lean): a vacuous sub-proposition under a conclusion head the probe does not unfold. The
# satisfiable pad `m = m` closes the NON-reducing ∃-closure, so before the reducing check each of these was WITNESSED
# with `⟨0, rfl, trivial⟩` (the step-4 re-review's example is `idv`). Each theorem is true (the module compiles; `slowv`
# is sorry'd, see there).
C2R_DEFS = """
namespace TpRed
-- `slow n k` = sum of 2^n distinct leaves; written with `Nat.rec`, not a `match`, because the replay carries no matcher
-- or smart-unfolding data for replayed definitions, so whnf there could not evaluate a structural `match` at all
noncomputable def slow (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun k => k) (fun _ ih k => ih (2 * k) + ih (2 * k + 1)) n
theorem idv : ∀ m : ℕ, m = m → id (∀ n : ℕ, n < 0 → n = 7) :=
  fun _ _ n hn => absurd hn (Nat.not_lt_zero n)
theorem andv : ∀ m : ℕ, m = m → (∀ n : ℕ, n < 0 → n = 7) ∧ True :=
  fun _ _ => ⟨fun n hn => absurd hn (Nat.not_lt_zero n), trivial⟩
theorem iffv : ∀ m : ℕ, m = m → ((∀ n : ℕ, n < 0 → n = 7) ↔ True) :=
  fun _ _ => ⟨fun _ => trivial, fun _ n hn => absurd hn (Nat.not_lt_zero n)⟩
theorem notv : ∀ m : ℕ, m = m → ¬¬(∀ n : ℕ, n < 0 → n = 7) :=
  fun _ _ h => h fun n hn => absurd hn (Nat.not_lt_zero n)
theorem letv : ∀ m : ℕ, m = m → let k := 0; ∀ n : ℕ, n < k → n = 7 :=
  fun _ _ n hn => absurd hn (Nat.not_lt_zero n)
theorem betav : ∀ m : ℕ, m = m → (fun P : Prop => P) (∀ n : ℕ, n < 0 → n = 7) :=
  fun _ _ n hn => absurd hn (Nat.not_lt_zero n)
theorem honest (m : ℕ) (h : m < 3) : id (∀ n : ℕ, n < 5 → n < 6) := fun n hn => by omega
-- fix round 1 (Ruling 3): heads the descent does not open
theorem orv : ∀ m : ℕ, m = m → (∀ n : ℕ, n < 0 → n = 7) ∨ False :=
  fun _ _ => Or.inl fun n hn => absurd hn (Nat.not_lt_zero n)
theorem exv : ∀ m : ℕ, m = m → ∃ k : ℕ, ∀ n : ℕ, n < 0 → n = k :=
  fun _ _ => ⟨7, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
structure S : Prop where
  h : ∀ n : ℕ, n < 0 → n = 7
theorem structv : ∀ m : ℕ, m = m → S := fun _ _ => ⟨fun n hn => absurd hn (Nat.not_lt_zero n)⟩
theorem eqv : ∀ m : ℕ, m = m → ((∀ n : ℕ, n < 0 → n = 7) = True) :=
  fun _ _ => eq_true fun n hn => absurd hn (Nat.not_lt_zero n)
-- fix round 2 (Ruling 4): the task-0 review's repros (C1, C2, I1), each WITNESSED by a witness that also closes the
-- reduced closure before the allowlist
theorem pinv : ∀ m : ℕ, m = m → ∀ P : Prop, P = (∀ n : ℕ, n < 0 → n = 7) → P := by
  intro _ _ P h; subst h; exact fun n hn => absurd hn (Nat.not_lt_zero n)
theorem pinfv : ∀ F : ℕ → Prop, F = (fun k => ∀ n : ℕ, n < 0 → n = k) → F 7 := by
  intro F h; subst h; exact fun n hn => absurd hn (Nat.not_lt_zero n)
open Classical in
theorem decv : ∀ m : ℕ, m = m → decide (∀ n : ℕ, n < 0 → n = 7) = true :=
  fun _ _ => decide_eq_true fun n hn => absurd hn (Nat.not_lt_zero n)
open Classical in
theorem itecv : ∀ m : ℕ, m = m → (if (∀ n : ℕ, n < 0 → n = 7) then 0 else 1) = 0 :=
  fun _ _ => if_pos fun n hn => absurd hn (Nat.not_lt_zero n)
theorem plv : ∀ m : ℕ, m = m → Nonempty (PLift (∀ n : ℕ, n < 0 → n = 7)) :=
  fun _ _ => ⟨⟨fun n hn => absurd hn (Nat.not_lt_zero n)⟩⟩
theorem subtv : ∀ m : ℕ, m = m → Nonempty {_u : Unit // ∀ n : ℕ, n < 0 → n = 7} :=
  fun _ _ => ⟨⟨(), fun n hn => absurd hn (Nat.not_lt_zero n)⟩⟩
theorem subsv : ∀ m : ℕ, m = m → Subsingleton (Fin 0) := fun _ _ => ⟨fun a => a.elim0⟩
open Classical in
theorem itev : ∀ x : ℕ, x = (if (∀ n : ℕ, n < 0 → n = 7) then 0 else 1) → x = 0 := by
  intro x hx; rw [hx, if_pos fun n hn => absurd hn (Nat.not_lt_zero n)]
-- (`Nat.lt`, not `<`: under the binder `inst` is the local instance, and `<` would mean `inst` itself)
theorem instv : ∀ inst : LT ℕ, inst = ⟨fun a b => ∀ n : ℕ, Nat.lt n 0 → a = b⟩ → @LT.lt ℕ inst 1 2 := by
  intro inst h; rw [h]; exact fun n hn => absurd hn (Nat.not_lt_zero n)
noncomputable def hide (n : ℕ) : ℕ := by classical exact if (∀ k : ℕ, k < 0 → k = 7) then n else n + 1
theorem hidev : ∀ m : ℕ, m = m → hide m = m := fun m _ => by
  unfold hide; rw [if_pos fun n hn => absurd hn (Nat.not_lt_zero n)]
theorem realv (x : ℝ) (h : x < 3) : x < 5 := by linarith
-- fix round 3 (Ruling 5): R1, a vacuous proposition at a negative position of a hypothesis
theorem iffh : ∀ x : ℕ, (x = 0 ↔ ∀ n : ℕ, n < 0 → n = 7) → x = 0 :=
  fun _ h => h.2 fun n hn => absurd hn (Nat.not_lt_zero n)
theorem imph : ∀ x : ℕ, ((∀ n : ℕ, n < 0 → n = 7) → x = 0) → x = 0 :=
  fun _ h => h fun n hn => absurd hn (Nat.not_lt_zero n)
theorem iffb : ∀ b : Bool, (b = true ↔ ∀ n : ℕ, n < 0 → n = 7) → b = true :=
  fun _ h => h.2 fun n hn => absurd hn (Nat.not_lt_zero n)
theorem orh : ∀ x : ℕ, (x = 0 ∨ ¬∀ n : ℕ, n < 0 → n = 7) → x = 0 :=
  fun _ h => h.elim id fun hv => absurd (fun n hn => absurd hn (Nat.not_lt_zero n)) hv
theorem insth : ∀ inst : LT ℕ, (∀ a b : ℕ, @LT.lt ℕ inst a b ↔ ∀ n : ℕ, Nat.lt n 0 → a = b) → @LT.lt ℕ inst 1 2 :=
  fun _ h => (h 1 2).2 fun n hn => absurd hn (Nat.not_lt_zero n)
-- R2: a local structure as a binder type hides a hypothesis in its fields
structure SS where
  x : ℕ
  h : (∀ n : ℕ, n < 0 → n = 7) → x = 0
theorem strh : ∀ m : ℕ, m = m → ∀ s : SS, s.x = 0 := fun _ _ s => s.h fun n hn => absurd hn (Nat.not_lt_zero n)
-- R3: a structural `match` predicate under a library head (the walked and the witnessed term must be one)
def F : ℕ → Prop
  | 0 => ∀ n : ℕ, n < 0 → n = 7
  | k + 1 => F k
theorem fv : ∀ m : ℕ, m = m → id (F 3) := by
  intro _ _; show F 0; exact fun n hn => absurd hn (Nat.not_lt_zero n)
-- M6: a bare `True` conclusion says nothing
theorem truev : ∀ m : ℕ, m = m → True := fun _ _ => trivial
noncomputable def R (k : ℕ) : Prop := Nat.rec (motive := fun _ => Prop) True (fun _ _ => True) k
-- true, but the kernel would have to evaluate `slow 40 0` to check a proof, so it is sorry'd (the replay allows sorry;
-- no verdict reads the theorem's own proof). Binders before the `:` would make `sorry` itself whnf the target.
theorem slowv : ∀ m : ℕ, m = m → R (slow 40 0) := sorry
end TpRed
"""
PAD = "⟨0, rfl, trivial⟩"


@pytest.fixture(scope="module")
def c2r_module():
    built = _build_module(Path(LEAN_ENV), C2R_DEFS)
    yield built
    _remove_module(built)


@lean
@pytest.mark.parametrize("theorem", ["TpRed.idv", "TpRed.andv", "TpRed.iffv", "TpRed.notv", "TpRed.letv",
                                     "TpRed.betav"])
def test_lean_c2r_vacuity_under_a_closed_head_is_never_witnessed(c2r_module, theorem):   # MUST-FAIL control
    r = _probe(c2r_module, theorem, PAD)
    assert r.verdict == "PROBE_ONLY" and "witness does not survive reduction" in r.detail, r.detail
    print(f"C2R {theorem} with {PAD}: {r.verdict} -- {r.detail}")


@lean
def test_lean_c2r_honest_witness_survives_reduction(c2r_module):          # MUST-PASS control
    # the pad alone does not survive (`n < 5` is hidden under `id`); a witness that also covers it does
    r = _probe(c2r_module, "TpRed.honest", "⟨0, by norm_num, trivial⟩")
    assert r.verdict == "PROBE_ONLY" and "witness does not survive reduction" in r.detail, r.detail
    w = "by first | exact ⟨0, by norm_num, trivial⟩ | exact ⟨0, by norm_num, 0, by norm_num, trivial⟩"
    r = _probe(c2r_module, "TpRed.honest", w)
    assert r.verdict == "WITNESSED", r.detail


@lean
def test_lean_c2r_reduction_timeout_is_probe_only(c2r_module):            # MUST-FAIL control (fail closed)
    # `unfoldHeads` opens the local `R` (delta and beta only, cheap); whnf of the result then reduces the recursor's
    # major `slow 40 0` at default transparency (a matcher's major, as in `ite`, is reduced at `instances` only and
    # stays stuck): 2^40 distinct closed terms, so whnf's cache does not help. The reducing step runs out of its
    # heartbeat budget, and the witness that closed the non-reducing closure does not count
    r = _probe(c2r_module, "TpRed.slowv", PAD)
    assert r.verdict == "PROBE_ONLY" and "witness does not survive reduction" in r.detail, r.detail
    assert "the reducing check timed out at maxHeartbeats 200000" in r.detail, r.detail


@lean
@pytest.mark.parametrize("theorem", ["TpRed.orv", "TpRed.exv", "TpRed.structv", "TpRed.eqv"])
def test_lean_c2r_unopened_conclusion_is_never_witnessed(c2r_module, theorem):   # MUST-FAIL (Rulings 3, 4)
    # reduction stops at `∨`, `∃`, a local structure, and `=` between propositions; the pad closes the reduced closure
    # (nothing was opened), so before Ruling 3 each was WITNESSED; since Ruling 4 the allowlist refuses each
    r = _probe(c2r_module, theorem, PAD)
    assert r.verdict == "PROBE_ONLY" and "outside the WITNESSED allowlist" in r.detail, r.detail
    print(f"C2R-U {theorem} with {PAD}: {r.verdict} -- {r.detail}")


# Fix round 2 (Ruling 4): every task-0 review repro is outside the allowlist, so never WITNESSED (each was WITNESSED at
# 4c8e862 with this witness, except where the report says otherwise). `hidev` hides `V` in a LOCAL definition's body,
# which only the delta-expanded walk sees.
ALLOW_REPROS = [("TpRed.pinv", "⟨0, rfl, _, rfl, trivial⟩"), ("TpRed.pinfv", "⟨_, rfl, trivial⟩"),
                ("TpRed.decv", PAD), ("TpRed.itecv", PAD), ("TpRed.plv", PAD), ("TpRed.subtv", PAD),
                ("TpRed.subsv", PAD), ("TpRed.itev", "⟨_, rfl, trivial⟩"), ("TpRed.instv", "⟨_, rfl, trivial⟩"),
                ("TpRed.hidev", PAD)]


@lean
@pytest.mark.parametrize("theorem,witness", ALLOW_REPROS)
def test_lean_c2r_allowlist_repros_are_never_witnessed(c2r_module, theorem, witness):   # MUST-FAIL (Ruling 4)
    r = _probe(c2r_module, theorem, witness)
    assert r.verdict == "PROBE_ONLY" and "outside the WITNESSED allowlist" in r.detail, r.detail
    print(f"ALLOW {theorem} with {witness}: {r.verdict} -- {r.detail}")


# Fix round 3 (Ruling 5): the R1, R2, R3 and M6 repros, each WITNESSED (or not, see the report) at 3b25ae0.
ATOMIC_REPROS = [("TpRed.iffh", "⟨0, ⟨fun _ n hn => absurd hn (Nat.not_lt_zero n), fun _ => rfl⟩, trivial⟩"),
                 ("TpRed.imph", "⟨0, fun _ => rfl, trivial⟩"),
                 ("TpRed.iffb", "⟨true, ⟨fun _ n hn => absurd hn (Nat.not_lt_zero n), fun _ => rfl⟩, trivial⟩"),
                 ("TpRed.orh", "⟨0, Or.inl rfl, trivial⟩"),
                 ("TpRed.insth", "⟨⟨fun a b => ∀ n : ℕ, Nat.lt n 0 → a = b⟩, fun _ _ => Iff.rfl, trivial⟩"),
                 ("TpRed.strh", "⟨0, rfl, ⟨0, fun _ => rfl⟩, trivial⟩"), ("TpRed.fv", PAD), ("TpRed.truev", PAD)]


@lean
@pytest.mark.parametrize("theorem,witness", ATOMIC_REPROS)
def test_lean_c2r_atomic_repros_are_never_witnessed(c2r_module, theorem, witness):   # MUST-FAIL (Ruling 5)
    r = _probe(c2r_module, theorem, witness)
    assert r.verdict == "PROBE_ONLY", r.detail
    if theorem == "TpRed.fv":      # R3: refused either way, by the reduced witness or by the walk of the same term
        assert "outside the WITNESSED allowlist" in r.detail or "witness does not survive reduction" in r.detail
    else:
        assert "outside the WITNESSED allowlist" in r.detail, r.detail
    print(f"ATOMIC {theorem} with {witness}: {r.verdict} -- {r.detail}")


@lean
def test_lean_c2r_allowlist_keeps_real_inequalities(c2r_module):               # MUST-PASS (Ruling 4)
    r = _probe(c2r_module, "TpRed.realv", "⟨0, by norm_num, trivial⟩")
    assert r.verdict == "WITNESSED", r.detail

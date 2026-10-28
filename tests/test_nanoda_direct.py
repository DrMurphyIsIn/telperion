"""The "nanoda-direct" second-kernel route (step 0b Task 3, 2026-10-28).

Seven proved nodes have never had a second-kernel judge because no Comparator bundle can
consume them. This route replays lean4export + nanoda directly on the node's OWN registered
theorem -- no Comparator statement-identity step -- so every record it writes carries
`route = "nanoda-direct"` and is reported differently.

Every test here either calls pure functions (`classify`, `export_cmd`, `nanoda_config`,
`verdict_of_log`) or calls `run_direct` with an INJECTED `run`: no lake, no lean4export, no
nanoda_bin is ever invoked. `test_export_target_is_node_theorem` reads real files from the
repo's own `AND_g2_reflected_band` node (its artifact and statement text) to prove the
theorem-name derivation is the real grant-gate mechanism, not a guess -- but still never runs
a tool: `run` is the same kind of stub as everywhere else in this file.
"""
from __future__ import annotations

import dataclasses
import hashlib
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions import nanoda_direct  # noqa: E402
from telperion.missions.nanoda_direct import NanodaDirectError, Tools, run_direct  # noqa: E402
from telperion.missions.provenance import (  # noqa: E402
    closure_digest, closure_files, lake_workspace, render_provenance_report, rejudge_problem,
    sha256_file,
)
from telperion.missions.registry import Campaign  # noqa: E402
from telperion.missions.rejudge import (  # noqa: E402
    parse_rejudge_header, parse_rejudge_route, rejudge_log_verdict,
)
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, Proof, RejudgeRecord, save_manifest, save_node,
)
from telperion.missions.statements import write_statement  # noqa: E402

TELPERION_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# classify: the verdict over raw export/nanoda output, never from a flag
# ---------------------------------------------------------------------------

def test_pass_classification():
    assert nanoda_direct.classify(
        0, "<ndjson export bytes>\n", 0, "Checked 7 declarations with no errors\n") == "pass"


def test_empty_export_fails():
    # export produced nothing, even though it exited 0
    assert nanoda_direct.classify(0, "", 0, "Checked 7 declarations with no errors\n") == "fail"
    # export itself failed
    assert nanoda_direct.classify(1, "", 1, "") == "fail"
    # Review Focus 3 / controller note: nanoda checking ZERO declarations is FAIL even with
    # exit 0, a clean export, and the real success-message SHAPE (main.rs:34 with n=0) --
    # "no errors" is not the same claim as "something was checked and accepted".
    assert nanoda_direct.classify(0, "x\n", 0, "Checked 0 declarations with no errors\n") == "fail"


def test_nanoda_error_fails():
    # parser.rs:837's exact wording, as main.rs's Debug impl prints it (confirmed against the
    # step 0 negative-control log, which named "propext"; a sorry-bodied theorem names
    # "sorryAx" -- both must fail here, by exit code AND by the Error: line).
    assert nanoda_direct.classify(
        0, "x\n", 1,
        'Error: export file declares unpermitted axiom "propext"\n\n'
        'run with `-h` or `--help` for help\n') == "fail"
    assert nanoda_direct.classify(
        0, "x\n", 1, 'Error: export file declares unpermitted axiom "sorryAx"\n') == "fail"
    # an Error: line with exit 0 (should never happen, but the check must not trust exit alone)
    assert nanoda_direct.classify(
        0, "x\n", 0,
        'Checked 7 declarations with no errors\nError: something else\n') == "fail"


def test_export_cmd_and_nanoda_config_shape():
    cmd = nanoda_direct.export_cmd(Path("/isl/lean"), "Foo.Bar", "Foo.Bar.thm",
                                   Path("/tools/lean4export"))
    assert cmd == ["lake", "env", "/tools/lean4export", "Foo.Bar", "--", "Foo.Bar.thm"]
    cfg = nanoda_direct.nanoda_config(Path("/tmp/x/export.txt"))
    assert cfg["export_file_path"] == "/tmp/x/export.txt"
    assert set(cfg["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}
    assert cfg["unpermitted_axiom_hard_error"] is True
    assert cfg["nat_extension"] is True and cfg["string_extension"] is True
    assert cfg["print_success_message"] is True   # nanoda's own default is False
    assert cfg["print_axioms"] is False   # nanoda's own default is True (util.rs:938)


def test_nanoda_config_disables_print_axioms():
    """nanoda's `print_axioms` defaults to true (util.rs:938); with no pretty-print
    destination configured, nanoda appends "Unable to print axioms" (pretty_printer.rs:384)
    to an otherwise-clean run, AFTER check_all_declars already accepted the proof
    (main.rs:27-30) -- output-only, but not the `_SUCCESS_RE` shape `classify` accepts.
    Controller ruling 0b-6: fix the CONFIG, not the parser."""
    cfg = nanoda_direct.nanoda_config(Path("/tmp/x/export.txt"))
    assert cfg == {
        "export_file_path": "/tmp/x/export.txt",
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
        "print_axioms": False,
    }


def test_pretty_printer_error_variant_still_fails():
    """The real nanoda-direct re-judge output that caused the FAIL this task fixes: nanoda
    accepted the proof (exit 0) but still printed the pretty-printer error because
    `print_axioms` was left at its (true) default. Controller ruling 0b-6: the config is the
    fix, and the classifier must NOT be widened to accept this variant line -- this exact
    line, with exit 0, must still read "fail"."""
    assert nanoda_direct.classify(
        0, "<ndjson export bytes>\n", 0,
        'Checked 28216 declarations with no typechecker errors, 1 pretty printer errors: '
        '["Unable to print axioms"]\n') == "fail"


# ---------------------------------------------------------------------------
# run_direct: a synthetic island (no real lake/lean/nanoda; `run` is a stub)
# ---------------------------------------------------------------------------

def _tmp_island_node(tmp_path: Path, *, thm_short: str = "a_thm",
                     stmt_short: str = None, slug: str = "HV_x") -> tuple[Path, Path, Node]:
    """A real judge island (`<tel>/examples/isl/lean/A.lean`, one lean_lib) plus a campaign
    whose node's artifact lives on it, and a real statement file written by `write_statement`
    (the grant gate's own renderer -- same mechanism `resolve_theorem` is tested against
    elsewhere in this suite). `stmt_short` defaults to `thm_short` (a matching pair); pass a
    different name to model statement/artifact drift (Review Focus 2's "typo").
    """
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "Isl"\n\n[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text(f"theorem {thm_short} : True := trivial\n")
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name=slug.replace("_", ".", 1), title="t", kind="lemma", status="proved",
        depends_on=(), statement_module=f"Statements.{slug}",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True, created="2026-10-28", updated="2026-10-28",
    )
    manifest = MissionManifest(
        name="Demo.hv", title="Demo", description="synthetic", goal_node=slug,
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    write_statement(camp, node, f"import Mathlib\ntheorem {stmt_short or thm_short} : True",
                    manifest)
    return tel, camp, node


def _stub_run(export_out="<export bytes>\n", nanoda_out="Checked 3 declarations with no errors\n",
              export_rc=0, nanoda_rc=0, export_err="", nanoda_err=""):
    """Review fix round 1 (2026-10-28), item 5: `run` returns (rc, stdout, stderr) -- stdout
    and stderr separately, so `run_direct` can write stdout-only to `export.txt` while still
    logging stderr (where a real Lean PANIC under LEAN_ABORT_ON_PANIC=1 would land)."""
    calls = []

    def run(cmd, *, cwd):
        calls.append((list(cmd), Path(cwd)))
        if cmd[0] == "lake":
            return export_rc, export_out, export_err
        return nanoda_rc, nanoda_out, nanoda_err
    return run, calls


def test_log_has_route_and_header(tmp_path):
    tel, camp, node = _tmp_island_node(tmp_path)
    artifact = camp / node.proof.artifact
    run, calls = _stub_run()
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run)
    text = log_path.read_text()

    sha = sha256_file(artifact)
    csha = closure_digest(camp, node)
    assert f"REJUDGE-HEADER node=HV_x artifact_sha256={sha} closure_sha256={csha}" in text
    assert "REJUDGE-ROUTE nanoda-direct" in text
    assert parse_rejudge_header(text) == ("HV_x", sha)
    assert parse_rejudge_route(text) == "nanoda-direct"
    assert "REJUDGE-EXPORT exit=0" in text and "REJUDGE-NANODA exit=0" in text
    assert rejudge_log_verdict(text, []) == "pass"
    # the export ran with cwd = the island's lean dir, and nanoda last (over its own config)
    assert calls[0][1].resolve() == (tel / "examples" / "isl" / "lean").resolve()
    assert calls[1][0][0] == "/tools/nanoda_bin"


def test_export_target_is_node_theorem():
    """Real repo files (AND_g2_reflected_band's artifact + statement): the export command's
    LAST argument is the node's own registered theorem, resolved the grant gate's way
    (`guard_anchors.resolve_theorem`) -- never a hand-typed `MissionJudge.<slug>` guess. No
    tool is invoked: `run` is a stub that never shells out."""
    from telperion.missions.schema import load_node
    camp = TELPERION_ROOT / "missions" / "anduril"
    node = load_node(camp / "nodes" / "AND_g2_reflected_band.toml")
    run, calls = _stub_run()
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        tools = Tools(telperion_root=TELPERION_ROOT, lean4export=Path("/tools/lean4export"),
                      nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=Path(td))
        log_path = run_direct(camp, node, tools=tools, run=run)
        text = log_path.read_text()
    export_cmd_used = calls[0][0]
    assert export_cmd_used == ["lake", "env", "/tools/lean4export", "ReflectedBand_t14",
                               "--", "ReflectedBand_t14.pilot"]
    assert "theorem=ReflectedBand_t14.pilot" in text
    assert "module=ReflectedBand_t14" in text
    assert "island=zeta_reflection" in text


def test_export_target_typo_fails_setup_rather_than_exporting_wrong_constant(tmp_path):
    """Review Focus 2: when the statement no longer names a theorem the artifact declares
    (drift -- the "typo" case), `run_direct` refuses outright (no log, no export command
    issued) rather than falling back to some other constant."""
    tel, camp, node = _tmp_island_node(tmp_path, thm_short="a_thm", stmt_short="not_a_thm")
    run, calls = _stub_run()
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    with pytest.raises(NanodaDirectError):
        run_direct(camp, node, tools=tools, run=run)
    assert calls == []        # no export command was ever issued


def test_run_direct_bad_nanoda_output_records_fail(tmp_path):
    tel, camp, node = _tmp_island_node(tmp_path)
    run, _ = _stub_run(nanoda_out='Error: export file declares unpermitted axiom "sorryAx"\n',
                      nanoda_rc=1)
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run)
    assert rejudge_log_verdict(log_path.read_text(), []) == "fail"


def test_run_direct_zero_declarations_records_fail(tmp_path):
    tel, camp, node = _tmp_island_node(tmp_path)
    run, _ = _stub_run(nanoda_out="Checked 0 declarations with no errors\n")
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run)
    assert rejudge_log_verdict(log_path.read_text(), []) == "fail"


# ---------------------------------------------------------------------------
# run_direct pre/post hashing (Review fix round 2, gap 2): the header binds to the digests
# taken BEFORE the build (the queue script hashes right before `timed_build`); the run is
# re-hashed afterward, and a mismatch fails the node -- a source edited mid-run must never
# produce a silent pass bound to a digest that no longer describes what was actually built.
# ---------------------------------------------------------------------------

def test_run_direct_pre_hash_matches_post_hash_passes(tmp_path):
    tel, camp, node = _tmp_island_node(tmp_path)
    artifact = camp / node.proof.artifact
    pre_sha = sha256_file(artifact)
    pre_closure = closure_digest(camp, node)
    run, _ = _stub_run()
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run,
                          pre_artifact_sha256=pre_sha, pre_closure_sha256=pre_closure)
    text = log_path.read_text()
    assert f"artifact_sha256={pre_sha}" in text
    assert "sources changed" not in text
    assert rejudge_log_verdict(text, []) == "pass"


def test_run_direct_source_changed_during_run_fails(tmp_path):
    """The artifact is edited (here, as a side effect of the injected export call) AFTER the
    pre-build hash was taken but DURING the run -- the post-run re-hash must catch it and
    fail the node, even though export/nanoda both otherwise look like a clean pass."""
    tel, camp, node = _tmp_island_node(tmp_path)
    artifact = camp / node.proof.artifact
    pre_sha = sha256_file(artifact)
    pre_closure = closure_digest(camp, node)

    def run(cmd, *, cwd):
        if cmd[0] == "lake":
            artifact.write_text("theorem a_thm : True := trivial  -- edited mid-run\n")
            return 0, "<export bytes>\n", ""
        return 0, "Checked 3 declarations with no errors\n", ""

    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run,
                          pre_artifact_sha256=pre_sha, pre_closure_sha256=pre_closure)
    text = log_path.read_text()
    assert f"artifact_sha256={pre_sha}" in text   # header still binds to the PRE value
    assert "sources changed during the run" in text
    assert rejudge_log_verdict(text, []) == "fail"


def test_run_direct_closure_changed_during_run_fails(tmp_path):
    """Same idea, but the import CLOSURE changes (a sibling the artifact imports is edited),
    not the artifact file itself."""
    tel, camp, node = _tmp_island_node(tmp_path)
    (tel / "examples" / "isl" / "lean" / "B.lean").write_text("-- nothing imports this yet\n")
    artifact = camp / node.proof.artifact
    pre_sha = sha256_file(artifact)
    pre_closure = closure_digest(camp, node)

    def run(cmd, *, cwd):
        if cmd[0] == "lake":
            artifact.write_text("import B\ntheorem a_thm : True := trivial\n")
            return 0, "<export bytes>\n", ""
        return 0, "Checked 3 declarations with no errors\n", ""

    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run,
                          pre_artifact_sha256=pre_sha, pre_closure_sha256=pre_closure)
    text = log_path.read_text()
    assert "sources changed during the run" in text
    assert rejudge_log_verdict(text, []) == "fail"


def test_run_direct_no_pre_hash_falls_back_to_call_time_hash(tmp_path):
    """Omitting pre_artifact_sha256/pre_closure_sha256 (every caller before this fix round)
    keeps the previous behaviour exactly: hash once, at call time, bind the header to that."""
    tel, camp, node = _tmp_island_node(tmp_path)
    artifact = camp / node.proof.artifact
    run, _ = _stub_run()
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    log_path = run_direct(camp, node, tools=tools, run=run)
    text = log_path.read_text()
    assert f"artifact_sha256={sha256_file(artifact)}" in text
    assert rejudge_log_verdict(text, []) == "pass"


# ---------------------------------------------------------------------------
# rejudge_log_verdict / parse_rejudge_route: the branch over REJUDGE-ROUTE
# ---------------------------------------------------------------------------

def test_comparator_log_without_route_line_defaults_and_is_unaffected():
    """A pre-Task-3 Comparator log (no REJUDGE-ROUTE line at all) still reads "comparator",
    and its per-part verdict rule is completely untouched by this task."""
    log = ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
          "==================== REJUDGE-PART 1/1 X (comparator exit 0, peak 1 kB) "
          "====================\n"
          "Lean default kernel accepts the solution\nNanoda kernel accepts the solution\n"
          "Your solution is okay!\n")
    assert parse_rejudge_route(log) == "comparator"
    assert rejudge_log_verdict(log, ["X"]) == "pass"


def test_nanoda_direct_route_ignores_part_slugs():
    log = ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
          "REJUDGE-ROUTE nanoda-direct\n"
          "==================== REJUDGE-EXPORT exit=0 ====================\n"
          "bytes\n"
          "==================== REJUDGE-NANODA exit=0 ====================\n"
          "Checked 1 declarations with no errors\n")
    # part_slugs is nonsense on purpose: a nanoda-direct log never renders a Comparator
    # bundle, so there is no part count to check it against.
    assert rejudge_log_verdict(log, ["this-is-not-a-real-part", "neither-is-this"]) == "pass"


def test_malformed_nanoda_direct_log_fails():
    assert rejudge_log_verdict("REJUDGE-ROUTE nanoda-direct\nnoise only\n", []) == "fail"


def test_route_must_be_in_valid_set():
    """Review fix round 1 (2026-10-28), item 4: a third route value must fail outright, not
    fall through to the Comparator per-part rule just because it is not literally
    "nanoda-direct"."""
    log = ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
          "REJUDGE-ROUTE something-else\n")
    assert rejudge_log_verdict(log, ["X"]) == "fail"
    assert rejudge_log_verdict(log, []) == "fail"


# ---------------------------------------------------------------------------
# verdict_of_log / _parse_sections hardening (Review fix round 1, item 4): exactly one
# REJUDGE-HEADER on line 1, exactly one REJUDGE-ROUTE on line 2, exactly one EXPORT section
# followed by exactly one NANODA section in that order, "Checked N" exactly once with N >= 1.
# ---------------------------------------------------------------------------

def _good_log(export_body="bytes\n", nanoda_body="Checked 3 declarations with no errors\n",
             export_rc=0, nanoda_rc=0) -> str:
    return ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
           "REJUDGE-ROUTE nanoda-direct\n"
           f"==================== REJUDGE-EXPORT exit={export_rc} ====================\n"
           f"{export_body}"
           f"==================== REJUDGE-NANODA exit={nanoda_rc} ====================\n"
           f"{nanoda_body}")


def test_verdict_of_log_well_formed_passes():
    assert nanoda_direct.verdict_of_log(_good_log()) == "pass"


def test_verdict_of_log_no_header_fails():
    no_header = _good_log().split("\n", 1)[1]   # drop line 1 entirely
    assert nanoda_direct.verdict_of_log(no_header) == "fail"
    assert nanoda_direct.verdict_of_log("") == "fail"
    assert nanoda_direct.verdict_of_log("just one line, no newline") == "fail"


def test_verdict_of_log_two_concatenated_logs_fails():
    """Two complete, individually-valid logs pasted one after another is NOT a valid single
    log: there is a second REJUDGE-HEADER/REJUDGE-ROUTE pair sitting where NANODA's body
    should be taken as ending, and a third+fourth section delimiter follow."""
    two = _good_log() + _good_log()
    assert nanoda_direct.verdict_of_log(two) == "fail"


def test_verdict_of_log_second_export_section_fails():
    """A second EXPORT section instead of NANODA right after the first -- not "EXPORT then
    NANODA in that order"."""
    log = ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
          "REJUDGE-ROUTE nanoda-direct\n"
          "==================== REJUDGE-EXPORT exit=0 ====================\n"
          "bytes\n"
          "==================== REJUDGE-EXPORT exit=0 ====================\n"
          "bytes again\n"
          "==================== REJUDGE-NANODA exit=0 ====================\n"
          "Checked 3 declarations with no errors\n")
    assert nanoda_direct.verdict_of_log(log) == "fail"


def test_verdict_of_log_duplicate_nanoda_section_fails():
    log = _good_log() + "==================== REJUDGE-NANODA exit=0 ====================\n" \
        "Checked 9 declarations with no errors\n"
    assert nanoda_direct.verdict_of_log(log) == "fail"


def test_classify_checked_five_then_checked_zero_fails():
    """Two contradictory success lines in the nanoda output: ambiguous, never a pass."""
    assert nanoda_direct.classify(
        0, "bytes\n", 0,
        "Checked 5 declarations with no errors\nChecked 0 declarations with no errors\n"
    ) == "fail"
    log = _good_log(nanoda_body="Checked 5 declarations with no errors\n"
                    "Checked 0 declarations with no errors\n")
    assert nanoda_direct.verdict_of_log(log) == "fail"


def test_verdict_of_log_route_line_inside_tool_output_does_not_confuse_the_parser():
    """A decoy `REJUDGE-ROUTE nanoda-direct` line buried inside the nanoda body must not make
    an otherwise-malformed log (here: line 2 is NOT a route line at all -- it is garbage)
    read as valid."""
    log = ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
          "not actually a route line\n"
          "==================== REJUDGE-EXPORT exit=0 ====================\n"
          "bytes\n"
          "==================== REJUDGE-NANODA exit=0 ====================\n"
          "REJUDGE-ROUTE nanoda-direct\n"
          "Checked 3 declarations with no errors\n")
    assert nanoda_direct.verdict_of_log(log) == "fail"
    assert rejudge_log_verdict(log, []) == "fail"


def test_classify_panic_in_export_fails():
    """Review fix round 1 (2026-10-28), item 5: LEAN_ABORT_ON_PANIC=1 turns a Lean panic
    during the export into a hard abort; a PANIC line anywhere in the export output fails,
    independent of the exit code."""
    assert nanoda_direct.classify(
        0, "PANIC at foo@Export.lean:12:3: Constant not found\n", 0,
        "Checked 3 declarations with no errors\n") == "fail"
    assert nanoda_direct.classify(
        1, "some bytes\nPANIC at foo@Export.lean:12:3: Constant not found\n", 1, "") == "fail"


# ---------------------------------------------------------------------------
# rejudge_problem / second_kernel_claimed: a passing nanoda-direct record satisfies the
# second-kernel requirement for a NON-heavy node (every one of the 7 real nodes' shape --
# heavy_certificates unset, no [comparator] record at all). Review fix round 1 (2026-10-28),
# item 2.
# ---------------------------------------------------------------------------

def test_rejudge_problem_accepts_direct_pass(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    assert node.comparator is None
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)), route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    assert rejudge_problem(tmp_path, node) == ""


def test_rejudge_problem_still_flags_a_failing_direct_record(tmp_path):
    """Before this fix, `rejudge_problem`'s `not needs_rejudge(node)` early return made a FAIL
    record on a non-heavy, no-[comparator] node (every one of the 7) invisible."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="fail",
                        log_sha256="c" * 64, route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    assert "FAILED" in rejudge_problem(tmp_path, node)


def test_rejudge_problem_flags_a_stale_sha_direct_record(tmp_path):
    """A record bound to an artifact digest the current artifact no longer matches was ALSO
    invisible before this fix, on a non-heavy node."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256="0" * 64, verdict="pass",
                        log_sha256="c" * 64, route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    problem = rejudge_problem(tmp_path, node)
    assert problem != "" and "artifact" in problem


def test_rejudge_problem_crashes_fixed_why_text_on_non_heavy_no_comparator(tmp_path):
    """Regression for the crash the review found: computing `why` used to dereference
    `node.comparator.second_kernel` unconditionally whenever `heavy_certificates` was False --
    AttributeError on a node whose `comparator` is None. A FAILing record exercises that path."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    assert node.comparator is None
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256="0" * 64, verdict="fail",
                        log_sha256="c" * 64, route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    rejudge_problem(tmp_path, node)   # must not raise


def test_second_kernel_claimed_false_with_no_record_and_not_heavy(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    from telperion.missions.provenance import second_kernel_claimed
    assert second_kernel_claimed(node) is False
    assert rejudge_problem(tmp_path, node) == ""


# ---------------------------------------------------------------------------
# Controller ruling 0b-4 (2026-10-28, review fix round 1 item 2): a node that `needs_rejudge`
# (heavy_certificates, or a Lean-kernel-only [comparator] record) is NOT satisfied by a
# nanoda-direct record, however cleanly it passes -- that route has no statement-identity
# step, so it cannot discharge the stronger Comparator requirement.
# ---------------------------------------------------------------------------

def test_ruling_0b4_heavy_node_rejects_nanoda_direct_even_passing(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)), route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    problem = rejudge_problem(tmp_path, node)
    assert problem == "heavy node requires a Comparator re-judge; nanoda-direct is not sufficient"


def test_ruling_0b4_heavy_node_with_comparator_route_is_fine(tmp_path):
    """Regression: a heavy node's ORDINARY (route="comparator") passing re-judge is
    completely unaffected by the ruling."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)))
    assert rec.route == "comparator"
    node = dataclasses.replace(node, rejudge=rec)
    assert rejudge_problem(tmp_path, node) == ""


def test_ruling_0b5_unrecognized_route_rejected(tmp_path):
    """Controller ruling 0b-5 (2026-10-28, review fix round 2): a record whose `route` is
    not in `rejudge.VALID_ROUTES` is rejected outright, on a heavy node (needs_rejudge) and
    on a non-heavy one (second_kernel_claimed only) alike."""
    from telperion.missions.rejudge import VALID_ROUTES
    from missions_fixtures import minimal_proved_node

    for heavy in (True, False):
        node = minimal_proved_node(tmp_path, heavy=heavy)
        sha = sha256_file(tmp_path / node.proof.artifact)
        rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                            comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                            log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                            closure_files=len(closure_files(tmp_path, node)),
                            route="some-other-route")
        assert rec.route not in VALID_ROUTES
        node = dataclasses.replace(node, rejudge=rec)
        problem = rejudge_problem(tmp_path, node)
        assert problem != "" and "not a recognized route" in problem, (heavy, problem)


# ---------------------------------------------------------------------------
# provenance report: the route label (Review Focus 5)
# ---------------------------------------------------------------------------

def test_report_labels_route(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)), route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    manifest = MissionManifest(
        name="Demo.goal", title="t", description="d", goal_node="n",
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    campaign = Campaign(root=tmp_path, manifest=manifest, nodes={"n": node})
    out = render_provenance_report(campaign)
    assert "nanoda-direct" in out
    assert "no Comparator statement check" in out
    # must NOT read like the stronger, Comparator-checked line (Review Focus 5)
    assert "Lean kernel + nanoda (local re-judge" not in out


def test_report_comparator_route_wording_unchanged(tmp_path):
    """Regression: an ordinary (route="comparator", the default) passing re-judge keeps its
    existing wording -- this task must not touch that line."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)))
    assert rec.route == "comparator"
    node = dataclasses.replace(node, rejudge=rec)
    manifest = MissionManifest(
        name="Demo.goal", title="t", description="d", goal_node="n",
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    campaign = Campaign(root=tmp_path, manifest=manifest, nodes={"n": node})
    out = render_provenance_report(campaign)
    assert "Lean kernel + nanoda (local re-judge" in out
    assert "nanoda-direct" not in out


# ---------------------------------------------------------------------------
# CLI: `mission rejudge-record` accepts a nanoda-direct log for ANY proved node
# ---------------------------------------------------------------------------

def _cli(mroot: Path, *args: str) -> int:
    return main(["mission", "--missions-root", str(mroot), *args])


def _campaign(tmp_path: Path, *, heavy: bool = False, judge_via: str = "") -> Path:
    """A campaign whose node's artifact lives on a real (synthetic) judge island, with a
    statement file written by the grant gate's own renderer -- Controller Ruling 0b-9's
    record-time binding resolves the theorem (`guard_anchors.resolve_theorem`) and module
    (`judge.module_name_of`) from exactly these files."""
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "Isl"\n\n[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text("theorem demo_hv : True := trivial\n")
    mroot = tel / "missions"
    croot = mroot / "demo"
    (croot / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.hv", title="Demo Campaign", description="synthetic",
        goal_node="Demo_hv", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, croot / "mission.toml")
    node = Node(
        name="Demo.hv", title="node", kind="lemma", status="proved", depends_on=(),
        statement_module="Statements.Demo_hv",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=heavy, judge_via=judge_via,
        created="2026-10-28", updated="2026-10-28",
    )
    save_node(node, croot / "nodes" / "Demo_hv.toml")
    write_statement(croot, node, "import Mathlib\ntheorem demo_hv : True", manifest)
    return mroot


def _art(mroot: Path) -> Path:
    return mroot.parent / "examples" / "isl" / "lean" / "A.lean"


#: A minimal lean4export 3.1.0-shaped export that declares theorem `demo_hv`: the name
#: interned as `{"in":N,"str":{"pre":P,"str":S}}`, then a `thm` line naming it.
_EXPORT_DEMO = ('{"in":1,"str":{"pre":0,"str":"demo_hv"}}\n'
                '{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":0}}\n')


def _direct_log(mroot: Path, *, nanoda_out: str = "Checked 4 declarations with no errors\n",
               export_rc: int = 0, nanoda_rc: int = 0, theorem: str = "demo_hv",
               module: str = "A", info: bool = True, export_body: str = _EXPORT_DEMO) -> str:
    art = _art(mroot)
    sha = hashlib.sha256(art.read_bytes()).hexdigest()
    from telperion.missions.schema import load_node
    csha = closure_digest(mroot / "demo", load_node(mroot / "demo" / "nodes" / "Demo_hv.toml"))
    info_line = (f"REJUDGE-INFO artifact={art.resolve()} theorem={theorem} module={module} "
                 "island=isl\n") if info else ""
    return (f"REJUDGE-HEADER node=Demo_hv artifact_sha256={sha} closure_sha256={csha}\n"
           "REJUDGE-ROUTE nanoda-direct\n"
           + info_line +
           f"==================== REJUDGE-EXPORT exit={export_rc} ====================\n"
           + export_body +
           f"==================== REJUDGE-NANODA exit={nanoda_rc} ====================\n"
           f"{nanoda_out}")


def test_cli_accepts_nanoda_direct_for_non_heavy_node(tmp_path):
    """The core CLI change: a non-heavy node with no [comparator] record at all -- exactly the
    7 nodes' shape -- is refused on the Comparator route (see
    test_cli_non_heavy_node_exit2_no_record in test_missions_rejudge.py) but ACCEPTED on
    nanoda-direct."""
    mroot = _campaign(tmp_path, heavy=False)
    log = tmp_path / "direct.log"
    log.write_text(_direct_log(mroot))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    from telperion.missions.schema import load_node
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None
    assert node.rejudge.verdict == "pass"
    assert node.rejudge.route == "nanoda-direct"


def test_cli_nanoda_direct_fail_records_fail(tmp_path, capsys):
    mroot = _campaign(tmp_path, heavy=False)
    log = tmp_path / "direct.log"
    log.write_text(_direct_log(
        mroot, nanoda_out='Error: export file declares unpermitted axiom "sorryAx"\n',
        nanoda_rc=1))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 1
    err = capsys.readouterr().err
    assert "REJUDGE FAIL" in err and "REPORT TO OWNER" in err
    from telperion.missions.schema import load_node
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge.verdict == "fail"
    assert node.rejudge.route == "nanoda-direct"


def test_cli_nanoda_direct_stale_artifact_refused(tmp_path, capsys):
    """The route changes nothing about the artifact-digest binding: a stale header is still
    refused, exit 2, no record."""
    mroot = _campaign(tmp_path, heavy=False)
    log = tmp_path / "direct.log"
    text = _direct_log(mroot).replace(
        hashlib.sha256(_art(mroot).read_bytes()).hexdigest(), "0" * 64, 1)
    log.write_text(text)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    assert "CURRENT artifact" in capsys.readouterr().err
    from telperion.missions.schema import load_node
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


# ---------------------------------------------------------------------------
# lake_workspace (Controller Ruling 0b-7): the smallest lakefile directory -- island
# lean dir or one of its immediate subdirectories -- that declares a `lean_lib`
# covering the artifact's own module, e.g. zzl_aux (23 libs) under
# zeta_zero_localization's monolith lakefile.toml (27,090 libs, which cannot even spawn
# `lake env`). Every test here parses only synthetic lakefile.toml/lake-manifest.json
# text on disk -- no lake, lean or nanoda is ever invoked.
# ---------------------------------------------------------------------------

def _lib_block(names):
    return "".join(f'[[lean_lib]]\nname = "{n}"\n' for n in names)


def _manifest_json(pkgs):
    import json
    return json.dumps({"version": 7, "packages": list(pkgs)})


def _tmp_two_level_island(tmp_path, *, island="isl_ws", root_libs, sub_libs=None,
                          sub_name="sub_aux", root_pkgs=(), sub_pkgs=()):
    """A synthetic island at `<tel>/examples/<island>/lean`: the ROOT lakefile declares
    *root_libs* (which must include "Target" for the fallback-to-root tests to have
    anything to declare); an optional immediate subdirectory *sub_name* (`srcDir =
    ".."`, the zzl_aux shape) declares *sub_libs*. Each may carry its own
    lake-manifest.json. Returns (campaign_root, node, root_dir, sub_dir_or_None)."""
    tel = tmp_path / "telperion"
    lean = tel / "examples" / island / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text(f'name = "{island}"\n\n' + _lib_block(root_libs))
    (lean / "Target.lean").write_text("theorem target_thm : True := trivial\n")
    if root_pkgs:
        (lean / "lake-manifest.json").write_text(_manifest_json(root_pkgs))
    sub_dir = None
    if sub_libs is not None:
        sub_dir = lean / sub_name
        sub_dir.mkdir()
        (sub_dir / "lakefile.toml").write_text(
            f'name = "{sub_name}"\nsrcDir = ".."\n\n' + _lib_block(sub_libs))
        if sub_pkgs:
            (sub_dir / "lake-manifest.json").write_text(_manifest_json(sub_pkgs))
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="Statements.HV_x",
        proof=Proof(f"../../examples/{island}/lean/Target.lean", "lean_module", "direct"),
        created="2026-10-28", updated="2026-10-28",
    )
    return camp, node, lean.resolve(), (sub_dir.resolve() if sub_dir is not None else None)


def test_lake_workspace_picks_smaller_subdir_declaring_module(tmp_path):
    """The zzl_aux shape: the root lakefile has many libs (here 6); an immediate
    subdirectory declares the SAME module with far fewer (here 1) -- the subdirectory
    wins."""
    camp, node, root_dir, sub_dir = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "O2", "O3", "O4", "O5", "Target"], sub_libs=["Target"])
    assert lake_workspace(camp, node) == sub_dir
    assert sub_dir != root_dir


def test_lake_workspace_falls_back_to_root_when_no_subdir_declares_module(tmp_path):
    """A subdirectory exists and has its own lakefile.toml, but declares some OTHER
    module, not the artifact's own -- it is not a candidate, so the island lean dir
    (root) is used, exactly the behaviour every other route already relies on."""
    camp, node, root_dir, sub_dir = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "Target"], sub_libs=["O1"])
    assert sub_dir is not None   # the subdir exists...
    ws = lake_workspace(camp, node)
    assert ws == root_dir        # ...but is not picked: it does not declare Target


def test_lake_workspace_tie_break_is_deterministic_by_path(tmp_path):
    """Two subdirectories declare the module with the SAME lib count: the choice must
    not depend on filesystem iteration order, so it is broken by path, and is stable
    across repeated calls."""
    camp, node, root_dir, _sub = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "O2", "Target"], sub_libs=None)
    lean = root_dir
    for name in ("sub_b", "sub_a"):   # created out of alphabetical order on purpose
        d = lean / name
        d.mkdir()
        (d / "lakefile.toml").write_text(f'name = "{name}"\nsrcDir = ".."\n\n'
                                         + _lib_block(["Target"]))
    expected = (lean / "sub_a").resolve()
    ws = lake_workspace(camp, node)
    assert ws == expected
    assert lake_workspace(camp, node) == ws   # repeated call: same answer


def test_lake_workspace_rejects_subdir_with_own_copy_of_module(tmp_path):
    """Fix 1 (2026-10-28): a subdir lakefile WITHOUT `srcDir = ".."` that declares the
    SAME module name but keeps its own COPY of the file (fewer libs than the root, so
    it would otherwise win on size) is not a candidate at all -- its declared module
    resolves to a DIFFERENT file than the artifact, and accepting it would build and
    export that copy while `closure_digest` goes on hashing the original. The root (many
    libs) must still be returned."""
    camp, node, root_dir, _sub = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "O2", "O3", "O4", "O5", "Target"], sub_libs=None)
    fake_dir = root_dir / "fake_aux"
    fake_dir.mkdir()
    (fake_dir / "lakefile.toml").write_text('name = "fake_aux"\n\n' + _lib_block(["Target"]))
    (fake_dir / "Target.lean").write_text("theorem target_thm : True := trivial  -- COPY\n")
    ws = lake_workspace(camp, node)
    assert ws == root_dir
    assert ws != fake_dir.resolve()


def test_lake_workspace_accepts_subdir_whose_srcdir_points_at_same_file(tmp_path):
    """Fix 1's same-file check must not merely tolerate the zzl_aux shape by accident:
    a subdir with `srcDir = ".."` declares the module but resolves it to the IDENTICAL
    file the root also declares (one file on disk, two lakefiles), so it is still
    accepted and still wins on size."""
    camp, node, root_dir, sub_dir = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "O2", "O3", "O4", "O5", "Target"], sub_libs=["Target"])
    from telperion.missions import coverage
    sub_pkg = coverage._package(sub_dir)
    assert coverage._lib_module_file((sub_pkg,), "Target") == (root_dir / "Target.lean").resolve()
    assert lake_workspace(camp, node) == sub_dir


def test_closure_digest_pins_follow_chosen_workspace(tmp_path):
    """Controller Ruling 0b-7: the closure digest's manifest PINS come from
    `lake_workspace`'s own lake-manifest.json, not the island root's -- a dependency
    bump recorded only in the unused root manifest must not move the digest, while one
    recorded in the chosen workspace's own manifest must."""
    camp, node, root_dir, sub_dir = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "Target"], sub_libs=["Target"],
        root_pkgs=[{"type": "git", "name": "RootDep", "rev": "r1"}],
        sub_pkgs=[{"type": "git", "name": "SubDep", "rev": "s1"}])
    assert lake_workspace(camp, node) == sub_dir

    base = closure_digest(camp, node)

    (root_dir / "lake-manifest.json").write_text(_manifest_json(
        [{"type": "git", "name": "RootDep", "rev": "r2"}]))
    assert closure_digest(camp, node) == base, (
        "changing the ROOT's manifest (not the built workspace) must not move the digest")

    (sub_dir / "lake-manifest.json").write_text(_manifest_json(
        [{"type": "git", "name": "SubDep", "rev": "s2"}]))
    assert closure_digest(camp, node) != base, (
        "changing the CHOSEN workspace's own manifest must move the digest")


def test_lake_workspace_off_island_returns_artifact_dir(tmp_path):
    """No `examples/<island>/lean` tree at all (every `minimal_proved_node`-style
    fixture used across the provenance/rejudge test suites): falls back to the
    artifact's own directory, exactly like `_closure_workspace`'s existing fallback --
    so switching `closure_digest`'s pins to `lake_workspace` changes nothing for them."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    assert lake_workspace(tmp_path, node) == tmp_path.resolve()


def test_lake_workspace_real_registry():
    """Real-registry check (skipped if the registry files are absent): the 4
    zeta_zero_localization nodes this task fixes resolve to zzl_aux, the slim
    sub-workspace CI actually builds from -- while a heavy ladder node and the
    already-bound quasicrystal node are UNCHANGED from their island lean dir."""
    camp_mm = TELPERION_ROOT / "missions" / "mirrormere"
    camp_and = TELPERION_ROOT / "missions" / "anduril"
    bragg_toml = camp_mm / "nodes" / "MM_bragg_defect_witness.toml"
    ladder_toml = camp_and / "nodes" / "AND_ladder_h8000_kernel.toml"
    leakage_toml = camp_mm / "nodes" / "MM_leakage_composite_zero.toml"
    if not (bragg_toml.is_file() and ladder_toml.is_file() and leakage_toml.is_file()):
        pytest.skip("real mission registry not present")

    from telperion.missions import judge
    from telperion.missions.rejudge import island_of_artifact
    from telperion.missions.schema import load_node

    bragg = load_node(bragg_toml)
    ws = lake_workspace(camp_mm, bragg)
    assert ws.name == "zzl_aux"

    for camp, node_path in ((camp_and, ladder_toml), (camp_mm, leakage_toml)):
        n = load_node(node_path)
        artifact = (camp / n.proof.artifact).resolve()
        troot = camp.parent.parent
        island = island_of_artifact(troot, artifact)
        island_dir = judge.island_dir(troot, island).resolve()
        assert lake_workspace(camp, n) == island_dir


# ---------------------------------------------------------------------------
# closure_support_files follows lake_workspace (Fix 2, 2026-10-28)
# ---------------------------------------------------------------------------

def test_closure_support_files_follows_lake_workspace(tmp_path):
    """`closure_support_files` must include the lakefile.toml / lake-manifest.json of
    the workspace `lake_workspace` actually picks to build and export from (here the
    smaller subdir), not only the island root's -- the back-fill git rule
    (`mission rejudge-backfill-closure`) must also watch whatever could move
    `closure_digest`'s manifest pins under Controller Ruling 0b-7, and the island
    root's own files (already covered by `_closure_workspace`) must stay covered too."""
    from telperion.missions.provenance import closure_support_files

    camp, node, root_dir, sub_dir = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "O2", "Target"], sub_libs=["Target"],
        root_pkgs=[{"type": "git", "name": "RootDep", "rev": "r1"}],
        sub_pkgs=[{"type": "git", "name": "SubDep", "rev": "s1"}])
    assert lake_workspace(camp, node) == sub_dir

    support = closure_support_files(camp, node)
    assert (root_dir / "lakefile.toml").resolve() in support
    assert (root_dir / "lake-manifest.json").resolve() in support
    assert (sub_dir / "lakefile.toml").resolve() in support
    assert (sub_dir / "lake-manifest.json").resolve() in support


# ===========================================================================
# Controller Ruling 0b-9 (2026-10-28): the final fix wave.
# ===========================================================================

# ---------------------------------------------------------------------------
# Fix 1: the durable registry marker `second_kernel_route`
# ---------------------------------------------------------------------------

def _passing_direct_record(root: Path, node: Node, route: str = "nanoda-direct") -> RejudgeRecord:
    return RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                         comparator_tag="v4.32.0",
                         artifact_sha256=sha256_file(root / node.proof.artifact),
                         verdict="pass", log_sha256="c" * 64,
                         closure_sha256=closure_digest(root, node),
                         closure_files=len(closure_files(root, node)), route=route)


def test_second_kernel_route_roundtrips_and_validates(tmp_path):
    from telperion.missions.schema import SchemaError, _doc_to_node, _node_to_doc
    from missions_fixtures import minimal_proved_node
    node = dataclasses.replace(minimal_proved_node(tmp_path, heavy=False),
                               second_kernel_route="nanoda-direct")
    doc = _node_to_doc(node)
    assert doc["second_kernel_route"] == "nanoda-direct"
    assert _doc_to_node(doc, tmp_path / "n.toml").second_kernel_route == "nanoda-direct"
    assert "second_kernel_route" not in _node_to_doc(
        dataclasses.replace(node, second_kernel_route=""))      # unset: not serialised
    with pytest.raises(SchemaError, match="second_kernel_route"):
        dataclasses.replace(node, second_kernel_route="lean-only")


def test_marker_without_record_fails(tmp_path):
    """Deleting `[rejudge]` from a MARKED node is a problem -- before the marker, the same
    deletion on a non-heavy node made `second_kernel_claimed` False and the claim vanished."""
    from missions_fixtures import minimal_proved_node
    from telperion.missions.provenance import second_kernel_claimed
    node = minimal_proved_node(tmp_path, heavy=False)
    unmarked = dataclasses.replace(node, rejudge=None)
    assert rejudge_problem(tmp_path, unmarked) == ""            # no claim: nothing to check
    marked = dataclasses.replace(unmarked, second_kernel_route="nanoda-direct")
    assert second_kernel_claimed(marked)
    assert rejudge_problem(tmp_path, marked) == (
        "second_kernel_route=nanoda-direct declared but no re-judge recorded")


def test_marker_route_mismatch_fails(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = _passing_direct_record(tmp_path, node)
    ok = dataclasses.replace(node, rejudge=rec, second_kernel_route="nanoda-direct")
    assert rejudge_problem(tmp_path, ok) == ""
    edited = dataclasses.replace(ok, rejudge=dataclasses.replace(rec, route="comparator"))
    problem = rejudge_problem(tmp_path, edited)
    assert "second_kernel_route=nanoda-direct declared" in problem and "'comparator'" in problem


def test_needs_rejudge_node_marked_nanoda_direct_fails(tmp_path):
    """Ruling 0b-4 applies to the CLAIM as well as the record."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    rec = _passing_direct_record(tmp_path, node)
    marked = dataclasses.replace(node, rejudge=rec, second_kernel_route="nanoda-direct")
    assert "nanoda-direct is not sufficient" in rejudge_problem(tmp_path, marked)


def test_needs_rejudge_includes_judge_via_heavy(tmp_path):
    from missions_fixtures import minimal_proved_node
    from telperion.missions.provenance import needs_rejudge
    node = minimal_proved_node(tmp_path, heavy=False)
    assert not needs_rejudge(node)
    assert needs_rejudge(dataclasses.replace(node, judge_via="heavy"))


def _verify_copy(tmp_path, campaign, islands, edit):
    """Copy a real campaign (+ the named islands' lean sources, never .lake) under
    `<tmp>/telperion/`, apply `edit(nodes_dir)`, return verify_campaign's errors."""
    import shutil
    from telperion.missions.verify import verify_campaign
    troot = tmp_path / "telperion"
    dst = troot / "missions" / campaign
    if not (TELPERION_ROOT / "missions" / campaign).is_dir():
        pytest.skip("real registry absent")
    shutil.copytree(TELPERION_ROOT / "missions" / campaign, dst)
    for isl in islands:
        src = TELPERION_ROOT / "examples" / isl / "lean"
        if src.is_dir():
            shutil.copytree(src, troot / "examples" / isl / "lean",
                            ignore=shutil.ignore_patterns(".lake"))
    edit(dst / "nodes")
    return verify_campaign(dst).errors


def test_verify_fails_when_rejudge_deleted_from_marked_node(tmp_path):
    from telperion.missions.schema import load_node
    slug = "MM_leakage_composite_zero"

    def edit(nd):
        p = nd / f"{slug}.toml"
        n = load_node(p)
        save_node(dataclasses.replace(n, second_kernel_route="nanoda-direct", rejudge=None), p)
    errors = _verify_copy(tmp_path, "mirrormere", ["quasicrystal"], edit)
    assert any(slug in e and "second_kernel_route=nanoda-direct declared but no re-judge "
               "recorded" in e for e in errors), errors


def test_verify_fails_when_marked_route_edited(tmp_path):
    from telperion.missions.schema import load_node
    slug = "MM_leakage_composite_zero"

    def edit(nd):
        p = nd / f"{slug}.toml"
        n = load_node(p)
        assert n.rejudge is not None and n.rejudge.route == "nanoda-direct"
        save_node(dataclasses.replace(n, second_kernel_route="nanoda-direct",
                                      rejudge=dataclasses.replace(n.rejudge, route="comparator")),
                  p)
    errors = _verify_copy(tmp_path, "mirrormere", ["quasicrystal"], edit)
    assert any(slug in e and "second_kernel_route=nanoda-direct declared but the [rejudge] "
               "record's route is 'comparator'" in e for e in errors), errors


def test_verify_fails_h11000_style_judge_via_heavy_with_nanoda_direct_record(tmp_path):
    """The reviewer's shape: an h11000-style node (no [comparator] record), its
    heavy_certificates flag DELETED, judge_via = "heavy" kept, and a nanoda-direct record.
    Before Ruling 0b-9, needs_rejudge ignored judge_via, so the nanoda-direct record stood in
    for the Comparator re-judge Ruling 0b-4 demands."""
    from telperion.missions.schema import load_node
    slug = "AND_ladder_h11000_kernel"

    def edit(nd, keep_marker):
        p = nd / f"{slug}.toml"
        n = load_node(p)
        assert n.comparator is None and n.judge_via == "heavy"
        save_node(dataclasses.replace(
            n, heavy_certificates=False,
            second_kernel_route=(n.second_kernel_route if keep_marker else ""),
            rejudge=dataclasses.replace(n.rejudge, route="nanoda-direct")), p)
    # marker removed too (the reviewer's pre-marker shape): judge_via alone must catch it
    errors = _verify_copy(tmp_path / "a", "anduril", ["zeta_reflection"],
                          lambda nd: edit(nd, keep_marker=False))
    assert any(slug in e and "nanoda-direct is not sufficient" in e for e in errors), errors
    # marker kept (the committed registry marks h11000 "comparator"): fails on the marker too
    errors = _verify_copy(tmp_path / "b", "anduril", ["zeta_reflection"],
                          lambda nd: edit(nd, keep_marker=True))
    assert any(slug in e and "second_kernel_route=comparator declared but the [rejudge] "
               "record's route is 'nanoda-direct'" in e for e in errors), errors


def test_cli_second_kernel_mark(tmp_path, capsys):
    """`mission second-kernel-mark` refuses without a record, on the wrong route, and on a
    stale record; writes the marker only when the current record passes on that route."""
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path, heavy=False)
    p = mroot / "demo" / "nodes" / "Demo_hv.toml"
    args = ["second-kernel-mark", "Demo_hv", "--campaign", "demo"]
    assert _cli(mroot, *args, "--route", "nanoda-direct") == 2          # no record yet
    log = tmp_path / "direct.log"
    log.write_text(_direct_log(mroot))
    assert _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
                "--comparator-tag", "v4.32.0") == 0
    assert _cli(mroot, *args, "--route", "comparator") == 2             # wrong route
    assert load_node(p).second_kernel_route == ""
    art = _art(mroot)
    original = art.read_text()
    art.write_text(original + "-- edited after the re-judge\n")
    assert _cli(mroot, *args, "--route", "nanoda-direct") == 2          # stale record
    assert load_node(p).second_kernel_route == ""
    art.write_text(original)
    assert _cli(mroot, *args, "--route", "nanoda-direct") == 0
    n = load_node(p)
    assert n.second_kernel_route == "nanoda-direct"
    assert 'second_kernel_route = "nanoda-direct"' in p.read_text()
    assert rejudge_problem(mroot / "demo", n) == ""


# ---------------------------------------------------------------------------
# Fix 2: bind the exported theorem (and module) at record time
# ---------------------------------------------------------------------------

def _record(mroot: Path, tmp_path: Path, text: str) -> int:
    log = tmp_path / "direct.log"
    log.write_text(text)
    return _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
                "--comparator-tag", "v4.32.0")


def test_cli_direct_swapped_theorem_refused(tmp_path, capsys):
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path)
    assert _record(mroot, tmp_path, _direct_log(mroot, theorem="other_thm")) == 2
    assert "registered theorem is 'demo_hv'" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_direct_missing_info_line_refused(tmp_path, capsys):
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path)
    assert _record(mroot, tmp_path, _direct_log(mroot, info=False)) == 2
    assert "exactly one REJUDGE-INFO line" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_direct_duplicate_info_line_refused(tmp_path, capsys):
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path)
    text = _direct_log(mroot)
    dup = [l for l in text.splitlines(keepends=True) if "theorem=" in l][0]
    text = text.replace(dup, dup + dup.replace("theorem=demo_hv", "theorem=other_thm"), 1)
    assert _record(mroot, tmp_path, text) == 2
    assert "found 2" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_direct_wrong_module_refused(tmp_path, capsys):
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path)
    assert _record(mroot, tmp_path, _direct_log(mroot, module="B")) == 2
    assert "artifact's module is 'A'" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_direct_pass_whose_export_lacks_the_theorem_refused(tmp_path, capsys):
    """The INFO line names the right theorem, but the export (what nanoda checked) declares
    a DIFFERENT constant: a pass over it is no pass for this node."""
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path)
    other = _EXPORT_DEMO.replace('"str":"demo_hv"', '"str":"other_thm"')
    assert _record(mroot, tmp_path, _direct_log(mroot, export_body=other)) == 2
    assert "does not declare theorem 'demo_hv'" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_info_binding_must_precede_export_section():
    """An INFO line inside the export (tool output) never counts as the binding."""
    from telperion.missions.nanoda_direct import BindingError, info_binding
    text = ("REJUDGE-HEADER node=X artifact_sha256=" + "a" * 64 + "\n"
            "REJUDGE-ROUTE nanoda-direct\n"
            "==================== REJUDGE-EXPORT exit=0 ====================\n"
            "REJUDGE-INFO theorem=t module=M\n"
            "==================== REJUDGE-NANODA exit=0 ====================\n")
    with pytest.raises(BindingError, match="found 0"):
        info_binding(text)


def test_export_declares_theorem_reads_lean4export_names():
    from telperion.missions.nanoda_direct import export_declares_theorem
    exp = ('{"in":1,"str":{"pre":0,"str":"Foo"}}\n'
           '{"in":2,"str":{"pre":1,"str":"bar"}}\n'
           '{"in":3,"str":{"pre":0,"str":"bar"}}\n'
           '{"thm":{"all":[2],"levelParams":[],"name":2,"type":0,"value":0}}\n'
           '{"def":{"all":[3],"hints":"abbrev","levelParams":[],"name":3,"safety":"safe","type":0,"value":0}}\n')
    assert export_declares_theorem(exp, "Foo.bar")
    assert not export_declares_theorem(exp, "bar")          # interned, but a def, not a thm
    assert not export_declares_theorem(exp, "Foo.baz")      # not interned at all


# ---------------------------------------------------------------------------
# Fix 6 (Minor 2): a nanoda-direct log for a needs_rejudge node is refused at record time
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("heavy,judge_via", [(True, ""), (False, "heavy")])
def test_cli_direct_log_refused_for_needs_rejudge_node(tmp_path, capsys, heavy, judge_via):
    from telperion.missions.schema import load_node
    mroot = _campaign(tmp_path, heavy=heavy, judge_via=judge_via)
    assert _record(mroot, tmp_path, _direct_log(mroot)) == 2
    assert "Ruling 0b-4" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_run_direct_writes_build_info_line(tmp_path):
    tel, camp, node = _tmp_island_node(tmp_path)
    run, _calls = _stub_run()
    tools = Tools(telperion_root=tel, lean4export=Path("/tools/lean4export"),
                  nanoda=Path("/tools/nanoda_bin"), nanoda_rev="f" * 40, out_dir=tmp_path / "rj")
    text = run_direct(camp, node, tools=tools, run=run,
                      build_info="exit=0 result=Build completed successfully (12 jobs).").read_text()
    pre = text.split("REJUDGE-EXPORT")[0]
    assert "REJUDGE-INFO build=exit=0 result=Build completed successfully (12 jobs)." in pre
    assert rejudge_log_verdict(text, []) == "pass"           # the line is preamble-legal
    from telperion.missions.nanoda_direct import info_binding
    assert info_binding(text) == ("a_thm", "A")               # still exactly one binding


# ---------------------------------------------------------------------------
# Fix 3: closure consistency in the BUILD workspace (0b-8 guard, transitively)
# ---------------------------------------------------------------------------

def _shadow_island(tmp_path, *, shadow: bool):
    """Target imports Mid imports Leaf, all in the island lean dir. Subdir `sub_aux` declares
    Target with a lib-level `srcDir = ".."` -- so the 0b-8 check (Target resolves to the
    artifact itself) passes -- but its PACKAGE srcDir is its own directory, and with
    *shadow* it carries its own `Leaf.lean`: in that workspace the transitive import Leaf
    resolves to the copy, not to the file the closure digest hashes."""
    camp, node, root_dir, _sub = _tmp_two_level_island(
        tmp_path, root_libs=["O1", "O2", "O3", "Target", "Mid", "Leaf"], sub_libs=None)
    (root_dir / "Target.lean").write_text("import Mid\ntheorem target_thm : True := trivial\n")
    (root_dir / "Mid.lean").write_text("import Leaf\ntheorem mid : True := trivial\n")
    (root_dir / "Leaf.lean").write_text("theorem leaf : True := trivial\n")
    sub = root_dir / "sub_aux"
    sub.mkdir()
    (sub / "lakefile.toml").write_text(
        'name = "sub_aux"\n\n[[lean_lib]]\nname = "Target"\nsrcDir = ".."\n')
    if shadow:
        (sub / "Leaf.lean").write_text("theorem leaf : True := trivial  -- SHADOW COPY\n")
    return camp, node, root_dir, sub.resolve()


def test_lake_workspace_rejects_candidate_shadowing_a_transitive_import(tmp_path):
    from telperion.missions import coverage
    camp, node, root_dir, sub = _shadow_island(tmp_path, shadow=True)
    # the 0b-8 guard alone is satisfied: Target itself resolves to the artifact ...
    assert coverage._lib_module_file((coverage._package(sub),), "Target") == \
        (root_dir / "Target.lean").resolve()
    # ... but Leaf, two imports down, resolves to the shadow copy in sub_aux's workspace
    assert coverage._module_file(coverage._workspace(sub), "Leaf") == (sub / "Leaf.lean").resolve()
    assert lake_workspace(camp, node) == root_dir


def test_lake_workspace_accepts_same_candidate_without_the_shadow(tmp_path):
    """Control: the identical layout minus the shadow copy -- sub_aux resolves every closure
    module to the island model's file, so it is accepted and wins on size."""
    camp, node, root_dir, sub = _shadow_island(tmp_path, shadow=False)
    assert lake_workspace(camp, node) == sub


@pytest.mark.parametrize("slug", ["MM_bragg_defect_witness", "MM_bragg_defect_witness_sie",
                                  "MM_offline_pairs_le_defect", "MM_recurrence_deficit_eq_excess"])
def test_real_zzl_nodes_still_pick_zzl_aux(slug):
    from telperion.missions.schema import load_node
    camp = TELPERION_ROOT / "missions" / "mirrormere"
    p = camp / "nodes" / f"{slug}.toml"
    if not p.is_file():
        pytest.skip("real registry absent")
    assert lake_workspace(camp, load_node(p)).name == "zzl_aux"


# ---------------------------------------------------------------------------
# Fix 6: coverage._imports fails CLOSED on an unparseable header line
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("header", [
    "import\n  B\n",                         # bare `import`, modules on the next line
    "import A\n  B\n",                       # continuation line after a one-line import
    "import A\nB C\n",
    "public import\n  B\n",
])
def test_imports_multiline_header_raises(tmp_path, header):
    from telperion.missions import coverage
    from telperion.missions.provenance import ClosureError
    f = tmp_path / "M.lean"
    f.write_text(header + "\ntheorem m : True := trivial\n")
    with pytest.raises(ClosureError, match="cannot parse import header line"):
        coverage._imports(f.resolve())


@pytest.mark.parametrize("after", [
    "open Real", "noncomputable section", "namespace Foo", "set_option maxHeartbeats 0",
    "@[simp] theorem m : True := trivial", "/-- doc -/\ntheorem m : True := trivial",
    "theorem m : True := trivial", "lean_lib Foo where", "universe u", "#check Nat",
])
def test_imports_normal_header_end_does_not_raise(tmp_path, after):
    from telperion.missions import coverage
    f = tmp_path / "M.lean"
    f.write_text("import A\nimport B C -- comment\n/- block\n comment -/\n" + after + "\n")
    assert coverage._imports(f.resolve()) == ("A", "B", "C")


def test_multiline_import_fails_the_closure(tmp_path):
    """End to end: a closure file with a multi-line import makes `closure_files` raise
    ClosureError (so rejudge-record/back-fill exit 2 and verify reports it), instead of
    dropping the continued modules from the digest."""
    from telperion.missions.provenance import ClosureError
    camp, node, root_dir, _sub = _tmp_two_level_island(tmp_path, root_libs=["Target", "B"])
    (root_dir / "B.lean").write_text("theorem b : True := trivial\n")
    (root_dir / "Target.lean").write_text("import\n  B\ntheorem target_thm : True := trivial\n")
    with pytest.raises(ClosureError, match="cannot parse import header line"):
        closure_files(camp, node)


def test_report_names_route_and_marker(tmp_path):
    """Ruling 0b-9: every passing second-kernel line names its route and the marker."""
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = _passing_direct_record(tmp_path, node)
    manifest = MissionManifest(
        name="Demo.goal", title="t", description="d", goal_node="n",
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    marked = dataclasses.replace(node, rejudge=rec, second_kernel_route="nanoda-direct")
    out = render_provenance_report(Campaign(root=tmp_path, manifest=manifest, nodes={"n": marked}))
    assert "[route=nanoda-direct, marker=nanoda-direct]" in out
    unmarked = dataclasses.replace(node, rejudge=rec)
    out = render_provenance_report(Campaign(root=tmp_path, manifest=manifest, nodes={"n": unmarked}))
    assert "[route=nanoda-direct, marker=unset]" in out

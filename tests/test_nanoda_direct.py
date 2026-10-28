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
    closure_digest, closure_files, render_provenance_report, rejudge_problem, sha256_file,
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
              export_rc=0, nanoda_rc=0):
    calls = []

    def run(cmd, *, cwd):
        calls.append((list(cmd), Path(cwd)))
        if cmd[0] == "lake":
            return export_rc, export_out
        return nanoda_rc, nanoda_out
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


# ---------------------------------------------------------------------------
# rejudge_problem: a passing nanoda-direct record satisfies the second-kernel requirement
# ---------------------------------------------------------------------------

def test_rejudge_problem_accepts_direct_pass(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64, closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)), route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    assert rejudge_problem(tmp_path, node) == ""


def test_rejudge_problem_still_flags_a_failing_direct_record(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="f" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="fail",
                        log_sha256="c" * 64, route="nanoda-direct")
    node = dataclasses.replace(node, rejudge=rec)
    assert "FAILED" in rejudge_problem(tmp_path, node)


# ---------------------------------------------------------------------------
# provenance report: the route label (Review Focus 5)
# ---------------------------------------------------------------------------

def test_report_labels_route(tmp_path):
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
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


def _campaign(tmp_path: Path, *, heavy: bool = False) -> Path:
    mroot = tmp_path / "missions"
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
        proof=Proof("proof/Demo_hv.lean", "lean_module", "direct"),
        heavy_certificates=heavy, created="2026-10-28", updated="2026-10-28",
    )
    save_node(node, croot / "nodes" / "Demo_hv.toml")
    art = croot / "proof" / "Demo_hv.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text("theorem demo_hv : 1 = 1 := by rfl\n")
    return mroot


def _direct_log(mroot: Path, *, nanoda_out: str = "Checked 4 declarations with no errors\n",
               export_rc: int = 0, nanoda_rc: int = 0) -> str:
    art = mroot / "demo" / "proof" / "Demo_hv.lean"
    sha = hashlib.sha256(art.read_bytes()).hexdigest()
    from telperion.missions.schema import load_node
    csha = closure_digest(mroot / "demo", load_node(mroot / "demo" / "nodes" / "Demo_hv.toml"))
    return (f"REJUDGE-HEADER node=Demo_hv artifact_sha256={sha} closure_sha256={csha}\n"
           "REJUDGE-ROUTE nanoda-direct\n"
           f"==================== REJUDGE-EXPORT exit={export_rc} ====================\n"
           "<export bytes>\n"
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
        hashlib.sha256((mroot / "demo" / "proof" / "Demo_hv.lean").read_bytes()).hexdigest(),
        "0" * 64, 1)
    log.write_text(text)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    assert "CURRENT artifact" in capsys.readouterr().err
    from telperion.missions.schema import load_node
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None

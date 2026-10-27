"""The `[rejudge]` record, its log parser, `rejudge_problem`, and `mission rejudge-record`.

heavy_certificates nodes exhaust a 16 GB CI runner under nanoda, so hosted CI judges them
with the Lean kernel only. The owner's rule (spec 5.1, step 0): such a node stays proved
only with a passing LOCAL re-judge (Comparator, nanoda ON) on its current artifact. The
verdict is derived from the Comparator log, never from a flag.
"""
from __future__ import annotations

import dataclasses
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, Proof, RejudgeRecord, SchemaError,
    load_node, save_manifest, save_node,
)
from telperion.missions.rejudge import parse_comparator_log  # noqa: E402

PASS_LOG = ("Lean default kernel accepts the solution\n"
            "Nanoda kernel accepts the solution\nYour solution is okay!\n")


def test_pass_needs_all_three_lines():
    assert parse_comparator_log(PASS_LOG) == "pass"


def test_rejudge_verdict_requires_nanoda_line():
    log = "Lean default kernel accepts the solution\nYour solution is okay!\n"
    assert parse_comparator_log(log) == "fail"


def test_any_error_line_fails():
    assert parse_comparator_log(PASS_LOG + "error: unpermitted axiom sorryAx\n") == "fail"


def test_bad_verdict_rejected():
    with pytest.raises(SchemaError):
        RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                      artifact_sha256="b" * 64, verdict="maybe", log_sha256="c" * 64)


def test_rejudge_roundtrip(tmp_path):
    from telperion.missions.schema import _node_to_doc, _doc_to_node
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                        artifact_sha256="b" * 64, verdict="pass", log_sha256="c" * 64, peak_rss_kb=1)
    node2 = _doc_to_node(_node_to_doc(dataclasses.replace(node, rejudge=rec)), tmp_path / "n.toml")
    assert node2.rejudge == rec


def test_rejudge_stale_artifact(tmp_path):
    from telperion.missions.provenance import rejudge_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)  # writes a real artifact file
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                        artifact_sha256="0" * 64, verdict="pass", log_sha256="c" * 64)
    assert "artifact" in rejudge_problem(tmp_path, dataclasses.replace(node, rejudge=rec))


def test_heavy_node_without_second_kernel_reads_lean_only(tmp_path):
    from telperion.missions.provenance import rejudge_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    assert rejudge_problem(tmp_path, node) != ""


def test_non_heavy_node_has_no_rejudge_problem(tmp_path):
    from telperion.missions.provenance import rejudge_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    assert rejudge_problem(tmp_path, node) == ""


def test_failed_rejudge_reports_fail(tmp_path):
    from telperion.missions.provenance import rejudge_problem
    from missions_fixtures import minimal_proved_node
    from telperion.missions.provenance import sha256_file
    node = minimal_proved_node(tmp_path, heavy=True)
    art_sha = sha256_file(tmp_path / node.proof.artifact)
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                        artifact_sha256=art_sha, verdict="fail", log_sha256="c" * 64)
    problem = rejudge_problem(tmp_path, dataclasses.replace(node, rejudge=rec))
    assert "FAILED" in problem


# ---------------------------------------------------------------------------
# CLI: `mission rejudge-record`
# ---------------------------------------------------------------------------

def _cli(mroot: Path, *args: str) -> int:
    return main(["mission", "--missions-root", str(mroot), *args])


def _campaign(tmp_path: Path) -> Path:
    """A minimal campaign with one heavy, proved node and its artifact on disk."""
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
        name="Demo.hv", title="heavy node", kind="lemma", status="proved", depends_on=(),
        statement_module="Statements.Demo_hv",
        proof=Proof("proof/Demo_hv.lean", "lean_module", "direct"),
        heavy_certificates=True, created="2026-10-27", updated="2026-10-27",
    )
    save_node(node, croot / "nodes" / "Demo_hv.toml")
    art = croot / "proof" / "Demo_hv.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text("theorem demo_hv : 1 = 1 := by rfl\n")
    return mroot


def test_cli_rejudge_record_pass_writes_record_exit0(tmp_path):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(PASS_LOG)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None
    assert node.rejudge.verdict == "pass"
    assert node.rejudge.comparator_tag == "v4.32.0"
    assert len(node.rejudge.nanoda_rev) == 40
    assert 'verdict = "pass"' in (mroot / "demo" / "nodes" / "Demo_hv.toml").read_text()


def test_cli_rejudge_record_fail_exit1_reports_to_owner(tmp_path, capsys):
    mroot = _campaign(tmp_path)
    log = tmp_path / "fail.log"
    log.write_text("Lean default kernel accepts the solution\nYour solution is okay!\n")
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 1
    err = capsys.readouterr().err
    assert "REJUDGE FAIL" in err and "REPORT TO OWNER" in err
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None
    assert node.rejudge.verdict == "fail"

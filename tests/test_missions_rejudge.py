"""The `[rejudge]` record, its log parser, `rejudge_problem`, and `mission rejudge-record`.

heavy_certificates nodes exhaust a 16 GB CI runner under nanoda, so hosted CI judges them
with the Lean kernel only. The owner's rule (spec 5.1, step 0): such a node stays proved
only with a passing LOCAL re-judge (Comparator, nanoda ON) on its current artifact. The
verdict is derived from the Comparator log, never from a flag.
"""
from __future__ import annotations

import dataclasses
import hashlib
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, Proof, Readback, RejudgeRecord, SchemaError,
    load_node, save_manifest, save_node,
)
from telperion.missions.rejudge import parse_comparator_log, parse_rejudge_header  # noqa: E402
from telperion.missions.statements import write_statement  # noqa: E402
from telperion.missions.verify import GateError, grant_status, verify_campaign  # noqa: E402

TELPERION_ROOT = Path(__file__).resolve().parents[1]

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
# parse_rejudge_header: binds a log to exactly one node and one artifact digest
# ---------------------------------------------------------------------------

def test_parse_rejudge_header_reads_node_and_sha():
    text = f"REJUDGE-HEADER node=Demo_hv artifact_sha256={'a' * 64}\n" + PASS_LOG
    assert parse_rejudge_header(text) == ("Demo_hv", "a" * 64)


def test_parse_rejudge_header_lowercases_sha():
    text = f"REJUDGE-HEADER node=Demo_hv artifact_sha256={'A' * 64}\n" + PASS_LOG
    assert parse_rejudge_header(text) == ("Demo_hv", "a" * 64)


def test_parse_rejudge_header_missing_returns_none():
    assert parse_rejudge_header(PASS_LOG) is None


def test_parse_rejudge_header_rejects_short_sha():
    text = f"REJUDGE-HEADER node=Demo_hv artifact_sha256={'a' * 63}\n" + PASS_LOG
    assert parse_rejudge_header(text) is None


def test_parse_rejudge_header_rejects_wrong_prefix():
    text = f"NOT-A-HEADER node=Demo_hv artifact_sha256={'a' * 64}\n" + PASS_LOG
    assert parse_rejudge_header(text) is None


# ---------------------------------------------------------------------------
# CLI: `mission rejudge-record`
# ---------------------------------------------------------------------------

def _cli(mroot: Path, *args: str) -> int:
    return main(["mission", "--missions-root", str(mroot), *args])


def _campaign(tmp_path: Path, *, heavy: bool = True, status: str = "proved",
             deprecated_reason: str = "") -> Path:
    """A minimal campaign with one node (status *status*) and its artifact on disk."""
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
        name="Demo.hv", title="heavy node", kind="lemma", status=status, depends_on=(),
        statement_module="Statements.Demo_hv",
        proof=Proof("proof/Demo_hv.lean", "lean_module", "direct"),
        heavy_certificates=heavy, created="2026-10-27", updated="2026-10-27",
        deprecated_reason=deprecated_reason,
    )
    save_node(node, croot / "nodes" / "Demo_hv.toml")
    art = croot / "proof" / "Demo_hv.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text("theorem demo_hv : 1 = 1 := by rfl\n")
    return mroot


def _artifact_sha256(mroot: Path, slug: str = "Demo_hv") -> str:
    art = mroot / "demo" / "proof" / f"{slug}.lean"
    return hashlib.sha256(art.read_bytes()).hexdigest()


def _header(mroot: Path, *, node: str = "Demo_hv", sha: str = None) -> str:
    sha = sha if sha is not None else _artifact_sha256(mroot)
    return f"REJUDGE-HEADER node={node} artifact_sha256={sha}\n"


def test_cli_rejudge_record_pass_writes_record_exit0(tmp_path):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot) + PASS_LOG)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None
    assert node.rejudge.verdict == "pass"
    assert node.rejudge.comparator_tag == "v4.32.0"
    assert len(node.rejudge.nanoda_rev) == 40
    assert node.updated == node.rejudge.date          # item 4: `updated` follows the record
    assert 'verdict = "pass"' in (mroot / "demo" / "nodes" / "Demo_hv.toml").read_text()


def test_cli_rejudge_record_fail_exit1_reports_to_owner(tmp_path, capsys):
    mroot = _campaign(tmp_path)
    log = tmp_path / "fail.log"
    log.write_text(_header(mroot) + "Lean default kernel accepts the solution\n"
                   "Your solution is okay!\n")
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 1
    err = capsys.readouterr().err
    assert "REJUDGE FAIL" in err and "REPORT TO OWNER" in err
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None
    assert node.rejudge.verdict == "fail"


def test_cli_log_sha256_is_over_raw_bytes_not_decoded_text(tmp_path):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    # A byte that is not valid UTF-8; read_text(errors="replace") would turn it into the
    # replacement character U+FFFD before hashing, giving a DIFFERENT digest than hashing
    # the raw bytes straight off disk. log_sha256 must be the latter.
    raw = (_header(mroot) + PASS_LOG).encode() + b"\xff\n"
    log.write_bytes(raw)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge.log_sha256 == hashlib.sha256(raw).hexdigest()


def test_cli_missing_header_exit2_no_record(tmp_path, capsys):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(PASS_LOG)                          # no REJUDGE-HEADER line at all
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    assert "REJUDGE-HEADER" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_wrong_node_header_exit2_no_record(tmp_path, capsys):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot, node="Some_other_node") + PASS_LOG)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    err = capsys.readouterr().err
    assert "Some_other_node" in err and "different node" in err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_stale_sha_header_exit2_no_record(tmp_path, capsys):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot, sha="0" * 64) + PASS_LOG)   # not the sha on disk
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    err = capsys.readouterr().err
    assert "CURRENT artifact" in err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_non_heavy_node_exit2_no_record(tmp_path, capsys):
    mroot = _campaign(tmp_path, heavy=False)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot) + PASS_LOG)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    assert "heavy_certificates" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_non_proved_node_exit2_no_record(tmp_path, capsys):
    """Controller ruling 6 (2026-10-27): a draft heavy node WITH its artifact on disk is
    pre-grant judging -- it now records. A deprecated one is still refused regardless of its
    artifact: a deprecated node is never a candidate for `mission grant`."""
    mroot = _campaign(tmp_path / "draft", status="draft")
    log = tmp_path / "draft-pass.log"
    log.write_text(_header(mroot) + PASS_LOG)
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None and node.rejudge.verdict == "pass"
    assert node.status == "draft"              # rejudge-record never flips status itself

    mroot2 = _campaign(tmp_path / "dep", status="deprecated",
                       deprecated_reason="superseded by a later node")
    log2 = tmp_path / "dep-pass.log"
    log2.write_text(_header(mroot2) + PASS_LOG)
    rc2 = _cli(mroot2, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log2),
              "--comparator-tag", "v4.32.0")
    assert rc2 == 2
    assert "deprecated" in capsys.readouterr().err
    assert load_node(mroot2 / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


# ---------------------------------------------------------------------------
# Enforcement (step 0, Task 5): `mission verify` and the grant gate both refuse a
# proved heavy_certificates node that lacks a passing, current local nanoda re-judge.
# ---------------------------------------------------------------------------

def _verify_copy_without_rejudge(tmp_path, campaign, slug):
    """Copy a real campaign, drop one node's [rejudge] record, run verify_campaign on the copy.

    The copy is rooted at ``tmp_path/telperion/missions/<campaign>``, mirroring the real
    ``<repo>/telperion/missions/<campaign>`` layout, rather than at ``tmp_path/<campaign>``: a
    campaign root two levels too shallow breaks two things verify_campaign needs. (1)
    `_repo_root` walks up three parents from the campaign root looking for
    `.github/workflows`; a shallow root makes it resolve outside tmp_path into the real
    filesystem. (2) several anduril nodes' `proof.artifact` is a path like
    `../../examples/zeta_reflection/lean/Arb4_h8000.lean`, relative to the campaign root; a
    shallow root makes that resolve to a nonexistent file, and verify_campaign reports the
    generic "artifact does not exist" and `continue`s past the node WITHOUT ever reaching the
    re-judge check for it. The real `examples/zeta_reflection/lean` tree (the only subtree
    anduril's nodes reference) is copied alongside the campaign so those artifact paths
    resolve to real files instead.
    """
    import shutil
    from telperion.missions.schema import load_node, save_node
    from telperion.missions.verify import verify_campaign
    troot = tmp_path / "telperion"
    dst = troot / "missions" / campaign
    shutil.copytree(TELPERION_ROOT / "missions" / campaign, dst)
    examples_lean = TELPERION_ROOT / "examples" / "zeta_reflection" / "lean"
    if examples_lean.is_dir():
        shutil.copytree(examples_lean, troot / "examples" / "zeta_reflection" / "lean")
    p = dst / "nodes" / f"{slug}.toml"
    save_node(dataclasses.replace(load_node(p), rejudge=None), p)
    return verify_campaign(dst).errors


def test_verify_rejects_proved_heavy_node_without_rejudge(tmp_path):
    errors = _verify_copy_without_rejudge(tmp_path, "anduril", "AND_ladder_h8000_kernel")
    assert any("AND_ladder_h8000_kernel" in e and "re-judge" in e for e in errors)


def test_grant_status_refuses_heavy_node_without_rejudge(tmp_path):
    """The grant gate enforces the same rule required_ci_problem already enforces: a heavy
    node may not be granted `proved` without a passing local nanoda re-judge on record."""
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = MissionManifest(
        name="Demo.gate", title="Demo Campaign", description="synthetic",
        goal_node="Demo_hv3", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, root / "mission.toml")

    stmt = "theorem lemma_hv3 : 1 + 1 = 2"
    node = Node(
        name="Demo.hv3", title="heavy node awaiting grant", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Demo_hv3",
        proof=Proof(artifact="proof/Demo_hv3.lean", artifact_kind="lean_module",
                   via="direct", closure_clean=False),
        readback=Readback(text="read-back of Demo.hv3, rendering the formal statement in "
                               "the auditor's own words at length", auditor="test-auditor",
                          date="2026-10-27"),
        heavy_certificates=True, created="2026-10-27", updated="2026-10-27",
    )
    save_node(node, root / "nodes" / "Demo_hv3.toml")
    write_statement(root, node, stmt, manifest)

    artifact_path = root / "proof" / "Demo_hv3.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(f"{stmt} := by simp\n")

    campaign = load_campaign(root)
    with pytest.raises(GateError, match="re-judge|heavy_certificates"):
        grant_status(campaign, "Demo_hv3", identity="gate@test", session="gate-session")
    # Refused: the on-disk status must remain open.
    assert load_node(root / "nodes" / "Demo_hv3.toml").status == "open"


def test_rejudge_record_then_grant_status_closes_the_loop(tmp_path):
    """Controller ruling 6 (2026-10-27): with `rejudge-record` accepting a pre-grant `open`
    heavy node (its proof linked, its artifact on disk), the full sequence --
    `rejudge-record` on a fresh heavy node, then `grant_status` -- succeeds end to end. Before
    ruling 6, `rejudge-record` required `status == 'proved'` while `grant_status` (Task 5)
    required a passing re-judge to grant, so no heavy node could ever freshly reach `proved`;
    this is the regression test for that deadlock."""
    mroot = tmp_path / "missions"
    croot = mroot / "loop"
    (croot / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Loop.goal", title="Loop Campaign", description="synthetic",
        goal_node="Loop_hv", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, croot / "mission.toml")

    stmt = "theorem loop_hv : 1 + 1 = 2"
    node = Node(
        name="Loop.hv", title="heavy node closing the loop", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Loop_hv",
        proof=Proof(artifact="proof/Loop_hv.lean", artifact_kind="lean_module",
                   via="direct", closure_clean=False),
        readback=Readback(text="read-back of Loop.hv, rendering the formal statement in the "
                               "auditor's own words at some length so it clears the "
                               "read-back floor", auditor="test-auditor", date="2026-10-27"),
        heavy_certificates=True, created="2026-10-27", updated="2026-10-27",
    )
    save_node(node, croot / "nodes" / "Loop_hv.toml")
    write_statement(croot, node, stmt, manifest)
    art = croot / "proof" / "Loop_hv.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text(f"{stmt} := by simp\n")

    # Pre-grant judging: the node is still `open`, with no `[rejudge]` yet.
    assert load_node(croot / "nodes" / "Loop_hv.toml").rejudge is None
    log = tmp_path / "pass.log"
    art_sha = hashlib.sha256(art.read_bytes()).hexdigest()
    log.write_text(f"REJUDGE-HEADER node=Loop_hv artifact_sha256={art_sha}\n" + PASS_LOG)
    rc = _cli(mroot, "rejudge-record", "Loop_hv", "--campaign", "loop", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    n = load_node(croot / "nodes" / "Loop_hv.toml")
    assert n.rejudge is not None and n.rejudge.verdict == "pass"
    assert n.status == "open"                 # rejudge-record never flips status itself

    granted = grant_status(load_campaign(croot), "Loop_hv", identity="gate@test",
                           session="gate-session")
    assert granted.status == "proved"
    assert load_node(croot / "nodes" / "Loop_hv.toml").status == "proved"

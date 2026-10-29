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


#: A one-part node log body, as rejudge_queue.sh writes it (see _part below).
def _one_part(slug: str, body: str) -> str:
    return (f"==================== REJUDGE-PART 1/1 {slug} (comparator exit 0, peak 1 kB) "
            "====================\n" + body)


@pytest.fixture
def one_part(monkeypatch):
    """The synthetic campaigns below have no island, so their bundle cannot be rendered;
    stand in a one-part render (the real render is exercised by the tests further down)."""
    import telperion.missions.rejudge as rj
    monkeypatch.setattr(rj, "expected_part_slugs", lambda camp, node, slug: [slug])


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


def test_cli_rejudge_record_pass_writes_record_exit0(tmp_path, one_part):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot) + _one_part("Demo_hv", PASS_LOG))
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


def test_cli_rejudge_record_fail_exit1_reports_to_owner(tmp_path, one_part, capsys):
    mroot = _campaign(tmp_path)
    log = tmp_path / "fail.log"
    log.write_text(_header(mroot) + _one_part("Demo_hv", "Lean default kernel accepts the solution\n"
                   "Your solution is okay!\n"))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 1
    err = capsys.readouterr().err
    assert "REJUDGE FAIL" in err and "REPORT TO OWNER" in err
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None
    assert node.rejudge.verdict == "fail"


def test_cli_log_sha256_is_over_raw_bytes_not_decoded_text(tmp_path, one_part):
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    # A byte that is not valid UTF-8; read_text(errors="replace") would turn it into the
    # replacement character U+FFFD before hashing, giving a DIFFERENT digest than hashing
    # the raw bytes straight off disk. log_sha256 must be the latter.
    raw = (_header(mroot) + _one_part("Demo_hv", PASS_LOG)).encode() + b"\xff\n"
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
    log.write_text(_header(mroot) + _one_part("Demo_hv", PASS_LOG))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    assert "heavy_certificates" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_non_proved_node_exit2_no_record(tmp_path, one_part, capsys):
    """Controller ruling 6 (2026-10-27): a draft heavy node WITH its artifact on disk is
    pre-grant judging -- it now records. A deprecated one is still refused regardless of its
    artifact: a deprecated node is never a candidate for `mission grant`."""
    mroot = _campaign(tmp_path / "draft", status="draft")
    log = tmp_path / "draft-pass.log"
    log.write_text(_header(mroot) + _one_part("Demo_hv", PASS_LOG))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    node = load_node(mroot / "demo" / "nodes" / "Demo_hv.toml")
    assert node.rejudge is not None and node.rejudge.verdict == "pass"
    assert node.status == "draft"              # rejudge-record never flips status itself

    mroot2 = _campaign(tmp_path / "dep", status="deprecated",
                       deprecated_reason="superseded by a later node")
    log2 = tmp_path / "dep-pass.log"
    log2.write_text(_header(mroot2) + _one_part("Demo_hv", PASS_LOG))
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
        shutil.copytree(examples_lean, troot / "examples" / "zeta_reflection" / "lean",
                        ignore=shutil.ignore_patterns(".lake"))   # sources only: .lake is ~12 GB
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


def test_rejudge_record_then_grant_status_closes_the_loop(tmp_path, one_part):
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
    log.write_text(f"REJUDGE-HEADER node=Loop_hv artifact_sha256={art_sha}\n"
                   + _one_part("Loop_hv", PASS_LOG))
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


def test_grant_status_refutation_of_heavy_node_not_blocked_by_missing_rejudge(tmp_path):
    """Controller ruling 7 (2026-10-27): the re-judge check in `grant_status` is scoped to a
    grant that would set `proved`. A heavy node correctly granted `refuted` must not be
    blocked by it -- a refutation artifact has no theorem for nanoda to replay, so it can
    never produce a passing re-judge log; model on
    test_gate_refuted_via_refutation_statement in test_missions_verify.py."""
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = MissionManifest(
        name="Demo.refute", title="Demo Campaign", description="synthetic",
        goal_node="Demo_hv4", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, root / "mission.toml")

    node_stmt = "theorem lemma_hv4 : False"
    refutation = "theorem lemma_hv4_neg : ¬False"
    node = Node(
        name="Demo.hv4", title="heavy node to be refuted", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Demo_hv4",
        proof=Proof(artifact="proof/Demo_hv4.lean", artifact_kind="lean_module",
                   via="direct", closure_clean=False),
        readback=Readback(text="read-back of Demo.hv4, rendering the formal statement in "
                               "the auditor's own words at some length so it clears the "
                               "read-back floor", auditor="test-auditor", date="2026-10-27"),
        refutation_statement=refutation,
        heavy_certificates=True, created="2026-10-27", updated="2026-10-27",
    )
    save_node(node, root / "nodes" / "Demo_hv4.toml")
    write_statement(root, node, node_stmt, manifest)

    artifact_path = root / "proof" / "Demo_hv4.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    # Artifact matches the refutation statement (NOT the original proposition).
    artifact_path.write_text(f"{refutation} := by\n  simp\n")

    campaign = load_campaign(root)
    # No [rejudge] record at all -- would block a grant to 'proved', must not block 'refuted'.
    assert load_node(root / "nodes" / "Demo_hv4.toml").rejudge is None
    result = grant_status(campaign, "Demo_hv4", identity="gate@test", session="gate-session")
    assert result.status == "refuted"
    assert load_node(root / "nodes" / "Demo_hv4.toml").status == "refuted"


# ---------------------------------------------------------------------------
# Final-fix 1: deleting `heavy_certificates` must not bypass the re-judge gate. A node whose
# `[comparator]` record says the judge ran with nanoda OFF (second_kernel = "none: ...") was
# judged Lean-kernel-only, so it is treated as heavy whether or not the flag is still there.
# ---------------------------------------------------------------------------

def _lean_only_record(art_sha: str, second_kernel: str = "none: heavy_certificates"):
    from telperion.missions.schema import ComparatorRecord
    return ComparatorRecord(run_id="1", date="2026-10-27", artifact_sha256=art_sha,
                            theorem="t", second_kernel=second_kernel)


def test_flagless_lean_only_node_needs_rejudge(tmp_path):
    from telperion.missions.provenance import rejudge_problem, sha256_file
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    node = dataclasses.replace(node, comparator=_lean_only_record(
        sha256_file(tmp_path / node.proof.artifact)))
    assert "Lean-kernel-only" in rejudge_problem(tmp_path, node)


def test_flagless_lean_only_node_with_current_pass_is_ok(tmp_path):
    from telperion.missions.provenance import (
        closure_digest, closure_files, rejudge_problem, sha256_file,
    )
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    sha = sha256_file(tmp_path / node.proof.artifact)
    # Step 0b Task 1 (2026-10-28): "current" now also means closure-bound. This fixture's
    # artifact is on no judge island, so its closure is just the artifact file itself.
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha, verdict="pass",
                        log_sha256="c" * 64,
                        closure_sha256=closure_digest(tmp_path, node),
                        closure_files=len(closure_files(tmp_path, node)))
    node = dataclasses.replace(node, comparator=_lean_only_record(sha), rejudge=rec)
    assert rejudge_problem(tmp_path, node) == ""


def test_non_heavy_nanoda_node_unaffected(tmp_path):
    from telperion.missions.provenance import rejudge_problem, sha256_file
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    node = dataclasses.replace(node, comparator=_lean_only_record(
        sha256_file(tmp_path / node.proof.artifact), second_kernel="nanoda"))
    assert rejudge_problem(tmp_path, node) == ""


def _verify_copy(tmp_path, campaign, edit):
    """Copy a real campaign (laid out as `_verify_copy_without_rejudge` explains), apply
    `edit(nodes_dir)`, and return verify_campaign's errors on the copy."""
    import shutil
    troot = tmp_path / "telperion"
    dst = troot / "missions" / campaign
    shutil.copytree(TELPERION_ROOT / "missions" / campaign, dst)
    for isl in ("zeta_reflection", "rvm_bridge"):
        src = TELPERION_ROOT / "examples" / isl / "lean"
        if src.is_dir():
            shutil.copytree(src, troot / "examples" / isl / "lean",
                            ignore=shutil.ignore_patterns(".lake"))   # .lake is 9-12 GB
    edit(dst / "nodes")
    return verify_campaign(dst).errors


_FLAGLESS = "MM_weil_positivity_prime_free_window"   # proved, per-PR, second_kernel = none


def test_verify_rejects_flagless_lean_only_node_without_rejudge(tmp_path):
    def edit(nd):
        p = nd / f"{_FLAGLESS}.toml"
        n = load_node(p)
        assert n.comparator.second_kernel.startswith("none")
        save_node(dataclasses.replace(n, heavy_certificates=False, rejudge=None), p)
    errors = _verify_copy(tmp_path, "mirrormere", edit)
    assert any(_FLAGLESS in e and "re-judge" in e for e in errors), errors


def test_verify_accepts_flagless_lean_only_node_with_current_rejudge(tmp_path):
    def edit(nd):
        p = nd / f"{_FLAGLESS}.toml"
        n = load_node(p)
        assert n.rejudge is not None and n.rejudge.verdict == "pass"
        save_node(dataclasses.replace(n, heavy_certificates=False), p)
    errors = _verify_copy(tmp_path, "mirrormere", edit)
    assert not any(_FLAGLESS in e and "re-judge" in e for e in errors), errors


def test_verify_normal_nanoda_node_needs_no_rejudge(tmp_path):
    """A proved node judged with nanoda ON (second_kernel = "nanoda", no flag) is unaffected."""
    picked = []

    def edit(nd):
        for p in sorted(nd.glob("*.toml")):
            n = load_node(p)
            if (n.status == "proved" and not n.heavy_certificates and n.rejudge is None
                    and n.comparator is not None and n.comparator.second_kernel == "nanoda"):
                picked.append(p.stem)
        assert picked, "mirrormere has no proved nanoda-judged node to check"
    errors = _verify_copy(tmp_path, "mirrormere", edit)
    assert not any("re-judge" in e for e in errors), errors


def test_cli_rejudge_record_accepts_flagless_lean_only_node(tmp_path, one_part):
    """The CLI gate uses the same predicate as rejudge_problem: no flag, but a [comparator]
    record with second_kernel = "none: ..." -> a re-judge may (and must) be recorded."""
    mroot = _campaign(tmp_path, heavy=False)
    p = mroot / "demo" / "nodes" / "Demo_hv.toml"
    save_node(dataclasses.replace(load_node(p), comparator=_lean_only_record(
        _artifact_sha256(mroot))), p)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot) + _one_part("Demo_hv", PASS_LOG))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 0
    assert load_node(p).rejudge.verdict == "pass"


# ---------------------------------------------------------------------------
# Final-fix 2: the verdict must cover EVERY part of the node, and accept lines must be whole
# lines. rejudge_queue.sh writes one block per Comparator part, each opened by
#   ==================== REJUDGE-PART i/n <part-slug> (comparator exit rc, peak K kB) ====================
# and `rejudge-record` renders the node's bundle (nanoda forced on) to learn n and the slugs.
# ---------------------------------------------------------------------------

def _part(i: int, n: int, slug: str, body: str, rc: int = 0) -> str:
    return (f"==================== REJUDGE-PART {i}/{n} {slug} (comparator exit {rc}, "
            f"peak 123 kB) ====================\n" + body)


def _parts_log(slugs, bodies=None, header: str = "") -> str:
    bodies = bodies or [PASS_LOG] * len(slugs)
    return header + "".join(_part(i, len(slugs), s, b) for i, (s, b) in
                            enumerate(zip(slugs, bodies), 1))


H8000 = ["AND_ladder_h8000_kernel__compose"] + [
    f"AND_ladder_h8000_kernel__seg_h{h}" for h in range(1000, 9000, 1000)]


def test_partial_multipart_log_fails():
    """Part 1 passed; part 2 was killed. Every accept line still appears once in the log."""
    from telperion.missions.rejudge import rejudge_log_verdict
    killed = "Building MissionChallenges.X__seg\nRunning nanoda kernel on solution\nKilled: 9\n"
    log = _parts_log(["X__a", "X__b"], [PASS_LOG, killed])
    assert parse_comparator_log(log) == "pass"          # the old whole-log rule was fooled
    assert rejudge_log_verdict(log, ["X__a", "X__b"]) == "fail"


def test_accept_strings_on_one_line_fail():
    one = ("Lean default kernel accepts the solution Nanoda kernel accepts the solution "
           "Your solution is okay!\n")
    from telperion.missions.rejudge import rejudge_log_verdict
    assert parse_comparator_log(one) == "fail"
    assert rejudge_log_verdict(_parts_log(["X"], [one]), ["X"]) == "fail"


def test_accept_line_must_be_whole_line():
    from telperion.missions.rejudge import rejudge_log_verdict
    body = PASS_LOG.replace("Your solution is okay!", "Your solution is okay! (not really)")
    assert parse_comparator_log(body) == "fail"
    assert rejudge_log_verdict(_parts_log(["X"], [body]), ["X"]) == "fail"
    # leading/trailing whitespace is stripped before the comparison
    assert parse_comparator_log("  " + PASS_LOG.replace("\n", "  \n")) == "pass"


def test_correct_one_part_log_passes():
    from telperion.missions.rejudge import rejudge_log_verdict
    assert rejudge_log_verdict(_parts_log(["X"]), ["X"]) == "pass"


def test_correct_nine_part_log_passes():
    from telperion.missions.rejudge import rejudge_log_verdict
    assert rejudge_log_verdict(_parts_log(H8000), H8000) == "pass"


def test_wrong_part_count_or_shape_fails():
    from telperion.missions.rejudge import rejudge_log_verdict
    assert rejudge_log_verdict(_parts_log(H8000[:8]), H8000) == "fail"     # 8 of 9 parts
    assert rejudge_log_verdict(PASS_LOG, ["X"]) == "fail"                  # no delimiter at all
    assert rejudge_log_verdict(_parts_log(["X", "X"]), ["X"]) == "fail"    # extra part
    assert rejudge_log_verdict(_parts_log(["Y"]), ["X"]) == "fail"         # wrong part slug
    swapped = _parts_log([H8000[1], H8000[0]] + H8000[2:])
    assert rejudge_log_verdict(swapped, H8000) == "fail"                   # wrong order
    nonzero = _part(1, 1, "X", PASS_LOG, rc=137)
    assert rejudge_log_verdict(nonzero, ["X"]) == "fail"                   # comparator exit != 0
    garbled = PASS_LOG + "==== REJUDGE-PART 1/1 X ====\n" + PASS_LOG
    assert rejudge_log_verdict(garbled, ["X"]) == "fail"                   # malformed delimiter
    errline = _parts_log(["X"]) + "error: rejudge_queue: compose verify did not pass (exit 1)\n"
    assert rejudge_log_verdict(errline, ["X"]) == "fail"                   # error line anywhere
    assert rejudge_log_verdict(_parts_log(["X"]), []) == "fail"            # zero expected parts


def test_expected_part_slugs_renders_real_h8000_as_nine_parts():
    from telperion.missions.rejudge import expected_part_slugs
    camp = TELPERION_ROOT / "missions" / "anduril"
    n = load_node(camp / "nodes" / "AND_ladder_h8000_kernel.toml")
    assert expected_part_slugs(camp, n, "AND_ladder_h8000_kernel") == H8000


def test_expected_part_slugs_missing_island_raises(tmp_path):
    from telperion.missions.rejudge import RejudgeSetupError, expected_part_slugs
    mroot = _campaign(tmp_path)
    camp = mroot / "demo"
    with pytest.raises(RejudgeSetupError):
        expected_part_slugs(camp, load_node(camp / "nodes" / "Demo_hv.toml"), "Demo_hv")


def test_cli_bundle_render_failure_exit2_no_record(tmp_path, capsys):
    """(d): the synthetic campaign's artifact is on no island, so the bundle cannot be
    rendered and the expected part count is unknown -> refuse, write nothing."""
    mroot = _campaign(tmp_path)
    log = tmp_path / "pass.log"
    log.write_text(_header(mroot) + _part(1, 1, "Demo_hv", PASS_LOG))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    assert "cannot render" in capsys.readouterr().err
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge is None


def test_cli_partial_multipart_log_records_fail(tmp_path, monkeypatch, capsys):
    import telperion.missions.rejudge as rj
    monkeypatch.setattr(rj, "expected_part_slugs", lambda *a, **k: ["Demo_hv__a", "Demo_hv__b"])
    mroot = _campaign(tmp_path)
    log = tmp_path / "partial.log"
    log.write_text(_parts_log(["Demo_hv__a", "Demo_hv__b"], [PASS_LOG, "Killed: 9\n"],
                              header=_header(mroot)))
    rc = _cli(mroot, "rejudge-record", "Demo_hv", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 1
    assert load_node(mroot / "demo" / "nodes" / "Demo_hv.toml").rejudge.verdict == "fail"


REAL_REJUDGE = Path.home() / "telperion-tools" / "rejudge"
if not REAL_REJUDGE.is_dir():                     # tests run as root; the logs are the owner's
    REAL_REJUDGE = Path("/Users/peterwmurphy/telperion-tools/rejudge")
REAL_NODES = [("mirrormere", "MM_weil_positivity_prime_free_window"),
              ("mirrormere", "MM_weil_positivity_window_two_fifths"),
              ("mirrormere", "MM_hodge1_window5493"),
              ("mirrormere", "MM_hodge1_rh_reduction"),
              ("mirrormere", "MM_hodge1_window45"),
              ("anduril", "AND_ladder_h8000_kernel"),
              ("anduril", "AND_ladder_h11000_kernel")]


@pytest.mark.parametrize("camp,slug", REAL_NODES)
def test_real_rejudge_logs_still_pass(camp, slug):
    """Regression: the 7 logs behind the committed [rejudge] records still read as PASS
    under the per-part rule, against the part count their bundles render today, and their
    bytes are the ones each record's log_sha256 names."""
    from telperion.missions.rejudge import expected_part_slugs, rejudge_log_verdict
    log = REAL_REJUDGE / slug / "rejudge.log"
    if not log.is_file():
        pytest.skip(f"{log} absent")
    croot = TELPERION_ROOT / "missions" / camp
    node = load_node(croot / "nodes" / f"{slug}.toml")
    raw = log.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == node.rejudge.log_sha256
    slugs = expected_part_slugs(croot, node, slug)
    assert len(slugs) == (9 if slug == "AND_ladder_h8000_kernel" else 1)
    assert rejudge_log_verdict(raw.decode(errors="replace"), slugs) == "pass"


# ---------------------------------------------------------------------------
# Closure digest (step 0b Task 1, 2026-10-28): a [rejudge] record now binds to the
# artifact's WHOLE import closure, not only the top-level file -- a ladder capstone's
# certificates live in imported modules.
# ---------------------------------------------------------------------------

def _closure_island(tmp_path: Path, *, sibling: bool = False):
    """A minimal real judge island under `<tmp_path>/telperion/examples/isl/lean`, whose
    artifact `A.lean` imports `B.lean` in the SAME island. With `sibling=True`, `A.lean`
    instead imports `Xi`, declared only in a `path`-required sibling package under
    `examples/sib/lean/core` -- the zeta_reflection -> zzl_core shape (Review Focus 1).
    Returns (campaign_root, node); campaign_root need not exist on disk for
    `closure_files`/`closure_digest`, which only resolve paths.
    """
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    if sibling:
        core = tel / "examples" / "sib" / "lean" / "core"
        core.mkdir(parents=True)
        (core / "lakefile.toml").write_text('name = "core"\n')
        (core / "Xi.lean").write_text("theorem xi : True := trivial\n")
        (lean / "lakefile.toml").write_text(
            'name = "Isl"\n\n[[require]]\nname = "core"\npath = "../../sib/lean/core"\n\n'
            '[[lean_lib]]\nname = "A"\n')
        (lean / "A.lean").write_text("import Xi\ntheorem a : True := trivial\n")
    else:
        (lean / "lakefile.toml").write_text(
            'name = "Isl"\n\n[[lean_lib]]\nname = "A"\n\n[[lean_lib]]\nname = "B"\n')
        (lean / "A.lean").write_text("import B\ntheorem a : True := trivial\n")
        (lean / "B.lean").write_text("theorem b : True := trivial\n")
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)          # so "camp / '../../examples/...'" traverses on disk
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True,
    )
    return camp, node


def test_digest_changes_when_imported_module_changes(tmp_path):
    from telperion.missions.provenance import closure_digest
    camp, node = _closure_island(tmp_path)
    before = closure_digest(camp, node)
    (tmp_path / "telperion" / "examples" / "isl" / "lean" / "B.lean").write_text(
        "theorem b : True := trivial  -- changed\n")
    after = closure_digest(camp, node)
    assert before != after            # A itself is untouched; its IMPORT changed


def test_digest_stable(tmp_path):
    from telperion.missions.provenance import closure_digest
    camp, node = _closure_island(tmp_path)
    assert closure_digest(camp, node) == closure_digest(camp, node)


def test_digest_covers_path_required_sibling(tmp_path):
    """Review Focus 1: a closure file outside the island. The digest must cover a
    required-package file the artifact imports, not only the island's own directory."""
    from telperion.missions.provenance import closure_digest, closure_files
    camp, node = _closure_island(tmp_path, sibling=True)
    files = closure_files(camp, node)
    xi = (tmp_path / "telperion" / "examples" / "sib" / "lean" / "core" / "Xi.lean").resolve()
    assert xi in files
    before = closure_digest(camp, node)
    xi.write_text("theorem xi : True := trivial  -- changed\n")
    after = closure_digest(camp, node)
    assert before != after


# ---------------------------------------------------------------------------
# Fix round 1 (Controller Ruling 0b-2, 2026-10-28): the first cut resolved a module
# under a candidate package directory by checking `D/module_path.lean` directly, which
# ignores `srcDir`. zzl_core declares `srcDir = ".."`, so its modules live one directory
# ABOVE zzl_core/ itself; the first cut silently read them as "external" and dropped
# them (and everything they import). Fixed by reusing coverage.py's srcDir-aware
# package model, and by FAILING CLOSED on any import that still cannot be resolved and
# is not a known library root.
# ---------------------------------------------------------------------------

def test_digest_covers_srcdir_sibling(tmp_path):
    """A sibling package whose lakefile declares `srcDir = ".."` (zzl_core's exact
    shape): its modules live OUTSIDE the package's own directory, and must still
    resolve into the closure -- along with that module's own import."""
    from telperion.missions.provenance import closure_files
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text(
        'name = "Isl"\n\n[[require]]\nname = "core"\npath = "../../sib/lean/core"\n\n'
        '[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text("import Xi\ntheorem a : True := trivial\n")
    core = tel / "examples" / "sib" / "lean" / "core"
    core.mkdir(parents=True)
    (core / "lakefile.toml").write_text(
        'name = "core"\nsrcDir = ".."\n\n[[lean_lib]]\nname = "Xi"\n')
    # srcDir = ".." : Xi.lean lives one directory ABOVE `core/`, not inside it -- the
    # exact shape of `examples/zeta_zero_localization/lean/zzl_core/lakefile.toml`.
    sib_root = tel / "examples" / "sib" / "lean"
    (sib_root / "Xi.lean").write_text("import Yi\ntheorem xi : True := trivial\n")
    (sib_root / "Yi.lean").write_text("theorem yi : True := trivial\n")
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True,
    )
    names = {f.name for f in closure_files(camp, node)}
    assert "Xi.lean" in names
    assert "Yi.lean" in names        # Xi's own import, transitively


def test_unresolvable_import_raises(tmp_path):
    """An import that resolves to no local file and is not a known library root must
    raise ClosureError, not silently vanish from the closure -- this is precisely how
    the srcDir bug (above) went unnoticed."""
    from telperion.missions.provenance import ClosureError, closure_files
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "Isl"\n\n[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text("import Ghost\ntheorem a : True := trivial\n")
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True,
    )
    with pytest.raises(ClosureError, match="Ghost"):
        closure_files(camp, node)


def test_core_root_import_is_excluded_not_an_error(tmp_path):
    """Controller Ruling 0b-3: a CORE_ROOT import (Init/Lean/Std/Lake) is excluded
    from the closure WITHOUT being an error and WITHOUT needing any manifest at all --
    it is the toolchain, never a `lake-manifest.json` dependency."""
    from telperion.missions.provenance import closure_files
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "Isl"\n\n[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text("import Init.Core\ntheorem a : True := trivial\n")
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True,
    )
    assert [f.name for f in closure_files(camp, node)] == ["A.lean"]


def _write_manifest(pkg_dir: Path, packages: list) -> None:
    import json
    (pkg_dir / "lake-manifest.json").write_text(json.dumps(
        {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": packages}))


def test_external_manifest_dependency_pins_its_rev(tmp_path):
    """Controller Ruling 0b-3: a non-path `lake-manifest.json` dependency is external
    (never a closure FILE -- its own `Foo.lean` is excluded), but its `rev` is PINNED
    in the digest: bumping it must change the digest even though no closure .lean file
    changed."""
    from telperion.missions.provenance import closure_digest, closure_files
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "Isl"\n\n[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text("import Foo\ntheorem a : True := trivial\n")
    _write_manifest(lean, [
        {"type": "git", "name": "Foo", "rev": "abc123", "url": "https://example/Foo"},
    ])
    foo_dir = lean / ".lake" / "packages" / "Foo"
    foo_dir.mkdir(parents=True)
    (foo_dir / "lakefile.toml").write_text('name = "Foo"\n\n[[lean_lib]]\nname = "Foo"\n')
    (foo_dir / "Foo.lean").write_text("theorem foo : True := trivial\n")
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True,
    )
    assert [f.name for f in closure_files(camp, node)] == ["A.lean"]   # Foo excluded
    before = closure_digest(camp, node)
    _write_manifest(lean, [
        {"type": "git", "name": "Foo", "rev": "def456", "url": "https://example/Foo"},
    ])
    after = closure_digest(camp, node)
    assert before != after


def test_import_matching_no_manifest_package_raises(tmp_path):
    """An import whose root matches neither a local package, a core root, nor any
    non-path manifest dependency must still raise -- having SOME manifest present
    (for an UNRELATED dependency) must not make an unrelated import pass through
    silently."""
    from telperion.missions.provenance import ClosureError, closure_files
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "Isl"\n\n[[lean_lib]]\nname = "A"\n')
    (lean / "A.lean").write_text("import Ghost\ntheorem a : True := trivial\n")
    _write_manifest(lean, [{"type": "git", "name": "Foo", "rev": "abc123"}])
    camp = tel / "missions" / "demo"
    camp.mkdir(parents=True)
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True,
    )
    with pytest.raises(ClosureError, match="Ghost"):
        closure_files(camp, node)


@pytest.mark.parametrize("slug,filename", [
    ("AND_ladder_h8000_kernel", "ZetaZeroConfinement.lean"),
    ("AND_ladder_h8000_kernel", "DlvpZetaZeroFree.lean"),
    ("AND_ladder_h11000_kernel", "ZetaZeroConfinement.lean"),
    ("AND_ladder_h11000_kernel", "DlvpZetaZeroFree.lean"),
    ("AND_g2_reflected_band", "XiLineZeros.lean"),
])
def test_real_closures_complete(slug, filename):
    """Controller Ruling 0b-2: on the REAL registry, the srcDir fix must actually
    recover the modules the first cut dropped. `ZetaZeroConfinement.lean` and
    `DlvpZetaZeroFree.lean` are reached from the h8000/h11000 ladders only through
    zzl_core's `srcDir = ".."` remap (and zzl_core's own require of zero_free_bridge);
    `XiLineZeros.lean` is reached from AND_g2_reflected_band's artifact through
    CheckBand.lean the same way."""
    from telperion.missions.provenance import closure_files
    from telperion.missions.registry import load_campaign
    anduril = TELPERION_ROOT / "missions" / "anduril"
    if not anduril.is_dir():
        pytest.skip("real repo layout absent")
    camp = load_campaign(anduril)
    node = camp.nodes[slug]
    files = closure_files(anduril, node)
    assert any(f.name == filename for f in files), (slug, filename, sorted(f.name for f in files))


def test_record_without_digest_is_a_problem(tmp_path):
    from telperion.missions.provenance import rejudge_problem, sha256_file
    camp, node = _closure_island(tmp_path)
    art = camp / node.proof.artifact
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="a" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha256_file(art),
                        verdict="pass", log_sha256="c" * 64)        # no closure_sha256
    node = dataclasses.replace(node, rejudge=rec)
    problem = rejudge_problem(camp, node)
    assert "closure" in problem and "back-fill" in problem


def test_stale_closure_fails_verify(tmp_path):
    """The exact check `verify_campaign` makes for a proved heavy node (`verify.py`
    calls `rejudge_problem` directly): a [rejudge] record whose closure digest no longer
    matches the CURRENT import closure is a problem, even though the artifact file
    itself -- and its own sha256 -- is unchanged (Review Focus 4's mirror: a change the
    back-fill rule must catch, caught here at verify time instead of back-fill time)."""
    from telperion.missions.provenance import closure_digest, rejudge_problem, sha256_file
    camp, node = _closure_island(tmp_path)
    art = camp / node.proof.artifact
    rec = RejudgeRecord(date="2026-10-28", machine="m", nanoda_rev="a" * 40,
                        comparator_tag="v4.32.0", artifact_sha256=sha256_file(art),
                        verdict="pass", log_sha256="c" * 64,
                        closure_sha256=closure_digest(camp, node), closure_files=2)
    node = dataclasses.replace(node, rejudge=rec)
    assert rejudge_problem(camp, node) == ""          # current as recorded
    (tmp_path / "telperion" / "examples" / "isl" / "lean" / "B.lean").write_text(
        "theorem b : True := trivial  -- changed after the re-judge\n")
    problem = rejudge_problem(camp, node)             # A.lean itself is still untouched
    assert "closure" in problem and "back-fill" in problem


def test_header_closure_mismatch_refused(tmp_path, one_part, capsys):
    """`mission rejudge-record` refuses (exit 2, no write) when the log's
    REJUDGE-HEADER names a closure_sha256 that does not match the artifact's CURRENT
    import closure -- the same rule as a stale artifact_sha256."""
    camp, node = _closure_island(tmp_path)
    mroot = camp.parent
    (camp / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.hv", title="Demo Campaign", description="synthetic",
        goal_node="HV_x", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, camp / "mission.toml")
    save_node(node, camp / "nodes" / "HV_x.toml")
    art = camp / node.proof.artifact
    sha = hashlib.sha256(art.read_bytes()).hexdigest()
    log = tmp_path / "pass.log"
    log.write_text(f"REJUDGE-HEADER node=HV_x artifact_sha256={sha} closure_sha256={'0' * 64}\n"
                  + _one_part("HV_x", PASS_LOG))
    rc = _cli(mroot, "rejudge-record", "HV_x", "--campaign", "demo", "--log", str(log),
             "--comparator-tag", "v4.32.0")
    assert rc == 2
    err = capsys.readouterr().err
    assert "closure_sha256" in err
    assert load_node(camp / "nodes" / "HV_x.toml").rejudge is None


# ---------------------------------------------------------------------------
# Back-fill (step 0b Task 2, 2026-10-28): closure_sha256 may be written for a node
# WITHOUT re-judging it, but only when git proves its closure files are unchanged.
# ---------------------------------------------------------------------------

def _git(repo: Path, *args: str) -> str:
    import subprocess
    out = subprocess.run(["git", *args], cwd=str(repo), capture_output=True, text=True)
    assert out.returncode == 0, (args, out.stdout, out.stderr)
    return out.stdout.strip()


def _backfill_repo(tmp_path: Path):
    """A tiny git repo at *tmp_path*, with a judge island (`A.lean` imports `B.lean`)
    and one campaign node ("demo"/"HV_x") carrying a passing [rejudge] record with no
    closure_sha256 -- exactly the shape of the 7 real heavy nodes before back-fill.
    Returns (mroot, campaign_root, since, repo)."""
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.email", "t@t")
    _git(tmp_path, "config", "user.name", "t")
    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text(
        'name = "Isl"\n\n[[lean_lib]]\nname = "A"\n\n[[lean_lib]]\nname = "B"\n')
    (lean / "A.lean").write_text("import B\ntheorem a : True := trivial\n")
    (lean / "B.lean").write_text("theorem b : True := trivial\n")
    camp = tel / "missions" / "demo"
    (camp / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.hv", title="Demo Campaign", description="synthetic",
        goal_node="HV_x", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, camp / "mission.toml")
    art = lean / "A.lean"
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40,
                        comparator_tag="v4.32.0",
                        artifact_sha256=hashlib.sha256(art.read_bytes()).hexdigest(),
                        verdict="pass", log_sha256="c" * 64,
                        note="local macOS re-judge, nanoda ON")
    node = Node(
        name="HV.x", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="S",
        proof=Proof("../../examples/isl/lean/A.lean", "lean_module", "direct"),
        heavy_certificates=True, rejudge=rec,
    )
    save_node(node, camp / "nodes" / "HV_x.toml")
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-q", "-m", "initial")
    since = _git(tmp_path, "rev-parse", "HEAD")
    return tel / "missions", camp, since, tmp_path


def test_backfill_writes_when_unchanged(tmp_path):
    from telperion.missions.provenance import closure_digest
    mroot, camp, since, repo = _backfill_repo(tmp_path)
    node = load_node(camp / "nodes" / "HV_x.toml")
    rc = _cli(mroot, "rejudge-backfill-closure", "HV_x", "--campaign", "demo",
             "--since", since)
    assert rc == 0
    n2 = load_node(camp / "nodes" / "HV_x.toml")
    assert n2.rejudge.closure_sha256 == closure_digest(camp, node)
    assert n2.rejudge.closure_files == 2            # A.lean + B.lean
    assert "closure back-filled" in n2.rejudge.note
    # Ruling 0b-9: the git clause names the support files (lakefiles, manifests,
    # lean-toolchain) the rule also covered -- here the island's lakefile.toml.
    assert f"no change to 2 closure files and 1 support files since {since}" in n2.rejudge.note
    assert n2.rejudge.note.startswith("local macOS re-judge, nanoda ON; ")


def test_backfill_refused_on_change(tmp_path, capsys):
    """Review Focus 4: a back-fill on a node whose closure changed must be refused and
    the node re-judged, never back-filled."""
    mroot, camp, since, repo = _backfill_repo(tmp_path)
    (repo / "telperion" / "examples" / "isl" / "lean" / "B.lean").write_text(
        "theorem b : True := trivial  -- edited after the re-judge\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "edit B after the re-judge")
    rc = _cli(mroot, "rejudge-backfill-closure", "HV_x", "--campaign", "demo",
             "--since", since)
    assert rc == 2
    err = capsys.readouterr().err
    assert "re-judge" in err.lower() and "back-fill" in err.lower()
    assert load_node(camp / "nodes" / "HV_x.toml").rejudge.closure_sha256 == ""


def test_backfill_refused_on_dirty_closure_file(tmp_path, capsys):
    """The other half of the rule: an UNCOMMITTED edit refuses just as a committed one
    does (`git status --porcelain`, not only `git log`)."""
    mroot, camp, since, repo = _backfill_repo(tmp_path)
    (repo / "telperion" / "examples" / "isl" / "lean" / "B.lean").write_text(
        "theorem b : True := trivial  -- dirty, uncommitted\n")
    rc = _cli(mroot, "rejudge-backfill-closure", "HV_x", "--campaign", "demo",
             "--since", since)
    assert rc == 2
    err = capsys.readouterr().err
    assert "dirty" in err.lower()
    assert load_node(camp / "nodes" / "HV_x.toml").rejudge.closure_sha256 == ""


# ---------------------------------------------------------------------------
# Controller Ruling 0b-9 (2026-10-28), Fix 4: lean-toolchain and lakefile CONTENT are in
# the digest; lean-toolchain is in the back-fill git rule; the re-bind note takes --reason.
# ---------------------------------------------------------------------------

def test_digest_covers_lean_toolchain(tmp_path):
    from telperion.missions.provenance import closure_digest
    camp, node = _closure_island(tmp_path)
    tc = tmp_path / "telperion" / "examples" / "isl" / "lean" / "lean-toolchain"
    tc.write_text("leanprover/lean4:v4.32.0\n")
    before = closure_digest(camp, node)
    tc.write_text("leanprover/lean4:v4.33.0\n")
    assert closure_digest(camp, node) != before


def test_digest_covers_lakefile_content(tmp_path):
    """An edit to the lakefile that changes neither the closure set nor any pin (here a
    package option) must still move the digest."""
    from telperion.missions.provenance import closure_digest, closure_files
    camp, node = _closure_island(tmp_path)
    lf = tmp_path / "telperion" / "examples" / "isl" / "lean" / "lakefile.toml"
    files = closure_files(camp, node)
    before = closure_digest(camp, node)
    lf.write_text(lf.read_text().replace('name = "Isl"\n',
                                         'name = "Isl"\nmoreLeanArgs = ["-DmaxHeartbeats=0"]\n'))
    from telperion.missions import coverage
    coverage._package.cache_clear(); coverage._workspace.cache_clear()
    assert closure_files(camp, node) == files
    assert closure_digest(camp, node) != before


def test_digest_covers_path_required_lakefile_lean(tmp_path):
    """A path-required package with a `lakefile.lean` (which coverage.py does not parse)
    still has its lakefile and toolchain hashed."""
    from telperion.missions.provenance import closure_digest, closure_support_files
    camp, node = _closure_island(tmp_path)
    lean = tmp_path / "telperion" / "examples" / "isl" / "lean"
    dep = tmp_path / "telperion" / "examples" / "dep" / "lean"
    dep.mkdir(parents=True)
    (dep / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage dep\n")
    (lean / "lakefile.toml").write_text((lean / "lakefile.toml").read_text()
                                        + '\n[[require]]\nname = "dep"\npath = "../../dep/lean"\n')
    from telperion.missions import coverage
    coverage._package.cache_clear(); coverage._workspace.cache_clear()
    before = closure_digest(camp, node)
    assert (dep / "lakefile.lean").resolve() in closure_support_files(camp, node)
    (dep / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage dep where\n")
    assert closure_digest(camp, node) != before


def test_support_files_include_lean_toolchain(tmp_path):
    from telperion.missions.provenance import closure_support_files
    camp, node = _closure_island(tmp_path)
    tc = tmp_path / "telperion" / "examples" / "isl" / "lean" / "lean-toolchain"
    tc.write_text("leanprover/lean4:v4.32.0\n")
    assert tc.resolve() in closure_support_files(camp, node)


def test_backfill_refused_when_lean_toolchain_changed(tmp_path, capsys):
    """lean-toolchain is in the git rule now: bumping it after the re-judge refuses a
    back-fill/re-bind (it must be re-judged)."""
    mroot, camp, since, repo = _backfill_repo(tmp_path)
    (repo / "telperion" / "examples" / "isl" / "lean" / "lean-toolchain").write_text(
        "leanprover/lean4:v4.33.0\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "toolchain bump after the re-judge")
    rc = _cli(mroot, "rejudge-backfill-closure", "HV_x", "--campaign", "demo", "--since", since)
    assert rc == 2
    assert "commit(s) touched its closure" in capsys.readouterr().err


def test_rebind_requires_reason_and_replaces_earlier_rebind_clauses(tmp_path, capsys):
    from telperion.missions.provenance import closure_digest
    mroot, camp, since, repo = _backfill_repo(tmp_path)
    p = camp / "nodes" / "HV_x.toml"
    n = load_node(p)
    old = ("local macOS re-judge, nanoda ON; closure back-filled 2026-10-28 (git: x); "
           "closure re-bound 2026-10-28 after srcDir fix (git: y); "
           "closure re-bound 2026-10-28 after srcDir fix (git: y)")
    save_node(dataclasses.replace(n, rejudge=dataclasses.replace(
        n.rejudge, closure_sha256="0" * 64, note=old)), p)
    _git(repo, "add", "-A"); _git(repo, "commit", "-q", "-m", "seed a stale digest")
    args = ["rejudge-backfill-closure", "HV_x", "--campaign", "demo", "--since", since, "--rebind"]
    assert _cli(mroot, *args) == 2                                   # no --reason
    assert "--reason" in capsys.readouterr().err
    assert load_node(p).rejudge.closure_sha256 == "0" * 64
    assert _cli(mroot, *args, "--reason", "digest widened (test)") == 0
    rec = load_node(p).rejudge
    assert rec.closure_sha256 == closure_digest(camp, load_node(p))
    clauses = rec.note.split("; ")
    assert clauses[:2] == ["local macOS re-judge, nanoda ON",
                           "closure back-filled 2026-10-28 (git: x)"]
    assert len(clauses) == 3 and clauses[2].startswith("closure re-bound ")
    assert ": digest widened (test) (git: no change to 2 closure files" in clauses[2]
    assert "after srcDir fix" not in rec.note
    # a second identical re-bind does not pile up clauses
    _git(repo, "add", "-A"); _git(repo, "commit", "-q", "-m", "rebind")
    assert _cli(mroot, *args, "--reason", "digest widened (test)") == 0
    assert load_node(p).rejudge.note == rec.note

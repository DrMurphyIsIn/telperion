"""Tests for `telperion mission …` CLI subtree (Task M7).

Run from telperion/:
    python3 -m pytest tests/test_missions_cli.py -v
"""
from __future__ import annotations

import dataclasses
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, Readback, Proof,
    load_node, save_manifest, save_node, slug_of,
)
from telperion.missions.statements import write_statement  # noqa: E402

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _manifest() -> MissionManifest:
    return MissionManifest(
        name="Demo.goal",
        title="Demo Campaign",
        description="A synthetic demonstration campaign for testing the registry.",
        goal_node="Demo_goal",
        environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0",
        sources=(),
    )


def make_demo_root(tmp_path: Path) -> tuple[Path, Path]:
    """Copy demo fixture into tmproot/demo/; return (missions_root, campaign_root)."""
    missions_root = tmp_path / "missions"
    missions_root.mkdir()
    campaign_root = missions_root / "demo"
    shutil.copytree(DEMO_FIXTURE, campaign_root)
    return missions_root, campaign_root


# ---------------------------------------------------------------------------
# T1: status exit 0 and shows node slugs
# ---------------------------------------------------------------------------

def test_mission_status_exit0_shows_nodes(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "status", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo_lemma_a" in out
    assert "Demo_lemma_b" in out


def test_mission_status_all_campaigns(tmp_path, capsys):
    """Status with no campaign argument iterates all campaigns."""
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "status"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo" in out


# ---------------------------------------------------------------------------
# T2: open-leaves shows Demo.lemma_a (dotted name), hides after claim,
#     --all shows it again
# ---------------------------------------------------------------------------

def test_open_leaves_shows_lemma_a(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "open-leaves", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    # cmd prints node.name (dotted form) + title
    assert "Demo.lemma_a" in out


def test_open_leaves_hides_after_claim(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    # Claim Demo_lemma_a — pass --campaign because there is only one campaign
    main(["mission", "--missions-root", str(mroot), "claim", "Demo_lemma_a",
          "--campaign", "demo", "--session", "sess-1"])
    capsys.readouterr()

    rc = main(["mission", "--missions-root", str(mroot), "open-leaves", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo.lemma_a" not in out


def test_open_leaves_all_shows_claimed(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    main(["mission", "--missions-root", str(mroot), "claim", "Demo_lemma_a",
          "--campaign", "demo", "--session", "sess-1"])
    capsys.readouterr()

    rc = main(["mission", "--missions-root", str(mroot), "open-leaves", "demo", "--all"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo.lemma_a" in out


# ---------------------------------------------------------------------------
# T3: add creates node + statement files; duplicate add exits 1
# ---------------------------------------------------------------------------

def test_add_creates_node_and_statement(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "New.lemma_x",
        "--title", "New lemma X",
        "--kind", "lemma",
        "--statement", "theorem new_x : 1 = 1",
    ])
    assert rc == 0
    node_file = campaign_root / "nodes" / "New_lemma_x.toml"
    assert node_file.exists()
    node = load_node(node_file)
    assert node.status == "draft"
    assert node.title == "New lemma X"

    stmt_file = campaign_root / "lean" / "Statements" / "New_lemma_x.lean"
    assert stmt_file.exists()
    content = stmt_file.read_text()
    assert "new_x" in content


def test_add_duplicate_exits1(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    main([
        "mission", "--missions-root", str(mroot), "add", "demo", "Dup.lemma",
        "--title", "Dup", "--kind", "lemma", "--statement", "theorem dup : True",
    ])
    capsys.readouterr()
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "Dup.lemma",
        "--title", "Dup again", "--kind", "lemma", "--statement", "theorem dup2 : True",
    ])
    assert rc == 1


def test_add_with_deps(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "Dep.lemma_z",
        "--title", "Dep lemma Z", "--kind", "lemma",
        "--statement", "theorem dep_z : 1 = 1",
        "--deps", "Demo_lemma_a",
    ])
    assert rc == 0
    node = load_node(campaign_root / "nodes" / "Dep_lemma_z.toml")
    assert "Demo_lemma_a" in node.depends_on


def test_add_statement_file_missing_exits1(tmp_path, capsys):
    """--statement-file pointing at a nonexistent file must exit 1, not traceback."""
    mroot, _ = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "File.lemma",
        "--title", "File lemma", "--kind", "lemma",
        "--statement-file", str(tmp_path / "nonexistent.lean"),
    ])
    assert rc == 1
    out = capsys.readouterr().out + capsys.readouterr().err
    # Should not be an uncaught traceback (no "Traceback" in output)
    assert "Traceback" not in out


# ---------------------------------------------------------------------------
# T4: audit records readback AND promotes draft -> open;
#     auditing an already-open/proved node returns 1
# ---------------------------------------------------------------------------

def test_audit_records_readback_and_promotes(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    # Demo_lemma_b is draft; audit it
    rc = main([
        "mission", "--missions-root", str(mroot), "audit", "Demo_lemma_b",
        "--campaign", "demo",
        "--text", "Statement says lemma B holds.",
        "--auditor", "operator",
    ])
    assert rc == 0
    node = load_node(campaign_root / "nodes" / "Demo_lemma_b.toml")
    assert node.readback is not None
    assert node.readback.auditor == "operator"
    assert node.status == "open"


def test_audit_already_open_exits1_readback_recorded(tmp_path, capsys):
    """Auditing an already-open node: readback is durably written, promote_to_open
    raises SchemaError (non-draft status guard), audit exits 1, on-disk status stays open."""
    mroot, campaign_root = make_demo_root(tmp_path)
    # Demo_lemma_a is already open (has a readback in fixture)
    rc = main([
        "mission", "--missions-root", str(mroot), "audit", "Demo_lemma_a",
        "--campaign", "demo",
        "--text", "Re-audit of already-open node.",
        "--auditor", "operator",
    ])
    # promote_to_open rejects non-draft status -> exit 1
    assert rc == 1
    # Readback is durably written even though promote failed
    node = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node.readback is not None
    assert node.readback.text == "Re-audit of already-open node."
    # Status must NOT regress
    assert node.status == "open"


def test_audit_proved_node_exits1_status_preserved(tmp_path, capsys):
    """Auditing a proved node: readback is durably written, promote_to_open raises
    SchemaError (proved is not draft), audit exits 1, on-disk status stays proved."""
    import dataclasses as _dc
    mroot, campaign_root = make_demo_root(tmp_path)
    from telperion.missions.schema import Proof, save_node
    # Mutate Demo_lemma_a on disk to proved (simulates a previously verified node)
    node_path = campaign_root / "nodes" / "Demo_lemma_a.toml"
    existing = load_node(node_path)
    proved = _dc.replace(
        existing,
        status="proved",
        proof=Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", True),
    )
    save_node(proved, node_path)

    rc = main([
        "mission", "--missions-root", str(mroot), "audit", "Demo_lemma_a",
        "--campaign", "demo",
        "--text", "Audit of a proved node should not regress it.",
        "--auditor", "operator",
    ])
    assert rc == 1
    # Readback written durably
    on_disk = load_node(node_path)
    assert on_disk.readback is not None
    assert on_disk.readback.text == "Audit of a proved node should not regress it."
    # Status must stay proved — the guard blocked the regression
    assert on_disk.status == "proved"


# ---------------------------------------------------------------------------
# T5: link then grant with matching artifact flips to proved
# ---------------------------------------------------------------------------

def test_link_then_grant_proves(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    manifest = _manifest()

    from telperion.missions.registry import load_campaign
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    stmt = "theorem demo_lemma_a : 1 = 1"
    write_statement(campaign_root, node, stmt, manifest)

    artifact_rel = "proof/Demo_lemma_a.lean"
    artifact_path = campaign_root / artifact_rel
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(f"{stmt} := by rfl\n")

    rc = main([
        "mission", "--missions-root", str(mroot), "link", "Demo_lemma_a",
        "--campaign", "demo",
        "--artifact", artifact_rel,
        "--kind", "lean_module",
        "--via", "direct",
    ])
    assert rc == 0
    node_after_link = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node_after_link.status == "open"

    rc2 = main([
        "mission", "--missions-root", str(mroot), "grant", "Demo_lemma_a",
        "--campaign", "demo",
    ])
    assert rc2 == 0
    node_after_grant = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node_after_grant.status == "proved"


def test_grant_mismatched_artifact_exits1(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    manifest = _manifest()

    from telperion.missions.registry import load_campaign
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    stmt = "theorem demo_lemma_a : 1 = 1"
    write_statement(campaign_root, node, stmt, manifest)

    artifact_rel = "proof/Demo_lemma_a.lean"
    artifact_path = campaign_root / artifact_rel
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text("theorem completely_different : 2 = 3 := by simp\n")

    main([
        "mission", "--missions-root", str(mroot), "link", "Demo_lemma_a",
        "--campaign", "demo",
        "--artifact", artifact_rel,
        "--kind", "lean_module",
        "--via", "direct",
    ])
    capsys.readouterr()

    rc = main([
        "mission", "--missions-root", str(mroot), "grant", "Demo_lemma_a",
        "--campaign", "demo",
    ])
    assert rc == 1
    node_after = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node_after.status == "open"


# ---------------------------------------------------------------------------
# T6: verify exit 0 on clean fixture, exit 1 after injecting mismatch
# ---------------------------------------------------------------------------

def test_verify_clean_fixture(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "verify", "demo"])
    assert rc == 0


def test_verify_exits1_with_mismatch(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    manifest = _manifest()

    from telperion.missions.registry import load_campaign
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    stmt = "theorem demo_lemma_a : 1 = 1"
    write_statement(campaign_root, node, stmt, manifest)

    artifact_rel = "proof/Demo_lemma_a.lean"
    artifact_path = campaign_root / artifact_rel
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text("theorem wrong : 2 + 2 = 5 := by simp\n")

    proved_node = dataclasses.replace(
        node,
        status="proved",
        proof=Proof(
            artifact=artifact_rel,
            artifact_kind="lean_module",
            via="direct",
            closure_clean=True,
        ),
    )
    save_node(proved_node, campaign_root / "nodes" / "Demo_lemma_a.toml")

    rc = main(["mission", "--missions-root", str(mroot), "verify", "demo"])
    assert rc == 1


# ---------------------------------------------------------------------------
# T7: attempt appends a line to the ledger
# ---------------------------------------------------------------------------

def test_attempt_appends_line(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot),
        "attempt", "Demo_lemma_a",
        "--campaign", "demo",
        "--session", "sess-test",
        "--route", "direct_proof",
        "--verdict", "Stalled",
        "--detail", "Not enough time",
    ])
    assert rc == 0
    ledger = campaign_root / "attempts.jsonl"
    assert ledger.exists()
    import json
    lines = [json.loads(l) for l in ledger.read_text().splitlines() if l.strip()]
    assert len(lines) >= 1
    assert lines[-1]["verdict"] == "Stalled"
    assert lines[-1]["route"] == "direct_proof"
    # FIX 4: node field must be the normalised slug, not raw dotted name
    assert lines[-1]["node"] == "Demo_lemma_a"


# ---------------------------------------------------------------------------
# T8: release removes the claim
# ---------------------------------------------------------------------------

def test_release_removes_claim(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    main(["mission", "--missions-root", str(mroot), "claim", "Demo_lemma_a",
          "--campaign", "demo", "--session", "sess-rel"])
    claim_file = campaign_root / "claims" / "Demo_lemma_a.toml"
    assert claim_file.exists()

    rc = main(["mission", "--missions-root", str(mroot), "release", "Demo_lemma_a",
               "--campaign", "demo", "--session", "sess-rel"])
    assert rc == 0
    assert not claim_file.exists()


# ---------------------------------------------------------------------------
# T9: graph outputs DOT to stdout
# ---------------------------------------------------------------------------

def test_graph_outputs_dot(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "graph", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "digraph" in out
    assert "Demo_lemma_a" in out


# ---------------------------------------------------------------------------
# FIX 1: global slug resolution — no --campaign when slug is unambiguous
# ---------------------------------------------------------------------------

def test_claim_without_campaign_resolves(tmp_path, capsys):
    """claim succeeds without --campaign when slug is in exactly one campaign."""
    mroot, campaign_root = make_demo_root(tmp_path)
    # No --campaign; single campaign root contains Demo_lemma_a
    rc = main([
        "mission", "--missions-root", str(mroot),
        "claim", "Demo_lemma_a",
        "--session", "auto-sess",
    ])
    assert rc == 0
    claim_file = campaign_root / "claims" / "Demo_lemma_a.toml"
    assert claim_file.exists()


def test_attempt_without_campaign_resolves(tmp_path, capsys):
    """attempt succeeds without --campaign when slug is in exactly one campaign."""
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot),
        "attempt", "Demo_lemma_a",
        "--session", "auto-sess",
        "--route", "direct",
        "--verdict", "NoGo",
        "--detail", "Tried and failed",
    ])
    assert rc == 0
    ledger = campaign_root / "attempts.jsonl"
    assert ledger.exists()


def test_ambiguous_slug_exits1(tmp_path, capsys):
    """When same slug exists in two campaigns and --campaign is omitted, exit 1."""
    mroot, campaign_root_a = make_demo_root(tmp_path)
    # Create a second campaign with the same Demo_lemma_a node slug
    campaign_root_b = mroot / "other"
    shutil.copytree(campaign_root_a, campaign_root_b)

    rc = main([
        "mission", "--missions-root", str(mroot),
        "claim", "Demo_lemma_a",
        "--session", "sess-x",
    ])
    assert rc == 1
    out = capsys.readouterr().out
    # Both campaign names should appear in the message
    assert "demo" in out
    assert "other" in out

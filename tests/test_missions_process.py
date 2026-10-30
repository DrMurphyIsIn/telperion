"""Step 5 Task 1: campaign statement freeze (`FREEZE.toml`), `mission freeze`/`unfreeze`,
and the drift check (`freeze_problems`)."""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, load_node, save_manifest, save_node,
)
from telperion.missions.statements import statement_body, write_statement  # noqa: E402
from telperion.missions.verify import GateError, grant_status  # noqa: E402
from telperion.missions.process import (  # noqa: E402
    freeze, freeze_grant_problem, freeze_path, freeze_problems, unfreeze,
)
from telperion.cli import main  # noqa: E402


def _campaign(root: Path, names=("Node_A", "Node_B")) -> MissionManifest:
    """A tiny campaign: two draft nodes, each with a statement file written through the
    normal tooling (`statements.write_statement`), and nothing else -- enough for
    freeze/unfreeze/freeze_problems, which only look at statement bodies."""
    manifest = MissionManifest(
        name="Demo.goal", title="Demo Campaign", description="synthetic",
        goal_node=names[0], environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    (root / "nodes").mkdir(parents=True, exist_ok=True)
    save_manifest(manifest, root / "mission.toml")
    for i, name in enumerate(names):
        node = Node(name=name, title=f"title of {name}", kind="lemma", status="draft",
                    depends_on=(), statement_module=f"Statements.{name}")
        save_node(node, root / "nodes" / f"{name}.toml")
        write_statement(root, node, f"theorem thm_{name} : {i} = {i}", manifest)
    return manifest


# ---------------------------------------------------------------------------
# freeze
# ---------------------------------------------------------------------------

def test_freeze_records_hashes(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    doc = freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    assert doc["version"] == 1
    assert doc["frozen"] == "2026-10-28"
    assert doc["identity"] == "alice@example.com"
    assert doc["session"] == "s1"
    campaign = load_campaign(root)
    assert set(doc["statements"]) == set(campaign.nodes)
    for slug, node in campaign.nodes.items():
        expected = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
        assert doc["statements"][slug] == expected
    assert freeze_path(root).exists()
    assert freeze_problems(root) == []


def test_freeze_refuses_when_already_frozen(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    with pytest.raises(ValueError, match="already frozen"):
        freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")


def test_freeze_requires_identity_and_session(tmp_path):
    from telperion.missions.provenance import ProvenanceError
    root = tmp_path / "demo"
    _campaign(root)
    with pytest.raises(ProvenanceError):
        freeze(root, identity="", session="s1", date="2026-10-28")
    with pytest.raises(ProvenanceError):
        freeze(root, identity="alice@example.com", session="", date="2026-10-28")


# ---------------------------------------------------------------------------
# drift
# ---------------------------------------------------------------------------

def test_statement_drift_detected(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, "theorem thm_Node_A : 99 = 99", manifest)

    problems = freeze_problems(root)
    assert any("statement drift" in p and "Node_A" in p for p in problems)


# ---------------------------------------------------------------------------
# unfreeze
# ---------------------------------------------------------------------------

def test_unfreeze_bumps_and_clears_drift(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, "theorem thm_Node_A : 99 = 99", manifest)
    assert freeze_problems(root) != []

    doc = unfreeze(root, author="alice@example.com", reason="statement revised",
                   readback_identity="bob@example.com", date="2026-10-29")

    assert doc["version"] == 2
    assert doc["unfreeze"] == [{
        "version": 2, "date": "2026-10-29", "author": "alice@example.com",
        "reason": "statement revised", "readback_identity": "bob@example.com",
    }]
    # Re-hashed ALL statements, not only the drifted one.
    campaign = load_campaign(root)
    for slug, node in campaign.nodes.items():
        expected = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
        assert doc["statements"][slug] == expected
    assert freeze_problems(root) == []


def test_unfreeze_without_freeze_fails(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    with pytest.raises(ValueError, match="FREEZE"):
        unfreeze(root, author="alice@example.com", reason="r",
                readback_identity="bob@example.com", date="2026-10-29")


def test_self_readback_rejected(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    # Case-folded comparison, same as provenance.independence_of.
    with pytest.raises(ValueError):
        unfreeze(root, author="alice@example.com", reason="whatever",
                readback_identity="Alice@Example.com", date="2026-10-29")
    # Nothing was written on refusal.
    assert freeze_problems(root) == []


def test_rewritten_freeze_without_unfreeze_fails(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    # Hand-edit: bump the version without adding a matching [[unfreeze]] entry.
    path = freeze_path(root)
    text = path.read_text().replace("version = 1", "version = 2", 1)
    path.write_text(text)

    problems = freeze_problems(root)
    assert any("version 2" in p and "unfreeze" in p for p in problems)


# ---------------------------------------------------------------------------
# the grant gate
# ---------------------------------------------------------------------------

def test_post_cutoff_node_needs_freeze_to_grant(tmp_path):
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))  # passing [checks]; freeze is separate

    with pytest.raises(GateError, match="frozen"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"

    assert freeze_grant_problem(root, node) != ""


def test_pre_cutoff_campaign_without_freeze_ok(tmp_path):
    from test_missions_checks import _grant_campaign

    root = _grant_campaign(tmp_path, created="2026-10-01")
    assert not freeze_path(root).exists()
    assert freeze_problems(root) == []

    node = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                        session="gate-session")
    assert node.status == "proved"


def test_open_post_cutoff_node_without_freeze_not_flagged(tmp_path):
    """A draft/open post-cutoff node has not been granted yet, so there is nothing to
    freeze; only a PROVED post-cutoff node makes a missing FREEZE.toml a problem."""
    from test_missions_checks import _grant_campaign

    root = _grant_campaign(tmp_path, created="2026-10-29")
    assert freeze_problems(root) == []


def test_proved_post_cutoff_campaign_with_freeze_removed_flagged(tmp_path):
    """`freeze_grant_problem` already refuses to grant a post-cutoff node without a
    FREEZE.toml recording it; a proved node with none on disk means the record was
    removed after the fact (the hand-edit case `verify_campaign` re-checks)."""
    from test_missions_checks import _art_sha, _grant_campaign, _grant, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    assert _grant(root).status == "proved"
    assert freeze_path(root).exists()

    freeze_path(root).unlink()

    problems = freeze_problems(root)
    assert any("FREEZE.toml" in p and "Demo_ck" in p for p in problems)


# ---------------------------------------------------------------------------
# CUTOFF single source of truth (Controller Ruling 1)
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# CLI: `mission freeze` / `mission unfreeze`
# ---------------------------------------------------------------------------

def test_cli_freeze_then_unfreeze(tmp_path, capsys):
    mroot = tmp_path / "missions"
    _campaign(mroot / "demo")

    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo",
              "--identity", "alice@example.com", "--session", "s1"])
    assert rc == 0
    assert freeze_path(mroot / "demo").exists()
    capsys.readouterr()

    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo",
              "--identity", "alice@example.com", "--session", "s1"])
    assert rc == 1
    assert "already frozen" in capsys.readouterr().out

    rc = main(["mission", "--missions-root", str(mroot), "unfreeze", "demo",
              "--author", "alice@example.com", "--reason", "r",
              "--readback-identity", "alice@example.com"])
    assert rc == 1
    assert "readback_identity" in capsys.readouterr().out

    rc = main(["mission", "--missions-root", str(mroot), "unfreeze", "demo",
              "--author", "alice@example.com", "--reason", "r",
              "--readback-identity", "bob@example.com"])
    assert rc == 0
    doc = _load_freeze_for_test(mroot / "demo")
    assert doc["version"] == 2


def test_cli_freeze_unknown_campaign(tmp_path):
    mroot = tmp_path / "missions"
    mroot.mkdir()
    rc = main(["mission", "--missions-root", str(mroot), "freeze", "nope",
              "--identity", "a@x", "--session", "s1"])
    assert rc == 1


def _load_freeze_for_test(root: Path) -> dict:
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib  # type: ignore[no-redef]
    return tomllib.loads(freeze_path(root).read_text())


def test_cutoff_is_single_source_of_truth():
    from telperion.missions.process import CUTOFF
    from telperion.missions.provenance import CHECKS_CUTOFF

    assert CHECKS_CUTOFF == CUTOFF
    assert CHECKS_CUTOFF is CUTOFF

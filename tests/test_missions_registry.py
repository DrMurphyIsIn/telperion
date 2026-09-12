"""Registry: campaign load, DAG, open-leaves, transitions, renders."""
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.schema import (  # noqa: E402
    Claim, Node, Proof, Readback, SchemaError,
    load_node, save_node, slug_of,
)
from telperion.missions.registry import (  # noqa: E402
    Campaign, load_campaign, assert_acyclic,
    open_leaves, promote_to_open, deprecate, set_proof,
    render_status, render_dot,
)

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def copy_demo(tmp_path: Path) -> Path:
    """Copy the demo fixture into tmp_path and return the campaign root."""
    dest = tmp_path / "demo"
    shutil.copytree(DEMO_FIXTURE, dest)
    return dest


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def test_load_campaign_and_unknown_dep_raises(tmp_path):
    # Load the fixture; assert we get 4 nodes keyed by slug.
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)
    assert len(campaign.nodes) == 4
    assert "Demo_goal" in campaign.nodes
    assert "Demo_lemma_a" in campaign.nodes

    # Write a node whose depends_on points at a slug that does not exist.
    bad_node = Node(
        name="Demo.bad",
        title="Bad node",
        kind="lemma",
        status="draft",
        depends_on=("Nope",),
        statement_module="Statements.Demo_bad",
        created="2026-09-11",
        updated="2026-09-11",
    )
    save_node(bad_node, root / "nodes" / "Demo_bad.toml")
    with pytest.raises(SchemaError, match="Nope"):
        load_campaign(root)


def test_assert_acyclic_detects_cycle(tmp_path):
    # Create a two-node cycle: a -> b -> a.
    # load_campaign now calls assert_acyclic internally, so the cycle is
    # detected at load time. We also verify assert_acyclic directly on a
    # hand-built Campaign to keep the public API tested.
    root = tmp_path / "cycle"
    root.mkdir()
    nodes_dir = root / "nodes"
    nodes_dir.mkdir()

    from telperion.missions.schema import MissionManifest, save_manifest
    save_manifest(MissionManifest(
        name="Cycle.goal",
        title="Cycle campaign",
        description="cycle test",
        goal_node="Cycle_a",
        environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0",
    ), root / "mission.toml")

    node_a = Node(
        name="Cycle.a", title="A", kind="lemma", status="draft",
        depends_on=("Cycle_b",), statement_module="Statements.Cycle_a",
        created="2026-09-11", updated="2026-09-11",
    )
    node_b = Node(
        name="Cycle.b", title="B", kind="lemma", status="draft",
        depends_on=("Cycle_a",), statement_module="Statements.Cycle_b",
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_a, nodes_dir / "Cycle_a.toml")
    save_node(node_b, nodes_dir / "Cycle_b.toml")

    # Cycle is caught at load time (load_campaign calls assert_acyclic)
    with pytest.raises(SchemaError) as exc_info:
        load_campaign(root)
    msg = str(exc_info.value)
    assert "Cycle_a" in msg
    assert "Cycle_b" in msg

    # Also verify assert_acyclic directly on a hand-built Campaign
    from telperion.missions.schema import MissionManifest as MM
    hand_built = Campaign(
        root=root,
        manifest=MM(
            name="Cycle.goal", title="Cycle campaign", description="cycle test",
            goal_node="Cycle_a", environment_toolchain="leanprover/lean4:v4.32.0",
            environment_mathlib_rev="v4.32.0",
        ),
        nodes={"Cycle_a": node_a, "Cycle_b": node_b},
    )
    with pytest.raises(SchemaError) as exc_info2:
        assert_acyclic(hand_built)
    msg2 = str(exc_info2.value)
    assert "Cycle_a" in msg2
    assert "Cycle_b" in msg2


def test_open_leaves_requires_deps_proved(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_a is open with no deps -> IS a leaf
    leaves = open_leaves(campaign)
    leaf_slugs = {n.name for n in leaves}
    assert "Demo.lemma_a" in leaf_slugs

    # Demo_goal is draft (not open) -> not a leaf regardless
    assert "Demo.goal" not in leaf_slugs

    # After lemma_a is proved and goal is opened, goal is a leaf only when b is also proved.
    # First prove lemma_a (set a proof on it).
    lemma_a = campaign.nodes["Demo_lemma_a"]
    proved_a = Node(
        **{f: getattr(lemma_a, f) for f in lemma_a.__dataclass_fields__
           if f not in ("status", "proof")},
        status="proved",
        proof=Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", True),
    )
    save_node(proved_a, root / "nodes" / "Demo_lemma_a.toml")

    # Open Demo_goal by first recording a readback on Demo_lemma_b (draft), then
    # open Demo_goal directly by mutating its node file.
    goal = campaign.nodes["Demo_goal"]
    opened_goal = Node(
        **{f: getattr(goal, f) for f in goal.__dataclass_fields__
           if f not in ("status", "readback")},
        status="open",
        readback=Readback("Goal holds when both lemmas hold.", "operator", "2026-09-11"),
    )
    save_node(opened_goal, root / "nodes" / "Demo_goal.toml")

    campaign2 = load_campaign(root)

    # Demo_goal depends on Demo_lemma_b which is still draft -> not a leaf
    leaves2 = open_leaves(campaign2)
    leaf_slugs2 = {n.name for n in leaves2}
    assert "Demo.goal" not in leaf_slugs2

    # Now prove lemma_b too
    lemma_b = campaign2.nodes["Demo_lemma_b"]
    proved_b = Node(
        **{f: getattr(lemma_b, f) for f in lemma_b.__dataclass_fields__
           if f not in ("status", "proof", "readback")},
        status="proved",
        proof=Proof("proof/Demo_lemma_b.lean", "lean_module", "direct", True),
        readback=Readback("Lemma B holds.", "operator", "2026-09-11"),
    )
    save_node(proved_b, root / "nodes" / "Demo_lemma_b.toml")

    campaign3 = load_campaign(root)
    leaves3 = open_leaves(campaign3)
    leaf_slugs3 = {n.name for n in leaves3}
    # Now Demo_goal is open and both deps proved -> IS a leaf
    assert "Demo.goal" in leaf_slugs3


def test_promote_to_open_requires_readback(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_b is draft with no readback -> promote_to_open raises
    with pytest.raises(SchemaError, match="readback"):
        promote_to_open(campaign, "Demo_lemma_b")

    # Record a readback on Demo_lemma_b and reload
    lemma_b = campaign.nodes["Demo_lemma_b"]
    with_readback = Node(
        **{f: getattr(lemma_b, f) for f in lemma_b.__dataclass_fields__
           if f != "readback"},
        readback=Readback("Lemma B statement: auxiliary bound holds.", "operator", "2026-09-11"),
    )
    save_node(with_readback, root / "nodes" / "Demo_lemma_b.toml")
    campaign2 = load_campaign(root)

    # Now promote_to_open should succeed
    result = promote_to_open(campaign2, "Demo_lemma_b")
    assert result.status == "open"


def test_promote_to_open_rejects_non_draft_status(tmp_path):
    """promote_to_open raises SchemaError when the node status is not 'draft'.

    This guards against status regressions: a proved/refuted/deprecated node
    must never be silently re-opened by the audit path.
    """
    import dataclasses as _dc
    root = copy_demo(tmp_path)
    # Demo_lemma_a is already open in the fixture; prove it on disk
    node_path = root / "nodes" / "Demo_lemma_a.toml"
    existing = load_node(node_path)
    proved = _dc.replace(
        existing,
        status="proved",
        proof=Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", True),
    )
    save_node(proved, node_path)

    campaign = load_campaign(root)

    # Calling promote_to_open on a proved node must raise SchemaError
    with pytest.raises(SchemaError, match="proved"):
        promote_to_open(campaign, "Demo_lemma_a")

    # On-disk status must remain proved — no silent regression
    on_disk = load_node(node_path)
    assert on_disk.status == "proved"

    # Same guard applies to a refuted node (schema requires proof when refuted)
    refuted = _dc.replace(
        existing,
        status="refuted",
        proof=Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", False),
    )
    save_node(refuted, node_path)
    campaign2 = load_campaign(root)
    with pytest.raises(SchemaError, match="refuted"):
        promote_to_open(campaign2, "Demo_lemma_a")
    on_disk2 = load_node(node_path)
    assert on_disk2.status == "refuted"


def test_set_proof_never_sets_proved(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_a is already open; attach a proof -> status must remain "open"
    proof = Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", True)
    result = set_proof(campaign, "Demo_lemma_a", proof)
    assert result.status == "open"
    assert result.proof is not None
    assert result.proof.artifact == "proof/Demo_lemma_a.lean"

    # Verify the file was saved with status "open"
    reloaded = load_node(root / "nodes" / "Demo_lemma_a.toml")
    assert reloaded.status == "open"
    assert reloaded.proof is not None


def test_mutators_update_campaign_nodes_in_memory(tmp_path):
    # After deprecate(), campaign.nodes reflects the change without reloading.
    # open_leaves and render_status on the SAME campaign object should see
    # the deprecated status immediately.
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_a is open before mutation
    assert campaign.nodes["Demo_lemma_a"].status == "open"
    leaves_before = open_leaves(campaign)
    assert any(n.name == "Demo.lemma_a" for n in leaves_before)

    # Deprecate it in place
    deprecate(campaign, "Demo_lemma_a", reason="Superseded by Demo.lemma_c")

    # In-memory campaign.nodes must reflect the new status immediately
    assert campaign.nodes["Demo_lemma_a"].status == "deprecated"

    # open_leaves on the same campaign object must no longer include it
    leaves_after = open_leaves(campaign)
    assert all(n.name != "Demo.lemma_a" for n in leaves_after)

    # render_status on same object must show the deprecated glyph for lemma_a.
    # Match the node's own line (starts with glyph + slug), not a dep-reference line.
    out = render_status(campaign)
    lines = out.splitlines()
    # Each node line has the form "  <glyph> <slug>  (<kind>, <status>)..."
    lemma_a_line = next(l for l in lines if "Demo_lemma_a  " in l)
    assert "†" in lemma_a_line


def test_render_status_contains_tree_and_statuses(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)
    output = render_status(campaign)

    # Output must contain the campaign title
    assert "Demo Campaign" in output

    # render_status uses slugs (slug_of(name)), not raw Lean names.
    # Verify the slug form is present for each node.
    assert "Demo_goal" in output
    assert "Demo_lemma_a" in output
    assert "Demo_lemma_b" in output
    assert "Demo_dead" in output

    # Status glyphs must appear: draft=·, open=○, deprecated=†
    assert "·" in output   # draft glyph (Demo_goal, Demo_lemma_b)
    assert "○" in output   # open glyph (Demo_lemma_a)
    assert "†" in output  # deprecated glyph (Demo_dead)

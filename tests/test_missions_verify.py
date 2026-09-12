"""Verify gate: invariant battery, proved/refuted status flip, closure fixpoint."""
from __future__ import annotations

import dataclasses
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, Proof, Readback, SchemaError,
    load_node, save_node, slug_of,
)
from telperion.missions.registry import (  # noqa: E402
    Campaign, load_campaign, set_proof,
)
from telperion.missions.statements import write_statement  # noqa: E402
from telperion.missions.verify import (  # noqa: E402
    GateError,
    _compute_closures,
    normalize_lean,
    statement_matches,
    refutation_matches,
    recompute_closures,
    grant_status,
    verify_campaign,
)

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"

# ---------------------------------------------------------------------------
# Shared manifest / helpers
# ---------------------------------------------------------------------------

def _manifest() -> MissionManifest:
    return MissionManifest(
        name="Demo.goal",
        title="Demo Campaign",
        description="A synthetic test campaign.",
        goal_node="Demo_goal",
        environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0",
        sources=(),
    )


def copy_demo(tmp_path: Path) -> Path:
    dest = tmp_path / "demo"
    shutil.copytree(DEMO_FIXTURE, dest)
    return dest


def _open_node_with_proof(name: str, artifact: str, via: str = "direct",
                          refutation_statement: str = "") -> Node:
    """Return an open Node with a proof link but status still 'open'."""
    return Node(
        name=name,
        title=f"Test node {name}",
        kind="lemma",
        status="open",
        depends_on=(),
        statement_module=f"Statements.{slug_of(name)}",
        proof=Proof(artifact=artifact, artifact_kind="lean_module",
                    via=via, closure_clean=False),
        refutation_statement=refutation_statement,
        created="2026-09-11",
        updated="2026-09-11",
    )


# ---------------------------------------------------------------------------
# T1: grant_status flips open -> proved on a matching artifact
# ---------------------------------------------------------------------------

def test_gate_grants_proved_on_matching_artifact(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    stmt = "theorem lemma_foo : 1 + 1 = 2"
    node = _open_node_with_proof("Test.foo", artifact="proof/Test_foo.lean")
    save_node(node, root / "nodes" / "Test_foo.toml")

    # Write the statement file (needed for regen check inside grant_status)
    write_statement(root, node, stmt, manifest)

    # Write the artifact file -- it must CONTAIN the node's statement
    artifact_path = root / "proof" / "Test_foo.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(
        "-- some preamble comment\n"
        f"{stmt}\n"
        "  := by\n"
        "  simp\n"
    )

    campaign = load_campaign(root)
    result = grant_status(campaign, "Test_foo")
    assert result.status == "proved"
    # On-disk file must also reflect proved
    assert load_node(root / "nodes" / "Test_foo.toml").status == "proved"


# ---------------------------------------------------------------------------
# T2: mismatched artifact raises GateError, status stays open
# ---------------------------------------------------------------------------

def test_gate_rejects_mismatched_statement(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    node_stmt = "theorem lemma_real : 2 + 2 = 4"
    wrong_stmt = "theorem lemma_wrong : 3 + 3 = 6"

    node = _open_node_with_proof("Test.real", artifact="proof/Test_real.lean")
    save_node(node, root / "nodes" / "Test_real.toml")
    write_statement(root, node, node_stmt, manifest)

    artifact_path = root / "proof" / "Test_real.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(f"{wrong_stmt} := by simp\n")

    campaign = load_campaign(root)
    with pytest.raises(GateError):
        grant_status(campaign, "Test_real")

    # On-disk status must remain open
    assert load_node(root / "nodes" / "Test_real.toml").status == "open"


# ---------------------------------------------------------------------------
# T3: refutation path flips open -> refuted when refutation_statement matches
# ---------------------------------------------------------------------------

def test_gate_refuted_via_refutation_statement(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    node_stmt = "theorem lemma_refuted : False"
    refutation = "theorem lemma_refuted_neg : ¬False"

    node = Node(
        name="Test.refuted",
        title="To be refuted",
        kind="lemma",
        status="open",
        depends_on=(),
        statement_module="Statements.Test_refuted",
        proof=Proof(artifact="proof/Test_refuted.lean",
                    artifact_kind="lean_module", via="direct",
                    closure_clean=False),
        refutation_statement=refutation,
        created="2026-09-11",
        updated="2026-09-11",
    )
    save_node(node, root / "nodes" / "Test_refuted.toml")
    write_statement(root, node, node_stmt, manifest)

    artifact_path = root / "proof" / "Test_refuted.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    # Artifact matches the refutation statement (NOT the original proposition)
    artifact_path.write_text(f"{refutation} := by\n  simp\n")

    campaign = load_campaign(root)
    result = grant_status(campaign, "Test_refuted")
    assert result.status == "refuted"
    assert load_node(root / "nodes" / "Test_refuted.toml").status == "refuted"


# ---------------------------------------------------------------------------
# T4: closure fixpoint: A reduction via B(proved) and C(open) -> clean only after C proved
# ---------------------------------------------------------------------------

def test_closure_fixpoint(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    # Node B: proved direct
    node_b = Node(
        name="Fix.b", title="B", kind="lemma", status="proved",
        depends_on=(), statement_module="Statements.Fix_b",
        proof=Proof(artifact="proof/Fix_b.lean", artifact_kind="lean_module",
                    via="direct", closure_clean=True),
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_b, root / "nodes" / "Fix_b.toml")

    # Node C: open (not yet proved)
    node_c = Node(
        name="Fix.c", title="C", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Fix_c",
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_c, root / "nodes" / "Fix_c.toml")

    # Node A: open, reduction via B and C, closure_clean=False
    node_a = Node(
        name="Fix.a", title="A", kind="lemma", status="open",
        depends_on=("Fix_b", "Fix_c"),
        statement_module="Statements.Fix_a",
        proof=Proof(artifact="proof/Fix_a.lean", artifact_kind="lean_module",
                    via="reduction", closure_clean=False),
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_a, root / "nodes" / "Fix_a.toml")

    campaign = load_campaign(root)
    closures = recompute_closures(campaign)

    # A is not clean because C is not proved
    assert closures.get("Fix_a") is False
    # B is direct-proved -> always clean
    assert closures.get("Fix_b") is True

    # Now prove C: make it proved with a direct proof
    node_c_proved = dataclasses.replace(node_c, status="proved",
                                        proof=Proof(artifact="proof/Fix_c.lean",
                                                    artifact_kind="lean_module",
                                                    via="direct", closure_clean=True))
    save_node(node_c_proved, root / "nodes" / "Fix_c.toml")
    campaign2 = load_campaign(root)
    closures2 = recompute_closures(campaign2)

    # Now A should be clean because both B and C are proved and clean
    assert closures2.get("Fix_a") is True


# ---------------------------------------------------------------------------
# T5: verify_campaign reports errors for missing artifacts and stale claims
# ---------------------------------------------------------------------------

def test_verify_report_flags_missing_artifact_and_stale_claims(tmp_path):
    root = copy_demo(tmp_path)
    manifest = _manifest()

    # Make Demo_lemma_a "proved" with a proof link but NO artifact file
    campaign = load_campaign(root)
    lemma_a = campaign.nodes["Demo_lemma_a"]
    proved_node = dataclasses.replace(
        lemma_a, status="proved",
        proof=Proof(artifact="proof/Demo_lemma_a.lean",
                    artifact_kind="lean_module", via="direct", closure_clean=True),
    )
    save_node(proved_node, root / "nodes" / "Demo_lemma_a.toml")

    # Add a stale claim file
    claims_dir = root / "claims"
    claims_dir.mkdir(exist_ok=True)
    from telperion.missions.schema import Claim, save_claim
    stale_claim = Claim(
        node="Demo.lemma_a",
        session="sess-old",
        started="2000-01-01T00:00:00",  # definitely stale
        ttl_hours=1,
    )
    save_claim(stale_claim, claims_dir / "Demo_lemma_a.toml")

    report = verify_campaign(root)

    # Missing artifact should appear as an error
    errors_combined = "\n".join(report.errors)
    assert "Demo_lemma_a" in errors_combined or "proof/Demo_lemma_a" in errors_combined

    # Stale claim should appear as a warning
    warnings_combined = "\n".join(report.warnings)
    assert "Demo_lemma_a" in warnings_combined or "stale" in warnings_combined.lower()

    # Overall not ok because of the missing artifact error
    assert not report.ok


# ---------------------------------------------------------------------------
# T6: normalize strips comments and sorry
# ---------------------------------------------------------------------------

def test_normalize_strips_comments_and_sorry():
    raw = (
        "-- inline comment\n"
        "theorem foo : 1 = 1 /- block comment -/ := by sorry"
    )
    result = normalize_lean(raw)
    assert "--" not in result
    assert "inline comment" not in result
    assert "block comment" not in result
    assert ":= by sorry" not in result
    # Core theorem text must survive
    assert "theorem foo" in result
    assert "1 = 1" in result

    # Plain := sorry also stripped
    raw2 = "theorem bar : True := sorry"
    result2 = normalize_lean(raw2)
    assert ":= sorry" not in result2
    assert "theorem bar" in result2


# ---------------------------------------------------------------------------
# C2: verify_campaign is read-only — stale closure_clean must be reported
#     but NOT repaired on disk
# ---------------------------------------------------------------------------

def test_verify_campaign_is_readonly_stale_closure_reported_not_repaired(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    # Node B: proved direct, clean
    node_b = Node(
        name="Ro.b", title="B", kind="lemma", status="proved",
        depends_on=(), statement_module="Statements.Ro_b",
        proof=Proof(artifact="proof/Ro_b.lean", artifact_kind="lean_module",
                    via="direct", closure_clean=True),
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_b, root / "nodes" / "Ro_b.toml")

    # Node C: open — NOT proved
    node_c = Node(
        name="Ro.c", title="C", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Ro_c",
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_c, root / "nodes" / "Ro_c.toml")

    # Node A: proved via reduction of B+C; closure_clean=True is STALE
    # (C is not proved, so the true value should be False)
    stmt_a = "theorem ro_a : True"
    artifact_path = root / "proof" / "Ro_a.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(f"{stmt_a} := by trivial\n")

    node_a = Node(
        name="Ro.a", title="A", kind="lemma", status="proved",
        depends_on=("Ro_b", "Ro_c"),
        statement_module="Statements.Ro_a",
        proof=Proof(artifact="proof/Ro_a.lean", artifact_kind="lean_module",
                    via="reduction", closure_clean=True),  # stale: should be False
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_a, root / "nodes" / "Ro_a.toml")

    # Write statement file so regen_diff passes for Ro_a
    write_statement(root, node_a, stmt_a, manifest)

    report = verify_campaign(root)

    # The stale closure_clean flag must appear as an error
    errors_combined = "\n".join(report.errors)
    assert "Ro_a" in errors_combined, f"Expected Ro_a closure error; got: {report.errors}"
    assert "closure_clean" in errors_combined

    # On-disk Ro_a must still carry the stale closure_clean=True (not repaired)
    on_disk = load_node(root / "nodes" / "Ro_a.toml")
    assert on_disk.proof is not None
    assert on_disk.proof.closure_clean is True, (
        "verify_campaign must NOT repair closure_clean on disk (it is read-only)"
    )


# ---------------------------------------------------------------------------
# I1: grant_status raises GateError on empty normalized statement
# ---------------------------------------------------------------------------

def test_gate_raises_on_empty_normalized_statement(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    # Statement file contains ONLY a header line + import lines — no proposition
    stmt_imports_only = "import Mathlib.Tactic"
    node = _open_node_with_proof("Test.empty", artifact="proof/Test_empty.lean")
    save_node(node, root / "nodes" / "Test_empty.toml")
    # Write statement file with imports-only body so _normalized_statement returns ""
    write_statement(root, node, stmt_imports_only, manifest)

    artifact_path = root / "proof" / "Test_empty.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text("-- proof\ntheorem something : True := by trivial\n")

    campaign = load_campaign(root)
    with pytest.raises(GateError, match="normalized statement is empty"):
        grant_status(campaign, "Test_empty")

    # Status must remain open
    assert load_node(root / "nodes" / "Test_empty.toml").status == "open"


# ---------------------------------------------------------------------------
# I2: refutation_matches fallback uses the proposition, not the module name
# ---------------------------------------------------------------------------

def test_refutation_matches_fallback_uses_proposition(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    prop = "theorem ref_prop : 1 = 2"
    node = Node(
        name="Test.ref_fallback",
        title="Refutation fallback test",
        kind="lemma",
        status="open",
        depends_on=(),
        statement_module="Statements.Test_ref_fallback",
        # No refutation_statement set -> fallback path
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node, root / "nodes" / "Test_ref_fallback.toml")
    write_statement(root, node, prop, manifest)

    norm_prop = normalize_lean(prop)

    # Artifact with ¬ AND the normalized proposition inline (not in a comment) -> matches.
    # norm_prop = "theorem ref_prop : 1 = 2"; we embed it literally in the proof body
    # so normalize_lean preserves it.
    artifact_match = f"theorem refutes_it : ¬(1 = 2) := by simp\naxiom base : {norm_prop}"
    assert refutation_matches(artifact_match, node, root) is True

    # Artifact with proposition but NO ¬ -> does not match
    artifact_no_neg = f"theorem no_neg : {norm_prop} := by simp\n"
    assert refutation_matches(artifact_no_neg, node, root) is False

    # Sanity: module name "Statements.Test_ref_fallback" must NOT be the criterion.
    # The module name alone (with ¬ present) should NOT satisfy the prop-containment check.
    artifact_module_name_only = "theorem x : ¬Statements.Test_ref_fallback := by simp"
    assert refutation_matches(artifact_module_name_only, node, root) is False


# ---------------------------------------------------------------------------
# I3: _normalized_statement handles blank first line correctly, and matches
#     write_statement output
# ---------------------------------------------------------------------------

def test_normalized_statement_matches_write_statement_output(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    manifest = _manifest()

    stmt = "theorem i3_check (n : Nat) : n = n"
    node = Node(
        name="Test.i3", title="I3 check", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Test_i3",
        created="2026-09-11", updated="2026-09-11",
    )
    write_statement(root, node, stmt, manifest)

    from telperion.missions.verify import _normalized_statement
    result = _normalized_statement(node, root)

    # Must contain the theorem declaration (sorry stripped)
    assert "theorem i3_check" in result
    assert ":= by sorry" not in result

    # Module name must NOT appear as the result
    assert result != "Statements.Test_i3"
    assert result != normalize_lean("Statements.Test_i3")


# ---------------------------------------------------------------------------
# F2 regression: direct-proved node with stored closure_clean=False keeps
# that False after recompute_closures, and a reduction depending on it
# also computes closure_clean=False.
#
# Controller ruling: via="direct" nodes store the authoritative closure_clean
# flag (e.g. for cross-island artifacts whose kernel CI is on another Lean
# island). _compute_closures must seed from the stored value, not overwrite
# it with unconditional True.
# ---------------------------------------------------------------------------

def test_direct_false_closure_survives_recompute(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    # Node D: proved, via=direct, but closure_clean=False (cross-island scenario:
    # kernel authority lives on a different Lean island not yet wired into CI).
    node_d = Node(
        name="Ci.d", title="D cross-island", kind="lemma", status="proved",
        depends_on=(), statement_module="Statements.Ci_d",
        proof=Proof(artifact="proof/Ci_d.lean", artifact_kind="lean_module",
                    via="direct", closure_clean=False),
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_d, root / "nodes" / "Ci_d.toml")

    # Node R: proved, via=reduction, depends only on D; closure_clean=True (stale).
    node_r = Node(
        name="Ci.r", title="R reduction of D", kind="lemma", status="proved",
        depends_on=("Ci_d",), statement_module="Statements.Ci_r",
        proof=Proof(artifact="proof/Ci_r.lean", artifact_kind="lean_module",
                    via="reduction", closure_clean=True),
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_r, root / "nodes" / "Ci_r.toml")

    campaign = load_campaign(root)
    closures = recompute_closures(campaign)

    # D is direct with stored False — must remain False, not be promoted to True.
    assert closures.get("Ci_d") is False, (
        "direct-proved node with stored closure_clean=False must stay False "
        "after recompute_closures (controller ruling: stored flag is authoritative)"
    )

    # R depends on D (which is not closure-clean) so R must also be False.
    assert closures.get("Ci_r") is False, (
        "reduction node depending on a False-closure direct node must also "
        "compute closure_clean=False"
    )

    # On-disk D must still carry False (recompute_closures only writes changes;
    # D's stored value already matches the computed value, so no write needed,
    # but either way the flag must remain False on disk).
    on_disk_d = load_node(root / "nodes" / "Ci_d.toml")
    assert on_disk_d.proof is not None
    assert on_disk_d.proof.closure_clean is False, (
        "recompute_closures must NOT flip a direct-proved node's closure_clean "
        "from False to True on disk"
    )

    # On-disk R must now carry False (its stale True was corrected by recompute).
    on_disk_r = load_node(root / "nodes" / "Ci_r.toml")
    assert on_disk_r.proof is not None
    assert on_disk_r.proof.closure_clean is False, (
        "recompute_closures must write back the corrected False for R, "
        "whose stale stored value was True"
    )

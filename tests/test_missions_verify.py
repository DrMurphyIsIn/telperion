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
    artifact_incompleteness_markers,
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
    """Return an open Node with a proof link but status still 'open'.

    The readback is part of the fixture because it is part of reality: `promote_to_open` is
    the only draft->open path and it refuses without one, so an `open` node always has a
    readback on record. Since 2026-09-19 `grant_status` re-checks it, which is what caught
    that these fixtures were modelling a state the registry cannot reach.
    """
    return Node(
        name=name,
        title=f"Test node {name}",
        kind="lemma",
        status="open",
        depends_on=(),
        statement_module=f"Statements.{slug_of(name)}",
        proof=Proof(artifact=artifact, artifact_kind="lean_module",
                    via=via, closure_clean=False),
        readback=Readback(text=f"read-back of {name}", auditor="test-auditor",
                          date="2026-09-11"),
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
        readback=Readback(text="read-back of Test_refuted", auditor="test-auditor",
                          date="2026-09-11"),
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


def test_normalize_strips_multiline_doc_comments_without_residue():
    # Regression (2026-09-16 grant pre-flight): a /-- doc comment -/ whose
    # opener line carries `--` was mutilated by line-comment stripping BEFORE
    # block stripping ran, leaving prose residue between adjacent decls and
    # breaking containment for AND_g2_reflected_band.
    raw = (
        "namespace ReflectedBand_t14\n"
        "/-- The boxes are nonoverlapping\n"
        "and strictly alternate in sign. -/\n"
        "def d : BandData := x\n"
        "end ReflectedBand_t14\n"
    )
    result = normalize_lean(raw)
    assert "alternate" not in result
    assert "/" not in result
    assert "namespace ReflectedBand_t14 def d : BandData := x end" in result


def test_normalize_handles_nested_block_comments():
    # Lean 4 block comments nest; the whole outer comment must vanish.
    raw = "theorem foo /- outer /- inner -/ still outer -/ : True := by sorry"
    result = normalize_lean(raw)
    assert "outer" not in result and "inner" not in result
    assert "theorem foo : True" in result


def test_normalize_line_comment_does_not_open_block():
    # `/-` inside a `--` line comment is inert; a later real `-/`-free code
    # line must survive.
    raw = "-- see /- the note\ntheorem baz : True := by sorry"
    result = normalize_lean(raw)
    assert "theorem baz : True" in result
    assert "note" not in result


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


# ---------------------------------------------------------------------------
# T9: the gate refuses to grant `proved` against an unfinished artifact
# (audit 2026-09-18: containment alone let a `:= by sorry` stub through, and
#  normalize_lean strips a trailing sorry, which made the stub match MORE easily)
# ---------------------------------------------------------------------------

def test_incompleteness_markers_ignore_comments_and_strings():
    assert artifact_incompleteness_markers("theorem a : True := by sorry") == ["sorry"]
    assert artifact_incompleteness_markers("theorem a : True := by admit") == ["admit"]
    assert artifact_incompleteness_markers("theorem a : True := by native_decide") == [
        "native_decide"
    ]
    # prose in a doc comment is NOT a marker (the repo writes "no `sorry`" on purpose)
    assert artifact_incompleteness_markers("/-- no `sorry` here -/\ntheorem a : True := trivial") == []
    assert artifact_incompleteness_markers("-- sorry, this is a line comment\ntheorem a : True := trivial") == []
    # a longer identifier that merely contains the token is not a marker
    assert artifact_incompleteness_markers("theorem sorryless : True := trivial") == []


def test_gate_refuses_proved_when_artifact_still_has_sorry(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    stmt = "theorem lemma_stub : 1 + 1 = 2"
    node = _open_node_with_proof("Test.stub", artifact="proof/Test_stub.lean")
    save_node(node, root / "nodes" / "Test_stub.toml")
    write_statement(root, node, stmt, manifest)

    artifact_path = root / "proof" / "Test_stub.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    # Contains the statement verbatim, but proves nothing.
    artifact_path.write_text(f"{stmt} := by sorry\n")

    campaign = load_campaign(root)
    with pytest.raises(GateError):
        grant_status(campaign, "Test_stub")
    assert load_node(root / "nodes" / "Test_stub.toml").status == "open"


def test_verify_campaign_flags_proved_node_with_sorry_artifact(tmp_path):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    stmt = "theorem lemma_stub2 : 1 + 1 = 2"
    node = _open_node_with_proof("Test.stub2", artifact="proof/Test_stub2.lean")
    save_node(node, root / "nodes" / "Test_stub2.toml")
    write_statement(root, node, stmt, manifest)

    artifact_path = root / "proof" / "Test_stub2.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    # A trailing `:= by sorry` is stripped by normalize_lean, so the node would be caught by
    # the containment check instead. Put a second declaration after it so the sorry is NOT
    # trailing and the incompleteness scan is the check under test.
    artifact_path.write_text(f"{stmt} := by sorry\ntheorem other_thm : True := trivial\n")

    # Force the node to `proved` on disk WITHOUT going through the gate, which is the
    # state the read-only battery has to be able to catch.
    save_node(dataclasses.replace(node, status="proved"), root / "nodes" / "Test_stub2.toml")

    report = verify_campaign(root)
    assert not report.ok
    assert any("sorry" in e for e in report.errors)


# ---------------------------------------------------------------------------
# T10: a node may not be granted against Lean that no CI job compiles
# (audit 2026-09-19: all six proved anduril nodes pointed at the zeta_reflection
#  island, which no workflow built; two rh nodes had the same shape a day earlier)
# ---------------------------------------------------------------------------

def _fake_repo(tmp_path, island: str, *, wire_ci: bool):
    """A miniature repo: one example island, and a workflow that may or may not build it."""
    repo = tmp_path / "repo"
    lean = repo / "telperion" / "examples" / island / "lean"
    lean.mkdir(parents=True)
    (lean / "Art.lean").write_text("theorem art_thm : 1 + 1 = 2 := by norm_num\n")
    # A real island declares its artifact as a (default) lib; since the closure audit (C2)
    # coverage is judged per MODULE through the lakefile, not per island directory.
    (lean / "lakefile.toml").write_text(
        'name = "Fake"\ndefaultTargets = ["Art"]\n\n[[lean_lib]]\nname = "Art"\n'
    )
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    body = "on: push\njobs:\n  build:\n    steps:\n"
    if wire_ci:
        body += (f"      - working-directory: telperion/examples/{island}/lean\n"
                 f"        run: lake build\n")
    else:
        # present, but only a python drift check -- no `lake build`, so no verification
        body += (f"      - working-directory: telperion/examples/{island}/lean\n"
                 f"        run: python generate.py --check\n")
    (wf / "ci.yml").write_text(body)
    return repo


def test_coverage_detects_island_ci_never_builds(tmp_path):
    from telperion.missions.coverage import artifact_coverage_error, ci_built_islands

    repo = _fake_repo(tmp_path, "lonely", wire_ci=False)
    art = repo / "telperion" / "examples" / "lonely" / "lean" / "Art.lean"
    assert ci_built_islands(repo) == set()
    err = artifact_coverage_error(art, repo)
    assert err is not None and "lonely" in err

    repo2 = _fake_repo(tmp_path / "b", "wired", wire_ci=True)
    art2 = repo2 / "telperion" / "examples" / "wired" / "lean" / "Art.lean"
    assert ci_built_islands(repo2) == {"wired"}
    assert artifact_coverage_error(art2, repo2) is None


def test_coverage_ignores_non_lean_and_non_island_artifacts(tmp_path):
    from telperion.missions.coverage import artifact_coverage_error

    repo = _fake_repo(tmp_path, "lonely", wire_ci=False)
    # a .md artifact has nothing to compile
    assert artifact_coverage_error(repo / "telperion" / "examples" / "lonely" / "x.md", repo) is None
    # campaign-local Lean is covered by the campaign's own build, not by an island job
    assert artifact_coverage_error(repo / "telperion" / "missions" / "rh" / "lean" / "S.lean", repo) is None


def test_coverage_counts_cd_inside_run(tmp_path):
    """Three jobs in the real repo address their island with `cd`, not working-directory."""
    from telperion.missions.coverage import ci_built_islands

    repo = tmp_path / "repo"
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text(
        "jobs:\n  b:\n    steps:\n      - run: |\n"
        "          cd telperion/examples/viacd/lean\n          lake build\n"
    )
    assert "viacd" in ci_built_islands(repo)


def test_coverage_fallback_agrees_with_yaml_on_the_real_repo():
    """The no-PyYAML fallback must not diverge from the YAML parser on this repo.

    The required `unit` job has no PyYAML, so the fallback is what actually runs there.
    """
    import pathlib as _p
    from telperion.missions import coverage as cov

    repo = _p.Path(__file__).resolve().parents[2]
    if not (repo / ".github" / "workflows").is_dir():
        pytest.skip("not running inside the repo")
    assert cov.ci_built_islands(repo) == cov._scan_islands_without_yaml(repo)


def test_coverage_refuses_to_report_everything_uncovered(tmp_path):
    """A broken parser must raise, not flunk every node.

    Regression test for this module's own first revision: it swallowed a missing PyYAML
    and returned an empty set, which reported every proved node in the registry as
    uncovered. One loud error beats N confident false ones.
    """
    from telperion.missions.coverage import CoverageParseError, _assert_parser_sane

    repo = tmp_path / "repo"
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text("jobs:\n  b:\n    steps:\n      - run: lake build\n")
    # steps_seen == 0 means the parser read nothing: that is the broken-parser signal
    with pytest.raises(CoverageParseError):
        _assert_parser_sane(repo, set(), 0)
    # but an empty answer AFTER genuinely walking steps is correct, not an error --
    # a repo whose build steps are all disabled is exactly that
    _assert_parser_sane(repo, set(), 3)
    # and a repo that genuinely builds nothing is fine either way
    (wf / "ci.yml").write_text("jobs:\n  b:\n    steps:\n      - run: echo hi\n")
    _assert_parser_sane(repo, set(), 0)


# ---------------------------------------------------------------------------
# T10b: MODULE-level coverage (closure audit C2, 2026-09-22). The island-level check was a
#  text match: the zeta_reflection workflow named five undeclared targets (`unknown target`),
#  ran a `lake env` that could not spawn `lean`, had never run -- and still vouched for six
#  proved nodes because the string `lake build` appeared under the island directory.
# ---------------------------------------------------------------------------

def _island(tmp_path, lakefile: str, files: dict, workflow: str, island: str = "isl"):
    repo = tmp_path / "repo"
    lean = repo / "telperion" / "examples" / island / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text(lakefile)
    for rel, text in files.items():
        f = lean / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text(workflow)
    return repo, lean


_TWO_LIBS = (
    'name = "Isl"\ndefaultTargets = ["Other"]\n\n'
    '[[lean_lib]]\nname = "Other"\n\n[[lean_lib]]\nname = "Art"\n'
)
_SRC = {"Art.lean": "import Mathlib\ntheorem t : True := trivial\n",
        "Other.lean": "theorem o : True := trivial\n"}


def _wf(run: str, extra: str = "", on: str = "on: push\n") -> str:
    body = "\n".join("          " + ln for ln in run.splitlines())
    return (f"{on}jobs:\n  b:\n    steps:\n      - working-directory: telperion/examples/isl/lean\n"
            f"{extra}        run: |\n{body}\n")


def test_island_built_but_artifact_module_not_is_uncovered(tmp_path):
    """A bare `lake build` whose defaultTargets never reach the artifact does not vouch for it."""
    from telperion.missions.coverage import artifact_coverage_error, ci_built_islands

    repo, lean = _island(tmp_path, _TWO_LIBS, _SRC, _wf("lake build"))
    assert ci_built_islands(repo) == {"isl"}  # the old floor passes...
    err = artifact_coverage_error(lean / "Art.lean", repo)
    assert err is not None and "compiled by no runnable CI step" in err  # ...the module gate does not
    assert artifact_coverage_error(lean / "Other.lean", repo) is None


def test_named_target_and_transitive_import_cover_the_artifact(tmp_path):
    from telperion.missions.coverage import artifact_coverage_error

    repo, lean = _island(tmp_path, _TWO_LIBS, _SRC, _wf("lake build Art"))
    assert artifact_coverage_error(lean / "Art.lean", repo) is None
    # reached only through an import of a default target
    src = dict(_SRC, **{"Other.lean": "import Art\n/- import Nope -/\ntheorem o : True := trivial\n"})
    repo2, lean2 = _island(tmp_path / "b", _TWO_LIBS, src, _wf("lake build"))
    assert artifact_coverage_error(lean2 / "Art.lean", repo2) is None


def test_undeclared_target_vouches_for_nothing_and_dooms_the_job(tmp_path):
    """The exact old zeta_reflection shape: `lake build <guard>` for a guard that is a .lean file
    but not a lean_lib (Lake: `unknown target`), followed by a guard-running step."""
    from telperion.missions.coverage import artifact_coverage_error

    src = dict(_SRC, **{"AxiomGuardArt.lean": "import Art\n#print axioms t\n"})
    wf = (
        "on: push\njobs:\n  b:\n    steps:\n"
        "      - working-directory: telperion/examples/isl/lean\n"
        "        run: lake build AxiomGuardArt\n"
        "      - working-directory: telperion/examples/isl/lean\n"
        "        run: |\n          for g in AxiomGuardArt; do\n"
        "            lake env lean \"$g.lean\" 2>&1 | tee out\n          done\n"
        "        shell: bash\n"
    )
    repo, lean = _island(tmp_path, _TWO_LIBS, src, wf)
    err = artifact_coverage_error(lean / "Art.lean", repo)
    assert err is not None and "compiled by no runnable CI step" in err
    # Declaring the guard as a lib is the fix: now the build step resolves and vouches.
    repo2, lean2 = _island(
        tmp_path / "b", _TWO_LIBS + '\n[[lean_lib]]\nname = "AxiomGuardArt"\n', src, wf
    )
    assert artifact_coverage_error(lean2 / "Art.lean", repo2) is None


def test_guard_run_by_lean_in_a_for_loop_covers_its_imports(tmp_path):
    from telperion.missions.coverage import ci_covered_lean_files

    src = dict(_SRC, **{"AxiomGuardArt.lean": "import Art\n#print axioms t\n"})
    wf = _wf('set -euo pipefail\nfor g in AxiomGuardArt; do\n  lake env lean "$g.lean"\ndone')
    repo, lean = _island(tmp_path, _TWO_LIBS, src, wf)
    cov = ci_covered_lean_files(repo)
    assert (lean / "Art.lean").resolve() in cov
    # an unknown loop variable cannot be resolved statically: no credit, no guess
    repo2, lean2 = _island(tmp_path / "b", _TWO_LIBS, src, _wf('lake env lean "$GUARD.lean"'))
    assert (lean2 / "Art.lean").resolve() not in ci_covered_lean_files(repo2)


def test_masked_or_unrunnable_builds_do_not_vouch(tmp_path):
    from telperion.missions.coverage import ci_covered_lean_files

    def covered(run, extra="", on="on: push\n", sub="x"):
        repo, lean = _island(tmp_path / sub, _TWO_LIBS, _SRC, _wf(run, extra, on))
        return (lean / "Art.lean").resolve() in ci_covered_lean_files(repo)

    assert covered("lake build Art", sub="ok")
    assert not covered("lake build Art || true", sub="ortrue")
    assert covered("lake build Art || { echo failed; exit 1; }", sub="orexit")
    # default `run` shell has no pipefail: `lake build | tee` exits with tee's status
    assert not covered("lake build Art 2>&1 | tee build.log", sub="tee")
    assert covered("lake build Art 2>&1 | tee build.log", extra="        shell: bash\n", sub="teebash")
    assert not covered("lake build Art", extra="        continue-on-error: true\n", sub="coe")
    assert not covered("lake build Art", extra="        if: false\n", sub="iffalse")
    assert not covered("lake build Art", on="", sub="notrigger")  # no `on:` -- never runs
    assert not covered('echo "then run lake build Art"', sub="echo")
    assert not covered("lake build $MODS", sub="var")


def test_globs_and_path_requires_resolve(tmp_path):
    """`globs = ["X.+"]` covers X and its submodules; an import may land in a path-required
    sibling package -- how zeta_reflection reaches XiLineZeros through zzl_core."""
    from telperion.missions.coverage import ci_covered_lean_files

    repo = tmp_path / "repo"
    sib = repo / "telperion" / "examples" / "sib" / "lean"
    (sib / "core").mkdir(parents=True)
    (sib / "core" / "lakefile.toml").write_text(
        'name = "core"\nsrcDir = ".."\n\n[[lean_lib]]\nname = "Xi"\n'
    )
    (sib / "Xi.lean").write_text("theorem xi : True := trivial\n")
    lakefile = (
        'name = "Isl"\ndefaultTargets = ["Pkg"]\n\n[[require]]\nname = "core"\n'
        'path = "../../sib/lean/core"\n\n[[lean_lib]]\nname = "Pkg"\nglobs = ["Pkg.+"]\n'
    )
    src = {"Pkg.lean": "theorem p : True := trivial\n",
           "Pkg/Sub.lean": "import Xi\ntheorem s : True := trivial\n"}
    _, lean = _island(tmp_path, lakefile, src, _wf("lake build"))
    cov = ci_covered_lean_files(repo)
    assert (lean / "Pkg" / "Sub.lean").resolve() in cov
    assert (sib / "Xi.lean").resolve() in cov


def test_mini_toml_reads_a_multiline_default_targets_array():
    from telperion.missions.coverage import _mini_toml

    doc = _mini_toml(
        'name = "Z"  # c\ndefaultTargets = ["A", "B",\n   "C"]\n[[lean_lib]]\nname = "A"\n'
        'roots = ["A"]\n[[require]]\nname = "zzl_core"\npath = "../x"\n'
    )
    assert doc["defaultTargets"] == ["A", "B", "C"]
    assert doc["lean_lib"] == [{"name": "A", "roots": ["A"]}]
    assert doc["require"][0]["path"] == "../x"


def test_mini_toml_agrees_with_tomllib_on_every_island_lakefile():
    """Python < 3.11 has no tomllib; the fallback must read the real lakefiles identically."""
    import pathlib as _p
    from telperion.missions.coverage import _mini_toml

    tomllib = pytest.importorskip("tomllib")
    repo = _p.Path(__file__).resolve().parents[2]
    files = sorted((repo / "telperion" / "examples").glob("*/lean/**/lakefile.toml"))
    files = [f for f in files if ".lake" not in f.parts]
    if not files:
        pytest.skip("not running inside the repo")
    keys = ("name", "srcDir", "defaultTargets")
    for f in files:
        a, b = tomllib.loads(f.read_text()), _mini_toml(f.read_text())
        assert {k: a.get(k) for k in keys} == {k: b.get(k) for k in keys}, f
        for sect, fields in (("lean_lib", ("name", "roots", "globs", "srcDir")),
                             ("require", ("name", "path"))):
            assert [{k: x.get(k) for k in fields} for x in a.get(sect, [])] == \
                   [{k: x.get(k) for k in fields} for x in b.get(sect, [])], (f, sect)


def test_module_coverage_without_pyyaml_agrees_on_the_real_repo():
    """The dependency-free workflow parser must give the same steps and the same covered files
    as PyYAML on this repo's real workflows (the required `unit` job must not depend on it)."""
    import pathlib as _p
    from telperion.missions import coverage as cov

    pytest.importorskip("yaml")
    repo = _p.Path(__file__).resolve().parents[2]
    if not (repo / ".github" / "workflows").is_dir():
        pytest.skip("not running inside the repo")
    a = [(s.workflow, s.job, s.workdir, s.run.strip(), s.pipefail)
         for s in cov.ci_runnable_steps(repo)]
    b = [(s.workflow, s.job, s.workdir, s.run.strip(), s.pipefail)
         for s in cov.ci_runnable_steps(repo, use_yaml=False)]
    assert a == b
    assert set(cov.ci_covered_lean_files(repo)) == set(cov.ci_covered_lean_files(repo, use_yaml=False))


def test_every_proved_anduril_artifact_is_module_covered_on_the_real_repo():
    """The six zeta_reflection artifacts must be compiled by the zeta-reflection job itself."""
    import pathlib as _p
    from telperion.missions import coverage as cov

    repo = _p.Path(__file__).resolve().parents[2]
    lean = repo / "telperion" / "examples" / "zeta_reflection" / "lean"
    if not lean.is_dir() or not (repo / ".github" / "workflows").is_dir():
        pytest.skip("not running inside the repo")
    covered = cov.ci_covered_lean_files(repo)
    for mod in ("CheckBand", "ReflectedBand_t14", "EMZetaTail", "EMZetaComplex",
                "ForgeFirstZeroKernel", "StirlingBinet"):
        jobs = covered.get((lean / f"{mod}.lean").resolve(), set())
        assert "telperion-zeta-reflection.yml:zeta-reflection-compiles" in jobs, mod


# ---------------------------------------------------------------------------
# T11: the nine false-`proved` paths found by the 2026-09-19 gate audit.
# Each test is named for the attack it blocks, not for the function it calls.
# ---------------------------------------------------------------------------

def test_suffix_extension_does_not_satisfy_a_statement():
    """`NoZero s ∨ True` must not satisfy a node claiming `NoZero s`.

    The normalized statement ends at the conclusion, so plain containment is a prefix
    match: an artifact that CONTINUES the conclusion still contains it, and proves
    something strictly weaker.
    """
    from telperion.missions.verify import statement_matches

    stmt = "theorem zeta_nonzero (s : C) : NoZero s"
    assert not statement_matches("theorem zeta_nonzero (s : C) : NoZero s ∨ True := by simp", stmt)
    assert not statement_matches("theorem hard : RH → RH := fun h => h", "theorem hard : RH")
    # the honest forms still match, in both proof-body spellings
    assert statement_matches("theorem zeta_nonzero (s : C) : NoZero s := by simp", stmt)
    assert statement_matches("theorem zeta_nonzero (s : C) : NoZero s :=\n  foo", stmt)


def test_statement_inside_a_string_literal_does_not_count():
    from telperion.missions.verify import statement_matches

    stmt = "theorem p : P"
    assert not statement_matches('def msg : String := "theorem p : P := by trivial"', stmt)


def test_artifact_may_not_assume_what_it_claims_to_prove():
    """A self-supplied `axiom` or `unsafe` is an incompleteness marker."""
    from telperion.missions.verify import artifact_incompleteness_markers

    assert "axiom" in artifact_incompleteness_markers("axiom cheat : False\ntheorem t : P := cheat.elim")
    assert "unsafe" in artifact_incompleteness_markers("unsafe def f : Nat := 0")
    # the axiom guards' own idiom must NOT trip it
    assert artifact_incompleteness_markers("#print axioms foo\ntheorem t : P := trivial") == []


# ---------------------------------------------------------------------------
# T9b: marker hardening (closure run 2026-09-22, section 2b): the assumption regex was
# anchored at line start, so every modifier form of `axiom` / `unsafe` passed, and the
# trust-boundary escapes (opaque, implemented_by, extern, debug.skipKernelTC,
# ofReduceBool, sorryAx) were not scanned at all.
# ---------------------------------------------------------------------------

_PROVED = "theorem t : 1 + 1 = 2 := rfl\n"

#: (artifact suffix, marker it must produce). Every one of these returned [] before
#: 2026-09-23 -- the negative fixtures.
_MUST_TRIP = [
    ("private axiom cheat : False", "axiom"),
    ("protected axiom cheat : False", "axiom"),
    ("noncomputable axiom cheat : Nat", "axiom"),
    ("@[simp] axiom cheat : False", "axiom"),
    ("@[simp]\naxiom cheat : False", "axiom"),
    ("/-- doc -/ axiom cheat : False", "axiom"),
    ("@[reducible] private axiom cheat : False", "axiom"),
    # Lean needs no newline between commands
    ("theorem ok : True := trivial axiom cheat : False", "axiom"),
    ("private unsafe def u : Nat := 0", "unsafe"),
    ("@[inline] unsafe def u : Nat := 0", "unsafe"),
    ("opaque cheat : Nat", "opaque"),
    ("private opaque cheat : Nat", "opaque"),
    ("@[implemented_by id] def f (n : Nat) : Nat := n", "implemented_by"),
    ('@[extern "c_fn"] def f (n : Nat) : Nat := n', "extern"),
    ("set_option debug.skipKernelTC true in\ntheorem k : True := trivial", "debug.skipKernelTC"),
    ("theorem r : True := Lean.ofReduceBool true true rfl ▸ trivial", "ofReduceBool"),
    ("theorem r : True := ofReduceBool true true rfl ▸ trivial", "ofReduceBool"),
    ("theorem r : 2 = 2 := Lean.ofReduceNat 2 2 rfl", "ofReduceNat"),
    ("theorem s : False := sorryAx False", "sorryAx"),
    ("theorem s : False := sorryAx False true", "sorryAx"),
]


@pytest.mark.parametrize("suffix,marker", _MUST_TRIP)
def test_hardened_markers_catch_modifier_and_escape_forms(suffix, marker):
    assert marker in artifact_incompleteness_markers(_PROVED + suffix + "\n")


#: Positive fixtures: legitimate Lean that must stay clean. Mentions in comments / doc
#: comments are prose; longer identifiers that merely CONTAIN a token are not the token;
#: `#print axioms` is the guards' idiom.
_MUST_STAY_CLEAN = [
    "#print axioms t",
    "-- no axiom, no opaque, no sorryAx, no ofReduceBool, no debug.skipKernelTC\n",
    "/-- axiom-clean: `#print axioms t` = [propext, Classical.choice, Quot.sound];\n"
    "    no `opaque`, no `@[implemented_by]`, no `@[extern]`, 0 sorryAx -/\n"
    "theorem u : True := trivial",
    "/- nested /- opaque -/ axiom -/ theorem u : True := trivial",
    "theorem axiom_free : True := trivial",
    "theorem axiomatic' : True := trivial",
    "theorem my_axiom : True := trivial",
    "def opaqueness : Nat := 0",
    "def externalBound : Nat := 0",
    "def isUnsafeFree : Bool := true",
    "def unsafeCount : Nat := 0",
    "theorem sorryAxFree : True := trivial",
    "theorem ofReduceBoolish : True := trivial",
    "theorem skipKernelTCx : True := trivial",
    "set_option maxHeartbeats 400000 in\ntheorem u : True := trivial",
    "theorem d : 2 + 2 = 4 := by decide",
]


@pytest.mark.parametrize("suffix", _MUST_STAY_CLEAN)
def test_hardened_markers_leave_legitimate_lean_clean(suffix):
    assert artifact_incompleteness_markers(_PROVED + suffix + "\n") == []


def test_gate_refuses_grant_against_modifier_axiom(tmp_path):
    """End to end through `grant_status`: `private axiom` used to pass the gate."""
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    stmt = "theorem hard_thm : 1 + 1 = 3"
    node = _open_node_with_proof("Test.cheat", artifact="proof/Test_cheat.lean")
    save_node(node, root / "nodes" / "Test_cheat.toml")
    write_statement(root, node, stmt, manifest)

    artifact_path = root / "proof" / "Test_cheat.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(f"@[simp] private axiom cheat : False\n{stmt} := cheat.elim\n")

    campaign = load_campaign(root)
    with pytest.raises(GateError, match=r"carries axiom in Lean code"):
        grant_status(campaign, "Test_cheat")
    assert load_node(root / "nodes" / "Test_cheat.toml").status == "open"


def test_verify_campaign_flags_proved_node_with_opaque_artifact(tmp_path):
    """The read-only battery (what the required `unit` job runs) catches an escape token."""
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    manifest = _manifest()
    from telperion.missions.schema import save_manifest
    save_manifest(manifest, root / "mission.toml")

    stmt = "theorem esc_thm : 1 + 1 = 2"
    node = _open_node_with_proof("Test.esc", artifact="proof/Test_esc.lean")
    save_node(node, root / "nodes" / "Test_esc.toml")
    write_statement(root, node, stmt, manifest)

    artifact_path = root / "proof" / "Test_esc.lean"
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(
        "set_option debug.skipKernelTC true in\n"
        f"{stmt} := by decide\n"
        "@[implemented_by id] def g (n : Nat) : Nat := n\n"
    )
    save_node(dataclasses.replace(node, status="proved"), root / "nodes" / "Test_esc.toml")

    report = verify_campaign(root)
    assert not report.ok
    joined = " ".join(report.errors)
    assert "debug.skipKernelTC" in joined and "implemented_by" in joined


def test_island_attribution_survives_path_traversal(tmp_path):
    """`../built/../unbuilt/X.lean` must be judged by where the file IS, not how it is spelled."""
    from telperion.missions.coverage import artifact_coverage_error

    repo = tmp_path / "repo"
    for isl in ("wired", "unbuilt"):
        (repo / "telperion" / "examples" / isl / "lean").mkdir(parents=True)
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text(
        "jobs:\n  b:\n    steps:\n      - working-directory: telperion/examples/wired/lean\n"
        "        run: lake build\n"
    )
    sneaky = repo / "telperion" / "examples" / "wired" / "lean" / ".." / ".." / "unbuilt" / "lean" / "U.lean"
    err = artifact_coverage_error(sneaky, repo)
    assert err is not None and "unbuilt" in err


def test_disabled_step_does_not_vouch_for_an_island(tmp_path):
    """A `lake build` under `if: false` never runs, so it is not evidence."""
    from telperion.missions.coverage import ci_built_islands

    repo = tmp_path / "repo"
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    (wf / "ci.yml").write_text(
        "jobs:\n  b:\n    steps:\n      - if: false\n"
        "        working-directory: telperion/examples/ghost/lean\n        run: lake build\n"
    )
    assert "ghost" not in ci_built_islands(repo)


# ---------------------------------------------------------------------------
# T12: data-integrity findings from the 2026-09-19 audit.
# ---------------------------------------------------------------------------

def test_node_write_is_atomic_so_a_reader_never_sees_a_torn_file(tmp_path):
    """A concurrent reader must see the old file or the new one, never a prefix.

    The audit walked every byte prefix of all 66 live node files and found 201 truncation
    points that load as a VALID Node with a field missing -- `readback` in 64 of 66 files.
    Combined with the registry's read-modify-write, a torn read permanently erases the
    record that gates promote_to_open.
    """
    from telperion.missions.schema import atomic_write_text

    target = tmp_path / "n.toml"
    target.write_text("old")
    atomic_write_text(target, "new content")
    assert target.read_text() == "new content"
    # nothing left behind
    assert [q.name for q in tmp_path.iterdir()] == ["n.toml"]


def test_saving_a_node_preserves_blocks_the_schema_does_not_model(tmp_path):
    """`[nonvacuity]` and `proof.fidelity_note` must survive a load/save cycle.

    A live node carries both. `fidelity_note` records that its proof is kernel-verified
    locally and NOT on main CI -- exactly the kind of honesty field whose loss matters --
    and any CLI mutation used to erase 1978 characters of it silently.
    """
    from telperion.missions.schema import load_node, save_node

    src = tmp_path / "n.toml"
    src.write_text(
        'name = "T.x"\ntitle = "t"\nkind = "lemma"\nstatus = "open"\n'
        'statement_module = "Statements.T_x"\ndepends_on = []\n\n'
        '[proof]\nartifact = "a.lean"\nartifact_kind = "lean_module"\nvia = "direct"\n'
        'closure_clean = false\nfidelity_note = "verified locally, NOT on main CI"\n\n'
        '[nonvacuity]\nwitness = "a concrete instance"\n'
    )
    before = src.read_text()
    save_node(load_node(src), src)
    after = src.read_text()
    assert "nonvacuity" in after
    assert "fidelity_note" in after
    assert "verified locally, NOT on main CI" in after
    assert "a concrete instance" in after
    assert len(after) >= len(before) - 8  # ordering may shift; content must not be lost


def test_open_leaves_survives_a_cross_campaign_dependency(tmp_path):
    """A qualified `<campaign>:<slug>` dep must not KeyError the command sessions run first."""
    from telperion.missions.registry import open_leaves
    from telperion.missions.schema import Node, Proof

    node = Node(name="T.x", title="t", kind="lemma", status="open",
                depends_on=("other:OTHER_dep",), statement_module="Statements.T_x")

    class _Campaign:
        nodes = {"T_x": node}
        root = tmp_path / "home"

    # unresolvable external dep counts as not proved, so the node is simply not a leaf
    assert open_leaves(_Campaign()) == []


# --- what closure_clean actually is, pinned so the docstring cannot drift again ------
#
# grant_status writes closure_clean as a copy of status.  _compute_closures then seeds
# from the stored flag and recomputes only `via = "reduction"` nodes, and verify_campaign
# cross-checks only reductions.  So for a DIRECT proof the flag is never derived from
# anything, and it is not a statement about discharged hypotheses.
#
# These tests do not ask anyone to "fix" that.  Preserving a stored False cannot work:
# nodes are authored with False, so every first-time grant would stay dirty.  Telling a
# deliberate False from a default one needs the closure_override_reason field of
# ascent-plan ops F1-3/F1-4, which is an owner's decision.  The behaviour is pinned here
# so the next reader is not misled by a docstring again.

def _granted_node(tmp_path, name, stmt):
    root = tmp_path / "campaign"
    root.mkdir()
    (root / "nodes").mkdir()
    from telperion.missions.schema import save_manifest
    save_manifest(_manifest(), root / "mission.toml")
    slug = slug_of(name)
    node = _open_node_with_proof(name, artifact=f"proof/{slug}.lean")
    assert node.proof.closure_clean is False, "every new node is authored dirty"
    save_node(node, root / "nodes" / f"{slug}.toml")
    write_statement(root, node, stmt, _manifest())
    art = root / "proof" / f"{slug}.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text(f"{stmt}\n  := by\n  simp\n")
    return root, slug


def test_grant_writes_closure_clean_as_a_copy_of_status(tmp_path):
    root, slug = _granted_node(tmp_path, "Test.flag", "theorem lemma_flag : 1 + 1 = 2")
    granted = grant_status(load_campaign(root), slug)
    assert granted.status == "proved"
    assert granted.proof.closure_clean is True, (
        "granting turns the authored False into True: a copy of status, not a derived "
        "fact about discharged hypotheses"
    )


def test_a_hand_set_dirty_flag_survives_for_a_direct_proof(tmp_path):
    """The only way to record a deliberate ruling today is to set it AFTER granting."""
    import dataclasses

    from telperion.missions.verify import _compute_closures

    root, slug = _granted_node(tmp_path, "Test.ruled", "theorem lemma_ruled : 2 + 2 = 4")
    grant_status(load_campaign(root), slug)
    campaign = load_campaign(root)
    node = campaign.nodes[slug]
    assert node.proof.closure_clean is True
    ruled = dataclasses.replace(node, proof=dataclasses.replace(node.proof, closure_clean=False))
    save_node(ruled, root / "nodes" / f"{slug}.toml")

    campaign = load_campaign(root)
    assert _compute_closures(campaign)[slug] is False, (
        "a direct proof's stored flag is authoritative; a hand-set ruling must survive"
    )

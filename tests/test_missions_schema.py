"""Schema round-trip, validation, and the closed-loop TOML fallback."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.missions.schema import (  # noqa: E402
    Claim, MissionManifest, Node, Proof, Readback, SchemaError,
    dumps_toml, load_claim, load_manifest, load_node, loads_toml,
    save_claim, save_manifest, save_node, slug_of,
)


def node(**kw):
    base = dict(name="BG.master_inequality", title="Master inequality",
                kind="milestone", status="draft", depends_on=("BG_g_step",),
                statement_module="Statements.BG_master_inequality",
                created="2026-09-11", updated="2026-09-11")
    base.update(kw)
    return Node(**base)


def test_slug_of_replaces_dots():
    assert slug_of("BG.master_inequality") == "BG_master_inequality"


def test_node_roundtrip_via_files(tmp_path):
    n = node(proof=Proof("proof/formalization/PotentialFinal.lean",
                         "lean_module", "direct", True),
             readback=Readback("says phi <= 1 on branches", "operator", "2026-09-11"))
    p = tmp_path / "n.toml"
    save_node(n, p)
    assert load_node(p) == n


def test_toml_dump_is_deterministic_and_sorted(tmp_path):
    n1, n2 = node(), node()
    assert dumps_toml(loads_toml(dumps_toml({"b": 1, "a": ["x", "y"]}))) == \
           dumps_toml({"a": ["x", "y"], "b": 1})
    p1, p2 = tmp_path / "a.toml", tmp_path / "b.toml"
    save_node(n1, p1); save_node(n2, p2)
    assert p1.read_text() == p2.read_text()


def test_mini_reader_parses_what_writer_emits():
    doc = {"name": "X.y", "n": 3, "flag": True, "deps": ["a", "b"],
           "proof": {"artifact": "p.lean", "closure_clean": False}}
    assert loads_toml(dumps_toml(doc)) == doc


def test_invalid_status_raises(tmp_path):
    with pytest.raises(SchemaError, match="status"):
        node(status="pending")


def test_deprecated_requires_reason():
    with pytest.raises(SchemaError, match="deprecated_reason"):
        node(status="deprecated")
    node(status="deprecated", deprecated_reason="superseded by BG.v2")  # ok


def test_proved_requires_proof():
    with pytest.raises(SchemaError, match="proof"):
        node(status="proved")


def test_dumps_roundtrip_embedded_newline_and_equals():
    # A value containing \n and " = " must survive dumps->loads->dumps unchanged.
    tricky = "line one\nkey = value\r\nline three"
    doc = {"note": tricky}
    assert loads_toml(dumps_toml(doc)) == doc
    assert dumps_toml(loads_toml(dumps_toml(doc))) == dumps_toml(doc)


def test_manifest_roundtrip_via_files(tmp_path):
    m = MissionManifest(
        name="BG.mission",
        title="Bethe-Gurland inequality campaign",
        description="Prove the BG conjecture end-to-end",
        goal_node="BG.master_inequality",
        environment_toolchain="leanprover/lean4:v4.33.1",
        environment_mathlib_rev="abc123",
        sources=("Statements/BG.lean", "Proofs/BG_final.lean"),
    )
    p = tmp_path / "mission.toml"
    save_manifest(m, p)
    assert load_manifest(p) == m


def test_claim_roundtrip_via_files(tmp_path):
    # Claim with superseded set
    c1 = Claim(node="BG.master_inequality", session="sess-abc",
               started="2026-09-11T10:00:00", ttl_hours=48,
               note="working on it", superseded="sess-old")
    p1 = tmp_path / "claim1.toml"
    save_claim(c1, p1)
    assert load_claim(p1) == c1

    # Claim with all defaults
    c2 = Claim(node="BG.phi_le_one", session="sess-xyz", started="2026-09-11T12:00:00")
    p2 = tmp_path / "claim2.toml"
    save_claim(c2, p2)
    assert load_claim(p2) == c2


def test_load_node_missing_key_raises_schema_error_with_path(tmp_path):
    # A TOML file missing the required 'name' field should raise SchemaError
    # whose message includes the file path.
    p = tmp_path / "broken.toml"
    p.write_text('title = "Missing name field"\nkind = "milestone"\nstatus = "draft"\n')
    with pytest.raises(SchemaError) as exc_info:
        load_node(p)
    assert str(p) in str(exc_info.value)

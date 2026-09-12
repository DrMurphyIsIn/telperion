"""Statements: render, write, regen_diff, scaffold_package."""
from __future__ import annotations

import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, SchemaError, slug_of,
)
from telperion.missions.statements import (  # noqa: E402
    statement_path,
    render_statement,
    write_statement,
    regen_diff,
    scaffold_package,
)

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _manifest() -> MissionManifest:
    return MissionManifest(
        name="Demo.goal",
        title="Demo Campaign",
        description="A synthetic demonstration campaign.",
        goal_node="Demo_goal",
        environment_toolchain="leanprover/lean4:v4.33.1",
        environment_mathlib_rev="abc123deadbeef",
        sources=(),
    )


def _node(name: str = "Demo.goal") -> Node:
    return Node(
        name=name,
        title="Demo goal theorem",
        kind="goal",
        status="draft",
        depends_on=(),
        statement_module=f"Statements.{slug_of(name)}",
        created="2026-09-11",
        updated="2026-09-11",
    )


STMT_WITHOUT_BODY = "theorem demo_goal (n : Nat) : n + 0 = n"
STMT_WITH_SORRY = "theorem demo_goal (n : Nat) : n + 0 = n := by sorry"
STMT_WITH_PLAIN_SORRY = "theorem demo_goal (n : Nat) : n + 0 = n := sorry"
STMT_WITH_IMPORTS = """\
import Mathlib.Algebra.Order.Ring.Lemmas
open Nat

theorem demo_goal (n : Nat) : n + 0 = n"""

# ---------------------------------------------------------------------------
# T1: render contains header + hash + normalized `:= by sorry`
# ---------------------------------------------------------------------------

def test_render_statement_header_and_body():
    node = _node()
    manifest = _manifest()
    content = render_statement(node, STMT_WITHOUT_BODY, manifest)

    # Header must start with the DO-NOT-EDIT sentinel
    assert "DO NOT EDIT BY HAND" in content
    # Header must reference the node slug
    slug = slug_of(node.name)
    assert f"node {slug}" in content
    # Header must contain a 16-char hex hash
    import re
    match = re.search(r"sha256 ([0-9a-f]{16})", content)
    assert match is not None, f"No 16-char sha256 found in header: {content!r}"
    # Statement body must end with := by sorry (normalized)
    assert content.rstrip().endswith(":= by sorry")
    # Already-normalized form must not be double-appended
    content2 = render_statement(node, STMT_WITH_SORRY, manifest)
    assert content2.count(":= by sorry") == 1
    # := sorry form must also be left as-is
    content3 = render_statement(node, STMT_WITH_PLAIN_SORRY, manifest)
    assert ":= sorry" in content3
    assert content3.count(":= by sorry") == 0


# ---------------------------------------------------------------------------
# T2: write then regen_diff == ""
# ---------------------------------------------------------------------------

def test_write_then_regen_diff_empty(tmp_path):
    node = _node()
    manifest = _manifest()
    root = tmp_path / "campaign"
    root.mkdir()

    written = write_statement(root, node, STMT_WITHOUT_BODY, manifest)
    assert written.exists()
    # Immediately after writing, regen_diff must be ""
    diff = regen_diff(root, node, manifest)
    assert diff == "", f"Expected empty diff but got: {diff!r}"


# ---------------------------------------------------------------------------
# T3: hand-edit -> regen_diff nonempty naming the node
# ---------------------------------------------------------------------------

def test_hand_edit_regen_diff_nonempty(tmp_path):
    node = _node()
    manifest = _manifest()
    root = tmp_path / "campaign"
    root.mkdir()

    written = write_statement(root, node, STMT_WITHOUT_BODY, manifest)
    # Simulate a hand edit: append a space to the file content
    original = written.read_text()
    written.write_text(original + "\n-- hand edit\n")

    diff = regen_diff(root, node, manifest)
    assert diff != "", "Expected nonempty diff after hand edit"
    # The diff description must name the node slug
    slug = slug_of(node.name)
    assert slug in diff, f"Expected slug {slug!r} in diff message: {diff!r}"


# ---------------------------------------------------------------------------
# T4: scaffold writes toolchain and lakefile with manifest env verbatim
# ---------------------------------------------------------------------------

def test_scaffold_package_toolchain_and_lakefile(tmp_path):
    manifest = _manifest()
    root = tmp_path / "campaign"
    root.mkdir()

    written = scaffold_package(root, manifest)
    paths = {p.name: p for p in written}

    # lean-toolchain must exist
    assert "lean-toolchain" in paths, f"lean-toolchain missing from {list(paths)}"
    toolchain_text = paths["lean-toolchain"].read_text()
    assert toolchain_text.strip() == manifest.environment_toolchain

    # lakefile.toml must exist
    assert "lakefile.toml" in paths, f"lakefile.toml missing from {list(paths)}"
    lakefile_text = paths["lakefile.toml"].read_text()
    assert manifest.environment_mathlib_rev in lakefile_text
    assert "Statements" in lakefile_text
    # Both must be present or deep-lean is silently vacuous / lake update fails
    assert 'defaultTargets = ["Statements"]' in lakefile_text, \
        "defaultTargets missing -- lake build would be a no-op"
    assert 'scope = "leanprover-community"' in lakefile_text, \
        "mathlib scope missing -- lake update would fail"


# ---------------------------------------------------------------------------
# T5: root module imports all statement modules sorted
# ---------------------------------------------------------------------------

def test_scaffold_root_module_sorted_imports(tmp_path):
    manifest = _manifest()
    root = tmp_path / "campaign"
    root.mkdir()

    # Write two statement files for two different nodes
    node_a = _node("Demo.alpha")
    node_b = _node("Demo.zeta")
    write_statement(root, node_a, STMT_WITHOUT_BODY, manifest)
    write_statement(root, node_b, STMT_WITHOUT_BODY, manifest)

    # Now scaffold; root module should import both
    written = scaffold_package(root, manifest)
    paths = {p.name: p for p in written}
    assert "Statements.lean" in paths, f"Statements.lean missing from {list(paths)}"

    root_text = paths["Statements.lean"].read_text()
    # Both slugs must appear as imports
    assert "Statements.Demo_alpha" in root_text
    assert "Statements.Demo_zeta" in root_text

    # Imports must be sorted
    lines = [l for l in root_text.splitlines() if l.startswith("import")]
    assert lines == sorted(lines), f"Imports not sorted: {lines}"

"""One-shot script to create the demo fixture using schema.save_* functions.

Run from the telperion/ directory:
    python3 tests/fixtures/missions/create_demo.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "src"))

from telperion.missions.schema import (
    MissionManifest, Node, Readback,
    save_manifest, save_node,
)

HERE = Path(__file__).parent / "demo"


def main():
    HERE.mkdir(parents=True, exist_ok=True)
    nodes_dir = HERE / "nodes"
    nodes_dir.mkdir(exist_ok=True)

    # mission.toml
    manifest = MissionManifest(
        name="Demo.goal",
        title="Demo Campaign",
        description="A synthetic demonstration campaign for testing the registry.",
        goal_node="Demo_goal",
        environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    save_manifest(manifest, HERE / "mission.toml")

    # Demo_goal: goal, draft, depends on Demo_lemma_a + Demo_lemma_b
    save_node(Node(
        name="Demo.goal",
        title="Demo goal theorem",
        kind="goal",
        status="draft",
        depends_on=("Demo_lemma_a", "Demo_lemma_b"),
        statement_module="Statements.Demo_goal",
        created="2026-09-11",
        updated="2026-09-11",
    ), nodes_dir / "Demo_goal.toml")

    # Demo_lemma_a: open, readback recorded
    save_node(Node(
        name="Demo.lemma_a",
        title="Demo lemma A",
        kind="lemma",
        status="open",
        depends_on=(),
        statement_module="Statements.Demo_lemma_a",
        readback=Readback(
            text="This statement says lemma A holds unconditionally.",
            auditor="operator",
            date="2026-09-11",
        ),
        created="2026-09-11",
        updated="2026-09-11",
    ), nodes_dir / "Demo_lemma_a.toml")

    # Demo_lemma_b: draft (no readback)
    save_node(Node(
        name="Demo.lemma_b",
        title="Demo lemma B",
        kind="lemma",
        status="draft",
        depends_on=(),
        statement_module="Statements.Demo_lemma_b",
        created="2026-09-11",
        updated="2026-09-11",
    ), nodes_dir / "Demo_lemma_b.toml")

    # Demo_dead: deprecated with reason
    save_node(Node(
        name="Demo.dead",
        title="Deprecated dead node",
        kind="lemma",
        status="deprecated",
        depends_on=(),
        statement_module="Statements.Demo_dead",
        deprecated_reason="Superseded by Demo.lemma_a",
        created="2026-09-11",
        updated="2026-09-11",
    ), nodes_dir / "Demo_dead.toml")

    print("Demo fixture written to", HERE)


if __name__ == "__main__":
    main()

"""Shared, minimal node fixtures for mission schema/provenance/CLI tests.

No `__init__.py` or `conftest.py` lives in tests/; pytest's rootdir-based sys.path
insertion (classic "prepend" import mode, no package markers) puts tests/ itself on
sys.path when a test file here is collected, so a plain `from missions_fixtures import
...` resolves -- `from tests.missions_fixtures import ...` would not.
"""
from pathlib import Path

from telperion.missions.schema import Node, Proof


def minimal_proved_node(root: Path, *, heavy: bool) -> Node:
    (root / "Art.lean").write_text("theorem t : True := trivial\n")
    proof = Proof(artifact="Art.lean", artifact_kind="lean_module", via="direct")
    return Node(name="n", title="t", kind="lemma", status="proved", depends_on=(),
                statement_module="S", proof=proof, heavy_certificates=heavy)

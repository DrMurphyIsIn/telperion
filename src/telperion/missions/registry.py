"""Missions campaign registry: load, DAG, open-leaves, transitions, renders.

All mutators (promote_to_open, deprecate, set_proof) save the modified node
file and bump `updated` to today's ISO date. They never grant `proved` or
`refuted` status — that is the exclusive domain of the verification gate
(Task 6, `mission verify`).

Status-machine transitions implemented here:
  draft --(readback recorded)--> open        [promote_to_open]
  any   --(with reason)--------> deprecated  [deprecate]
  open  --(proof linked)-------> open        [set_proof, status unchanged]

The `proved`/`refuted` flip is reserved for the verify gate.
"""
from __future__ import annotations

import dataclasses
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import Dict, List, Optional

from .schema import (
    Claim, MissionManifest, Node, Proof, SchemaError,
    load_manifest, load_node, save_node, slug_of,
)

# Status display glyphs (emitted in string output; never enter QuantConnect code)
_GLYPHS = {
    "draft":      "·",
    "open":       "○",
    "proved":     "✓",
    "refuted":    "✗",
    "deprecated": "†",
}


# ---------------------------------------------------------------------------
# Campaign dataclass
# ---------------------------------------------------------------------------

@dataclass
class Campaign:
    root: Path
    manifest: MissionManifest
    nodes: Dict[str, Node]   # keyed by slug


# ---------------------------------------------------------------------------
# Load
# ---------------------------------------------------------------------------

def load_campaign(root: Path) -> Campaign:
    """Load a campaign from *root* (a directory containing mission.toml + nodes/).

    Raises SchemaError if:
    - mission.toml or any node file is malformed
    - two node files have the same slug (duplicate name)
    - a depends_on target slug is not present in the loaded node set
    - the dependency graph contains a cycle (assert_acyclic is called here)
    """
    root = Path(root)
    manifest = load_manifest(root / "mission.toml")

    nodes: Dict[str, Node] = {}
    nodes_dir = root / "nodes"
    if nodes_dir.is_dir():
        for toml_file in sorted(nodes_dir.glob("*.toml")):
            node = load_node(toml_file)
            sl = slug_of(node.name)
            if sl in nodes:
                raise SchemaError(
                    f"Duplicate node slug {sl!r}: found in both "
                    f"{toml_file.name} and a previously loaded file."
                )
            nodes[sl] = node

    # Validate depends_on references
    for sl, node in nodes.items():
        for dep in node.depends_on:
            if dep not in nodes:
                raise SchemaError(
                    f"Node {sl!r} depends_on {dep!r} which is not in the campaign."
                )

    campaign = Campaign(root=root, manifest=manifest, nodes=nodes)
    assert_acyclic(campaign)
    return campaign


# ---------------------------------------------------------------------------
# DAG invariants
# ---------------------------------------------------------------------------

def assert_acyclic(campaign: Campaign) -> None:
    """Raise SchemaError naming a cycle if the dependency graph is cyclic."""
    # Iterative DFS with three-colour marking: 0=unvisited, 1=in-stack, 2=done
    WHITE, GREY, BLACK = 0, 1, 2
    color: Dict[str, int] = {sl: WHITE for sl in campaign.nodes}

    for start in campaign.nodes:
        if color[start] != WHITE:
            continue
        # DFS stack holds (slug, iterator-over-its-deps)
        stack: List[tuple] = [(start, iter(campaign.nodes[start].depends_on))]
        color[start] = GREY

        while stack:
            slug, deps_iter = stack[-1]
            try:
                dep = next(deps_iter)
            except StopIteration:
                color[slug] = BLACK
                stack.pop()
                continue

            if color.get(dep, BLACK) == GREY:
                # Back-edge: collect the cycle from the stack
                cycle_slugs = [s for s, _ in stack]
                idx = next(i for i, s in enumerate(cycle_slugs) if s == dep)
                cycle = cycle_slugs[idx:] + [dep]
                raise SchemaError(
                    f"Dependency cycle detected: {' -> '.join(cycle)}"
                )
            if color.get(dep, BLACK) == WHITE:
                color[dep] = GREY
                stack.append((dep, iter(campaign.nodes[dep].depends_on)))


# ---------------------------------------------------------------------------
# Open-leaves query
# ---------------------------------------------------------------------------

def open_leaves(
    campaign: Campaign,
    claims: Optional[Dict[str, Claim]] = None,
    include_claimed: bool = False,
) -> List[Node]:
    """Return open nodes whose every dependency is proved.

    A node with no dependencies is a leaf candidate if it is open.
    Freshly-claimed nodes are excluded unless *include_claimed* is True.

    Staleness semantics for claims belong to Task 3 (claims.load_fresh_claims).
    Callers pass ONLY fresh (non-expired) claims here; this function does not
    inspect TTL or claim timestamps. See claims.load_fresh_claims (Task 3).

    Args:
        campaign: loaded campaign.
        claims: mapping of node-slug -> Claim containing ONLY fresh claims
            (staleness filtering is the caller's responsibility).
        include_claimed: if False (default), exclude nodes that have an
            active claim in *claims*.

    Returns:
        List of Node objects satisfying the criteria, in deterministic order
        (sorted by slug).
    """
    claimed_slugs: set = set()
    if claims and not include_claimed:
        claimed_slugs = {slug_of(c.node) for c in claims.values()}

    result: List[Node] = []
    for sl in sorted(campaign.nodes):
        node = campaign.nodes[sl]
        if node.status != "open":
            continue
        if sl in claimed_slugs:
            continue
        # All dependencies must be proved
        all_deps_proved = all(
            campaign.nodes[dep].status == "proved"
            for dep in node.depends_on
        )
        if all_deps_proved:
            result.append(node)
    return result


# ---------------------------------------------------------------------------
# Mutators
# ---------------------------------------------------------------------------

def _today() -> str:
    return date.today().isoformat()


def _load_and_save(campaign: Campaign, slug: str, **changes) -> Node:
    """Load node from disk, apply changes via dataclasses.replace, save, return.

    Also updates campaign.nodes[slug] so callers see the new state without
    reloading the campaign.
    """
    node_path = campaign.root / "nodes" / f"{slug}.toml"
    node = load_node(node_path)
    new_node = dataclasses.replace(node, updated=_today(), **changes)
    save_node(new_node, node_path)
    campaign.nodes[slug] = new_node
    return new_node


def promote_to_open(campaign: Campaign, slug: str) -> Node:
    """Transition a draft node to open.

    Raises SchemaError if:
    - the node's status is not 'draft' (only draft->open is a valid transition here)
    - no readback is recorded on the node

    This is the ONLY draft->open path. The status guard is checked first so that
    callers cannot accidentally reopen proved/refuted/deprecated nodes.

    Loads the node exactly once: guard check and mutation happen on the
    same in-memory object, eliminating the TOCTOU window of a separate
    pre-check load.
    """
    node_path = campaign.root / "nodes" / f"{slug}.toml"
    node = load_node(node_path)
    if node.status != "draft":
        raise SchemaError(
            f"Cannot promote {slug!r} to open: status is {node.status!r}, "
            "only draft->open is allowed by promote_to_open."
        )
    if node.readback is None:
        raise SchemaError(
            f"Cannot promote {slug!r} to open: no readback recorded. "
            "Record a readback first (mission audit <slug>)."
        )
    new_node = dataclasses.replace(node, status="open", updated=_today())
    save_node(new_node, node_path)
    campaign.nodes[slug] = new_node
    return new_node


def deprecate(campaign: Campaign, slug: str, reason: str) -> Node:
    """Mark any node as deprecated, recording *reason*.

    SchemaError is raised by the Node schema if reason is empty.
    """
    if not reason:
        raise SchemaError(
            f"Cannot deprecate {slug!r}: reason must be non-empty."
        )
    return _load_and_save(campaign, slug, status="deprecated", deprecated_reason=reason)


def set_proof(campaign: Campaign, slug: str, proof: Proof) -> Node:
    """Record a proof artifact link on an open node.

    The status is intentionally NOT changed to 'proved' here. The status
    flip belongs to the verification gate (Task 6, mission verify), which
    kernel-checks the artifact and validates statement match. This function
    records the link and saves the node.
    """
    return _load_and_save(campaign, slug, proof=proof)


# ---------------------------------------------------------------------------
# Renders
# ---------------------------------------------------------------------------

def render_status(campaign: Campaign, claims: Optional[Dict[str, Claim]] = None) -> str:
    """Return a one-glance tree of the campaign with statuses.

    Format:
        <title>
          <glyph> <slug>  (<kind>, <status>)  [-> dep1, dep2, ...]
              (reduction, closure_clean=<bool>)   [if applicable]
    """
    lines = [campaign.manifest.title, ""]
    for sl in sorted(campaign.nodes):
        node = campaign.nodes[sl]
        glyph = _GLYPHS.get(node.status, "?")
        dep_str = ""
        if node.depends_on:
            dep_str = "  -> " + ", ".join(node.depends_on)
        lines.append(f"  {glyph} {sl}  ({node.kind}, {node.status}){dep_str}")
        # Annotation for reduction proofs
        if node.proof is not None and node.proof.via == "reduction":
            cc = str(node.proof.closure_clean).lower()
            lines.append(f"      (reduction, closure_clean={cc})")
    return "\n".join(lines) + "\n"


def render_dot(campaign: Campaign) -> str:
    """Return a DOT-language representation of the dependency DAG."""
    name = campaign.manifest.name.replace(".", "_")
    lines = [f'digraph {name} {{', '  rankdir=BT;']
    for sl in sorted(campaign.nodes):
        node = campaign.nodes[sl]
        glyph = _GLYPHS.get(node.status, "?")
        label = f"{glyph} {sl}"
        lines.append(f'  "{sl}" [label="{label}"];')
    for sl in sorted(campaign.nodes):
        node = campaign.nodes[sl]
        for dep in node.depends_on:
            lines.append(f'  "{sl}" -> "{dep}";')
    lines.append("}")
    return "\n".join(lines) + "\n"

"""Per-cert dependency extraction — the AXLE ``extract_decls`` lesson.

When many emitted certificate theorems share atoms (e.g. ``log54_sub_fstar_le`` is
reused by dozens of BG cells), you need to know, PER CERT, which other declarations
it leans on so you can:

* emit a single cert STANDALONE (pull in exactly its transitive atoms), and
* on changing a shared atom, re-verify EXACTLY the certs it touches (impact
  analysis) — not the whole bundle.

This module is pure text / graph — no Lean elaboration.  Reference detection is a
word-boundary match of a block's text against the corpus of KNOWN declaration
names (the bundle's own theorem/def names); Mathlib names are simply never in the
corpus and never counted.

conjecture1_proved = False.
"""
from __future__ import annotations

import re

from .bundle import parse_theorems, topo_sort_blocks

__all__ = ["extract_deps", "DepGraph", "minimal_snippet"]


def extract_deps(theorem_block: str, known_names) -> set:
    """Names from ``known_names`` that ``theorem_block`` references.

    Word-boundary match; the block's OWN declaration name (the first
    ``theorem``/``lemma``/``def`` header in the block) is excluded so a theorem is
    never reported as depending on itself.  ``known_names`` is the corpus of
    theorem/def names (an iterable); Mathlib names not in the corpus are ignored.
    """
    known = set(known_names)
    own = _own_name(theorem_block)
    refs = set()
    for cand in known:
        if cand == own:
            continue
        # Unicode-aware identifier boundary: Lean names contain Greek letters
        # (e.g. `ρwit`), primes, dots.  `\w` matches Unicode word chars in Py3, so
        # an ASCII-only boundary mis-splits `ρwit` and drops such deps entirely.
        if re.search(
            r"(?<![\w'.])" + re.escape(cand) + r"(?![\w'.])",
            theorem_block,
        ):
            refs.add(cand)
    return refs


# Name starts with a Unicode letter or `_` (not a digit), then word-chars / prime / dot.
_HEADER = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+((?![0-9])[\w'.]+)", re.M)


def _own_name(block: str):
    m = _HEADER.search(block)
    return m.group(1) if m else None


def _as_pairs(items) -> list:
    """Coerce input to a list of ``(name, block)`` pairs.

    Accepts either a list of ``(name, block)`` tuples, or the output of
    :func:`telperion.bundle.parse_theorems` (list of ``{"name","block",...}`` dicts).
    """
    pairs = []
    for it in items:
        if isinstance(it, dict):
            pairs.append((it["name"], it["block"]))
        else:
            name, block = it
            pairs.append((name, block))
    return pairs


class DepGraph:
    """Dependency graph over a corpus of named Lean blocks.

    Build from a list of ``(name, block)`` pairs OR from
    :func:`telperion.bundle.parse_theorems` output.  Edges are ``B -> A`` meaning
    "B references A" (B depends on A).
    """

    def __init__(self, items):
        pairs = _as_pairs(items)
        # first-seen order; first block wins for a repeated name.
        self._order: list = []
        self.blocks: dict = {}
        for name, block in pairs:
            if name not in self.blocks:
                self.blocks[name] = block
                self._order.append(name)
        self._names = set(self._order)
        # direct deps per name.
        self._deps: dict = {
            name: extract_deps(self.blocks[name], self._names) - {name}
            for name in self._order
        }
        # reverse edges.
        self._rev: dict = {name: set() for name in self._order}
        for name in self._order:
            for a in self._deps[name]:
                self._rev[a].add(name)

    # --- direct / transitive edges ------------------------------------------

    @property
    def names(self) -> list:
        """Declaration names in first-seen order."""
        return list(self._order)

    def deps(self, name: str) -> set:
        """Direct dependencies of ``name`` (names it references)."""
        return set(self._deps.get(name, set()))

    def transitive_deps(self, name: str) -> set:
        """All names reachable via dependency edges from ``name`` (excl. ``name``)."""
        return self._reach(name, self._deps)

    def dependents(self, name: str) -> set:
        """Direct reverse-dependents of ``name`` (names that reference it)."""
        return set(self._rev.get(name, set()))

    def transitive_dependents(self, name: str) -> set:
        """All names that (transitively) depend on ``name`` (excl. ``name``)."""
        return self._reach(name, self._rev)

    #: ``impact`` is the transitive dependent set — when a shared atom changes,
    #: exactly which certs must be re-verified.
    def impact(self, name: str) -> set:
        """Transitive dependents of ``name`` — the re-verification blast radius."""
        return self.transitive_dependents(name)

    def _reach(self, name: str, adj: dict) -> set:
        seen: set = set()
        stack = list(adj.get(name, set()))
        while stack:
            cur = stack.pop()
            if cur in seen or cur == name:
                continue
            seen.add(cur)
            stack.extend(adj.get(cur, set()))
        seen.discard(name)
        return seen

    # --- dead-atom detection -------------------------------------------------

    def dead_atoms(self, roots) -> set:
        """Names NOT reachable (as a dependency) from any root in ``roots``.

        ``roots`` is the set of goal/root theorem names being assembled.  A name is
        LIVE if it is a root or a transitive dependency of some root; everything
        else is a dead atom (present in the corpus but never pulled in by a goal).
        """
        roots = [r for r in roots if r in self._names]
        live: set = set(roots)
        for r in roots:
            live |= self.transitive_deps(r)
        return self._names - live


def minimal_snippet(name: str, all_blocks) -> str:
    """Self-contained Lean text for ``name`` + its transitive deps, topo-ordered.

    ``all_blocks`` is a list of ``(name, block)`` pairs or
    :func:`telperion.bundle.parse_theorems` output.  The returned string contains
    the block for ``name`` and every block it transitively depends on, ordered so
    each declaration appears BEFORE it is used (via
    :func:`telperion.bundle.topo_sort_blocks`).  No imports/namespace wrapping —
    it is the raw declaration bundle for a single cert.
    """
    g = DepGraph(all_blocks)
    if name not in g.blocks:
        raise KeyError(f"unknown declaration: {name!r}")

    wanted = {name} | g.transitive_deps(name)
    # Reconstruct dicts (name/statement/block) for the wanted subset, in first-seen
    # order, then topo-sort so deps precede dependents.
    subset = [
        {"name": nm, "statement": "", "block": g.blocks[nm]}
        for nm in g.names
        if nm in wanted
    ]
    ordered, _cycles = topo_sort_blocks(subset)
    return "\n\n".join(b["block"] for b in ordered) + "\n"

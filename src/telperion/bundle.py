"""Assemble many emitted certificate theorems into ONE Lean file, dedup'ing shared atoms.

The AXLE ``merge`` (+ ``merge_duplicates``) lesson: an emitter run per BG cell
produces one small Lean file each, and many cells reuse the SAME enclosure lemmas
(e.g. ``log54_sub_fstar_le`` is proved identically by several cells).  Emitting
each cell's file independently and then concatenating gives a Lean file that fails
to elaborate — the shared lemma is declared twice.  :func:`merge_bundle` collects
the theorem blocks from every source, keeps the FIRST occurrence of each name, and
drops later duplicates — but only when they are genuinely identical.  Two theorems
with the same NAME but DIFFERENT statements are a CONFLICT (an emitter bug or a
cell mismatch), and are surfaced loudly as ``ValueError`` rather than silently
merged.

Pure text: no Lean build is needed to parse/merge/stat.  The merged source can be
handed to :func:`telperion.verify.verify_lean` against a built environment to
kernel-check the whole assembled family in one pass.

conjecture1_proved = False.
"""
from __future__ import annotations

import hashlib
import re

from .normalize import canonical_statement

# A theorem/lemma header: `theorem <name>` or `lemma <name>` at line start (allowing
# a leading `@[...]` attribute or `private`/`noncomputable` etc. is out of scope — the
# emitted certificate blocks start plainly with the keyword).
_THM_HEADER = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")

# Lines that terminate a block WITHOUT being part of it (top-level structural lines).
_STRUCTURAL = re.compile(r"^(namespace|open|import|end|#)")

# A leading doc-comment line: `--` line comment or a `/- ... -/` block comment line.
_DOC_LINE = re.compile(r"^\s*(--|/-|-/|\|)")


def parse_theorems(content: str) -> list:
    """Split a Lean file (or emitted text) into theorem/lemma blocks.

    Returns a list of dicts ``{"name", "statement", "block"}`` in file order.

    - ``block`` runs from the ``theorem``/``lemma`` keyword (INCLUDING any leading
      ``--`` / ``/- -/`` doc-comment lines immediately above it) up to the next
      top-level ``theorem``/``lemma``/``end``/``namespace``/``open``/``import``/``#``
      line, or EOF.
    - ``statement`` is the text between the name and the ``:=`` (the signature),
      whitespace-collapsed.
    - ``namespace``/``open``/``import``/``end``/``#print`` lines are ignored.
    """
    lines = content.splitlines()
    n = len(lines)
    blocks = []
    i = 0
    while i < n:
        m = _THM_HEADER.match(lines[i])
        if not m:
            i += 1
            continue

        name = m.group(2)
        header_idx = i

        # Absorb a contiguous run of doc-comment lines IMMEDIATELY above the header.
        start = header_idx
        j = header_idx - 1
        while j >= 0 and _DOC_LINE.match(lines[j]):
            start = j
            j -= 1

        # Advance to the end of this block: next top-level theorem/lemma/structural
        # line, or EOF.  (A structural/header line that is INSIDE the proof body would
        # be indented; we only break on column-0 matches, which the keywords are.)
        k = header_idx + 1
        while k < n:
            if _THM_HEADER.match(lines[k]) or _STRUCTURAL.match(lines[k]):
                break
            k += 1

        # The block text: doc-comment (if any) + header .. up to (not including) line k,
        # trailing blank lines trimmed.
        block_lines = lines[start:k]
        while block_lines and not block_lines[-1].strip():
            block_lines.pop()
        block = "\n".join(block_lines)

        # Statement = signature between the name and `:=` (fall back to end of block).
        stmt = _extract_statement(block, name)

        blocks.append({"name": name, "statement": stmt, "block": block})
        i = k
    return blocks


def _extract_statement(block: str, name: str) -> str:
    """Recover the signature text (name .. before `:=`), whitespace-collapsed."""
    # Drop leading doc-comment lines for statement extraction.
    body_lines = [ln for ln in block.splitlines() if not _DOC_LINE.match(ln)]
    body = "\n".join(body_lines)
    # Find `theorem/lemma <name>` and slice from just after the name.
    m = re.search(r"(?:theorem|lemma)\s+" + re.escape(name), body)
    if not m:
        sig = body
    else:
        sig = body[m.end():]
    # Cut at the first `:=` (proof separator).
    idx = sig.find(":=")
    if idx != -1:
        sig = sig[:idx]
    sig = sig.strip()
    # Drop the leading proposition colon so `statement` is the bare proposition
    # (matching gap_fill's convention: the goal, not `name : goal`).
    if sig.startswith(":"):
        sig = sig[1:]
    return " ".join(sig.split())


def _normalize_statement(stmt: str) -> str:
    """Normalize a statement for conflict comparison: strip whitespace and ``: ℝ``."""
    s = " ".join(stmt.split())
    s = s.replace(": ℝ", "").replace(":ℝ", "")
    return " ".join(s.split())


def _referenced_names(block: str, own_name: str, universe: set) -> set:
    """Names in ``universe`` (word-boundary) that ``block`` mentions, minus ``own_name``.

    A dotted Lean name like ``Foo.bar`` will only match a universe name that is
    itself the full dotted token (word boundaries treat ``.`` as a boundary, so a
    bare ``bar`` in the universe would also match the ``bar`` inside ``Foo.bar`` —
    the universe here is the bundle's own theorem names, so Mathlib names such as
    ``Real.log`` are simply not in the universe and never match).
    """
    refs = set()
    for cand in universe:
        if cand == own_name:
            continue
        if re.search(r"(?<![A-Za-z0-9_'.])" + re.escape(cand) + r"(?![A-Za-z0-9_'.])", block):
            refs.add(cand)
    return refs


def topo_sort_blocks(theorems: list) -> tuple:
    """Dependency-order parsed theorem dicts (definition-before-use).

    ``theorems`` is a list of dicts as returned by :func:`parse_theorems`
    (``{"name", "statement", "block"}``).  A dependency edge ``B -> A`` is added
    when block ``B``'s text mentions declaration name ``A`` (word-boundary match
    against the SET of theorem names in this bundle; self-references and Mathlib
    names — anything not a bundle theorem name — are ignored).

    Returns ``(ordered_blocks, cycles)`` where ``ordered_blocks`` is a stable
    Kahn-topological ordering (every theorem appears AFTER the theorems it
    references) and ``cycles`` is a list of lists of names that participate in a
    dependency cycle.  On a cycle the members are kept in first-seen order and
    processing continues — nothing is dropped and it never raises.

    NOTE: if the same name occurs more than once (un-deduped input), the FIRST
    block for each name is used for edge/order purposes and every input block is
    still returned (later duplicates immediately after their first occurrence).
    """
    # First-seen order of names, and name -> list of blocks (dup-tolerant).
    order: list = []
    by_name: dict = {}
    for b in theorems:
        nm = b["name"]
        if nm not in by_name:
            by_name[nm] = []
            order.append(nm)
        by_name[nm].append(b)

    names = set(order)
    # deps[B] = set of A that B references (A defined-before B required).
    deps: dict = {}
    for nm in order:
        first = by_name[nm][0]
        deps[nm] = _referenced_names(first["block"], nm, names)

    # Kahn's algorithm on the DAG-part; indegree = number of unresolved deps.
    indeg = {nm: len(deps[nm]) for nm in order}
    # reverse edges: dependents[A] = names that depend on A
    dependents: dict = {nm: [] for nm in order}
    for nm in order:
        for a in deps[nm]:
            dependents[a].append(nm)

    resolved: list = []
    placed: set = set()
    # Ready = indegree 0, kept in first-seen order for stability.
    ready = [nm for nm in order if indeg[nm] == 0]
    while ready:
        nm = ready.pop(0)
        if nm in placed:
            continue
        resolved.append(nm)
        placed.add(nm)
        for d in dependents[nm]:
            indeg[d] -= 1
            if indeg[d] == 0 and d not in placed:
                # insert preserving first-seen order among currently-ready
                ready.append(d)
                ready.sort(key=order.index)

    # Remaining names are in one or more cycles. Report them and append in
    # first-seen order so nothing is dropped and elaboration is still attempted.
    remaining = [nm for nm in order if nm not in placed]
    cycles: list = []
    if remaining:
        cycles = _find_cycles(remaining, deps)
        resolved.extend(remaining)

    ordered_blocks: list = []
    for nm in resolved:
        ordered_blocks.extend(by_name[nm])
    return ordered_blocks, cycles


def _find_cycles(remaining: list, deps: dict) -> list:
    """Group ``remaining`` cyclic names into strongly-connected components.

    Restricts the dependency graph to ``remaining`` (the un-resolvable set from
    Kahn) and returns the SCCs that are genuine cycles (size >= 2, or a self-loop).
    Members within each returned cycle are in first-seen (``remaining``) order.
    """
    rem = set(remaining)
    # Tarjan's SCC over the induced subgraph.
    index_of: dict = {}
    low: dict = {}
    on_stack: dict = {}
    stack: list = []
    counter = [0]
    sccs: list = []

    def strongconnect(v):
        index_of[v] = counter[0]
        low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in deps.get(v, ()):
            if w not in rem:
                continue
            if w not in index_of:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif on_stack.get(w):
                low[v] = min(low[v], index_of[w])
        if low[v] == index_of[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for v in remaining:
        if v not in index_of:
            strongconnect(v)

    first_seen = {nm: i for i, nm in enumerate(remaining)}
    cycles: list = []
    for comp in sccs:
        if len(comp) >= 2 or (len(comp) == 1 and comp[0] in deps.get(comp[0], set())):
            cycles.append(sorted(comp, key=lambda nm: first_seen[nm]))
    return cycles


def _dedup_mode(dedup) -> str:
    """Normalize the ``dedup`` argument to one of ``name|type_hash|both|none``.

    Accepts the legacy boolean (``True`` -> name dedup, ``False`` -> no dedup) as
    well as the string modes.
    """
    if dedup is True:
        return "name"
    if dedup is False:
        return "none"
    if dedup in ("name", "type_hash", "both", "none"):
        return dedup
    raise ValueError(
        f"dedup must be one of True/False/'name'/'type_hash'/'both'/'none', got {dedup!r}"
    )


def _type_hash(statement: str) -> str:
    """Structural key for a statement: sha256 of its canonical form, 16 hex chars."""
    canon = canonical_statement(statement)
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()[:16]


def merge_bundle(
    blocks_or_files: list,
    *,
    dedup=True,
    topo: bool = False,
    imports=("import Mathlib",),
    prelude: str = "",
    namespace=None,
) -> str:
    """Combine multiple Lean sources into ONE file, dedup'ing shared theorem atoms.

    ``blocks_or_files``: a list of Lean source STRINGS, each possibly containing
    several theorems (as emitted per cell).

    - Collects every theorem block (via :func:`parse_theorems`).
    - ``dedup`` controls duplicate collapsing (the AXLE ``merge_duplicates`` lesson):

        * ``dedup="name"`` (or ``dedup=True``): NAME dedup — the first occurrence
          of each ``name`` is kept; a later theorem with the SAME name and
          (normalized) SAME statement is dropped.  A later theorem with the same
          name but a DIFFERENT statement is a CONFLICT and raises
          :class:`ValueError`.
        * ``dedup="type_hash"``: STRUCTURAL dedup (the alpha-equivalence analog) —
          two theorems with DIFFERENT names but the SAME canonical statement
          collapse to the first; later structural twins are dropped.
        * ``dedup="both"``: apply BOTH — name conflict detection AND structural
          dedup across differing names.
        * ``dedup=False`` (or ``dedup="none"``): keep every block as-is.

    - If ``topo`` is True, the surviving blocks are reordered so each theorem is
      defined BEFORE it is referenced (definition-before-use), via
      :func:`topo_sort_blocks`.  Default ``topo=False`` keeps first-seen order for
      backward compatibility.
    - Emits: the ``imports``, the ``prelude``, an optional ``namespace <ns>`` /
      ``end <ns>`` wrapper, then the surviving blocks.

    Returns the merged Lean source string.
    """
    mode = _dedup_mode(dedup)

    all_blocks: list = []
    for src in blocks_or_files:
        all_blocks.extend(parse_theorems(src))

    kept: list = []
    seen: dict = {}       # name -> normalized statement of the kept copy
    hashes: dict = {}     # type_hash -> name of the kept copy (structural dedup)
    for b in all_blocks:
        name = b["name"]
        if mode in ("name", "both") and name in seen:
            if _normalize_statement(b["statement"]) != seen[name]:
                raise ValueError(
                    f"merge conflict: theorem {name!r} appears with two different "
                    f"statements:\n  first: {seen[name]!r}\n  later: "
                    f"{_normalize_statement(b['statement'])!r}"
                )
            # identical duplicate name -> drop
            continue
        if mode in ("type_hash", "both"):
            h = _type_hash(b["statement"])
            if h in hashes:
                # structural twin under a different (or same) name -> drop
                continue
            hashes[h] = name
        seen[name] = _normalize_statement(b["statement"])
        kept.append(b)

    if topo:
        kept, _cycles = topo_sort_blocks(kept)

    parts: list = []
    for imp in imports:
        parts.append(imp)
    if imports:
        parts.append("")
    if prelude:
        parts.append(prelude.rstrip())
        parts.append("")
    if namespace:
        parts.append(f"namespace {namespace}")
        parts.append("")
    parts.append("\n\n".join(b["block"] for b in kept))
    if namespace:
        parts.append("")
        parts.append(f"end {namespace}")

    return "\n".join(parts).rstrip() + "\n"


def bundle_stats(merged: str) -> dict:
    """Report on a merged bundle: ``{n_theorems, n_unique, n_deduped, names}``.

    ``n_theorems`` = theorem blocks present in ``merged`` (post-merge, so already
    deduped).  ``n_unique`` = distinct names.  ``n_deduped`` = duplicate blocks
    still present (0 for a properly merged file).  ``names`` = names in order.
    """
    blocks = parse_theorems(merged)
    names = [b["name"] for b in blocks]
    unique = list(dict.fromkeys(names))
    return {
        "n_theorems": len(blocks),
        "n_unique": len(unique),
        "n_deduped": len(names) - len(unique),
        "names": names,
    }

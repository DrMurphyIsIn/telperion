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

import re

from .cert_meta import type_hash as _stmt_type_hash

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


def _ident_boundary(name: str) -> re.Pattern:
    """Whole-identifier matcher for a (possibly dotted/primed) Lean name — not preceded
    or followed by an identifier character, so ``foo`` does not match inside ``foobar``
    or ``foo.bar``."""
    return re.compile(r"(?<![A-Za-z0-9_'.])" + re.escape(name) + r"(?![A-Za-z0-9_'.])")


def _references(block_text: str, name: str, self_name: str) -> bool:
    """Does ``block_text`` (a theorem block whose own name is ``self_name``) reference
    the identifier ``name`` other than as its own header?"""
    if name == self_name:
        return False
    return bool(_ident_boundary(name).search(block_text))


def _topo_order(kept: list) -> list:
    """Stable topological sort of theorem blocks so a block that references another
    kept block's NAME comes AFTER it (dependencies first).  Kahn's algorithm with
    original order as the tie-break; any cycle is left in original relative order
    (never drops a block)."""
    names = [b["name"] for b in kept]
    by_name = {b["name"]: b for b in kept}
    # edges: dep -> {dependents}; indeg[b] = # of kept names b references.
    deps = {b["name"]: {a for a in names
                        if a != b["name"] and _references(b["block"], a, b["name"])}
            for b in kept}
    indeg = {n: len(deps[n]) for n in names}
    ready = [n for n in names if indeg[n] == 0]        # order preserved
    out: list = []
    while ready:
        n = ready.pop(0)
        out.append(n)
        for m in names:                                 # dependents of n, in order
            if n in deps[m] and indeg[m] > 0:
                deps[m].discard(n)
                indeg[m] -= 1
                if indeg[m] == 0:
                    ready.append(m)
    # append any cycle remainder in original order.
    if len(out) < len(names):
        out += [n for n in names if n not in out]
    return [by_name[n] for n in out]


def merge_bundle(
    blocks_or_files: list,
    *,
    dedup: bool = True,
    merge_duplicates: bool = False,
    topo_sort: bool = False,
    imports=("import Mathlib",),
    prelude: str = "",
    namespace=None,
) -> str:
    """Combine multiple Lean sources into ONE file, dedup'ing shared theorem atoms.

    ``blocks_or_files``: a list of Lean source STRINGS, each possibly containing
    several theorems (as emitted per cell).

    - Collects every theorem block (via :func:`parse_theorems`).
    - If ``dedup``: the first occurrence of each ``name`` is kept; a later theorem
      with the SAME name and the SAME statement (compared by ``cert_meta.type_hash``,
      so cosmetic ``: ℝ``/``: Real``/whitespace differences are ignored) is dropped.
      A later theorem with the same name but a STRUCTURALLY DIFFERENT statement is a
      CONFLICT and raises :class:`ValueError`.
    - If ``merge_duplicates`` (AXLE ``merge_duplicates``): after name dedup, atoms
      that share a ``type_hash`` under DIFFERENT names are collapsed to the FIRST
      name, and references to the dropped names are rewritten to it throughout the
      surviving blocks (prove once, reuse everywhere).
    - If ``topo_sort`` (AXLE dependency-ordered ``merge``): the kept blocks are
      reordered so a block that references another kept block's name comes AFTER it,
      so the merged file elaborates regardless of source order.
    - Emits: the ``imports``, the ``prelude``, an optional ``namespace <ns>`` /
      ``end <ns>`` wrapper, then the (deduped) blocks.

    Returns the merged Lean source string.
    """
    all_blocks: list = []
    for src in blocks_or_files:
        all_blocks.extend(parse_theorems(src))

    kept: list = []
    seen: dict = {}  # name -> type_hash of the kept copy
    for b in all_blocks:
        name = b["name"]
        if dedup and name in seen:
            if _stmt_type_hash(b["statement"]) != seen[name]:
                raise ValueError(
                    f"merge conflict: theorem {name!r} appears with two different "
                    f"statements:\n  first hash: {seen[name]!r}\n  later: "
                    f"{_normalize_statement(b['statement'])!r}"
                )
            # identical duplicate -> drop
            continue
        seen[name] = _stmt_type_hash(b["statement"])
        kept.append(b)

    # Cross-name structural dedup: collapse same-type_hash atoms with DIFFERENT names
    # to the first, rewriting references in surviving blocks.
    if merge_duplicates:
        canonical: dict = {}  # type_hash -> first name
        rename: dict = {}     # dropped name -> canonical name
        deduped: list = []
        for b in kept:
            h = _stmt_type_hash(b["statement"])
            if h in canonical and canonical[h] != b["name"]:
                rename[b["name"]] = canonical[h]
                continue
            canonical.setdefault(h, b["name"])
            deduped.append(b)
        if rename:
            for b in deduped:
                for old, new in rename.items():
                    b["block"] = _ident_boundary(old).sub(new, b["block"])
            kept = deduped

    if topo_sort:
        kept = _topo_order(kept)

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

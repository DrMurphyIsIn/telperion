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


def merge_bundle(
    blocks_or_files: list,
    *,
    dedup: bool = True,
    imports=("import Mathlib",),
    prelude: str = "",
    namespace=None,
) -> str:
    """Combine multiple Lean sources into ONE file, dedup'ing shared theorem atoms.

    ``blocks_or_files``: a list of Lean source STRINGS, each possibly containing
    several theorems (as emitted per cell).

    - Collects every theorem block (via :func:`parse_theorems`).
    - If ``dedup``: the first occurrence of each ``name`` is kept; a later theorem
      with the SAME name and (normalized) SAME statement is dropped.  A later
      theorem with the same name but a DIFFERENT statement is a CONFLICT and raises
      :class:`ValueError`.
    - Emits: the ``imports``, the ``prelude``, an optional ``namespace <ns>`` /
      ``end <ns>`` wrapper, then the (deduped) blocks in first-seen order.

    Returns the merged Lean source string.
    """
    all_blocks: list = []
    for src in blocks_or_files:
        all_blocks.extend(parse_theorems(src))

    kept: list = []
    seen: dict = {}  # name -> normalized statement of the kept copy
    for b in all_blocks:
        name = b["name"]
        if dedup and name in seen:
            if _normalize_statement(b["statement"]) != seen[name]:
                raise ValueError(
                    f"merge conflict: theorem {name!r} appears with two different "
                    f"statements:\n  first: {seen[name]!r}\n  later: "
                    f"{_normalize_statement(b['statement'])!r}"
                )
            # identical duplicate -> drop
            continue
        seen[name] = _normalize_statement(b["statement"])
        kept.append(b)

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

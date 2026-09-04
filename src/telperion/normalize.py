"""Canonical-form + proof-blanking utilities for emitted Lean (the AXLE
``normalize`` + ``theorem2sorry`` lesson).

Two jobs, both PURE TEXT (no Lean build):

1. :func:`normalize_lean` -- a CONSERVATIVE, semantics-preserving cosmetic pass
   over Lean source so that drift-diffs (``--check`` of a regenerated file
   against the committed one) are robust to whitespace-only churn.  It operates
   ONLY at the whitespace / blank-line level and NEVER touches token content, so
   it can never change the meaning of a declaration.

2. :func:`canonical_statement` -- normalize a theorem STATEMENT for
   comparison/hashing, so cosmetically-different-but-equal statements
   canonicalize to the same key.  This is the comparison key other modules can
   reuse (e.g. to dedupe or match gaps against a library).

3. :func:`theorem2sorry` -- replace the PROOF of each named theorem (or all) with
   a ``sorry``, keeping the doc comment and signature EXACTLY.  This is the
   "blank a proof to re-attack / regenerate" utility; it round-trips with
   :func:`telperion.gap_fill.extract_gaps` (which finds ``:= by sorry`` gaps).

conjecture1_proved = False.
"""
from __future__ import annotations

import re

__all__ = ["normalize_lean", "canonical_statement", "theorem2sorry"]


def normalize_lean(content: str) -> str:
    """Return a canonical cosmetic form of Lean ``content``.

    SAFE, semantics-preserving normalizations ONLY:

    * strip trailing whitespace on each line,
    * collapse runs of blank lines to at most one,
    * ensure the file ends with exactly one trailing newline.

    This DOES NOT alter token content -- it never inserts, deletes, or respaces
    anything *inside* a line's non-whitespace text (in particular it does not
    touch expression internals such as ``(7/4 : ℝ)``, which would be too risky).
    Consequently it can never change the meaning of any declaration, and it is
    idempotent: ``normalize_lean(normalize_lean(x)) == normalize_lean(x)``.
    """
    # Normalize line endings so the blank-line collapse is uniform, then strip
    # trailing whitespace per line.  We never touch a line's interior content.
    lines = content.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    stripped = [ln.rstrip() for ln in lines]

    out: list[str] = []
    prev_blank = False
    for ln in stripped:
        is_blank = ln == ""
        if is_blank and prev_blank:
            continue  # collapse runs of >1 blank line to a single blank line
        out.append(ln)
        prev_blank = is_blank

    # Drop leading/trailing blank lines, then re-append exactly one newline.
    while out and out[0] == "":
        out.pop(0)
    while out and out[-1] == "":
        out.pop()

    if not out:
        return "\n"
    return "\n".join(out) + "\n"


# `: ℝ` (with optional surrounding spaces), and a redundant `(: ℝ)`-style empty
# ascription, both collapse away for comparison purposes.
_ASCRIPTION = re.compile(r"\(\s*:\s*ℝ\s*\)")   # `(: ℝ)` redundant paren-ascription
_COLON_R = re.compile(r"\s*:\s*ℝ")            # `: ℝ` ascription (keep the operand)


def canonical_statement(statement: str) -> str:
    """Canonicalize a theorem STATEMENT for comparison / hashing.

    Strips ``: ℝ`` (and redundant ``(: ℝ)``) ascriptions, collapses whitespace
    runs to single spaces, and removes spaces immediately inside parentheses, so
    that cosmetically-different-but-mathematically-equal statements canonicalize
    to the SAME string.  Intended as a stable comparison key, NOT as valid Lean
    to re-emit.

    Example::

        canonical_statement("Real.log (7/4 : ℝ)  ≤  4 * FSTAR")
            == canonical_statement("Real.log (7/4) ≤ 4*FSTAR")
    """
    s = statement
    s = _ASCRIPTION.sub("", s)     # `(: ℝ)` -> ``  (drop the empty ascription)
    s = _COLON_R.sub("", s)        # `x : ℝ` -> `x`  (drop the type ascription)
    s = s.replace("*", " * ")      # normalize `4*FSTAR` vs `4 * FSTAR`
    s = re.sub(r"\s+", " ", s)     # collapse whitespace runs to single spaces
    s = re.sub(r"\(\s+", "(", s)   # no space just inside `(`
    s = re.sub(r"\s+\)", ")", s)   # no space just inside `)`
    return s.strip()


# theorem/lemma <name> <sig> := by <proof>   OR   := <term proof>.
# The signature runs up to the FIRST top-level `:=`; we keep everything through
# that `:=` verbatim and replace only the body.  `[\s\S]` matches across lines.
_THM = re.compile(
    r"((?:theorem|lemma)\s+([A-Za-z_][\w']*)\b[\s\S]*?:=)",
)


def _blank_body(text: str, start: int) -> tuple[str, int]:
    """Given ``text`` and the index just AFTER a declaration's ``:=``, return
    ``(replacement_body, end_index)`` -- the ``sorry`` body and the index one
    past the end of the original proof body.  The proof body ends at the next
    top-level declaration keyword (``theorem``/``lemma``/``def``/``end``/...) or
    end of file.  Whitespace/keyword after ``:=`` decides ``by sorry`` vs
    ``sorry`` (term mode)."""
    rest = text[start:]
    # Is this a tactic-mode (`:= by ...`) or term-mode (`:= <expr>`) proof?
    m_by = re.match(r"\s*by\b", rest)
    body = " by sorry" if m_by else " sorry"

    # Find where the proof body ends: the next top-level declaration or EOF.
    nxt = re.search(
        r"\n(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|end|section|namespace|open|/--)",
        rest,
    )
    if nxt:
        end = start + nxt.start()
    else:
        # No following declaration: consume to EOF but preserve trailing
        # whitespace/newline (so a final `... := by norm_num\n` -> `... := by
        # sorry\n`, not `... := by sorry`).
        end = start + len(rest.rstrip())
    return body, end


def theorem2sorry(content: str, names=None) -> str:
    """Blank the PROOF of each named theorem/lemma (all if ``names is None``).

    ``theorem foo : T := by <proof>`` -> ``theorem foo : T := by sorry`` and
    ``theorem foo : T := <term>`` -> ``theorem foo : T := sorry`` (term mode).
    The doc comment and signature are preserved EXACTLY; only the body after the
    top-level ``:=`` is replaced.  Non-named declarations are left UNTOUCHED.

    Round-trips with :func:`telperion.gap_fill.extract_gaps`: the blanked
    theorem reappears as a ``:= by sorry`` gap.
    """
    wanted = None if names is None else set(names)

    out: list[str] = []
    pos = 0
    for m in _THM.finditer(content):
        name = m.group(2)
        sig_end = m.end()  # index just past `:=`
        if wanted is not None and name not in wanted:
            continue
        body, body_end = _blank_body(content, sig_end)
        out.append(content[pos:sig_end])
        out.append(body)
        pos = body_end

    out.append(content[pos:])
    return "".join(out)

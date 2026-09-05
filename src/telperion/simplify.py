"""Mechanical, verify-guarded proof MINIMIZER for emitted Lean (the AXLE
``simplify_theorems`` lesson).

Round-2 deferred ``simplify_theorems`` as "needs proof search"; the third-tour
doc (``docs/AXLE_THIRD_TOUR_2026-09-04.md``, the ``simplify_theorems`` row)
RECONSIDERS that: AXLE's minimizer is NOT search -- it is a set of MECHANICAL
prune passes, each applied only if the result still verifies, iterated to a
fixed point, with ROLLBACK on any regression.  This module is the Telperion
analog, mirroring :mod:`telperion.repair`'s verify -> transform -> re-verify
structure (there for version-drift renames; here for pruning dead proof steps).

The one pass shipped here is :func:`remove_unused_haves`:

    for each ``have h : T := ...`` step whose bound name ``h`` is NOT referenced
    anywhere later in the proof, tentatively DELETE the step, re-verify the whole
    file against the built environment, and keep the deletion ONLY if the result
    still ``okay`` and ``axioms_clean`` -- otherwise roll the step back.

Two safety invariants make this sound as a pure text pass with a Lean backstop:

1. CONSERVATIVE reference check.  A ``have`` is a candidate ONLY when its bound
   name does not appear (word-boundary matched) anywhere in the proof text that
   FOLLOWS the step.  Anonymous ``have``s (``have : T := ...``, no name) are
   never touched -- their result feeds the next tactic implicitly.  A name that
   is a substring of a longer identifier (``h`` inside ``h2``, ``hpos`` inside
   ``hpos'``) does NOT count as a reference (word boundaries + a trailing
   ``[\\w']`` guard).

2. VERIFY-GUARDED with ROLLBACK.  Every tentative deletion is re-verified; the
   minimizer NEVER returns a version that fails to verify.  If the input itself
   verifies, the output is guaranteed kernel-green (rollback restores the last
   good text on any regression).  If the input does NOT verify, no pass is
   attempted and the input is returned unchanged.

Passes iterate to a fixed point: after any successful deletion the file text
changes (later ``have``s shift, names may become newly-unused), so the sweep is
repeated until a full pass removes nothing.

This is a MINIMIZER, not a prover: it only ever DELETES steps that were already
present and re-checks with the kernel.  It can never introduce a ``sorry`` or a
disallowed axiom (the guard rejects any such regression), and it can never make
a passing proof fail.

conjecture1_proved = False.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple

from .verify import VerifyResult, verify_lean


# A `have` step HEADER.  Named form only: `have <name> : ...` or `have <name> := ...`
# (the `: T` type ascription is optional in Lean, but a named have always has the
# bound identifier right after `have`).  We anchor on the leading-whitespace so the
# indentation column is captured for the block-extent computation.  Anonymous
# `have : T := ...` (no name) is deliberately NOT matched -- it has no name to check
# for non-use and its value is consumed by the following tactic implicitly.
_HAVE_HEADER = re.compile(
    r"^(?P<indent>[ \t]*)have[ \t]+(?P<name>[A-Za-z_][\w']*)[ \t]*(?::|:=)",
)


@dataclass
class HaveStep:
    """One named ``have`` step located in a proof, as a half-open line range.

    ``start_line``/``end_line`` are 0-based indices into the file's line list;
    the step occupies lines ``[start_line, end_line)``.  ``indent`` is the count
    of leading spaces/tabs on the header line (block-extent boundary).
    """

    name: str
    start_line: int          # 0-based index of the `have <name>` header line
    end_line: int            # 0-based EXCLUSIVE end (first line NOT in this step)
    indent: int              # leading-whitespace width of the header line


@dataclass
class SimplifyStep:
    """Record of one applied minimization (a removed ``have``)."""

    pass_name: str           # e.g. "remove_unused_haves"
    name: str                # the bound name of the removed `have`
    start_line: int          # 0-based header line index at removal time
    removed_lines: int       # how many source lines the step spanned


@dataclass
class SimplifyResult:
    """Structured result of :func:`simplify_proof`.

    ``content`` is the minimized source (guaranteed to verify iff the input did).
    ``applied`` lists every removed step, in removal order.  ``result`` is the
    FINAL :class:`telperion.verify.VerifyResult` for ``content``.  ``changed`` is
    a convenience flag (``bool(applied)``).
    """

    content: str
    applied: List[SimplifyStep] = field(default_factory=list)
    result: Optional[VerifyResult] = None

    @property
    def changed(self) -> bool:
        return bool(self.applied)

    def summary(self) -> str:
        n = len(self.applied)
        names = ", ".join(s.name for s in self.applied[:4])
        more = "" if n <= 4 else f" (+{n - 4} more)"
        gate = "?"
        if self.result is not None:
            gate = "OK" if (self.result.okay and self.result.axioms_clean) else "FAIL"
        return f"[{gate}] removed {n} unused have(s): {names}{more}"


# Word-boundary reference: the name preceded by a non-word char (or start) and NOT
# followed by another identifier char (so `h` does not match inside `h2`/`hpos`).
def _referenced(name: str, text: str) -> bool:
    """True iff ``name`` occurs as a WHOLE identifier token in ``text``.

    Conservative: uses ``\\b`` anchoring plus an explicit ``(?![\\w'])`` trailing
    guard so a shorter name is never seen inside a longer identifier (Lean allows
    a trailing prime in identifiers, which ``\\b`` alone would mis-handle).  A
    leading guard ``(?<![\\w'])`` likewise prevents matching a suffix.
    """
    pat = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
    return pat.search(text) is not None


def _find_have_steps(lines: List[str]) -> List[HaveStep]:
    """Locate every NAMED ``have`` step in ``lines`` as a line range.

    A step's extent is delimited by INDENTATION: the header line
    ``<indent>have <name> ...`` is followed by its continuation lines (the multi
    -line type signature and/or the ``:= by`` tactic block), all of which are
    either BLANK or indented STRICTLY DEEPER than the header.  The step ends at
    the first following NON-blank line whose indentation is ``<=`` the header's
    indentation (the next sibling tactic, or a dedent out of the block), or at
    end of file.

    This is the same block-structuring Lean's whitespace-sensitive ``by`` uses,
    computed purely textually.  Trailing blank lines between the step and the
    next sibling are left OUT of the step (assigned to neither) so removing the
    step does not delete a separating blank line belonging to the next tactic.
    """
    steps: List[HaveStep] = []
    n = len(lines)
    i = 0
    while i < n:
        m = _HAVE_HEADER.match(lines[i])
        if not m:
            i += 1
            continue
        indent = len(m.group("indent").expandtabs(1)) if "\t" in m.group("indent") \
            else len(m.group("indent"))
        name = m.group("name")
        j = i + 1
        last_content = i  # last line that genuinely belongs to this step
        while j < n:
            ln = lines[j]
            if ln.strip() == "":
                j += 1
                continue  # blank lines are provisional continuation
            cur_indent = _leading_width(ln)
            if cur_indent <= indent:
                break     # a sibling / dedent -> step ended before this line
            last_content = j
            j += 1
        steps.append(HaveStep(
            name=name, start_line=i, end_line=last_content + 1, indent=indent,
        ))
        i = last_content + 1
    return steps


def _leading_width(line: str) -> int:
    """Leading-whitespace width (tabs counted as 1 col, matching header parse)."""
    w = 0
    for ch in line:
        if ch == " " or ch == "\t":
            w += 1
        else:
            break
    return w


def find_have_steps(content: str) -> List[HaveStep]:
    """Public wrapper: locate NAMED ``have`` steps in ``content`` (no Lean build)."""
    return _find_have_steps(content.splitlines())


def unused_have_steps(content: str) -> List[HaveStep]:
    """The NAMED ``have`` steps whose bound name is not referenced LATER.

    A step is 'unused' iff its name does not appear (as a whole token) anywhere in
    the proof text that follows the END of its own step.  Pure text analysis (no
    Lean); this is the CANDIDATE set the verify-guarded pass will try to delete.
    Text before the step is intentionally NOT scanned: a ``have`` binds forward,
    so an earlier textual occurrence cannot be a use of this binding.
    """
    lines = content.splitlines()
    steps = _find_have_steps(lines)
    unused: List[HaveStep] = []
    for st in steps:
        tail = "\n".join(lines[st.end_line:])
        if not _referenced(st.name, tail):
            unused.append(st)
    return unused


def _delete_step(lines: List[str], step: HaveStep) -> List[str]:
    """Return a new line list with ``[step.start_line, step.end_line)`` removed."""
    return lines[:step.start_line] + lines[step.end_line:]


def _verify(content: str, *, env_dir, decls, allow_axioms) -> VerifyResult:
    return verify_lean(
        content, env_dir=env_dir, decls=list(decls), allow_axioms=list(allow_axioms),
    )


def _passes(result: VerifyResult) -> bool:
    """The keep-gate: a candidate deletion is accepted ONLY if the result still
    compiles AND is axioms-clean (no ``sorry``, no disallowed axiom)."""
    return result.okay and result.axioms_clean


def remove_unused_haves(
    content: str,
    *,
    env_dir,
    decls,
    allow_axioms=(),
    baseline: Optional[VerifyResult] = None,
) -> Tuple[str, List[SimplifyStep], VerifyResult]:
    """ONE fixed-point sweep of the unused-``have`` prune, verify-guarded.

    Repeatedly: recompute the unused-``have`` candidates on the CURRENT text,
    try to delete the FIRST one, re-verify; keep the deletion iff it still
    passes, else roll it back and move to the next candidate.  Because a
    successful deletion shifts line numbers and can free up further names, the
    candidate set is recomputed after every accepted removal; the sweep ends
    when a full recomputation yields no acceptable deletion.

    ``baseline`` may carry the already-known passing :class:`VerifyResult` for
    ``content`` (avoids one redundant verify when the caller has it).  It MUST
    correspond to ``content`` and MUST pass; if it does not pass (or is absent
    and the first verify fails), no deletion is attempted and ``content`` is
    returned unchanged.

    Returns ``(content, applied, final_result)``.  ``final_result`` always
    describes the returned ``content`` and is guaranteed to pass whenever the
    input passed.
    """
    current = _verify(content, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms) \
        if baseline is None else baseline
    if not _passes(current):
        # Input does not verify -> never risk producing something worse.
        return content, [], current

    applied: List[SimplifyStep] = []
    # `rejected` remembers (name, start_line) pairs that failed a deletion so the
    # inner loop does not retry them on the same text; cleared whenever a deletion
    # succeeds (line numbers shift, so prior rejections no longer apply).
    while True:
        candidates = unused_have_steps(content)
        if not candidates:
            break
        made_progress = False
        rejected_starts: set = set()
        for step in candidates:
            if step.start_line in rejected_starts:
                continue
            lines = content.splitlines(keepends=False)
            trial_lines = _delete_step(lines, step)
            trial = "\n".join(trial_lines)
            if content.endswith("\n"):
                trial += "\n"
            r = _verify(trial, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms)
            if _passes(r):
                content = trial
                current = r
                applied.append(SimplifyStep(
                    pass_name="remove_unused_haves",
                    name=step.name,
                    start_line=step.start_line,
                    removed_lines=step.end_line - step.start_line,
                ))
                made_progress = True
                break  # recompute candidates on the new (shorter) text
            else:
                rejected_starts.add(step.start_line)
        if not made_progress:
            break
    return content, applied, current


# The registry of mechanical passes, in application order.  Mirrors AXLE's named
# pass list; adding a new safe pass is a one-line append (each pass has the
# ``(content, *, env_dir, decls, allow_axioms, baseline) -> (content, applied,
# result)`` shape and MUST be verify-guarded + rollback-safe).
_PASSES = (
    ("remove_unused_haves", remove_unused_haves),
)


def simplify_proof(
    content: str,
    *,
    env_dir,
    decls,
    allow_axioms=(),
) -> SimplifyResult:
    """Mechanically minimize ``content`` against the built ``env_dir``.

    Runs every registered pass (currently :func:`remove_unused_haves`), each
    verify-guarded with rollback, iterating passes to a joint fixed point: the
    whole pass list is repeated until a full round removes nothing.  ``decls``
    are the declaration names to axiom-check on every re-verify (naming at least
    one is what makes ``axioms_clean`` meaningful -- see
    :class:`telperion.verify.VerifyResult`).

    GUARANTEE: if the INPUT verifies (``okay and axioms_clean`` under ``decls``),
    the returned :attr:`SimplifyResult.content` also verifies -- rollback ensures
    no pass ever commits a regression.  If the input does NOT verify, the input
    is returned unchanged with ``applied == []`` and the failing result attached.

    Returns a :class:`SimplifyResult`.
    """
    baseline = _verify(content, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms)
    if not _passes(baseline):
        return SimplifyResult(content=content, applied=[], result=baseline)

    applied: List[SimplifyStep] = []
    current_result = baseline
    while True:
        round_progress = False
        for _pass_name, fn in _PASSES:
            content, pass_applied, current_result = fn(
                content, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms,
                baseline=current_result,
            )
            if pass_applied:
                applied.extend(pass_applied)
                round_progress = True
        if not round_progress:
            break

    return SimplifyResult(content=content, applied=applied, result=current_result)


def _main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(
        description="Mechanically minimize a Lean proof (drop unused have steps)."
    )
    ap.add_argument("file", help="Lean source file to minimize")
    ap.add_argument("--env", required=True, help="pre-built Lake project dir")
    ap.add_argument("--decl", action="append", default=[], help="declaration to axiom-check")
    ap.add_argument("--allow-axiom", action="append", default=[])
    ap.add_argument("--write", action="store_true", help="overwrite FILE with the minimized proof")
    a = ap.parse_args(argv)
    content = Path(a.file).read_text(encoding="utf-8")
    res = simplify_proof(
        content, env_dir=a.env, decls=a.decl, allow_axioms=a.allow_axiom,
    )
    print(res.summary())
    for st in res.applied:
        print(f"  - removed have {st.name} ({st.removed_lines} line(s)) at line {st.start_line + 1}")
    if a.write and res.changed:
        Path(a.file).write_text(res.content, encoding="utf-8")
        print(f"wrote {a.file}")
    ok = res.result is not None and res.result.okay and res.result.axioms_clean
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())

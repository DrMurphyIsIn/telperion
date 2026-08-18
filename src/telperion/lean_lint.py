"""Soundness / honesty lint of emitted Lean text — the "green build != proved" gate.

This module COMPLEMENTS ``telperion.lint`` (which owns the structural failure
classes: unfilled template holes, missing provenance header, empty binders,
delimiter balance, duplicate declaration names).  It does NOT re-check any of
those.  Instead it targets the failure class where CI turns green but nothing
was actually proved:

  * ``sorry`` / ``admit``          — an incomplete proof that the kernel accepts
                                      as an axiom-like hole (ERROR).
  * ``axiom`` declarations         — smuggled axioms bypass the kernel's trust
                                      (ERROR).
  * decorative / trivial stubs     — ``theorem foo : True := trivial`` and kin,
                                      the ``Prop := True`` placeholder class from
                                      a real Lean audit where "no sorry" was
                                      misleading (WARN).
  * missing type ascription        — ``theorem foo ... := ...`` with no top-level
                                      ``:``: a value binding masquerading as a
                                      theorem, so the "statement" is whatever the
                                      body infers to (ERROR).
  * empty tactic block             — ``:= by`` with nothing after it (ERROR).

This is a PRE-CI HEURISTIC, not a Lean parser — the kernel remains the real
check.  Comments (``--`` line, ``/- -/`` block) and string literals are stripped
coarsely before scanning so a ``sorry`` in a doc comment is never flagged; the
stripping preserves line numbers so reported lines stay accurate.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class LeanLintIssue:
    line: int
    code: str
    severity: str  # "error" | "warn"
    message: str


class LeanLintError(ValueError):
    pass


# --- coarse comment / string stripping (line-count preserving) --------------

def _strip_comments_and_strings(text: str) -> str:
    """Blank out ``--`` line comments, ``/- -/`` block comments (nestable), and
    ``"..."`` string literals, replacing their contents with spaces so that
    line and column counts — and thus reported line numbers — are preserved.
    """
    out: list[str] = []
    i, n = 0, len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False
    while i < n:
        ch = text[i]
        two = text[i : i + 2]
        if ch == "\n":
            in_line_comment = False  # line comments end at newline
            out.append("\n")
            i += 1
            continue
        if in_line_comment:
            out.append(" ")
            i += 1
            continue
        if block_depth > 0:
            if two == "/-":
                block_depth += 1
                out.append("  ")
                i += 2
                continue
            if two == "-/":
                block_depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append(" ")
            i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < n and text[i + 1] != "\n":
                out.append("  ")
                i += 2
                continue
            if ch == '"':
                in_string = False
            out.append(" ")
            i += 1
            continue
        # not in any comment/string
        if two == "/-":
            block_depth += 1
            out.append("  ")
            i += 2
            continue
        if two == "--":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


# --- declaration scanning ---------------------------------------------------

_DECL = re.compile(r"^(?:noncomputable\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", re.M)
_TRIVIAL_STMT = re.compile(r":\s*(?:True|Prop)\s*(?::=|$)")
_TRIVIAL_BODY = re.compile(r":=\s*(?:by\s+)?(?:trivial|True\.intro|rfl)\s*$")


def _line_of(stripped: str, pos: int) -> int:
    return stripped.count("\n", 0, pos) + 1


def _declaration_spans(stripped: str):
    """Yield (name, start_pos, end_pos, body_text) for each theorem/lemma.

    A declaration runs from its keyword to the start of the next top-level
    declaration keyword (theorem/lemma/def/axiom/namespace/end) or EOF.
    """
    starts = [
        (m.start(), m.group(1))
        for m in _DECL.finditer(stripped)
    ]
    # boundaries: any of these keywords at line start ends the previous decl
    bounds = [
        m.start()
        for m in re.finditer(
            r"^(?:noncomputable\s+)?(?:theorem|lemma|def|axiom|namespace|end|instance|example)\b",
            stripped,
            re.M,
        )
    ]
    bounds.append(len(stripped))
    bounds = sorted(set(bounds))
    for start, name in starts:
        end = next(b for b in bounds if b > start)
        yield name, start, end, stripped[start:end]


def lint_lean_text(text: str, *, path: str | None = None) -> list[LeanLintIssue]:
    issues: list[LeanLintIssue] = []
    stripped = _strip_comments_and_strings(text)

    # 1. sorry / admit (whole-word, in code only)
    for m in re.finditer(r"\b(sorry|admit)\b", stripped):
        issues.append(
            LeanLintIssue(
                line=_line_of(stripped, m.start()),
                code="SORRY",
                severity="error",
                message=(
                    f"`{m.group(1)}` — incomplete proof; the kernel accepts it as a "
                    "hole, making CI green while proving nothing"
                ),
            )
        )

    # 2. axiom declarations
    for m in re.finditer(r"^(?:noncomputable\s+)?axiom\s+([A-Za-z0-9_'.]+)", stripped, re.M):
        issues.append(
            LeanLintIssue(
                line=_line_of(stripped, m.start()),
                code="AXIOM",
                severity="error",
                message=(
                    f"`axiom {m.group(1)}` — smuggled axiom bypasses the kernel's trust"
                ),
            )
        )

    # 3/4/5. per-declaration checks
    for name, start, _end, body in _declaration_spans(stripped):
        line = _line_of(stripped, start)

        # locate top-level `:=` (the value separator) if any
        assign_pos = body.find(":=")

        # 4. missing type ascription: no top-level `:` before `:=`
        head = body if assign_pos == -1 else body[:assign_pos]
        # a top-level `:` is one not inside brackets
        if _has_toplevel_colon(head):
            has_ascription = True
        else:
            has_ascription = False
        if assign_pos != -1 and not has_ascription:
            issues.append(
                LeanLintIssue(
                    line=line,
                    code="NO_ASCRIPTION",
                    severity="error",
                    message=(
                        f"theorem/lemma `{name}` has no top-level `:` type ascription "
                        "before `:=` — a value binding masquerading as a theorem"
                    ),
                )
            )

        # 5. empty tactic block: `:= by` then only whitespace to end
        if assign_pos != -1:
            tail = body[assign_pos:]
            if re.fullmatch(r":=\s*by\s*", tail):
                issues.append(
                    LeanLintIssue(
                        line=line,
                        code="EMPTY_TACTIC",
                        severity="error",
                        message=(
                            f"theorem/lemma `{name}` has an empty `:= by` tactic block"
                        ),
                    )
                )

        # 3. trivial / decorative stub (WARN)
        collapsed = " ".join(body.split())
        stmt_trivial = bool(_TRIVIAL_STMT.search(collapsed))
        body_trivial = bool(_TRIVIAL_BODY.search(collapsed))
        if stmt_trivial or body_trivial:
            issues.append(
                LeanLintIssue(
                    line=line,
                    code="TRIVIAL_STUB",
                    severity="warn",
                    message=(
                        f"theorem/lemma `{name}` is a decorative stub "
                        "(`: True`/`: Prop` statement or trivial proof) — "
                        "`no sorry` can hide a `Prop := True` placeholder here"
                    ),
                )
            )

    issues.sort(key=lambda x: (x.line, x.code))
    return issues


def _has_toplevel_colon(head: str) -> bool:
    """True if ``head`` contains a ``:`` at bracket-depth 0 (a real type
    ascription), ignoring the ``:`` inside ``:=`` (which won't appear here since
    head is sliced before ``:=``).
    """
    depth = 0
    opens = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closers = {")", "]", "}", "⟩"}
    for ch in head:
        if ch in opens:
            depth += 1
        elif ch in closers:
            if depth > 0:
                depth -= 1
        elif ch == ":" and depth == 0:
            return True
    return False


def lint_lean_file(path) -> list[LeanLintIssue]:
    p = Path(path)
    return lint_lean_text(p.read_text(encoding="utf-8"), path=str(p))


def check_lean_text(text: str, *, path=None, strict: bool = False) -> None:
    """Raise ``LeanLintError`` if any error-severity issue exists (and any warn
    too when ``strict=True``).  The message lists every offending issue.
    """
    issues = lint_lean_text(text, path=path)
    fatal = [
        i for i in issues if i.severity == "error" or (strict and i.severity == "warn")
    ]
    if fatal:
        where = f" ({path})" if path else ""
        lines = "\n  ".join(
            f"L{i.line} [{i.code}/{i.severity}] {i.message}" for i in fatal
        )
        raise LeanLintError(f"Lean soundness lint failed{where}:\n  " + lines)

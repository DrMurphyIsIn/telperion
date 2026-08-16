"""Structural lint of emitted Lean text — the last gate before freeze.

Not a Lean parser (the kernel is the real check); this catches the mechanical
failure classes that waste a CI round-trip: unfilled template holes, unbalanced
delimiters, duplicate theorem/def names within or across an EmitResult's
files, and missing provenance headers.  A LintError is a refusal: nothing is
written.
"""
from __future__ import annotations

import re

_NAME = re.compile(r"^(?:noncomputable )?(?:theorem|def|lemma) ([A-Za-z0-9_'.]+)", re.M)
_PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
_CLOSER = {v: k for k, v in _PAIRS.items()}


class LintError(ValueError):
    pass


def lint_text(fname: str, text: str) -> list[str]:
    problems: list[str] = []
    if "«" in text or "»" in text:
        line = next(
            i + 1 for i, ln in enumerate(text.splitlines()) if "«" in ln or "»" in ln
        )
        problems.append(f"{fname}:{line}: unfilled template hole marker")
    if not text.startswith("/- telperion"):
        problems.append(f"{fname}: missing provenance header")
    # delimiter balance, ignoring comments and strings coarsely
    stack: list[tuple[str, int]] = []
    for i, ln in enumerate(text.splitlines(), 1):
        if ln.lstrip().startswith("--"):
            continue
        for ch in ln:
            if ch in _PAIRS:
                stack.append((ch, i))
            elif ch in _CLOSER:
                if not stack or stack[-1][0] != _CLOSER[ch]:
                    problems.append(f"{fname}:{i}: unbalanced {ch!r}")
                    stack.clear()
                    break
                stack.pop()
    if stack:
        ch, i = stack[0]
        problems.append(f"{fname}:{i}: unclosed {ch!r}")
    return problems


def lint_files(files: dict[str, str]) -> None:
    """Lint every file and enforce global theorem/def name uniqueness."""
    problems: list[str] = []
    seen: dict[str, str] = {}
    for fname, text in files.items():
        problems.extend(lint_text(fname, text))
        for m in _NAME.finditer(text):
            name = m.group(1)
            if name in seen:
                problems.append(
                    f"{fname}: duplicate declaration {name!r} (also in {seen[name]})"
                )
            else:
                seen[name] = fname
    if problems:
        raise LintError("emitted-Lean lint failed:\n  " + "\n  ".join(problems))

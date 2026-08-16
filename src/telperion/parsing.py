"""Safe expression parsing for the string-taking surfaces (CLI probe/diagnose,
MCP tools).

sympy's ``sympify``/``parse_expr`` evaluate Python under the hood — fine for
expressions you wrote, unacceptable for a tool surface an agent or remote
client feeds strings into.  ``safe_parse_expr`` accepts only the arithmetic
grammar a rational-function inequality needs: numbers, the declared symbols,
``+ - * / ** ^ ( )`` and whitespace.  Anything else — names, attributes,
brackets, quotes, lambdas — is rejected BEFORE the sympy parser ever sees it.
"""
from __future__ import annotations

import re

import sympy as sp

_TOKEN = re.compile(
    r"\s+|(?P<num>\d+(?:\.\d+)?)|(?P<name>[A-Za-z_][A-Za-z0-9_]*)|(?P<op>\*\*|[-+*/^()])"
)


class UnsafeExpressionError(ValueError):
    pass


def safe_parse_expr(text: str, symbols) -> sp.Expr:
    """Parse an arithmetic expression over the declared nonnegative symbols.

    Rejects any token that is not a number, a declared symbol name, or an
    arithmetic operator/parenthesis — before parsing.  '^' is accepted as
    exponentiation (Lean habit) and rewritten to '**'.
    """
    if len(text) > 20_000:
        raise UnsafeExpressionError("expression too long")
    allowed_names = {str(s) for s in symbols}
    pos = 0
    for m in _TOKEN.finditer(text):
        if m.start() != pos:
            raise UnsafeExpressionError(
                f"illegal character at position {pos}: {text[pos:pos + 10]!r}"
            )
        pos = m.end()
        name = m.group("name")
        if name is not None and name not in allowed_names:
            raise UnsafeExpressionError(
                f"unknown name {name!r} (declared symbols: {sorted(allowed_names)})"
            )
    if pos != len(text):
        raise UnsafeExpressionError(
            f"illegal character at position {pos}: {text[pos:pos + 10]!r}"
        )
    local = {str(s): s for s in symbols}
    return sp.parse_expr(text.replace("^", "**"), local_dict=local, evaluate=True)

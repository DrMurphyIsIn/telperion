"""Assemble emitted certificates into a hazard-safe, self-building Lean LEAF file.

The recurring pipeline behind the Kelmans merge-table ports (two-hub, assisted-merge,
general-environment, dichotomy) and the RH cosine leaves is always the same:

    a family of per-cell sympy certificates (each an all-nonneg polynomial on the orthant,
    a sign-flipped one, a constrained-cone one, or a finite rational fact)
        -> emit each as a Lean theorem (emit_nonneg_orthant / emit_domain_to_orthant / norm_num)
        -> wrap them in ONE self-building `R3Cert.+`-style leaf with a module docstring.

Done four times by hand in throwaway scripts, it kept re-introducing two Lean-comment
hazards: a `-/` inside docstring prose silently CLOSES the block comment (the `3-/4-hub`
bug), and a sympy `**` power leaks where Lean wants `^`.  This module codifies the pipeline
AND makes those two failure modes impossible: `render_leaf` scans the assembled text and
RAISES rather than shipping a file that won't parse.

`positivity_leaf` is the one-call front-end: give it a prefix, a list of cert specs, and a
module docstring, and it returns the complete Lean file text.  Each emitter it delegates to
is UNTRUSTED — the Lean kernel remains the sole arbiter.  conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from .emit_nonneg_orthant import nonneg_orthant_cert
from .emit_domain_to_orthant import domain_to_orthant_cert

__all__ = ["scan_hazards", "render_leaf", "positivity_leaf", "rational_pos_cert"]


def scan_hazards(text: str) -> list[str]:
    """Return a list of Lean-comment/operator hazards in ``text`` (empty = clean).

    Detects (1) any ``**`` (a leaked sympy power; Lean uses ``^``), and (2) a ``-/`` that
    appears INSIDE a block-comment body rather than closing it — the token that silently ends
    a `/- … -/` or `/-- … -/` comment early.  The scan walks comments explicitly so a `-/` in
    code (impossible) vs prose is judged correctly.
    """
    hazards: list[str] = []
    if "**" in text:
        n = text.count("**")
        hazards.append(f"{n} occurrence(s) of `**` (sympy power leaked; Lean uses `^`)")
    # Walk the text tracking in-comment vs in-code.  In code, `/-` opens a comment; a `-/`
    # seen in CODE (before any opener) is a STRAY comment-close — the tell-tale of a premature
    # `-/` in earlier docstring prose (the `3-/4` bug), which orphans the intended close.
    i, n = 0, len(text)
    while i < n:
        nxt_open = text.find("/-", i)
        nxt_close = text.find("-/", i)
        if nxt_close == -1:
            break
        if nxt_open != -1 and nxt_open < nxt_close:
            close = text.find("-/", nxt_open + 2)   # first close of this comment
            if close == -1:
                hazards.append(f"unterminated block comment opened at offset {nxt_open}")
                break
            i = close + 2
        else:
            hazards.append(
                f"stray `-/` in code at offset {nxt_close} — a `-/` in docstring prose "
                f"closes the comment early (the `3-/4` hazard); rewrite e.g. `3- /4`"
            )
            i = nxt_close + 2
    return hazards


def rational_pos_cert(name: str, value, *, doc: str | None = None) -> str:
    """Emit ``theorem name : (0:ℝ) < (p/q : ℝ) := by norm_num`` for a positive rational
    ``value`` (a finite exception fact).  Raises if ``value ≤ 0``."""
    v = sp.nsimplify(value)
    if v <= 0:
        raise ValueError(f"{name}: value {v} is not strictly positive")
    lit = f"({v.p}/{v.q} : ℝ)" if v.q != 1 else f"({v.p} : ℝ)"
    docblock = f"/-- {doc} -/\n" if doc else ""
    return f"{docblock}theorem {name} : (0:ℝ) < {lit} := by norm_num"


def _emit_spec(prefix: str, spec: dict) -> str:
    """Dispatch one cert spec to the right emitter.  Spec kinds:

      * ``orthant``  : {suffix, poly, syms, [sign=1], [doc]}   -> nonneg_orthant_cert(sign*poly)
      * ``domain``   : {suffix, poly, constraints, [sign=1], [doc]} -> domain_to_orthant_cert
      * ``rational`` : {suffix, value, [doc]}                  -> rational_pos_cert
    """
    kind = spec.get("kind", "orthant")
    name = f"{prefix}_{spec['suffix']}"
    doc = spec.get("doc")
    sign = spec.get("sign", 1)
    if kind == "orthant":
        poly = sp.expand(sign * spec["poly"])
        return nonneg_orthant_cert(name, poly, spec["syms"], doc=doc)
    if kind == "domain":
        poly = sp.expand(sign * spec["poly"])
        return domain_to_orthant_cert(name, poly, spec["constraints"], doc=doc)
    if kind == "rational":
        return rational_pos_cert(name, spec["value"], doc=doc)
    raise ValueError(f"{name}: unknown cert kind {kind!r}")


def render_leaf(
    *,
    module_doc: str,
    namespace: str,
    theorems,
    imports=("Mathlib",),
) -> str:
    """Assemble a complete Lean leaf: module docstring, imports, namespace, theorems.

    Scans the assembled text for comment/operator hazards and RAISES on any (so a
    non-parsing file is never returned).  ``theorems`` is a list of ready Lean theorem
    strings.
    """
    imp = "\n".join(f"import {m}" for m in imports)
    body = "\n\n".join(theorems)
    text = (
        f"/-\n{module_doc.rstrip()}\n-/\n"
        f"{imp}\n\n"
        f"namespace {namespace}\n\n"
        f"{body}\n\n"
        f"end {namespace}\n"
    )
    hz = scan_hazards(text)
    if hz:
        raise ValueError("cert_leaf hazards: " + "; ".join(hz))
    return text


def positivity_leaf(
    prefix: str,
    specs,
    *,
    module_doc: str,
    namespace: str = "R3Cert.Step3",
    imports=("Mathlib",),
) -> str:
    """One-call pipeline: a family of cert specs -> a hazard-safe self-building Lean leaf.

    Each spec (see ``_emit_spec``) is dispatched to `emit_nonneg_orthant`,
    `emit_domain_to_orthant`, or the norm_num rational front-end; the results are assembled
    by `render_leaf` (which enforces hazard-freedom).
    """
    theorems = [_emit_spec(prefix, s) for s in specs]
    return render_leaf(
        module_doc=module_doc, namespace=namespace, theorems=theorems, imports=imports
    )

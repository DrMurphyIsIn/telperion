"""Non-vacuity gate — Telperion pointed at its own emitted output.

The trust model guarantees the Lean kernel never accepts a FALSE theorem.  It
does NOT guarantee the theorem SAYS anything: a reflexive tautology (`X = X`),
`0 = 0`, or `0 ≤ 0` compiles green while proving nothing about the certificate.
That is the one soundness-adjacent failure the kernel cannot catch — because the
emitted statement, not the proof, is where the meaning lives.

This module is that missing check, in two complementary layers:

1. `check_nonvacuous(text)` — STRUCTURAL, runs on every emitted body in `emit()`
   (alongside the `sorry`/`axiom` soundness lint).  It parses each theorem's
   conclusion and refuses a reflexive (in)equality `t ⋈ t`.  This is exactly the
   class that let a WZ emitter render `X = X` (kernel green, Python silently the
   real checker) slip through hand review.

2. `assert_certificate_sensitive(...)` — SEMANTIC, for the identity-carrying
   special emitters (wz, putinar, cone).  It rebuilds the claim expression from a
   CORRUPTED certificate and requires the corruption to break it (the claim must
   be `0` for the true certificate and non-`0` for a perturbation).  A claim that
   survives every corruption is not verifying its certificate — refused.

Both are "faithfulness discipline aimed at the generator itself": the same
seeded-exact-point / independent-oracle stance `faithfulness.py` takes for the
certifiers, now applied to what the emitters actually write.
"""
from __future__ import annotations

from typing import Any, Callable, Sequence

import sympy as sp


class NonVacuityError(ValueError):
    """An emitted theorem states a tautology and verifies nothing."""


# ---------------------------------------------------------------------------
# Layer 1 — structural: reject reflexive / trivial emitted statements
# ---------------------------------------------------------------------------

# Binary relations that, applied to two identical sides, are content-free.
_RELATIONS = ("=", "≤", "<", "≥", ">", "≠", "↔")


def _normalize_side(s: str) -> str:
    """Collapse a rendered term to a comparison normal form: drop whitespace and
    `(... : ℝ)` / `(...:ℝ)` type ascriptions and one layer of wrapping parens, so
    `(0:ℝ)` and `0` compare equal (both are the trivial `0 ≤ 0` shape)."""
    t = "".join(s.split())
    # strip a type ascription of the whole side:  (BODY:ℝ) -> BODY
    while t.startswith("(") and t.endswith(")"):
        inner = t[1:-1]
        # only unwrap a balanced outer pair
        depth = 0
        balanced = True
        for i, ch in enumerate(inner):
            depth += (ch == "(") - (ch == ")")
            if depth < 0:
                balanced = False
                break
        if not balanced or depth != 0:
            break
        # drop a trailing ":<type>" ascription inside the parens (top level)
        d = 0
        cut = None
        for i, ch in enumerate(inner):
            d += (ch == "(") - (ch == ")")
            if d == 0 and ch == ":":
                cut = i
        t = inner[:cut] if cut is not None else inner
    return t


def _split_top_relation(concl: str) -> tuple[str, str] | None:
    """Split a conclusion on its FIRST top-level (paren-depth-0) relation.
    Returns (lhs, rhs) or None if no top-level relation is present."""
    depth = 0
    for i, ch in enumerate(concl):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch in _RELATIONS:
            # avoid the `:=` / `=>` / `≠`-as-`≥` false matches: `=` after `:` or
            # before `>` is handled since `:=`/`=>` never appear in a conclusion
            # (statement text is taken strictly between `:` and `:=`).
            return concl[:i], concl[i + 1:]
    return None


def _conclusion(stmt: str) -> str:
    """Strip `∀ …,` quantifier blocks and hypothesis arrows `H → … →` from a
    theorem statement, leaving the final conclusion."""
    s = stmt.strip()
    # peel leading  ∀ <binders>,  blocks (comma ends each; no comma in binders)
    while s.startswith("∀") or s.startswith("Ā") or s.startswith("∀"):
        comma = _top_level_comma(s)
        if comma is None:
            break
        s = s[comma + 1:].strip()
    # drop hypothesis arrows at top level, keep the last segment (the conclusion)
    parts = _split_top_level(s, "→")
    return parts[-1].strip()


def _top_level_comma(s: str) -> int | None:
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch == ",":
            return i
    return None


def _split_top_level(s: str, sep: str) -> list[str]:
    out, depth, last = [], 0, 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            out.append(s[last:i])
            i += len(sep)
            last = i
            continue
        i += 1
    out.append(s[last:])
    return out


def _iter_theorem_statements(text: str):
    """Yield (name, statement_text) for each `theorem <name> : <stmt> :=` in a
    Lean body.  Statements may span multiple lines (joined)."""
    import re

    # match `theorem NAME ... : STMT :=`  (STMT is up to the first top-level `:=`)
    for m in re.finditer(r"\btheorem\s+(\S+)", text):
        name = m.group(1)
        rest = text[m.end():]
        # find the `:` that starts the type (after optional binders up to `:`)
        colon = rest.find(":")
        assign = rest.find(":=")
        if colon == -1 or assign == -1 or colon >= assign:
            continue
        stmt = rest[colon + 1:assign]
        yield name, " ".join(stmt.split())


def _is_reflexive(stmt: str) -> bool:
    """True if a theorem's conclusion is `t ⋈ t` (identical sides normalized)."""
    split = _split_top_relation(_conclusion(stmt))
    return split is not None and _normalize_side(split[0]) == _normalize_side(split[1])


def check_nonvacuous(text: str, path: str | None = None) -> None:
    """Refuse a WHOLLY VACUOUS emitted body — one whose every theorem conclusion
    is reflexive (`X = X`, `0 ≤ 0`), so the emission proves nothing at all.

    This is the collapse class: an emitter that was meant to produce a
    substantive claim renders a tautology instead (the WZ `X = X` bug — a single
    reflexive theorem is a wholly-vacuous body).  A body that MIXES a tight-but-
    genuine ingredient (e.g. a monotone-tail base `b(s₀) ≤ B` that happens to be
    `1 ≤ 1` at a tie) with substantive theorems is NOT flagged here — per-instance
    rigor for identity certificates is the semantic `assert_certificate_sensitive`
    gate's job, which passes a tight-but-certificate-dependent claim.  Runs on
    emitted bodies only (not the trusted profile prelude); a family that
    intentionally emits an all-trivial body opts out via
    `LeanProfile(allow_reflexive=True)`."""
    where = f" in {path}" if path else ""
    thms = list(_iter_theorem_statements(text))
    if not thms:
        return
    reflexive = [name for name, stmt in thms if _is_reflexive(stmt)]
    if len(reflexive) == len(thms):
        raise NonVacuityError(
            f"WHOLLY VACUOUS body{where}: every theorem is reflexive "
            f"({', '.join(reflexive)}) — the emission compiles but verifies "
            "nothing. An emitter meant to produce a substantive claim has "
            "collapsed it to a tautology (the X=X class). If the triviality is "
            "intentional, set LeanProfile(allow_reflexive=True)."
        )


# ---------------------------------------------------------------------------
# Layer 2 — semantic: the certificate must be load-bearing
# ---------------------------------------------------------------------------

def assert_certificate_sensitive(
    build_claim: Callable[[Any], sp.Expr],
    base_cert: Any,
    perturbations: Sequence[Callable[[Any], Any]],
    *,
    label: str,
) -> int:
    """Require the emitted claim to DEPEND on the certificate.

    `build_claim(cert)` returns the sympy expression the emitted theorem asserts
    is identically zero (the denominator-cleared identity, `p − Σσᵢgᵢ`, …).  For
    the true certificate it must vanish; for at least one perturbed certificate it
    must NOT vanish — otherwise the claim is insensitive to the certificate (it
    would hold for a corrupted one too), i.e. vacuous.

    Returns the index of the first perturbation that breaks the claim.  Raises
    `NonVacuityError` if none does, or `ValueError` if the base claim does not
    vanish (a certifier bug — the honest self-check)."""
    base = sp.expand(build_claim(base_cert))
    if base != 0:
        raise ValueError(
            f"{label}: base claim does not vanish (expand = {base}); the "
            "certificate does not close the identity")
    for i, perturb in enumerate(perturbations):
        broken = sp.expand(build_claim(perturb(base_cert)))
        if broken != 0:
            return i
    raise NonVacuityError(
        f"{label}: VACUOUS — the emitted claim is identically zero for every "
        "tested certificate corruption; the theorem does not verify the "
        "certificate (the X=X class). No Lean should be emitted."
    )

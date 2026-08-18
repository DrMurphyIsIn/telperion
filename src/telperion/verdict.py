"""The honest-verdict record — the load-bearing meta-skill (pattern #8).

Distilled from the Brualdi-Goldwasser crux campaign, where 20+ probes closed
with a zero false-positive rate.  The discipline that achieved that was NOT any
single clever test; it was closing EVERY probe with one explicit verdict from a
fixed four-state taxonomy, and owning self-corrections rather than quietly
editing them away.  This module makes that discipline structural.

Four verdicts, and nothing else:

  * VALIDATED               — the claim holds, decided in EXACT arithmetic.
  * OBSTRUCTED_AND_LOCATED  — the claim does not close, and the obstruction is
                              EXHIBITED (a witness / a located cell / a tie).
                              "It failed" is not a verdict; "it failed HERE,
                              because of THIS" is.
  * NULL                    — the probe found no signal; a clean negative.
  * RE_DERIVATION           — a prior claim was wrong; this records the
                              correction and names what it supersedes.

The second load-bearing rule: **no floats at decision points.**  The comparison
that DECIDES a verdict must run on exact rationals (int / Fraction / sympy
Rational).  A float at a decision point is refused — `require_exact` and
`decide` are the only sanctioned way to compare-to-decide, exactly as `emit()`
is the only sanctioned way to reach Lean.  Floats are fine for display,
heuristics, and search; they are forbidden the moment a boolean verdict hangs
on them.

This is the honesty engine's spine: every other probe in Telperion (diagnose,
relax, hunt, the certificate emitters) is only as trustworthy as the discipline
of closing it with one of these four and refusing float-decided outcomes.
`conjecture1_proved=False` remains a VALIDATED-gated fact, never a default.
"""
from __future__ import annotations

import operator
from dataclasses import dataclass, field
from enum import Enum
from fractions import Fraction

import sympy as sp


class FloatAtDecisionPoint(Exception):
    """A float (or otherwise inexact value) reached a verdict decision point.

    Decisions are exact by construction; this is refused loudly, the same way a
    non-Polya numerator is refused at certification.  Use exact rationals, or if
    the quantity is genuinely transcendental, bracket it exactly first (see
    `IntervalBracketEmitter`) and decide on the rational enclosure."""


class Verdict(str, Enum):
    VALIDATED = "VALIDATED"
    OBSTRUCTED_AND_LOCATED = "OBSTRUCTED_AND_LOCATED"
    NULL = "NULL"
    RE_DERIVATION = "RE_DERIVATION"


def require_exact(value, label: str = "value") -> Fraction:
    """Coerce an exact-rational decision value to Fraction, or refuse.

    Accepts int, Fraction, sympy Rational/Integer.  Refuses Python float, sympy
    Float, complex, numpy floats, and non-numeric symbols with
    FloatAtDecisionPoint — a decision must not hang on an inexact value."""
    if isinstance(value, bool):  # already a decided boolean; pass through as 0/1
        return Fraction(int(value))
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, Fraction):
        return value
    if isinstance(value, sp.Basic):
        if value.is_Integer:
            return Fraction(int(value))
        if value.is_Rational:
            return Fraction(int(value.p), int(value.q))
        if getattr(value, "is_Float", False):
            raise FloatAtDecisionPoint(
                f"{label} is a sympy Float ({value}) at a decision point — "
                f"decisions must be exact"
            )
        raise FloatAtDecisionPoint(
            f"{label} is not exact-rational ({value!r}) at a decision point"
        )
    if isinstance(value, float):
        raise FloatAtDecisionPoint(
            f"{label} is a Python float ({value!r}) at a decision point — "
            f"bracket it exactly and decide on the enclosure"
        )
    raise FloatAtDecisionPoint(
        f"{label} has non-exact type {type(value).__name__} at a decision point"
    )


_OPS = {
    "<": operator.lt, "<=": operator.le, ">": operator.gt,
    ">=": operator.ge, "==": operator.eq, "!=": operator.ne,
}


def decide(lhs, op: str, rhs, label: str = "decision") -> bool:
    """The sanctioned compare-to-decide primitive: exact operands, exact result.

    Both sides pass through `require_exact` first, so a float-decided verdict is
    impossible by construction.  Returns the exact boolean."""
    if op not in _OPS:
        raise ValueError(f"unknown comparison {op!r}; use one of {sorted(_OPS)}")
    a = require_exact(lhs, f"{label}.lhs")
    b = require_exact(rhs, f"{label}.rhs")
    return _OPS[op](a, b)


@dataclass(frozen=True)
class ProbeVerdict:
    """The closing record of one probe: a claim, one of four verdicts, the exact
    evidence that decided it, and — where the verdict demands it — a located
    obstruction or the prior claim being corrected.

    The __post_init__ invariants make the honest-verdict discipline structural:
    you cannot record OBSTRUCTED without locating the obstruction, cannot record
    RE_DERIVATION without naming what it supersedes, cannot record VALIDATED
    without exact evidence."""

    claim: str
    verdict: Verdict
    evidence: tuple[str, ...] = ()
    obstruction: str | None = None      # required for OBSTRUCTED_AND_LOCATED
    corrected_from: str | None = None   # required for RE_DERIVATION
    detail: str = ""

    def __post_init__(self):
        v = self.verdict
        if v == Verdict.OBSTRUCTED_AND_LOCATED and not self.obstruction:
            raise ValueError(
                "OBSTRUCTED_AND_LOCATED requires a located obstruction (a "
                "witness / cell / tie) — 'it failed' is not a verdict"
            )
        if v == Verdict.RE_DERIVATION and not self.corrected_from:
            raise ValueError(
                "RE_DERIVATION requires naming the prior claim it corrects "
                "(own the self-correction, do not silently edit it away)"
            )
        if v == Verdict.VALIDATED and not self.evidence:
            raise ValueError(
                "VALIDATED requires at least one exact evidence item — a claim "
                "with no recorded exact ground is not validated"
            )

    def render(self) -> str:
        lines = [f"{self.verdict.value}: {self.claim}"]
        if self.corrected_from:
            lines.append(f"  supersedes: {self.corrected_from}")
        if self.obstruction:
            lines.append(f"  obstruction: {self.obstruction}")
        for e in self.evidence:
            lines.append(f"  · {e}")
        if self.detail:
            lines.append(f"  {self.detail}")
        return "\n".join(lines)

    def to_route_entry(self, ledger, route: str, target: str | None = None) -> bool:
        """Record this verdict into a RouteLedger (dedup-append); returns True if
        newly recorded.  The canonical four-state verdict becomes the entry's
        verdict field, so ROUTES.md speaks one vocabulary."""
        from .ledger import fingerprint_text

        tgt = target or self.claim
        detail = self.detail or self.obstruction or self.corrected_from or ""
        if self.evidence:
            detail = (detail + " | " if detail else "") + "; ".join(self.evidence)
        return ledger.record(
            target=tgt, fingerprint=fingerprint_text(self.claim),
            route=route, verdict=self.verdict.value, detail=detail,
        )


# --- constructors: one per verdict, so closing a probe reads as its verdict ---

def validated(claim: str, *evidence: str, detail: str = "") -> ProbeVerdict:
    return ProbeVerdict(claim, Verdict.VALIDATED, tuple(evidence), detail=detail)


def obstructed(claim: str, obstruction: str, *evidence: str,
               detail: str = "") -> ProbeVerdict:
    return ProbeVerdict(claim, Verdict.OBSTRUCTED_AND_LOCATED, tuple(evidence),
                        obstruction=obstruction, detail=detail)


def null(claim: str, *evidence: str, detail: str = "") -> ProbeVerdict:
    return ProbeVerdict(claim, Verdict.NULL, tuple(evidence), detail=detail)


def re_derivation(claim: str, corrected_from: str, *evidence: str,
                  detail: str = "") -> ProbeVerdict:
    return ProbeVerdict(claim, Verdict.RE_DERIVATION, tuple(evidence),
                        corrected_from=corrected_from, detail=detail)


def probe(fn):
    """Decorator: a probe MUST close with a ProbeVerdict.

    Structural enforcement, the emit()-refuses-without-validation pattern for
    reasoning: a function marked @probe that returns anything else raises, so a
    probe cannot quietly end without an explicit verdict."""
    from functools import wraps

    @wraps(fn)
    def wrapper(*args, **kwargs):
        out = fn(*args, **kwargs)
        if not isinstance(out, ProbeVerdict):
            raise TypeError(
                f"@probe {fn.__name__} must return a ProbeVerdict (close with an "
                f"explicit verdict), got {type(out).__name__}"
            )
        return out

    return wrapper

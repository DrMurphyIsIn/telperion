"""The atomic single-goal backend operation.

`prove_goal(target, symbols)` is the primitive an external prover loop, a
benchmark harness, or an autoformalization front-door calls: one scalar
inequality goal ``0 <= target`` (symbols assumed ``>= 0``) in, a self-contained
kernel-checkable Lean theorem out — or, on refusal, the same FALSE /
NOT_POLYA / CERTIFIABLE triage `diagnose` gives, so the caller learns *why* and
(for FALSE) gets an exact rational counterexample.

The trust model is unchanged: `prove_goal` only runs the enforced
certify -> validate -> emit workflow on a one-instance family; a wrong
certificate is still a Lean compile error, never a false theorem.  This module
adds no new trusted surface — it is a thin, deterministic front door onto the
existing pipeline plus emitter auto-selection.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

import sympy as sp

from .certify import certify
from .diagnose import diagnose_expr
from .emit import DirectPolyaEmitter
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import ValidationReport, emit


@dataclass(frozen=True)
class ProofResult:
    """Outcome of a single-goal proof attempt.

    ``verdict`` is one of PROVED (Lean in ``lean``, emitter named), FALSE
    (rational ``counterexample``), NOT_POLYA_IN_THIS_FORM (remedy ``hints``),
    or CERTIFIABLE (the goal is true and in-shape but no wired emitter closed
    it — a coverage gap, not a soundness event).
    """

    proved: bool
    verdict: str
    lean: str | None = None
    emitter: str | None = None
    detail: str = ""
    counterexample: dict | None = None
    hints: tuple[str, ...] = ()

    def render(self) -> str:
        if self.proved:
            return f"PROVED via {self.emitter}"
        out = [f"{self.verdict}: {self.detail}"]
        if self.counterexample:
            wit = ", ".join(f"{k} = {v}" for k, v in self.counterexample.items())
            out.append(f"  witness: {wit}")
        out.extend(f"  hint: {h}" for h in self.hints)
        return "\n".join(out)


# A rung builds the (family, emitter) pair for one certificate shape, or returns
# None when the shape does not apply to this target.  The ladder is tried in
# order; the first rung that certifies AND emits wins.  This is the Phase-0.1
# kind-router: v1.1 covers the rational-inequality workhorse (Pólya) plus a
# polynomial-nonnegativity fallback (exact SOS, which reaches the interior ties
# Pólya cannot).  Putinar / Handelman / WZ / CG rungs slot in here next.
def _base_family(target: sp.Expr, syms: tuple, name: str) -> InequalityFamily:
    return InequalityFamily(
        name=name,
        symbols=syms,
        grid=GridSpec([("_", [0])]),
        lean_name=lambda pt: name.lower(),
        target=lambda pt: target,
    )


def _direct_polya_rung(target: sp.Expr, syms: tuple, name: str):
    return _base_family(target, syms, name), DirectPolyaEmitter()


def _sos_rung(target: sp.Expr, syms: tuple, name: str):
    # SOS proves `0 <= p` over ALL reals for a polynomial p (an exact rational
    # PSD-Gram decomposition) — a strictly stronger claim than the nonneg-orthant
    # goal, so it soundly discharges it, and it reaches perfect-square interior
    # ties Pólya refuses.  Non-polynomial targets fall through untouched; a
    # polynomial that is not globally SOS makes certify refuse, so no false claim.
    if not target.is_polynomial(*syms):
        return None
    from .emit_sos import SOSEmitter, sos_family

    fam = sos_family(
        name=name,
        symbols=syms,
        grid=GridSpec([("_", [0])]),
        lean_name=lambda pt: name.lower(),
        target=lambda pt: target,
    )
    return fam, SOSEmitter()


def _rational_sos_rung(target: sp.Expr, syms: tuple, name: str):
    # Artin/Positivstellensatz: `0 <= p` over ALL reals for a polynomial p that
    # is nonnegative but NOT a sum of squares (e.g. Motzkin), via a strictly
    # positive multiplier q with `q·p = Σ dᵢℓᵢ²`.  Strictly more general than the
    # plain SOS rung, so it sits after it.  Needs the SDP finder (cvxpy); absent
    # it, find_rational_sos returns None and this rung is skipped.
    if not target.is_polynomial(*syms):
        return None
    from .emit_rational_sos import (
        RationalSOSEmitter, find_rational_sos, rational_sos_family,
    )

    found = find_rational_sos(target, syms)
    if found is None:
        return None
    q, sos = found
    fam = rational_sos_family(
        name=name,
        symbols=syms,
        grid=GridSpec([("_", [0])]),
        lean_name=lambda pt: name.lower(),
        spec=lambda pt: (target, q, sos),
    )
    return fam, RationalSOSEmitter()


_DEFAULT_RUNGS = (_direct_polya_rung, _sos_rung, _rational_sos_rung)


def prove_goal(
    target: sp.Expr,
    symbols: Sequence[sp.Symbol],
    *,
    name: str = "Goal",
    namespace: tuple[str, ...] | None = None,
    emitters: Sequence[object] | None = None,
    trials: int = 400,
) -> ProofResult:
    """Certify and emit ``0 <= target`` as one Lean theorem, or triage the refusal.

    ``symbols`` are the free variables (assumed nonnegative).  On success the
    returned ``lean`` is a complete, stamped, self-contained theorem; on failure
    the caller gets the triage so it can branch (retry lifted, hand off, give up).

    Without ``emitters`` the kind-router ladder is used (Pólya, then SOS).
    Passing ``emitters`` overrides it with those emitters over the base family
    (back-compat / explicit control).
    """
    syms = tuple(symbols)
    profile = LeanProfile(namespace=namespace or (name,))
    green = ValidationReport(checks=(("prove_goal", True),))

    if emitters is not None:
        rungs = [
            (lambda t, s, n, e=e: (_base_family(t, s, n), e)) for e in emitters
        ]
    else:
        rungs = _DEFAULT_RUNGS

    for rung in rungs:
        built = rung(target, syms, name)
        if built is None:
            continue
        fam, emitter = built
        try:
            certified = certify(fam)
            result = emit(certified, profile, [emitter], green)
        except Exception:
            # Certification refused or this rung couldn't render — try the next;
            # if none closes, we fall through to the triage below.
            continue
        lean = next(iter(result.files.values()))
        return ProofResult(
            proved=True,
            verdict="PROVED",
            lean=lean,
            emitter=type(emitter).__name__,
            detail=f"certified and emitted via {type(emitter).__name__}",
        )

    diag = diagnose_expr(target, syms, trials=trials)
    return ProofResult(
        proved=False,
        verdict=diag.verdict,
        detail=diag.detail,
        counterexample=diag.counterexample,
        hints=diag.hints,
    )

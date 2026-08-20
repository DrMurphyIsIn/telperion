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


# Emitter ladder for v1: the rational-inequality workhorse.  The full
# kind-detecting router (SOS / Putinar / Handelman / WZ / CG / ...) is Phase 0.1.
def _default_ladder() -> list:
    return [DirectPolyaEmitter()]


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
    """
    syms = tuple(symbols)
    ladder = list(emitters) if emitters is not None else _default_ladder()
    profile = LeanProfile(namespace=namespace or (name,))
    green = ValidationReport(checks=(("prove_goal", True),))

    fam = InequalityFamily(
        name=name,
        symbols=syms,
        grid=GridSpec([("_", [0])]),
        lean_name=lambda pt: name.lower(),
        target=lambda pt: target,
    )

    for emitter in ladder:
        try:
            certified = certify(fam)
            result = emit(certified, profile, [emitter], green)
        except Exception:
            # Certification refused or this emitter couldn't render — try the
            # next rung; if none closes, we fall through to the triage below.
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

"""Backend-lift harness (Phase 1): quantify what a deterministic certificate
backend adds to an LLM prover on certificate-shaped goals.

The thesis under test: an LLM prover that dispatches certificate-shaped subgoals
to Telperion solves goals it misses alone, deterministically and at
CPU-seconds cost instead of pass@N sampling.  This module runs the *backend*
side for real (`prove_goal`) and takes the *prover* side as a pluggable set of
already-solved names — a stub in tests, the real open prover (Goedel-Prover-V2)
in a cloud run.  Keeping the prover behind a name-set seam means the harness is
deterministic, GPU-free, and unit-testable, while the measured comparison stays
honest (same problem list, same solved/unsolved accounting).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence

import sympy as sp

from .prove import prove_goal


@dataclass(frozen=True)
class LiftProblem:
    """One certificate-shaped goal ``0 <= target`` over nonnegative ``symbols``."""

    name: str
    target: sp.Expr
    symbols: tuple[sp.Symbol, ...]


@dataclass(frozen=True)
class LiftOutcome:
    """The backend's deterministic result on one problem."""

    name: str
    backend_proved: bool
    verdict: str
    emitter: str | None = None


@dataclass(frozen=True)
class LiftReport:
    """Backend-vs-prover accounting over a problem suite."""

    total: int
    backend_solved: set[str]
    prover_solved: set[str]
    lift: set[str]            # solved by backend, missed by the prover alone


def run_backend(problems: Sequence[LiftProblem]) -> list[LiftOutcome]:
    """Run the deterministic certificate backend on every problem."""
    outcomes: list[LiftOutcome] = []
    for p in problems:
        res = prove_goal(p.target, p.symbols, name=_lean_name(p.name))
        outcomes.append(
            LiftOutcome(
                name=p.name,
                backend_proved=res.proved,
                verdict=res.verdict,
                emitter=res.emitter,
            )
        )
    return outcomes


def lift_report(
    outcomes: Iterable[LiftOutcome],
    prover_solved: set[str],
) -> LiftReport:
    """Compare the backend's solved set against the prover's solved set.

    ``lift`` is the decision-relevant number: problems the backend proves that
    the prover alone did not — the net-new coverage a backend integration buys.
    """
    outcomes = list(outcomes)
    backend_solved = {o.name for o in outcomes if o.backend_proved}
    return LiftReport(
        total=len(outcomes),
        backend_solved=backend_solved,
        prover_solved=set(prover_solved),
        lift=backend_solved - set(prover_solved),
    )


def _lean_name(problem_name: str) -> str:
    # Lean identifiers: keep it simple and valid for the emitted theorem name.
    cleaned = "".join(c if c.isalnum() else "_" for c in problem_name)
    return cleaned[:1].upper() + cleaned[1:] if cleaned else "Goal"

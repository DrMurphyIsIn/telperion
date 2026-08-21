"""Phase 1 backend-lift harness: measure what a certificate backend adds to a
(pluggable) LLM prover on certificate-shaped goals.

The prover side is a plain callable ``name -> bool`` (solved-alone), so the
harness is fully testable locally with a stub; the real open prover
(Goedel-Prover-V2) plugs into the same seam in a cloud run.  The backend side is
deterministic `prove_goal`, run here for real.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.backend_lift import (  # noqa: E402
    LiftProblem,
    lift_report,
    run_backend,
)

u = sp.Symbol("u", nonnegative=True)


def _suite():
    return [
        # certifiable rational inequality — backend proves it
        LiftProblem("provable", (1 + u) / (u + 1) - sp.Rational(1) / (u + 2), (u,)),
        # false — backend must NOT claim it
        LiftProblem("false_goal", u - 1, (u,)),
        # true but a RATIONAL interior tie — outside both the Pólya and SOS
        # rungs (SOS is polynomial-only), so still unsolved by the backend
        LiftProblem("rational_tie", (u - 1) ** 2 / (u + 1), (u,)),
    ]


def test_run_backend_solves_only_the_certifiable_goal():
    outcomes = {o.name: o for o in run_backend(_suite())}

    assert outcomes["provable"].backend_proved is True
    assert outcomes["provable"].verdict == "PROVED"
    assert outcomes["false_goal"].backend_proved is False
    assert outcomes["false_goal"].verdict == "FALSE"
    assert outcomes["rational_tie"].backend_proved is False


def test_lift_report_counts_problems_the_backend_adds_over_the_prover():
    outcomes = run_backend(_suite())
    # stub prover: solves nothing on its own
    report = lift_report(outcomes, prover_solved=set())

    assert report.backend_solved == {"provable"}
    assert report.lift == {"provable"}          # solved by backend, missed by prover
    assert report.total == 3


def test_lift_is_zero_when_prover_already_solves_everything_the_backend_does():
    outcomes = run_backend(_suite())
    report = lift_report(outcomes, prover_solved={"provable"})

    assert report.lift == set()                 # no net-new problems
    assert report.backend_solved == {"provable"}

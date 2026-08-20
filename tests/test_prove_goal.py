"""The atomic single-goal backend op: `prove_goal(target, symbols)`.

An external prover loop / benchmark harness / autoformalization front-door all
need the same primitive — one goal in, a self-contained Lean proof term out, or
a triage (FALSE + rational counterexample / NOT_POLYA + hints).  This is the
foundation Phase of the superiority roadmap.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.prove import prove_goal  # noqa: E402

u = sp.Symbol("u", nonnegative=True)


def test_prove_goal_returns_lean_for_provable_inequality():
    # 0 <= (1+u)/(u+1) - 1/(u+2) = (u+1)/(u+2), true for all u >= 0.
    res = prove_goal((1 + u) / (u + 1) - sp.Rational(1) / (u + 2), symbols=(u,))

    assert res.proved is True
    assert res.verdict == "PROVED"
    assert res.emitter == "DirectPolyaEmitter"
    assert "theorem" in res.lean


def test_prove_goal_triages_false_inequality_with_counterexample():
    # 0 <= u - 1 is FALSE at u = 0 (target = -1); expect a rational witness.
    res = prove_goal(u - 1, symbols=(u,))

    assert res.proved is False
    assert res.verdict == "FALSE"
    assert res.counterexample is not None
    # the witness must actually drive the target strictly negative
    witness = {sp.Symbol(k, nonnegative=True): v for k, v in res.counterexample.items()}
    assert (u - 1).subs(witness) < 0


def test_prove_goal_triages_interior_tie_as_not_polya_with_hint():
    # 0 <= (u-1)^2 is TRUE but has an interior tie at u=1, so no Pólya
    # certificate exists — diagnose must route to NOT_POLYA and hint SOS.
    res = prove_goal((u - 1) ** 2, symbols=(u,))

    assert res.proved is False
    assert res.verdict == "NOT_POLYA_IN_THIS_FORM"
    assert res.counterexample is None
    assert any("SOS" in h for h in res.hints)

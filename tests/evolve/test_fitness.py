from __future__ import annotations

import sympy as sp
from telperion import InequalityFamily, GridSpec
from telperion.evolve.fitness import (
    DISPROVEN, hunt_is_true, certify_score, score_family, FitnessResult,
)

u = sp.Symbol("u", nonnegative=True)


def _toy(lift, target="true"):
    tgt = (
        (lambda pt: (u**2 - u + pt["a"]) / (u + 1)) if target == "true"
        else (lambda pt: (u - 1) / (u + 1))
    )
    return InequalityFamily(
        name="ToyLift", symbols=(u,), grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"toy_lift_a{pt['a']}", target=tgt, auto_lift=lift,
    )


def test_hunt_rejects_false_claim_with_witness():
    ok, art = hunt_is_true(_toy(0, "false"), [u])
    assert ok is False
    assert art["witness"] == {"u": 0} or art["witness_value"] < 0


def test_hunt_accepts_true_claim():
    ok, _ = hunt_is_true(_toy(0, "true"), [u])
    assert ok is True


def test_certify_fails_on_naive_shape_passes_on_lift():
    ok0, nfail, art = certify_score(_toy(0))
    assert ok0 is False and nfail >= 1 and "reason" in art
    ok1, _, _ = certify_score(_toy(1))
    assert ok1 is True


def test_score_orders_disproven_below_wrongshape_below_certifying():
    false_r = score_family(_toy(0, "false"), [u], complexity=0)
    naive_r = score_family(_toy(0, "true"), [u], complexity=0)
    good_r = score_family(_toy(1, "true"), [u], complexity=1)
    assert false_r.score == DISPROVEN
    assert false_r.score < naive_r.score < good_r.score
    assert good_r.tag.startswith("CERTIFIES")
    assert isinstance(good_r, FitnessResult)

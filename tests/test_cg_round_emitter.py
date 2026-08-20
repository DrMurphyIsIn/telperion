"""Chvatal-Gomory integer-rounding emitter (VIPR-style) -- pipeline + controls.

Proves a linear goal over INTEGER variables from a derivation of two rule kinds:
`lincomb` (a nonnegative rational combination of prior facts) and `cg_round`
(from an integer-coefficient fact `Sigma c_j x_j >= v`, since the LHS is an
integer, derive `Sigma c_j x_j >= ceil(v)`).  The certifier verifies every step
EXACTLY and refuses on the first mismatch; the emitter passes the non-vacuity
gate AND a rounding-sensitivity self-check (perturbing a ceil back to its
pre-rounding value must break the chain).  Kernel verdict is CI-only.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp
from fractions import Fraction as Fr

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, CGRoundEmitter, LeanProfile,
    ValidationReport, certify, check_lean_text, emit, cg_round_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam):
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [CGRoundEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    return res, body


# ---------------------------------------------------------------------------
# The canonical CG example: 2x >= 1 over the integers rounds to 2x >= 1 (no gain)
# -- instead the load-bearing case is a NON-integer bound that rounds up.
# From `3x >= 2` (x integer) we get `x >= ceil(2/3) = 1`; halving needs the
# integrality, so it is genuinely a Chvatal-Gomory cut.
# ---------------------------------------------------------------------------

def _spec_single_round(pt):
    x = sp.Symbol("x")
    facts = [({"x": 3}, Fr(2))]                 # 3x >= 2
    deriv = [
        {"rule": "cg_round", "src": 0},        # 3x >= ceil(2) ... but coeffs on x=3,
        # actually we want to divide first: use lincomb to scale to x >= 2/3.
    ]
    return facts, deriv, ({"x": 1}, Fr(1))


def test_cg_round_single_cut_certifies_and_emits():
    x = sp.Symbol("x")
    # facts: 3x >= 2.  lincomb (1/3)* -> x >= 2/3.  cg_round -> x >= ceil(2/3)=1.
    # goal: x >= 1.
    fam = cg_round_family(
        "CG", (x,), GridSpec([("j", [0])]), lambda pt: "cg",
        lambda pt: (
            [({"x": 3}, Fr(2))],
            [
                {"rule": "lincomb", "combo": {0: Fr(1, 3)}, "const": Fr(0)},  # x >= 2/3
                {"rule": "cg_round", "src": 1},                              # x >= 1
            ],
            ({"x": 1}, Fr(1)),
        ),
    )
    res, body = _emit_clean(fam)
    assert res.n_theorems == 1
    assert "Int" in body                       # integer variables
    assert "theorem cg" in body


def test_cg_round_refuses_noninteger_coefficient():
    x = sp.Symbol("x")
    # cg_round on a fact whose x-coefficient is 1/2 (LHS not guaranteed integer)
    fam = cg_round_family(
        "Bad", (x,), GridSpec([("j", [0])]), lambda pt: "bad",
        lambda pt: (
            [({"x": Fr(1, 2)}, Fr(1, 4))],       # (1/2) x >= 1/4  -- non-integer coeff
            [{"rule": "cg_round", "src": 0}],
            ({"x": Fr(1, 2)}, Fr(1, 2)),
        ),
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_cg_round_refuses_vacuous_rounding():
    x = sp.Symbol("x")
    # v already integer (2): cg_round claims a strict gain -> refused as vacuous.
    fam = cg_round_family(
        "Vac", (x,), GridSpec([("j", [0])]), lambda pt: "vac",
        lambda pt: (
            [({"x": 1}, Fr(2))],                 # x >= 2, already integer
            [{"rule": "cg_round", "src": 0}],  # ceil(2) = 2, no gain -> vacuous
            ({"x": 1}, Fr(2)),
        ),
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_cg_round_refuses_negative_multiplier():
    x, y = sp.symbols("x y")
    # lincomb with a NEGATIVE multiplier flips the inequality sense -> refused.
    fam = cg_round_family(
        "Neg", (x, y), GridSpec([("j", [0])]), lambda pt: "neg",
        lambda pt: (
            [({"x": 1}, Fr(1)), ({"y": 1}, Fr(1))],
            [{"rule": "lincomb", "combo": {0: Fr(1), 1: Fr(-1)}, "const": Fr(0)}],
            ({"x": 1, "y": -1}, Fr(0)),
        ),
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_cg_round_refuses_goal_not_dominated():
    x = sp.Symbol("x")
    # derive x >= 1, but claim the goal x >= 2 -- not dominated -> refused.
    fam = cg_round_family(
        "Dom", (x,), GridSpec([("j", [0])]), lambda pt: "dom",
        lambda pt: (
            [({"x": 3}, Fr(2))],
            [
                {"rule": "lincomb", "combo": {0: Fr(1, 3)}, "const": Fr(0)},
                {"rule": "cg_round", "src": 1},   # x >= 1
            ],
            ({"x": 1}, Fr(2)),                       # claim x >= 2 -- too strong
        ),
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_cg_round_sensitivity_gate():
    # The certifier's rounding-sensitivity self-check: replacing ceil(v) back to
    # v must break the goal-domination (otherwise the round did no work).  A
    # derivation whose goal holds WITHOUT the rounding step is refused.
    x = sp.Symbol("x")
    # goal x >= 2/3 is already met by the pre-round fact x >= 2/3: the cg_round
    # step is not load-bearing for THIS goal -> the sensitivity gate refuses.
    fam = cg_round_family(
        "Sens", (x,), GridSpec([("j", [0])]), lambda pt: "sens",
        lambda pt: (
            [({"x": 3}, Fr(2))],
            [
                {"rule": "lincomb", "combo": {0: Fr(1, 3)}, "const": Fr(0)},
                {"rule": "cg_round", "src": 1},   # x >= 1
            ],
            ({"x": 1}, Fr(2, 3)),                    # goal met pre-round -> not sensitive
        ),
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_cg_round_byte_stability():
    x = sp.Symbol("x")
    spec = lambda pt: (
        [({"x": 3}, Fr(2))],
        [
            {"rule": "lincomb", "combo": {0: Fr(1, 3)}, "const": Fr(0)},
            {"rule": "cg_round", "src": 1},
        ],
        ({"x": 1}, Fr(1)),
    )
    fam = cg_round_family("S", (x,), GridSpec([("j", [0])]), lambda pt: "s", spec)
    a, _ = _emit_clean(fam)
    b, _ = _emit_clean(cg_round_family(
        "S", (x,), GridSpec([("j", [0])]), lambda pt: "s", spec))
    assert a.files == b.files


def test_cg_round_multivariable_lincomb():
    x, y = sp.symbols("x y")
    # x >= 1, y >= 1  ==(sum)==>  x + y >= 2 (already integer, no round needed)
    fam = cg_round_family(
        "MV", (x, y), GridSpec([("j", [0])]), lambda pt: "mv",
        lambda pt: (
            [({"x": 1}, Fr(1)), ({"y": 1}, Fr(1))],
            [{"rule": "lincomb", "combo": {0: Fr(1), 1: Fr(1)}, "const": Fr(0)}],
            ({"x": 1, "y": 1}, Fr(2)),
        ),
    )
    res, body = _emit_clean(fam)
    assert res.n_theorems == 1

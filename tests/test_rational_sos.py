"""Rational-SOS (Artin denominator) emitter: 0 <= p for nonneg-but-not-SOS p.

Reaches the class the plain SOS emitter cannot (Hilbert: nonnegativity != SOS).
Finds a strictly-positive multiplier q with q*p an exact rational SOS, then
divides q out.  SDP-backed (cvxpy-guarded); untrusted -- the certifier re-verifies
q*p = SOS exactly, so a miss is a refusal.
"""
import sys
from pathlib import Path
import pytest
import sympy as sp

pytest.importorskip("cvxpy")
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, RationalSOSEmitter, ValidationReport,
    certify, check_lean_text, check_nonvacuous, emit, find_rational_sos,
    rational_sos_family,
)

GREEN = ValidationReport(checks=(("spot", True),))
x, y = sp.symbols("x y")
MOTZKIN = x ** 4 * y ** 2 + x ** 2 * y ** 4 - 3 * x ** 2 * y ** 2 + 1


def test_motzkin_is_not_plain_sos_but_rational_sos_finds_it():
    from telperion.sos_sdp import gram_sdp
    # Motzkin is NOT a plain SOS
    assert gram_sdp(MOTZKIN, [x, y], 3)[0] is None
    # ...but the Artin finder finds q > 0 with q*Motzkin an exact SOS
    found = find_rational_sos(MOTZKIN, (x, y))
    assert found is not None
    q, sos = found
    assert sp.expand(q * MOTZKIN - sum(c * b ** 2 for c, b in sos)) == 0


def test_rational_sos_finder_mode_certifies_and_emits():
    fam = rational_sos_family("R", (x, y), GridSpec([("j", [0])]), lambda pt: "m",
                              lambda pt: (MOTZKIN, None, None))
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [RationalSOSEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    check_nonvacuous(body)
    assert res.n_theorems == 1
    assert all(t in body for t in ("positivity", "ring", "nlinarith", "mul_pos"))


def test_rational_sos_refuses_negative():
    with pytest.raises(CertificationError):
        certify(rational_sos_family("B", (x, y), GridSpec([("j", [0])]),
                                    lambda pt: "b", lambda pt: (x ** 2 - 2, None, None)))

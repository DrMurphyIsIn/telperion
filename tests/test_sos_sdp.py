"""SDP-SOS + complementary-slackness duality tests (skipped without cvxpy)."""
import sys
from pathlib import Path

import pytest
import sympy as sp

pytest.importorskip("cvxpy")

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.sos_sdp import (  # noqa: E402
    gram_sdp,
    lean_certificate,
    sos_sdp_certificate,
)

x, y = sp.symbols("x y")
P = 2 * x**2 - 2 * x * y + 2 * y**2 - 2 * x - 2 * y + 2   # interior tie at (1,1)


def test_gram_is_psd_and_exact():
    Q, mons = gram_sdp(P, [x, y], half_deg=1)
    assert Q is not None
    mvec = sp.Matrix(mons)
    assert sp.expand((mvec.T * Q * mvec)[0] - P) == 0        # exact Gram
    assert all(ev >= 0 for ev in Q.eigenvals())              # PSD


def test_sos_exact_and_tight_variety():
    cert, tight = sos_sdp_certificate(P, [x, y])
    assert sp.expand(cert.as_expr() - P) == 0                # exact SOS
    # complementary slackness: common zeros of square bases = the tie (1,1)
    sol = sp.solve(list(tight), [x, y], dict=True)
    assert {x: sp.Integer(1), y: sp.Integer(1)} in sol


def test_interior_zero_beyond_polya():
    # P vanishes at an interior point (1,1) -> NOT a nonneg-coeff/Polya form,
    # yet the SDP certifies it
    assert P.subs({x: 1, y: 1}) == 0
    assert lean_certificate("t", P, [x, y]) is not None


def test_lean_reports_tight_variety():
    lean = lean_certificate("t", P, [x, y])
    assert "tight variety" in lean and "positivity" in lean and "**" not in lean

"""Convex-hinge certificate — the reusable primitive under G1 Stage-II floors and
the R7 ledger.  Both use the folded hinge potential `φ(y) = c·(y − t0)₊` (the
same hinge as the closed R3 `phi_le_one` proof).

The load-bearing hinge fact is superadditivity of the positive part:

    Σᵢ (yᵢ − t0)₊  ≥  ( Σᵢ yᵢ − k·t0 )₊         (k = #children)

i.e. the sum of per-node hinge slacks is at least the hinge of the total — the
"context-free class floor" shape (min at equal children).  It is exact and
kernel-checkable: `posPart` is subadditive, so the positive part of a sum is at
most the sum of positive parts.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.hinge import (  # noqa: E402
    HingeFloorCertificate,
    hinge_floor_certificate,
    verify_hinge_floor,
)


def test_certifies_the_hinge_superadditivity_floor():
    # c=1, t0=1/4, three children — the floor Σ(yᵢ−t0)₊ ≥ (Σyᵢ − 3·t0)₊ holds.
    cert = hinge_floor_certificate(c=sp.Rational(1), t0=sp.Rational(1, 4), k=3)

    assert isinstance(cert, HingeFloorCertificate)
    assert verify_hinge_floor(cert) is True
    assert cert.k == 3


def test_verify_rejects_a_negative_slope():
    # c < 0 makes the hinge concave — the floor direction flips; must be refused.
    assert hinge_floor_certificate(c=sp.Rational(-1), t0=sp.Rational(1, 4), k=3) is None


def test_floor_is_exact_at_the_all_equal_point():
    # the min of Σφ(yᵢ) − φ(Σyᵢ − (k-1)t0) is 0 at equal children ≥ t0 — the
    # certificate records this tightness (Jensen equality on the linear branch).
    cert = hinge_floor_certificate(c=sp.Rational(2), t0=sp.Rational(23, 100), k=4)
    assert verify_hinge_floor(cert) is True
    assert cert.tight_at_equal is True

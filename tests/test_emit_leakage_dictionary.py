"""Tests for the leakage_dictionary emitter (PROGRAM MIRRORMERE, ROUTE A item A2b).

Covers the three things that make the certificate an instrument rather than a restatement:

  1. the divisor recursion is RE-DERIVED exactly and reproduces the published `b(n)` row of
     QC_AXIOMS_DRAFT.md:481 (Davenport-Heilbronn) and its von Mangoldt control (zeta);
  2. `certify` REFUSES in BOTH directions -- a vanishing claim for a non-multiplicative
     amplitude, and a leak claim for a completely-multiplicative one;
  3. the emitted Lean carries the row (so a corrupted row is kernel-rejectable) and the
     `log 6` decomposition it needs.

conjecture1_proved = False.
"""
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.emit_leakage_dictionary import (  # noqa: E402
    K, LeakageDictionaryEmitter, _lg, _log_expr, certify_leakage_dictionary_point,
    interval_of, leakage_certificate, leakage_dictionary_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

CHI5 = [1, -1, -1, 1, 0]
DH = [1, K, -K, -1, 0]
ZETA = [1]


# ---------------------------------------------------------------------------
# 1.  The row is RE-DERIVED, and it matches the published table
# ---------------------------------------------------------------------------
def _numeric_row(vec, period, n, kappa_value):
    """Evaluate the certified symbolic row at the true kappa, as floats."""
    cert = leakage_certificate(vec, period, n, "leaks" if vec is DH else "vanishes")
    subs = {K: kappa_value}
    for p in (2, 3, 5, 7):
        subs[_lg(p)] = sp.log(p)
    return {d: float(sp.N(e.subs(subs))) for d, e in cert.row}


def test_dh_row_matches_published_table():
    """QC_AXIOMS_DRAFT.md:481 publishes DH b(2)=+0.1969, b(3)=-0.3121, b(6)=+1.9364."""
    kappa = (sp.sqrt(10 - 2 * sp.sqrt(5)) - 2) / (sp.sqrt(5) - 1)
    row = _numeric_row(DH, 5, 6, kappa)
    assert row[1] == 0.0
    assert abs(row[2] - 0.1969) < 5e-5
    assert abs(row[3] - (-0.3121)) < 5e-5
    assert abs(row[6] - 1.9364) < 5e-5


def test_completely_multiplicative_row_cancels_at_the_composite():
    """The positive control: a Dirichlet character's row vanishes at n = 6, exactly."""
    cert = leakage_certificate(CHI5, 5, 6, "vanishes")
    assert dict(cert.row)[6] == 0
    assert cert.completely_multiplicative is True
    # ... and the prime layer is NOT zero, so the vanishing has content.
    assert dict(cert.row)[2] != 0


def test_zeta_fiber_row_is_von_mangoldt():
    """`a = 1` is the zeta fiber: b = Lambda, so b 2 = log 2 and b 6 = 0."""
    cert = leakage_certificate(ZETA, 1, 6, "vanishes")
    row = dict(cert.row)
    assert row[6] == 0
    assert sp.simplify(row[2] - _lg(2)) == 0
    assert sp.simplify(row[3] - _lg(3)) == 0


def test_dh_row_is_the_expected_closed_form():
    """b 6 = (1 + kappa^2)(log 2 + log 3) -- the two cross terms ADD, they do not cancel."""
    cert = leakage_certificate(DH, 5, 6, "leaks")
    got = dict(cert.row)[6]
    want = (1 + K ** 2) * (_lg(2) + _lg(3))
    assert sp.expand(got - want) == 0


# ---------------------------------------------------------------------------
# 2.  The negative control bites in BOTH directions
# ---------------------------------------------------------------------------
def test_refuses_vanishing_claim_for_non_multiplicative_amplitude():
    with pytest.raises(ValueError, match="NOT completely"):
        leakage_certificate(DH, 5, 6, "vanishes")


def test_refuses_leak_claim_for_completely_multiplicative_amplitude():
    with pytest.raises(ValueError, match="COMPLETELY MULTIPLICATIVE"):
        leakage_certificate(CHI5, 5, 6, "leaks")


def test_refuses_prime_power_index():
    """4 and 9 are prime powers: the dictionary says nothing there, either way."""
    for n in (4, 9, 25):
        with pytest.raises(ValueError, match="PRIME POWER"):
            leakage_certificate(DH, 5, n, "leaks")


def test_refuses_unnormalized_amplitude():
    with pytest.raises(ValueError, match="normalized"):
        leakage_certificate([2, 1, 1, 1, 0], 5, 6, "leaks")


def test_refuses_empty_enclosure():
    with pytest.raises(ValueError, match="empty enclosure"):
        leakage_certificate(DH, 5, 6, "leaks", enclosure=(F(2), F(1)))


def test_complete_multiplicativity_is_decided_not_sampled():
    """A sequence that is multiplicative on small inputs but not a character is caught."""
    bad = [1, 1, 1, 1, 1]        # the all-ones period-5 vector IS a character (trivial mod 1)
    assert leakage_certificate(bad, 5, 6, "vanishes").completely_multiplicative is True
    worse = [1, 2, 1, 1, 0]      # a(2)a(3) = 2 but a(6) = a(1) = 1
    with pytest.raises(ValueError, match="NOT completely"):
        leakage_certificate(worse, 5, 6, "vanishes")


# ---------------------------------------------------------------------------
# 3.  The emitted Lean carries the certificate
# ---------------------------------------------------------------------------
def _emit(vec, period, n, claim, enclosure=None, name="leak_t"):
    fam = leakage_dictionary_family(
        "T", GridSpec([("case", [0])]), lambda pt: name,
        spec=lambda pt: {"vec": vec, "period": period, "n": n, "claim": claim,
                         "enclosure": enclosure})
    inst, nchk = certify_leakage_dictionary_point(fam, {"case": 0}, name)

    class _V:
        instances = [inst]

    body, nthm = LeakageDictionaryEmitter(
        atom_bounds_lean=(("K", "Quasicrystal.dhKappa_bounds", F(1, 4), F(3, 10)),
                          ("Lg2", "Quasicrystal.log_two_bounds", F(69, 100), F(70, 100)),
                          ("Lg3", "Quasicrystal.log_three_bounds", F(109, 100), F(110, 100)))
    ).emit_body(_V(), LeanProfile(namespace=("X",)))
    return body, nthm, nchk


def test_emitted_dh_carries_the_row_and_the_log_decomposition():
    body, nthm, nchk = _emit(DH, 5, 6, "leaks")
    assert nchk == 4                       # one check per divisor of 6
    assert "theorem leak_t_b_6" in body
    assert "Real.log 6 = Real.log 2 + Real.log 3" in body
    assert "Quasicrystal.dhKappa ^ 2" in body
    # the verdict, the instrument and the falsification twin
    assert "leak_t_composite_leak_pos" in body
    assert "leak_t_not_completelyMultiplicative" in body
    assert "leak_t_multiplicativity_is_necessary" in body
    assert "sorry" not in body


def test_emitted_control_certifies_zero():
    body, _nthm, _n = _emit(CHI5, 5, 6, "vanishes")
    assert "theorem leak_t_composite_vanishes" in body
    assert "b 6 = 0" in body
    assert "multiplicativity_is_necessary" not in body   # twin only on the leaking side


def test_enclosure_is_computed_not_supplied():
    """The emitter's own interval arithmetic must pin the published +1.9364."""
    cert = leakage_certificate(DH, 5, 6, "leaks")
    S = sum((F(-1, 2) ** (i + 1) / F(i + 1) for i in range(24)), F(0))
    l2 = (F(6931471803, 10 ** 10), F(6931471808, 10 ** 10))
    l3 = (l2[0] + (-S - F(1, 2) ** 24), l2[1] + (-S + F(1, 2) ** 24))
    kb = (F(284079041, 10 ** 9), F(142039523, 500000000))
    lo, hi = interval_of(dict(cert.row)[6], {K: kb, _lg(2): l2, _lg(3): l3})
    # The published +1.9364 is the 4-decimal ROUNDING of the true 1.9363560766...,
    # so the certified interval must round to it, not contain it.
    assert round(float(lo), 4) == 1.9364 and round(float(hi), 4) == 1.9364
    assert float(lo) > 1.93635 and float(hi) < 1.93637


def test_log_expr_is_on_the_prime_basis():
    """`log 6 = log 2 + log 3` is an identity of the representation, which is WHY the
    completely-multiplicative row cancels exactly instead of approximately."""
    assert sp.expand(_log_expr(6) - (_lg(2) + _lg(3))) == 0
    assert sp.expand(_log_expr(4) - 2 * _lg(2)) == 0

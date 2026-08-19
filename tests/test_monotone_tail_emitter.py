"""First-class monotone-ratio tail emitter: pipeline flow, honesty, negatives.

The Lean kernel is the arbiter (CI `lake build`); these are the pre-CI
self-checks — exact ratio derivation, the Polya nonincreasing-tail cert, the
exact base fact, byte-stability, `check_lean_text` cleanliness, and the two
negative controls (increasing b, base violated)."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
)
from telperion.emit_monotone_tail import (  # noqa: E402
    MonotoneRatioTailEmitter,
    MonotoneTailPayload,
    monotone_tail_family,
)
from telperion.lean_lint import check_lean_text

s = sp.Symbol("s")


def _near_star_b():
    """b(s) = Phi^11(N(0,s)) = (64/621)^(2s+1) a_hub(s)^11 (3/2)^(11s).

    A real positive sequence (transcendental in s) whose ratio is the rational
    (486/529)(1+1/(4s^2+11s+6))^11, nonincreasing for s >= 5, with b(5) = 1."""
    a_hub = (4 * s + 3) / (3 * (s + 1))
    return sp.Rational(64, 621) ** (2 * s + 1) * a_hub ** 11 * sp.Rational(3, 2) ** (11 * s)


def _family(b=None, s0=5, bound=1):
    b = b if b is not None else _near_star_b()
    return monotone_tail_family(
        name="MonoTailTest",
        symbols=(),
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "nearstar_tail",
        spec=lambda pt: (b, s0, bound, s),
    )


def _emit(fam):
    return emit(
        certify(fam),
        LeanProfile(namespace=("G1", "MonoTail")),
        [MonotoneRatioTailEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )


def test_kind_is_monotone_tail():
    assert _family().kind == "monotone_tail"


def test_ratio_is_rational_and_matches():
    cf = certify(_family())
    pl: MonotoneTailPayload = cf.instances[0].payload
    expected = sp.Rational(486, 529) * (1 + 1 / (4 * s * s + 11 * s + 6)) ** 11
    assert sp.simplify(pl.ratio - expected) == 0
    # ratio is a rational function of s (num, den are polynomials)
    num, den = sp.fraction(sp.together(pl.ratio))
    assert sp.Poly(sp.expand(num), s).total_degree() >= 0
    assert sp.Poly(sp.expand(den), s).total_degree() >= 0


def test_base_value_exact():
    cf = certify(_family())
    pl: MonotoneTailPayload = cf.instances[0].payload
    assert pl.base_value == 1  # b(5) = 1 exactly (the tie)
    assert pl.base_value <= pl.bound


def test_step_cert_is_polya_nonneg():
    cf = certify(_family())
    pl: MonotoneTailPayload = cf.instances[0].payload
    t = pl.t_symbol
    # numerator all-nonneg, denominator all-positive over t
    pn = sp.Poly(sp.expand(pl.step_cert.numerator), t)
    pd = sp.Poly(sp.expand(pl.step_cert.denominator), t)
    assert all(c >= 0 for c in pn.coeffs())
    assert all(c > 0 for c in pd.coeffs())
    # the cert IS 1 - r(s0 + t)
    recon = sp.together(pl.step_cert.numerator / pl.step_cert.denominator)
    assert sp.simplify(recon - (1 - pl.ratio.subs(s, pl.s0 + t))) == 0


def test_emit_produces_three_theorems_per_instance():
    res = _emit(_family())
    text = res.files["MonoTailTest.lean"]
    assert "theorem nearstar_tail_step" in text
    assert "theorem nearstar_tail_base" in text
    assert "theorem nearstar_tail_tail" in text
    assert "positivity" in text
    assert "norm_num" in text
    assert "Nat.le_induction" in text
    assert res.n_theorems == 3


def test_lean_text_clean():
    res = _emit(_family())
    check_lean_text(res.files["MonoTailTest.lean"])


def test_byte_stability():
    a = _emit(_family()).files["MonoTailTest.lean"]
    b = _emit(_family()).files["MonoTailTest.lean"]
    assert a == b


def test_negative_control_A_increasing_b_refused():
    # b(s) = 2 - 1/(s+1) is INCREASING -> r(s) > 1 -> 1 - r(s) < 0 -> no Polya
    inc = 2 - 1 / (s + 1)
    with pytest.raises(CertificationError):
        certify(_family(b=inc, s0=1, bound=10))


def test_negative_control_B_base_violated_refused():
    # a nonincreasing b (1/(s+1)) but bound below the base b(s0)
    dec = 1 / (s + 1)  # b(1) = 1/2, nonincreasing
    with pytest.raises(CertificationError):
        certify(_family(b=dec, s0=1, bound=sp.Rational(1, 4)))  # 1/2 > 1/4


def test_positive_control_simple_decreasing():
    # a clean rational decreasing b with b(s0) <= B
    dec = 1 / (s + 1)  # r(s) = (s+1)/(s+2) < 1, decreasing; b(1) = 1/2
    fam = monotone_tail_family(
        name="SimpleDec",
        symbols=(),
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "simple_dec",
        spec=lambda pt: (dec, 1, sp.Rational(1, 2), s),
    )
    res = emit(
        certify(fam),
        LeanProfile(namespace=("G1", "SimpleDec")),
        [MonotoneRatioTailEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )
    check_lean_text(res.files["SimpleDec.lean"])

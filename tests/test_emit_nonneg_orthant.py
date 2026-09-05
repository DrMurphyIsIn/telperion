"""The nonneg-orthant emitter reproduces the Kelmans two-hub / assisted-merge cert
bodies and rejects mis-shaped inputs."""
import sympy as sp
import pytest

from telperion.emit_nonneg_orthant import (
    nonneg_orthant_cert,
    monomial_nonneg_hint,
    poly_lean_terms,
)


def _two_hub_num(cA):
    x, y = sp.symbols("x y", nonnegative=True)
    pA, pB = 1 + x, 1 + y
    K = pA + pB
    V, W = sp.Rational(621, 64), sp.Rational(513, 80)
    z15, z14 = sp.Rational(3, 23), sp.Rational(3, 19)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    m = 5 - cA
    S_T = m * z14 + (K + 1 - m) * z15
    lhs = (W / V) ** m * V * (1 + S_T / (K + 1))
    zA, zB = zs(pA + 1, cA), zs(pB + 1, 0)
    rhs = Fs(pA + 1, cA) * ((1 + pA * zA * z15) * (1 + pB * zB * z15) + zA * zB)
    num, den = sp.fraction(sp.together(lhs - rhs))
    pn = sp.Poly(sp.expand(num), x, y)
    dens = [sp.Rational(c).q for c in pn.coeffs()]
    L = sp.ilcm(*dens) if len(dens) > 1 else dens[0]
    return sp.expand(num * L), (x, y)


# The polynomial bodies as shipped in R47R7KelmansTwoHubCert.lean (c0 and c5).
_TWO_HUB_BODY = {
    0: "2108756468*x*y*y + 2108756468*x*x*y + 7183219186*y*y + 24070628096*x*y + "
       "7183219186*x*x + 28147580320*y + 28147580320*x + 13037927646",
    5: "21411*x*y + 21411*y + 61776*x + 61776",
}


@pytest.mark.parametrize("cA", [0, 5])
def test_two_hub_body_reproduced(cA):
    poly, syms = _two_hub_num(cA)
    p = sp.Poly(poly, *syms)
    assert poly_lean_terms(p, ["x", "y"]) == _TWO_HUB_BODY[cA]


@pytest.mark.parametrize("cA", range(6))
def test_two_hub_cert_emits_and_covers_monomials(cA):
    poly, syms = _two_hub_num(cA)
    cert = nonneg_orthant_cert(f"two_hub_gap_pos_c{cA}", poly, syms)
    assert cert.startswith("theorem two_hub_gap_pos_c")
    assert "nlinarith [" in cert
    # every degree>=2 monomial must have a hint so nlinarith can close
    p = sp.Poly(sp.expand(poly), *syms)
    for exps, _ in p.terms():
        if sum(exps) >= 2:
            hint = monomial_nonneg_hint(exps, ["hx", "hy"])
            assert hint in cert


def test_monomial_hint_shapes():
    assert monomial_nonneg_hint((0, 0), ["hx", "hy"]) is None
    assert monomial_nonneg_hint((1, 0), ["hx", "hy"]) == "hx"
    # left-fold over the flattened factor list [x,x,y] / [x,y,y] (nlinarith ring-normalizes)
    assert monomial_nonneg_hint((2, 1), ["hx", "hy"]) == "mul_nonneg (mul_nonneg hx hx) hy"
    assert monomial_nonneg_hint((1, 2), ["hx", "hy"]) == "mul_nonneg (mul_nonneg hx hy) hy"


def test_rejects_negative_coefficient():
    x, y = sp.symbols("x y", nonnegative=True)
    with pytest.raises(ValueError, match="negative coefficient"):
        nonneg_orthant_cert("bad", 5 + x - 2 * y, (x, y))


def test_rejects_nonpositive_constant():
    x, y = sp.symbols("x y", nonnegative=True)
    with pytest.raises(ValueError, match="not strictly positive"):
        nonneg_orthant_cert("bad", x + y, (x, y))

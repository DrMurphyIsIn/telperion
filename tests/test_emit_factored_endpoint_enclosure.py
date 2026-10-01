"""Tests for the factored_endpoint_enclosure emitter (0 <= F on closed boxes touching a
singular endpoint, by factorization plus a box sign) and for the ``log_taylor`` face of
``transcendental_enclosure`` that supplies its signed-remainder log bounds.

Offline: exact certificate construction and re-verification, every refusal, an independent
high-precision check of the certified claims (mpmath on a grid, including the endpoint), the
emitted Lean text, and the frozen dogfood.  The kernel run is the dogfood ``lake build`` (CI)
and the lean-gated negative controls (``test_negctrl_factored_endpoint_enclosure``).

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import mpmath as mp  # noqa: E402
import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_factored_endpoint_enclosure import (  # noqa: E402
    L_SYM,
    LOG_EXP_SPEC,
    LOG_SHARP_FALSE_SPEC,
    LOG_SHARP_SPEC,
    PADE_SPEC,
    RATIONAL_SPEC,
    SYNTH2_MARGIN_FALSE_SPEC,
    SYNTH2_MARGIN_SPEC,
    SYNTH2_SPEC,
    X_SYM,
    FactoredEndpointEnclosureEmitter,
    FactoredEndpointRefusal,
    bernstein2,
    factored_endpoint_certificate,
    factored_endpoint_enclosure_family,
    verify_certificate,
)
from telperion.emit_transcendental_enclosure import (  # noqa: E402
    TranscendentalEnclosureEmitter,
    log_taylor_lean,
    log_taylor_poly,
    transcendental_enclosure_certificate,
    transcendental_enclosure_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "factored_endpoint_enclosure"
mp.mp.dps = 40

_ALL = {"log_exp": LOG_EXP_SPEC, "log_sharp": LOG_SHARP_SPEC, "rational": RATIONAL_SPEC,
        "synth2": SYNTH2_SPEC, "pade": PADE_SPEC, "synth2_margin": SYNTH2_MARGIN_SPEC}


def _emit_one(spec, name="inst"):
    fam = factored_endpoint_enclosure_family(
        "FEETest", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec)
    rep = emit(certify(fam), LeanProfile(namespace=("FEETest",)),
               [FactoredEndpointEnclosureEmitter()],
               ValidationReport(checks=(("factored_endpoint_enclosure", True),)))
    return next(iter(rep.files.values()))


def _mpF(cert, lv, xv=0):
    f = sp.lambdify((L_SYM, X_SYM), cert.F, modules="mpmath")
    return f(mp.mpf(lv), mp.mpf(xv))


# ---- log_taylor face of transcendental_enclosure ------------------------------------------

@pytest.mark.parametrize("n", range(1, 9))
def test_log_taylor_remainder_sign(n):
    u = sp.Symbol("u")
    T = sp.lambdify(u, log_taylor_poly(n, u), modules="mpmath")
    for uv in ("0", "0.001", "0.3", "1", "2.5", "17", "1000"):
        gap = mp.log(1 + mp.mpf(uv)) - T(mp.mpf(uv))
        assert (-1) ** n * gap >= 0          # odd: log <= T; even: T <= log


def test_log_taylor_face_certificate_and_refusals():
    c = transcendental_enclosure_certificate(face="log_taylor", orders=[3, 2, 3])
    assert c.face == "log_taylor" and c.orders == (2, 3)
    for bad in ([0], [17], [2.0], []):
        with pytest.raises(ValueError, match="REFUSED"):
            transcendental_enclosure_certificate(face="log_taylor", orders=bad)


def test_log_taylor_lean_text():
    text, n = log_taylor_lean("LT", [2, 5])
    assert n == 8
    for s in ("theorem log_le_T", "theorem T_le_log", "theorem lower_2", "theorem upper_5",
              "Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5",
              "u - u ^ 2 / 2 ≤ Real.log (1 + u)", "namespace LT", "end LT"):
        assert s in text, s
    assert "sorry" not in text and "native_decide" not in text


def test_log_taylor_face_emits_through_transcendental_emitter():
    fam = transcendental_enclosure_family(
        "TETest", GridSpec([("case", [0])]), lambda pt: "lt",
        spec=lambda pt: {"face": "log_taylor", "orders": [1, 4]})
    rep = emit(certify(fam), LeanProfile(namespace=("TETest",)),
               [TranscendentalEnclosureEmitter()],
               ValidationReport(checks=(("transcendental_enclosure", True),)))
    text = next(iter(rep.files.values()))
    assert "namespace lt_logTaylor" in text and "theorem upper_1" in text
    assert "theorem lower_4" in text


# ---- the certificate -----------------------------------------------------------------------

@pytest.fixture(scope="module")
def certs():
    return {k: factored_endpoint_certificate(**v) for k, v in _ALL.items()}


def test_dogfood_factorizations(certs):
    l = L_SYM
    assert certs["log_exp"].H == sp.expand(l / 2 - l ** 2 / 3)
    assert certs["log_exp"].orders == (3,)
    assert certs["rational"].H == sp.expand(5 + 4 * l) and certs["rational"].orders == ()
    assert certs["synth2"].H == sp.expand((X_SYM - l) ** 2 + l * X_SYM)
    assert certs["pade"].orders == (5,) and certs["pade"].k == 4
    assert certs["pade"].H == sp.Rational(1, 12) - l / 10 - sp.Rational(2, 5) * l ** 2
    assert len(certs["synth2"].boxes) == 3            # splits in x, then in l
    for c in certs.values():
        assert c.checked
        verify_certificate(c)


def test_pade_auto_order_skips_order_three():
    """Order 3 divides by l^4 but gives H = -2/3 < 0; the search moves on to order 5."""
    with pytest.raises(FactoredEndpointRefusal):
        factored_endpoint_certificate(**PADE_SPEC, orders=(3,))
    assert factored_endpoint_certificate(**PADE_SPEC).orders == (5,)


@pytest.mark.parametrize("name", list(_ALL))
def test_claims_hold_numerically_including_endpoint(certs, name):
    c = certs[name]
    A, B = c.l_range
    C, Dd = c.x_range
    for i in range(41):
        lv = A + (B - A) * sp.Rational(i, 40)
        xs = [C + (Dd - C) * sp.Rational(j, 10) for j in range(11)] if c.two_var else [0]
        for xv in xs:
            v = _mpF(c, mp.mpf(lv.p) / lv.q, mp.mpf(sp.Rational(xv).p) / sp.Rational(xv).q)
            assert v >= -mp.mpf(10) ** -35, (name, lv, xv, v)
            # H is the quotient's polynomial floor: H(l) * t^k <= D F
            Hv = c.H.subs({L_SYM: lv, X_SYM: xv})
            assert Hv >= 0


def test_sharp_constant_margins():
    f = lambda l: (l - mp.log(1 + l)) / l ** 2  # noqa: E731
    m = f(mp.mpf(1) / 10)
    assert mp.mpf(117) / 250 < m < mp.mpf(47) / 100
    assert abs(m - mp.mpf(117) / 250) < mp.mpf(1) / 1000
    assert abs(m - mp.mpf(47) / 100) < mp.mpf(11) / 10000


def test_bernstein2_identity_and_endpoint_coefficient():
    P = sp.Poly(L_SYM ** 2 - L_SYM * X_SYM + X_SYM ** 2, L_SYM, X_SYM, domain="QQ")
    a, b, c, d = sp.Rational(0), sp.Rational(1, 2), sp.Rational(1, 8), sp.Rational(1)
    p, q, w = bernstein2(P, a, b, c, d)
    rhs = sum(w[i][j] * (L_SYM - a) ** i * (b - L_SYM) ** (p - i) * (X_SYM - c) ** j
              * (d - X_SYM) ** (q - j) for i in range(p + 1) for j in range(q + 1))
    assert sp.expand(P.as_expr() - rhs) == 0
    # the corner coefficient times its scale is the corner value
    assert w[0][0] * (b - a) ** p * (d - c) ** q == P.as_expr().subs({L_SYM: a, X_SYM: c})


# ---- refusals -------------------------------------------------------------------------------

@pytest.mark.parametrize("spec, match", [
    (LOG_SHARP_FALSE_SPEC, "FALSE: the claim fails at l = 1/10"),
    (SYNTH2_MARGIN_FALSE_SPEC, "FALSE: the claim fails at l = 1/8, x = 1/4"),
    (dict(LOG_EXP_SPEC, k=3), "does not divide"),
    (dict(LOG_EXP_SPEC, F="sin(l)"), "only log"),
    (dict(LOG_EXP_SPEC, F="exp(l) - 1 - l"), "only log"),
    (dict(LOG_EXP_SPEC, s="1/20"), "inside the domain"),
    (dict(LOG_EXP_SPEC, side="left"), "inside the domain"),
    (dict(LOG_EXP_SPEC, side="up"), "side"),
    (dict(LOG_EXP_SPEC, l_range=(0.0, "1/10")), "floats"),
    (dict(LOG_EXP_SPEC, F="l - log(1 + l) + 0.5*l**2"), "float"),
    (dict(LOG_EXP_SPEC, orders=(2,)), "wrong parity"),
    (dict(LOG_EXP_SPEC, orders=(3, 5)), "log atoms"),
    (dict(LOG_EXP_SPEC, F="log(1 + l)**2", orders=None), "not linear in its log"),
    (dict(LOG_EXP_SPEC, F="log(1 + log(1 + l))", orders=None), "nested log"),
    (dict(LOG_EXP_SPEC, F="l/log(2 + l)", orders=None), "denominator"),
    (dict(LOG_EXP_SPEC, F="l - log(1 + l) + y"), "free symbols"),
    (dict(LOG_EXP_SPEC, F="sqrt(l)"), "non-integer powers"),
    (dict(LOG_EXP_SPEC, H="l"), "does not satisfy"),
    (dict(LOG_EXP_SPEC, k=0), "k = 0"),
    (dict(LOG_EXP_SPEC, l_range=("1/10", "0")), "reversed"),
    # a TRUE claim whose log argument 1 + u has u = -l/2 < 0: no signed-remainder bound
    (dict(F="l**2 + l**2*log(1 - l/2)", s=0, k=2, l_range=("0", "1")), "OBSTRUCTED"),
    # the denominator changes sign inside the domain (and F < 0 left of the pole)
    (dict(F="l**4/(l - 1/2)", s=0, k=4, l_range=("0", "1")), "FALSE"),
])
def test_refusals(spec, match):
    with pytest.raises(FactoredEndpointRefusal, match=match):
        factored_endpoint_certificate(**spec)


def test_left_side_endpoint():
    """The mirror image: F = (1 - l)^2 (2 - l) on [1/2, 1], vanishing at s = 1 from the left."""
    c = factored_endpoint_certificate(F="(1 - l)**2*(2 - l)", s=1, k=2, side="left",
                                      l_range=("1/2", "1"))
    assert c.sigma == -1 and c.H == sp.expand(2 - L_SYM)
    text = _emit_one(dict(F="(1 - l)**2*(2 - l)", s=1, k=2, side="left",
                          l_range=("1/2", "1")), "mirror")
    assert "(1 - l) ^ 2 * mirror_H l" in text


def test_verify_rejects_tampering(certs):
    c = certs["log_sharp"]
    with pytest.raises(FactoredEndpointRefusal):
        verify_certificate(replace(c, H=c.H + 1))
    with pytest.raises(FactoredEndpointRefusal):
        verify_certificate(replace(c, k=3))
    bc = c.boxes[0]
    with pytest.raises(FactoredEndpointRefusal):
        verify_certificate(replace(c, boxes=(replace(bc, box=(0, sp.Rational(1, 20), None,
                                                               None)),)))


def test_forged_certificate_is_unchecked():
    c = factored_endpoint_certificate(**LOG_SHARP_FALSE_SPEC, max_depth=0, check=False)
    assert not c.checked and len(c.boxes) == 1 and not c.boxes[0].ok()


# ---- emission ------------------------------------------------------------------------------

def test_emitted_text_shape():
    text = _emit_one(PADE_SPEC, "pade")
    for s in ("theorem factored_endpoint_core", "theorem factored_endpoint_quot",
              "theorem pade :", "theorem pade_quot", "theorem pade_fac", "theorem pade_b0_H",
              "theorem pade_b0_low", "theorem pade_b0_D", "theorem pade_b0 ",
              "FEELogTaylor.upper_5", "noncomputable def pade_F", "field_simp",
              "∀ l ∈ Set.Icc (0 : ℝ) (1 / 3 : ℝ), 0 ≤ pade_F l"):
        assert s in text, s
    assert "sorry" not in text and "axiom " not in text and "native_decide" not in text
    assert "admit" not in text


def test_two_variable_union_follows_the_tree():
    text = _emit_one(SYNTH2_SPEC, "s2")
    assert "rcases le_total x (9 / 16 : ℝ) with h | h" in text
    assert "rcases le_total l (1 / 4 : ℝ) with h | h" in text
    assert "∀ x ∈ Set.Icc (1 / 8 : ℝ) (1 : ℝ), 0 ≤ s2_F l x" in text


def test_generic_section_emitted_once_for_several_instances():
    fam = factored_endpoint_enclosure_family(
        "FEETwo", GridSpec([("case", [0, 1])]),
        lambda pt: ["one", "two"][pt["case"]],
        spec=lambda pt: [LOG_EXP_SPEC, PADE_SPEC][pt["case"]])
    rep = emit(certify(fam), LeanProfile(namespace=("FEETwo",)),
               [FactoredEndpointEnclosureEmitter()],
               ValidationReport(checks=(("factored_endpoint_enclosure", True),)))
    text = next(iter(rep.files.values()))
    assert text.count("theorem factored_endpoint_core") == 1
    assert text.count("theorem log_le_T") == 1
    assert "theorem upper_3" in text and "theorem upper_5" in text
    assert "theorem one :" in text and "theorem two :" in text


def test_emitter_for_kind():
    assert (type(emitter_for("factored_endpoint_enclosure")).__name__
            == "FactoredEndpointEnclosureEmitter")


def test_dogfood_is_frozen():
    import subprocess
    r = subprocess.run([sys.executable, str(_EX / "generate.py"), "--check"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr

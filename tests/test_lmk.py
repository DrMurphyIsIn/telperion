"""L+M+K tests: dual-engine validation, certification cache, interval symbols."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BilinearBoxEmitter,
    CertificationError,
    DiskCache,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    interval_family,
)

u, v = sp.symbols("u v", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


# ---- L: dual-engine ---------------------------------------------------------
def test_dual_engine_agreement_passes():
    fam = InequalityFamily(
        name="DE",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"de_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
        independent_target=lambda pt, point: (
            (pt["a"] + point["u"]) / (point["u"] + 1)
            - Fraction(pt["a"]) / (point["u"] + 2)
        ),
    )
    cf = certify(fam)
    assert cf.checks_passed >= 2 + 6  # certs + 3 dual checks per instance


def test_dual_engine_disagreement_refused():
    fam = InequalityFamily(
        name="DE2",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "de2_a1",
        target=lambda pt: (1 + u) / (u + 2),
        independent_target=lambda pt, point: (2 + point["u"]) / (point["u"] + 2),
    )
    with pytest.raises(CertificationError, match="DUAL-ENGINE"):
        certify(fam)


# ---- M: cache ---------------------------------------------------------------
def test_cache_hits_on_recertification(tmp_path):
    fam = InequalityFamily(
        name="CA",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"ca_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )
    cf1 = certify(fam, cache_dir=tmp_path / "c")
    cf2 = certify(fam, cache_dir=tmp_path / "c")
    for a, b in zip(cf1.instances, cf2.instances):
        assert sp.expand(a.corners[0].numerator - b.corners[0].numerator) == 0
    # entries were written and reused
    assert len(list((tmp_path / "c").glob("*.json"))) == 3
    # cached REFUSALS replay too
    bad = InequalityFamily(
        name="CB",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "cb_a1",
        target=lambda pt: u - 3,
    )
    with pytest.raises(CertificationError):
        certify(bad, cache_dir=tmp_path / "c")
    with pytest.raises(CertificationError):
        certify(bad, cache_dir=tmp_path / "c")


def test_memoize_decorator(tmp_path):
    from telperion import memoize

    cache = DiskCache(tmp_path / "m")
    calls = []

    @memoize(cache, key_fn=lambda x: ("f", x))
    def slow(x):
        calls.append(x)
        return [x, x * 2]

    assert slow(3) == [3, 6]
    assert slow(3) == [3, 6]
    assert calls == [3]


# ---- K: interval symbols ----------------------------------------------------
rho, sigma = sp.symbols("rho sigma", nonnegative=True)


def test_interval_family_single_bracket_certifies_and_emits():
    # claim: for all rho in [1/2, 3/2]: 0 <= 2 - rho*u/(1+u)   (linear in rho)
    fam = interval_family(
        name="IV1",
        symbols=(u,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "iv1",
        target=lambda pt: 2 - rho * u / (1 + u),
        brackets={rho: (sp.Rational(1, 2), sp.Rational(3, 2))},
    )
    cf = certify(fam)
    assert len(cf.instances[0].corners) == 4
    res = emit(cf, LeanProfile(prelude="theorem bilinear_corner_nonneg : True := trivial"),
               [BilinearBoxEmitter()], GREEN)
    text = next(iter(res.files.values()))
    # the quantified interval statement: floor + cap hypotheses on rho
    assert "(hQ0 : ((1) / (2)) ≤ rho)" in text
    assert "(hQ1 : rho ≤ ((3) / (2)))" in text


def test_interval_family_two_brackets():
    # for rho in [1,2], sigma in [1/4,1/2]: 0 <= 3 - rho*u/(1+u) - sigma
    fam = interval_family(
        name="IV2",
        symbols=(u,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "iv2",
        target=lambda pt: 3 - rho * u / (1 + u) - sigma,
        brackets={rho: (sp.Integer(1), sp.Integer(2)),
                  sigma: (sp.Rational(1, 4), sp.Rational(1, 2))},
    )
    cf = certify(fam)
    assert len(cf.instances[0].corners) == 4


def test_interval_family_refuses_false_bracket():
    # 1 - rho*u/(1+u) is FALSE for rho = 3 at large u -> corner refusal
    fam = interval_family(
        name="IV3",
        symbols=(u,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "iv3",
        target=lambda pt: 1 - rho * u / (1 + u),
        brackets={rho: (sp.Integer(2), sp.Integer(3))},
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_interval_family_refuses_quadratic_dependence():
    fam = interval_family(
        name="IV4",
        symbols=(u,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "iv4",
        target=lambda pt: 1 + rho**2,
        brackets={rho: (sp.Integer(0), sp.Integer(1))},
    )
    with pytest.raises(CertificationError, match="not bilinear"):
        certify(fam)


def test_interval_floor_style_claim():
    # a miniature of the G1 floor shape: p*L - a*G - C >= floor with L, G in
    # brackets (linear in each) — p=3, a=1, C=1/10, floor=0 at the worst corner
    L, G = sp.symbols("L G", nonnegative=True)
    fam = interval_family(
        name="Floor",
        symbols=(),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "floor0",
        target=lambda pt: 3 * L - G - sp.Rational(1, 10),
        brackets={L: (sp.Rational(206586, 10**6), sp.Rational(206587, 10**6)),
                  G: (sp.Rational(405465, 10**6), sp.Rational(405466, 10**6))},
    )
    cf = certify(fam)   # worst corner: 3*L_lo - G_hi - 1/10 = 0.619758 - 0.405466 - 0.1 > 0
    assert len(cf.instances) == 1

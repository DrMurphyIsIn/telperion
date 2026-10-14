"""Rigorous segment-enclosure winding (telperion.arb_winding) and the DH routes through it.

Regression tests for the 2026-10-14 soundness audit
(~/e9-research/review_telperion_winding/REVIEW_telperion_winding_2026-10-14.md): the old node-sampling
count (now arb_dh.winding_number_sampled_heuristic) can return a WRONG integer; the segment method must not.
conjecture1_proved = False.
"""
import json
import random
import warnings
from fractions import Fraction as F
from pathlib import Path

import pytest

flint = pytest.importorskip("flint")

from flint import acb, arb, fmpq  # noqa: E402

from telperion import arb_dh  # noqa: E402
from telperion.arb_winding import (  # noqa: E402
    METHOD, _frac_interval, count_strips, from_series, localise_zero, rigorous_winding,
)

_DH_ZEROS = Path(__file__).resolve().parents[1] / "examples/quasicrystal/zoo_data/dh_zeros.json"


def _q(x):
    x = F(x)
    return arb(fmpq(x.numerator, x.denominator))


def _poly(roots):
    """prod (s - r) over acb_series, exact rational roots."""
    def f(s):
        out = None
        for (rr, ri) in roots:
            t = s - acb(_q(rr), _q(ri))
            out = t if out is None else out * t
        return out
    return f


def _exact_eval(roots):
    """Exact zero-width evaluation of prod (z - r): the most favourable input node sampling can get."""
    def ev(x, y, prec=128):
        x, y = F(x), F(y)
        vr, vi = F(1), F(0)
        for (rr, ri) in roots:
            ar, ai = x - rr, y - ri
            vr, vi = vr * ar - vi * ai, vr * ai + vi * ar
        return vr, vr, vi, vi
    return ev


def _true_count(roots, box):
    re0, re1, im0, im1 = box
    return sum(1 for (r, i) in roots if re0 < r < re1 and im0 < i < im1)


# Audit counterexample C: a zero pair at x = 1/7 (never a dyadic node), ~1e-9 above the bottom edge.
_C = [(F(1, 7), F(1, 10**9)), (F(1, 7) + F(1, 10**10), F(2, 10**9))]
_UNIT = (F(0), F(1), F(0), F(1))


def test_counterexample_c_rigorous_gives_two():
    assert rigorous_winding(_poly(_C), *_UNIT, prec=128) == 2


@pytest.mark.parametrize("nps", [24, 48, 96, 192])
def test_counterexample_c_heuristic_returns_one(monkeypatch, nps):
    """DOCUMENTS THE FLAW: node sampling returns 1 for a box holding 2 zeros, at every density, and does
    not raise.  If this ever starts failing, the heuristic changed; it is still not a rigorous method."""
    monkeypatch.setattr(arb_dh, "dh_eval", _exact_eval(_C))
    assert arb_dh.winding_number_sampled_heuristic(*_UNIT, prec=128, n_per_side=nps) == 1


def test_case_b_three_zeros():
    x = F(25, 48)
    roots = [(x, F(1, 10**6)), (x + F(1, 10**7), F(2, 10**6)), (F(1, 2), F(1, 2))]
    assert rigorous_winding(_poly(roots), *_UNIT, prec=128) == 3


def test_fuzz_near_edge_clusters_never_wrong():
    random.seed(20261014)
    for _ in range(25):
        roots = []
        for _ in range(random.randint(1, 3)):
            side = random.randint(0, 3)
            u = F(random.randint(1, 10**6 - 1), 10**6)
            d = F(random.choice([-1, 1]) * random.randint(1, 1000), 10**random.randint(4, 7))
            base = {0: (u, d), 1: (1 + d, u), 2: (u, 1 + d), 3: (d, u)}[side]
            for j in range(random.randint(1, 3)):
                off = F(j, 10**random.randint(5, 8))
                roots.append((base[0] + off, base[1] + off / 3))
        try:
            w = rigorous_winding(_poly(roots), *_UNIT, prec=128, max_depth=60)
        except RuntimeError:
            continue  # a refusal is allowed; a wrong integer is not
        assert w == _true_count(roots, _UNIT)


def test_zero_on_contour_refused():
    with pytest.raises(RuntimeError):
        rigorous_winding(_poly([(F(1, 3), F(0))]), *_UNIT, prec=128, max_depth=30)


def test_inverted_box_refused():
    with pytest.raises(ValueError):
        rigorous_winding(_poly([(F(1, 2), F(1, 2))]), 1, 0, 0, 1)


def test_pole_guard():
    """winding = zeros - poles, so a box containing a declared pole is refused.  zeta has no zero in
    [1/2, 2] x [-1, 1] and a simple pole at s = 1: undeclared, the count would come out -1."""
    def zeta(s):
        return s.zeta()
    assert rigorous_winding(zeta, "1/2", 2, -1, 1, prec=96) == -1          # what the guard prevents
    z = from_series(zeta, name="zeta", poles=[(1, 0)])
    with pytest.raises(ValueError, match="pole"):
        rigorous_winding(z, "1/2", 2, -1, 1, prec=96)
    with pytest.raises(ValueError, match="pole"):                           # pole on the closed edge
        rigorous_winding(z, 1, 2, -1, 1, prec=96)
    assert rigorous_winding(z, "1/2", 2, 1, 2, prec=96) == 0                # pole outside: fine


def test_localise_zero_shrinks_to_width():
    roots = [(F(3, 10), F(7, 10))]
    box = localise_zero(_poly(roots), 0, 1, 0, 1, width=F(1, 100), prec=96)
    assert box[0] < roots[0][0] < box[1] and box[2] < roots[0][1] < box[3]
    assert max(box[1] - box[0], box[3] - box[2]) <= F(1, 100)


def test_dh_series_matches_ctypes_dh_eval():
    v = arb_dh.dh_analytic().point(acb(_q("4/5"), _q("857/10")), 128)
    a = (*_frac_interval(v.real), *_frac_interval(v.imag))
    b = arb_dh.dh_eval("4/5", "857/10", 128)
    assert a[0] <= b[1] and b[0] <= a[1] and a[2] <= b[3] and b[2] <= a[3]


def test_dh_eval_refuses_oversized_rational():
    with pytest.raises(ValueError):
        arb_dh.dh_eval(F(2**70 + 1, 2**70), 10)


def test_deprecated_alias_warns_and_is_rigorous(monkeypatch):
    monkeypatch.setattr(arb_dh, "dh_series", _poly(_C))
    with warnings.catch_warnings(record=True) as rec:
        warnings.simplefilter("always")
        assert arb_dh.winding_number(*_UNIT, prec=96, n_per_side=8) == 2
    assert any(issubclass(r.category, DeprecationWarning) for r in rec)


def test_dh_crown_box_certified():
    """QC_DH_SCOUT section 4, cited by examples/wall_barrier/lean/FEUniformBarrierAM.lean."""
    c = arb_dh.certify_offline_zero("79/100", "83/100", "8568/100", "8572/100")
    assert c["winding"] == 1 and c["side"] == "right" and c["method"] == METHOD


def test_dh_fifth_offline_zero_certified():
    """The off-line zero near 0.8698 + 240.405i that the literature-seeded inventory missed (audit 4)."""
    c = arb_dh.certify_offline_zero("35610821/40960000", "1782031077/2048000000",
                                    "19693950062217/81920000000", "2461750006093/10240000000")
    assert c["winding"] == 1


def test_dh_dominant_term_right_halfplane():
    assert arb_dh.dh_right_halfplane_nonvanishing(2)["certified"]


def test_dh_completeness_to_300():
    """Rigorous total over [-1, 2] x [1/20, 300] is 214 = 204 on-line + 2 * 5 off-line (each off-line
    zero rho has the partner 1 - conj(rho) in the left half).  Re >= 2 is zero-free by the dominant term
    and Re <= -1 by the functional equation, so this box holds every zero with 1/20 <= Im <= 300."""
    r = count_strips(arb_dh.dh_analytic(), -1, 2, F(1, 20), 300, cuts=[10 * k for k in range(1, 30)], prec=96)
    assert r["total"] == 214

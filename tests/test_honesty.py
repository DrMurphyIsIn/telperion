"""Honesty-engine tests: tie pinning, anchors, hunt (3 modes), relaxation probe."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    GridSpec,
    InequalityFamily,
    certify,
)
from telperion.hunt import hunt_diverse, hunt_evolve, hunt_minimum  # noqa: E402
from telperion.relax import relax_probe  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)


def _fam(target, ties=None, anchors=None):
    return InequalityFamily(
        name="H",
        symbols=(u, v),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "H_a1",
        target=target,
        ties=ties,
        anchors=anchors,
    )


# ---- tie pinning ------------------------------------------------------------
def test_correct_boundary_tie_passes():
    cf = certify(
        _fam(lambda pt: u * v / (1 + u), ties=lambda pt: [{u: sp.Integer(0)}])
    )
    assert cf.checks_passed >= 3  # certificate + tie tightness + tie exactness


def test_wrong_tie_declaration_refused():
    with pytest.raises(CertificationError, match="not tight"):
        certify(
            _fam(lambda pt: (1 + u * v) / (1 + u), ties=lambda pt: [{u: sp.Integer(0)}])
        )


def test_overclaiming_certificate_refused():
    # target vanishes at the tie, but the (interior) tie cannot be achieved by
    # any nonneg-coefficient certificate except zero — certification of a
    # nonzero family must flag the slack rather than silently overclaim.
    fam = InequalityFamily(
        name="HO",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "HO_a1",
        # (u-1)^2*u^2... polya-certifiable spelling that is NOT tight at u=2:
        target=lambda pt: (1 + u) / (2 + u),
        ties=lambda pt: [{u: sp.Integer(2)}],
    )
    with pytest.raises(CertificationError, match="not tight"):
        certify(fam)


def test_anchor_pass_and_mismatch():
    ok = _fam(
        lambda pt: (1 + u * v) / (1 + u),
        anchors=lambda pt: [({u: sp.Integer(1), v: sp.Integer(3)}, sp.Integer(2))],
    )
    assert certify(ok).checks_passed >= 2
    bad = _fam(
        lambda pt: (1 + u * v) / (1 + u),
        anchors=lambda pt: [({u: sp.Integer(1), v: sp.Integer(3)}, sp.Integer(7))],
    )
    with pytest.raises(CertificationError, match="anchor mismatch"):
        certify(bad)


# ---- hunt -------------------------------------------------------------------
def test_hunt_descent_finds_exact_disproof():
    res = hunt_minimum((u - 1) ** 2 + (v - 2) ** 2 - sp.Rational(1, 64), (u, v))
    assert res.is_disproof
    assert res.minimum == sp.Rational(-1, 64)
    assert res.argmin == {"u": 1, "v": 2}


def test_hunt_evolve_handles_multimodal():
    f = (u - 1) ** 2 * (u - 16) ** 2 / 256 + v**2
    res = hunt_evolve(f, (u, v), seed=1)
    assert res.minimum == 0
    assert res.argmin["u"] in (1, 16)


def test_hunt_diverse_finds_both_ties():
    f = (u - 1) ** 2 * (u - 16) ** 2 / 256 + v**2
    results = hunt_diverse(f, (u, v), iters=600, seed=1, top=4)
    exact_ties = {r.argmin["u"] for r in results if r.minimum == 0}
    assert {1, 16} <= exact_ties  # BOTH basins — the pure minimizer finds one


def test_hunt_respects_box():
    res = hunt_minimum(u - 5, (u,), hi={u: sp.Integer(3)})
    assert res.minimum == -5 and res.argmin["u"] == 0


# ---- relaxation probe -------------------------------------------------------
def test_relax_detects_arithmetic_family():
    # (K-1)(K-2) >= 0 for every integer K, false at K = 3/2
    fam = InequalityFamily(
        name="R",
        symbols=(),
        grid=GridSpec([("K", [1, 2, 3])]),
        lean_name=lambda pt: f"R_K{pt['K']}",
        target=lambda pt: (pt["K"] - 1) * (pt["K"] - 2),
    )
    verdict = relax_probe(fam, "K", iters=150)
    assert verdict.verdict == "ARITHMETIC"
    assert verdict.witness_value < 0
    assert 1 < verdict.witness["K"] < 2


def test_relax_smooth_family():
    fam = InequalityFamily(
        name="RS",
        symbols=(u,),
        grid=GridSpec([("K", [1, 2, 3])]),
        lean_name=lambda pt: f"RS_K{pt['K']}",
        target=lambda pt: (pt["K"] + u) / (pt["K"] + 1),
    )
    verdict = relax_probe(fam, "K", iters=100)
    assert verdict.verdict == "SMOOTH_SO_FAR"
    assert verdict.segments_checked == 2

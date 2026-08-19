"""BG-derived first-class emitters (2026-08-19): pipeline + negative controls.

Each shape flows through the single enforced certify->validate->emit->freeze
API.  For each: a positive family certifies and emits soundness-lint-clean Lean,
and an out-of-class family is REFUSED at certification (the negative control) —
no Lean is produced for a non-member.  The Lean kernel verdict is CI-only.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, ValidationReport,
    certify, check_lean_text, emit,
)
from telperion import (  # noqa: E402
    ConeFarkasEmitter, InterlacingEmitter, LatticeBoxEmitter,
    LogConcaveSinglePointEmitter, TelescopingPotentialEmitter,
    UnimodalMaxEmitter, UNIMODAL_PRELUDE, TELESCOPE_PRELUDE,
    cone_family, interlacing_family, lattice_box_family, logconcave_family,
    telescope_family, unimodal_max_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam, emitter, prelude=""):
    """certify -> emit -> assert the soundness lint is clean; return the body."""
    res = emit(certify(fam), LeanProfile(namespace=("T",), prelude=prelude),
               [emitter], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    return res, body


# --- cone / Farkas ----------------------------------------------------------

def test_cone_positive_and_refusal():
    x, y = sp.symbols("x y")
    fam = cone_family("Cone", (x, y), GridSpec([("c", [2, 3])]),
                      lambda pt: f"cone_{pt['c']}",
                      lambda pt: (sp.expand(pt["c"] * (x - y) ** 2 + 3 * y ** 2),
                                  [(x - y) ** 2, y ** 2]))
    res, body = _emit_clean(fam, ConeFarkasEmitter())
    assert res.n_theorems == 2 and "positivity" in body
    # x is not a nonnegative combination of squares
    bad = cone_family("Bad", (x, y), GridSpec([("c", [1])]), lambda pt: "bad",
                      lambda pt: (x, [(x - y) ** 2, y ** 2]))
    with pytest.raises(CertificationError):
        certify(bad)


# --- unimodal integer maximum ----------------------------------------------

def test_unimodal_positive_and_refusal():
    s = sp.Symbol("s", nonnegative=True)
    fam = unimodal_max_family("Uni", GridSpec([("j", [0])]), lambda pt: "uni",
                              lambda pt: ((10 - s) / (s + 1), 0, s))
    res, body = _emit_clean(fam, UnimodalMaxEmitter(), prelude=UNIMODAL_PRELUDE)
    assert "_cross_hi" in body and "positivity" in body
    # a strictly-increasing ratio never crosses 1 -> refused
    bad = unimodal_max_family("Bad", GridSpec([("j", [0])]), lambda pt: "bad",
                              lambda pt: ((s + 3) / (s + 1), 0, s))
    with pytest.raises(CertificationError):
        certify(bad)


def test_unimodal_prelude_lemma_present():
    assert "theorem unimodal_peak" in UNIMODAL_PRELUDE
    check_lean_text("/- telperion -/\n" + UNIMODAL_PRELUDE)  # no sorry/axiom/stub


# --- telescoping potential --------------------------------------------------

def test_telescope_positive_and_refusal():
    u = sp.Symbol("u", nonnegative=True)
    fam = telescope_family("Tele", (u,), GridSpec([("c", [1, 2])]),
                           lambda pt: f"tele_{pt['c']}",
                           lambda pt: ((pt["c"] * u ** 2 + u + 1, u ** 2 + 3), (u,)))
    res, body = _emit_clean(fam, TelescopingPotentialEmitter(), prelude=TELESCOPE_PRELUDE)
    assert res.n_theorems == 4 and "positivity" in body
    # a negative margin is not a super-solution -> refused
    bad = telescope_family("Bad", (u,), GridSpec([("c", [1])]), lambda pt: "bad",
                           lambda pt: ((u - 5,), (u,)))
    with pytest.raises(CertificationError):
        certify(bad)


def test_telescope_prelude_lemma_present():
    assert "theorem RTree.telescope" in TELESCOPE_PRELUDE
    check_lean_text("/- telperion -/\n" + TELESCOPE_PRELUDE)


# --- lattice box (d-dim integer Positivstellensatz) -------------------------

def test_lattice_box_positive_and_refusal():
    k = sp.Symbol("k")
    # f(k) = 100 - k^2 on k >= 0: base box [0,0] holds (f(0)=100 <= 100) and the
    # tail f(k)-f(k+1) = 2k+1 >= 0 (nonincreasing) -> f(k) <= 100 for all k.
    fam = lattice_box_family("Lat", (k,), GridSpec([("j", [0])]), lambda pt: "lat",
                             lambda pt: (100 - k ** 2, 100, (0,), (2 * k + 1,)))
    _res, body = _emit_clean(fam, LatticeBoxEmitter())
    assert "norm_num" in body or "positivity" in body
    # base-box violation: f(k)=k, bound 5, but f(6)=6 > 5
    bad = lattice_box_family("Bad", (k,), GridSpec([("j", [0])]), lambda pt: "bad",
                             lambda pt: (k, 5, (10,), (sp.Integer(-1),)))
    with pytest.raises(CertificationError):
        certify(bad)


# --- log-concave single point ----------------------------------------------

def test_logconcave_positive_and_refusal():
    k = sp.Symbol("k", positive=True)
    fam = logconcave_family("LC", (k,), GridSpec([("j", [0])]), lambda pt: "lc",
                            lambda pt: ((k + 1) / (k + 2), 1, k))
    _res, body = _emit_clean(fam, LogConcaveSinglePointEmitter())
    assert "norm_num" in body
    # 1/(k+1) is NOT log-concave (F(k+1)F(k-1) > F(k)^2) -> refused
    bad = logconcave_family("Bad", (k,), GridSpec([("j", [0])]), lambda pt: "bad",
                            lambda pt: (1 / (k + 1), 1, k))
    with pytest.raises(CertificationError):
        certify(bad)


# --- interlacing / real-rootedness -----------------------------------------

def test_interlacing_positive_and_refusal():
    x = sp.Symbol("x")
    # (x+1)^4 -> coefficients [1,4,6,4,1], real-rooted, Newton-log-concave
    fam = interlacing_family("Int", (x,), GridSpec([("j", [0])]), lambda pt: "int",
                             lambda pt: ((1, 4, 6, 4, 1), x))
    _res, body = _emit_clean(fam, InterlacingEmitter())
    assert "norm_num" in body
    # x^2 + 1 is not real-rooted -> refused
    bad = interlacing_family("Bad", (x,), GridSpec([("j", [0])]), lambda pt: "bad",
                             lambda pt: ((1, 0, 1), x))
    with pytest.raises(CertificationError):
        certify(bad)


# --- byte-stability (the drift-net guarantee) -------------------------------

def test_bg_emitter_byte_stability():
    x, y = sp.symbols("x y")
    def build():
        fam = cone_family("Cone", (x, y), GridSpec([("c", [2, 3])]),
                          lambda pt: f"cone_{pt['c']}",
                          lambda pt: (sp.expand(pt["c"] * (x - y) ** 2 + 3 * y ** 2),
                                      [(x - y) ** 2, y ** 2]))
        return emit(certify(fam), LeanProfile(namespace=("T",)),
                    [ConeFarkasEmitter()], GREEN)
    assert build().input_hash == build().input_hash

"""SOS-Positivstellensatz-refutation SDP finder (`sdp_finder.find_sos_refutation`).

Upgrades `SOSRefutationEmitter` from checker to searcher: supply the system, and
Telperion searches the SOS multipliers σ and free multipliers λ that refute it
over ℝ (via an SDP, cvxpy), rationalizes exactly, and verifies.  The finder is
untrusted — the certifier re-verifies — so a search that does not rationalize is
a refusal, never a wrong theorem.  (The Putinar finder lives in `sos_sdp` with
its own tests.)

Needs cvxpy (skipped where absent, e.g. the sympy-only CI cells); the frozen
example Lean is compile-gated regardless.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

pytest.importorskip("cvxpy")

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, SOSRefutationEmitter, ValidationReport, certify,
    check_lean_text, emit, find_sos_refutation, sos_refutation_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def test_find_sos_refutation_closes_real_gap():
    x, y = sp.symbols("x y")
    # x^2 + 1 = 0 is ℝ-infeasible only by positivity -> the finder must discover
    # an SOS σ0 (here x^2) and a free multiplier λ.
    r = find_sos_refutation([], [x ** 2 + 1], (x, y), half_deg=1)
    assert r is not None
    s0, sig, lam = r
    recon = (sum(c * b ** 2 for c, b in s0)
             + sum(g * sum(c * b ** 2 for c, b in st) for g, st in sig)
             + sum(h * l for h, l in lam))
    assert sp.expand(recon + 1) == 0  # equals -1


def test_sos_refutation_finder_mode_certifies_and_emits():
    x = sp.Symbol("x")
    fam = sos_refutation_family("SF", (x,), GridSpec([("j", [0])]), lambda pt: "sf",
                                lambda pt: (None, [], [(x ** 2 + 1, "he1")]))
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [SOSRefutationEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "False" in body and "linarith" in body


def test_sos_refutation_finder_refuses_satisfiable():
    x, y = sp.symbols("x y")
    # x - y = 0 alone is satisfiable -> no refutation
    assert find_sos_refutation([], [x - y], (x, y), half_deg=1) is None

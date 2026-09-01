"""Putinar certificate FINDER — upgrading the constrained-SOS emitter from
checker to searcher.

`find_putinar_certificate` searches (numeric SDP -> EXACT rational rounding) for
SOS multipliers `sigma_0, sigma_i` with `p = sigma_0 + Sum sigma_i g_i` on the
constraint set `{g_i >= 0}`; the emitter uses it whenever a family returns
``sigma0 = None`` / ``constraints`` with ``sigma_i = None``.  The finder is
untrusted — every result is re-verified EXACTLY by `certify_putinar_point`
before any Lean is emitted — so these tests cover that it FINDS real
certificates, is DETERMINISTIC (byte-stable output), re-verifies exactly over
Q, and REFUSES (cleanly) when it cannot.  Skipped without cvxpy.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

pytest.importorskip("cvxpy")

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, ConstrainedSOSEmitter, GridSpec, LeanProfile,
    ValidationReport, certify, check_lean_text, emit, putinar_family,
)
from telperion.sos_sdp import find_putinar_certificate  # noqa: E402

GREEN = ValidationReport(checks=(("spot", True),))


def _recon(sigma0, constraints, syms):
    """sigma_0 + Sum sigma_i * g_i from finder-shaped (coef, base) term lists."""
    def sos(terms):
        return sum((sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in terms),
                   sp.Integer(0))
    acc = sos(sigma0)
    for g, sigma_i, _hyp in constraints:
        acc += sp.sympify(g) * sos(sigma_i)
    return sp.expand(acc)


def test_finder_finds_box_instance():
    # p = 2 - x^2 - y^2 >= 0 on the box [-1,1]^2 (a genuine Putinar instance:
    # nonnegative there but NOT globally — needs the constraints).
    x, y = sp.symbols("x y")
    p = 2 - x ** 2 - y ** 2
    gens = [(1 - x, "a"), (1 + x, "b"), (1 - y, "c"), (1 + y, "d")]
    res = find_putinar_certificate(p, gens, (x, y), half_deg=2)
    assert res is not None
    sigma0, constraints = res
    # EXACT reconstruction over Q — no floats survive into the certificate.
    assert _recon(sigma0, constraints, (x, y)) == sp.expand(p)
    # every multiplier coefficient a nonnegative rational
    for _g, sigma_i, _hyp in constraints:
        for c, _b in sigma_i:
            assert sp.nsimplify(c).is_rational and sp.nsimplify(c) >= 0


def test_finder_finds_interval_instance():
    # p = x^3 + x >= 0 on {x >= 0}: classic single-constraint Putinar.
    x = sp.Symbol("x")
    p = x ** 3 + x
    res = find_putinar_certificate(p, [(x, "hx")], (x,), half_deg=2)
    assert res is not None
    sigma0, constraints = res
    assert _recon(sigma0, constraints, (x,)) == sp.expand(p)


def test_finder_is_deterministic():
    x, y = sp.symbols("x y")
    p = 2 - x ** 2 - y ** 2
    gens = [(1 - x, "a"), (1 + x, "b"), (1 - y, "c"), (1 + y, "d")]
    a = find_putinar_certificate(p, gens, (x, y), half_deg=2)
    b = find_putinar_certificate(p, gens, (x, y), half_deg=2)
    assert a == b  # byte-stability of frozen output depends on this


def test_finder_refuses_negative_target():
    # p = x - 2 is NEGATIVE on {x >= 0} (at x=0): no Putinar certificate exists.
    x = sp.Symbol("x")
    assert find_putinar_certificate(x - 2, [(x, "hx")], (x,), half_deg=2) is None


def test_finder_mode_certifies_and_emits():
    # spec returns sigma0=None with sigma_i=None constraints -> Telperion finds
    # the multipliers, certifies EXACTLY, then emits.
    x, y = sp.symbols("x y")

    def spec(pt):
        p = 2 - x ** 2 - y ** 2
        constraints = [(1 - x, None, "a"), (1 + x, None, "b"),
                       (1 - y, None, "c"), (1 + y, None, "d")]
        return (p, None, constraints)

    fam = putinar_family("F", (x, y), GridSpec([("j", [0])]),
                         lambda pt: "putinar_found", spec,
                         constants={"putinar_half_deg": 2})
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [ConstrainedSOSEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "positivity" in body


def test_finder_mode_refuses_when_no_certificate():
    x = sp.Symbol("x")

    def spec(pt):
        return (x - 2, None, [(x, None, "hx")])

    fam = putinar_family("B", (x,), GridSpec([("j", [0])]),
                         lambda pt: "putinar_none", spec)
    with pytest.raises(CertificationError):
        certify(fam)


def test_finder_result_re_verifies_exactly():
    # The finder's own output must pass the EXISTING exact certifier unchanged
    # (the honesty contract: the finder is untrusted, the certifier is the gate).
    x, y = sp.symbols("x y")
    p = 2 - x ** 2 - y ** 2
    gens = [(1 - x, "a"), (1 + x, "b"), (1 - y, "c"), (1 + y, "d")]
    res = find_putinar_certificate(p, gens, (x, y), half_deg=2)
    assert res is not None
    sigma0, constraints = res

    from telperion.emit_constrained_sos import certify_putinar_point
    from telperion.family import InequalityFamily

    def spec(pt):
        return (p, sigma0, constraints)

    fam = InequalityFamily(
        name="V", symbols=(x, y), grid=GridSpec([("j", [0])]),
        lean_name=lambda pt: "v", special=("putinar", spec),
    )
    inst, checks = certify_putinar_point(fam, {"j": 0}, "v")
    assert checks >= 1  # exact identity + per-coefficient checks all passed


# --------------------------------------------------------------------------- #
# EQUALITY-constrained Positivstellensatz: p = σ_0 + Σ σ_i g_i + Σ λ_j h_j     #
# with FREE (arbitrary-sign) λ_j — certifies nonnegativity on the recursion-   #
# constrained (reachable) VARIETY {h_j = 0}, not the free box.                 #
# --------------------------------------------------------------------------- #

def test_finder_finds_equality_certificate():
    # p = x*y is NEGATIVE off the variety {x - y = 0} (e.g. x=1,y=-1 -> -1), so
    # NO free-box SOS/Putinar certificate exists; on the variety it equals
    # x^2 >= 0.  The finder must use the FREE equality multiplier λ·(x-y).
    x, y = sp.symbols("x y")
    p = x * y
    res = find_putinar_certificate(p, constraints=[], syms=(x, y),
                                   equalities=[(x - y, "heq")])
    assert res is not None
    sigma0, constraints, equalities = res
    # exact reconstruction over Q, INCLUDING the free multiplier term
    recon = sum((sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in sigma0),
                sp.Integer(0))
    for h, lam, _hyp in equalities:
        recon += sp.sympify(lam) * sp.sympify(h)
    assert sp.expand(recon - p) == 0
    # σ_0 coefficients still nonnegative (it is a genuine SOS); the certificate
    # is impossible without the equality (p < 0 somewhere off the variety)
    for c, _b in sigma0:
        assert sp.nsimplify(c) >= 0
    assert sp.expand(p.subs({x: 1, y: -1})) < 0


def test_equality_finder_mode_certifies_and_emits():
    # Full path: spec returns a 4-tuple with equalities; Telperion finds the
    # certificate, re-verifies EXACTLY, and emits Lean that discharges the
    # equality hypothesis (λ·h = 0 by rw) and closes by linarith.
    x, y = sp.symbols("x y")

    def spec(pt):
        return (x * y, None, [], [(x - y, None, "heq")])

    fam = putinar_family("E", (x, y), GridSpec([("j", [0])]),
                         lambda pt: "putinar_eq_found", spec,
                         constants={"putinar_half_deg": 1})
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [ConstrainedSOSEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1
    assert "x - y = 0 →" in body           # the equality became a hypothesis
    assert "rw [heq]" in body              # the free multiplier is zeroed on it
    assert "linarith" in body


def test_equality_certificate_reconstruction_is_gated():
    # A WRONG equality multiplier must be REFUSED by the exact certifier (the
    # honesty contract holds for the ideal part too).
    from telperion.emit_constrained_sos import certify_putinar_point
    from telperion.family import InequalityFamily
    x, y = sp.symbols("x y")

    def spec(pt):
        # claim x*y = (x)^2 + (WRONG λ = 0)*(x - y) — does NOT reconstruct
        return (x * y, [(sp.Integer(1), x)], [], [(x - y, sp.Integer(0), "heq")])

    fam = InequalityFamily(
        name="W", symbols=(x, y), grid=GridSpec([("j", [0])]),
        lean_name=lambda pt: "w", special=("putinar", spec),
    )
    with pytest.raises(ValueError):
        certify_putinar_point(fam, {"j": 0}, "w")

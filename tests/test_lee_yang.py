"""LeeYangStablePair emitter tests (offline, self-contained).

The global certify()/emit() dispatch is NOT wired for kind ``lee_yang_stable_pair``
(the parent session owns the registry wiring), so these tests drive the emitter
DIRECTLY: build the certificate, construct a CertifiedFamily under certify.py's
construction guard, and call ``LeeYangStablePairEmitter().emit_body`` — then lint
the emitted Lean text.

Shape: Schur–Cohn stability of a concrete rational-coefficient polynomial (the
finite-checkable core of the Kurasov–Sarnak Fourier-quasicrystal zeros-on-a-line
analogue).  The builder REFUSES any degenerate / borderline / verdict-mismatched
config (honest refusal); the emitted theorem is a true, non-vacuous, norm_num-
decidable rational Jury-chain positivity, recomputed from the coefficient
literals.  It is NOT a statement about ζ's RH.  conjecture1_proved = False.

Every "expected" stability verdict below is cross-checked numerically inside the
test via sympy nroots (the same cross-check the builder performs).
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import (  # noqa: E402
    CertifiedFamily,
    _construction_guard,
)
from telperion.emit_lee_yang import (  # noqa: E402
    LeeYangStablePairEmitter,
    certify_lee_yang_stable_pair_point,
    lee_yang_stable_pair_certificate,
    lee_yang_stable_pair_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _refused(**kw) -> bool:
    try:
        lee_yang_stable_pair_certificate(**kw)
        return False
    except ValueError:
        return True


def _numeric_moduli(coeffs):
    """The actual |root| of p(z) = Σ coeffs[i] zⁱ (ascending), for in-test
    cross-checking the expected stability verdict independently of the builder."""
    z = sp.Symbol("z")
    poly = sp.Poly(sum(sp.Rational(c) * z**i for i, c in enumerate(coeffs)), z)
    return [complex(r) for r in poly.nroots(maxsteps=200)]


# --------------------------------------------------------------------------- #
# 1. builder: accepts valid stable configs, refuses each bad case             #
# --------------------------------------------------------------------------- #


def test_accepts_inside_stable_quadratic():
    # p(z) = z² − z/4 + 1/8, ascending [1/8, −1/4, 1].
    coeffs = [sp.Rational(1, 8), sp.Rational(-1, 4), 1]
    mods = [abs(r) for r in _numeric_moduli(coeffs)]
    assert all(m < 1 for m in mods), mods  # verify inside-stability numerically first
    cert = lee_yang_stable_pair_certificate(coeffs, "inside")
    assert cert.mode == "inside"
    assert all(t > 0 for t in cert.tests)
    assert len(cert.tests) == 2  # degree 2 → two reduction levels
    assert cert.tests == (sp.Rational(63, 64), sp.Rational(3773, 4096))


def test_accepts_outside_stable_linear():
    # p(z) = z − 2, ascending [−2, 1]; single root at 2 (outside the closed disk).
    coeffs = [-2, 1]
    mods = [abs(r) for r in _numeric_moduli(coeffs)]
    assert all(m > 1 for m in mods), mods  # verify outside-stability numerically
    cert = lee_yang_stable_pair_certificate(coeffs, "outside")
    assert cert.mode == "outside"
    assert all(t > 0 for t in cert.tests)
    # tested polynomial is the reciprocal [1, −2]; test quantity (−2)² − 1² = 3.
    assert cert.tests == (sp.Integer(3),)


def test_refuses_borderline_root_on_circle():
    # p(z) = z − 1: root exactly on the unit circle → borderline, refuse.
    mods = [abs(r) for r in _numeric_moduli([-1, 1])]
    assert any(abs(m - 1) < 1e-9 for m in mods), mods
    assert _refused(coeffs=[-1, 1], mode="inside")
    assert _refused(coeffs=[-1, 1], mode="outside")


def test_refuses_outside_verdict_mismatch():
    # p(z) = z − 1/2: root at 1/2 (INSIDE closed disk) → 'outside' verdict false.
    mods = [abs(r) for r in _numeric_moduli([sp.Rational(-1, 2), 1])]
    assert all(m < 1 for m in mods), mods
    assert _refused(coeffs=[sp.Rational(-1, 2), 1], mode="outside")
    # …but it IS accepted in 'inside' mode (root inside the open disk).
    cert = lee_yang_stable_pair_certificate([sp.Rational(-1, 2), 1], "inside")
    assert all(t > 0 for t in cert.tests)


def test_refuses_inside_verdict_mismatch():
    # p(z) = z − 2 in 'inside' mode: root at 2 is OUTSIDE → verdict mismatch.
    assert _refused(coeffs=[-2, 1], mode="inside")


def test_refuses_degree_cap():
    # degree 13 > 12 expression-size cap.
    assert _refused(coeffs=[1] * 14, mode="inside")


def test_refuses_bad_mode_degree_zero_and_zero_leading():
    assert _refused(coeffs=[sp.Rational(1, 8), sp.Rational(-1, 4), 1], mode="lee_yang")
    assert _refused(coeffs=[1], mode="inside")          # degree 0 (constant)
    assert _refused(coeffs=[1, 2, 0], mode="inside")    # aₙ = 0 (inexact degree)
    assert _refused(coeffs=[0, 1], mode="outside")      # a₀ = 0 → root at 0, inside


def test_refuses_non_rational_coefficient():
    assert _refused(coeffs=[sp.sqrt(2), 1], mode="inside")


# --------------------------------------------------------------------------- #
# 2. emit the theorem directly and lint it                                    #
# --------------------------------------------------------------------------- #


def _build_certified_family(fam, pts):
    """Certify the given points via the arm's point function and wrap them in a
    CertifiedFamily under certify.py's construction guard (the global dispatch
    is not wired for this kind)."""
    instances = []
    checks = 0
    for pt in pts:
        inst, n = certify_lee_yang_stable_pair_point(fam, pt, fam.lean_name(pt))
        instances.append(inst)
        checks += n
    _construction_guard.open = True
    try:
        return CertifiedFamily(
            family=fam, instances=tuple(instances), checks_passed=checks)
    finally:
        _construction_guard.open = False


def _emit_text(fam, pts):
    cf = _build_certified_family(fam, pts)
    text, n = LeeYangStablePairEmitter().emit_body(cf, LeanProfile(namespace=("LY",)))
    return text, n


def test_emit_inside_jury_chain_lints_and_is_deterministic():
    fam = lee_yang_stable_pair_family(
        "LY", GridSpec([("_", [0])]), lambda pt: "lee_yang_inside",
        spec=lambda pt: [sp.Rational(1, 8), sp.Rational(-1, 4), 1])
    pts = list(fam.grid.points())
    text, n = _emit_text(fam, pts)
    assert n == 1
    assert "theorem lee_yang_inside_jury" in text
    # the Jury chain: strict positivity conjuncts closed by norm_num
    assert "> 0" in text
    assert "∧" in text          # multi-level chain (degree 2 → two conjuncts)
    assert "norm_num" in text
    assert "^2" in text         # test quantities are (lead)^2 − (const)^2
    # honesty seam present in the emitted comment
    assert "conjecture1_proved = False" in text
    assert "Kurasov" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic
    text2, _ = _emit_text(fam, pts)
    assert text2 == text


def test_emit_outside_mode_uses_reciprocal():
    fam = lee_yang_stable_pair_family(
        "LY2", GridSpec([("_", [0])]), lambda pt: "lee_yang_outside",
        spec=lambda pt: ([-2, 1], "outside"))
    pts = list(fam.grid.points())
    text, _ = _emit_text(fam, pts)
    assert "theorem lee_yang_outside_jury" in text
    assert "mode='outside'" in text
    assert "reciprocal" in text
    assert "> 0" in text
    assert "norm_num" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors

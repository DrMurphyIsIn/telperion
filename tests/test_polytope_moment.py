"""PolytopeMoment emitter tests (offline, self-contained).

The global certify()/emit() dispatch is NOT wired for kind ``polytope_moment``
(the parent session owns the registry wiring), so these tests drive the emitter
DIRECTLY: build the certificate, construct a CertifiedFamily under certify.py's
construction guard, and call ``PolytopeMomentEmitter().emit_body`` — then lint
the emitted Lean text.

Shape: exact-rational simplex-moment certificate, identity (10.1) / Lemma 10.1 of
the Axiom Math bgp212 ("H1 ≤ 212") development.  The builder REFUSES any bad or
false configuration (honest refusal); the emitted theorem is a true, non-vacuous,
norm_num-decidable rational EQUALITY re-executing the closed form.  The integral
semantics + triangulation validity are the documented out-of-kernel seam.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import (  # noqa: E402
    CertifiedFamily,
    _construction_guard,
)
from telperion.emit_polytope_moment import (  # noqa: E402
    PolytopeMomentEmitter,
    certify_polytope_moment_point,
    polytope_moment_certificate,
    polytope_moment_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _refused(simplices, total) -> bool:
    try:
        polytope_moment_certificate(simplices, total)
        return False
    except ValueError:
        return True


# --------------------------------------------------------------------------- #
# 1. builder: accepts a valid instance, refuses each bad case                 #
# --------------------------------------------------------------------------- #


def test_accepts_single_monomial():
    # R=1, m=2, monomial z1*z2 (e=(1,1)): moment = 1^4 * (1!*1!) / 4! = 1/24.
    cert = polytope_moment_certificate(
        [(1, 2, [(1, (1, 1))])], sp.Rational(1, 24))
    assert cert.total == sp.Rational(1, 24)
    assert len(cert.pieces) == 1
    p = cert.pieces[0]
    assert p.value == sp.Rational(1, 24)
    assert p.R == sp.Integer(1)
    assert p.m == 2
    assert p.es == (1, 1)


def test_refuses_wrong_total():
    assert _refused([(1, 2, [(1, (1, 1))])], sp.Rational(1, 25))
    assert _refused([(1, 2, [(1, (1, 1))])], sp.Integer(0))


def test_refuses_nonpositive_scale():
    assert _refused([(0, 2, [(1, (1, 1))])], sp.Integer(0))
    assert _refused([(-1, 2, [(1, (1, 1))])], sp.Integer(0))


def test_refuses_bad_exponent():
    assert _refused([(1, 2, [(1, (-1, 1))])], sp.Integer(0))
    assert _refused([(1, 2, [(1, (sp.Rational(1, 2), 1))])], sp.Integer(0))


def test_refuses_bad_dimension_and_empty():
    assert _refused([(1, -1, [(1, (1, 1))])], sp.Integer(0))       # m<0
    assert _refused([(1, sp.Rational(3, 2), [(1, (1,))])], sp.Integer(0))  # m frac
    assert _refused([(1, 2, [])], sp.Integer(0))                   # empty pieces
    assert _refused([], sp.Integer(0))                             # empty simplices


def test_refuses_term_cap():
    # 401 monomial terms > _MAX_TERMS (400): must refuse regardless of total.
    pieces = [(sp.Integer(0), (0,)) for _ in range(401)]
    assert _refused([(1, 1, pieces)], sp.Integer(0))


# --------------------------------------------------------------------------- #
# 2. a multi-piece / multi-simplex instance sums correctly                    #
# --------------------------------------------------------------------------- #


def test_two_piece_sum():
    # Simplex A: R=1, m=2, z1*z2 -> 1/24.
    # Simplex B: R=1, m=1, constant 1 (e=()) -> 1^1 * (empty prod=1) / 1! = 1;
    #            coeff 2 -> 2.  Grand total 1/24 + 2 = 49/24.
    simplices = [
        (1, 2, [(1, (1, 1))]),
        (1, 1, [(2, ())]),
    ]
    total = sp.Rational(1, 24) + sp.Integer(2)
    cert = polytope_moment_certificate(simplices, total)
    assert cert.total == sp.Rational(49, 24)
    assert len(cert.pieces) == 2
    assert cert.pieces[0].value == sp.Rational(1, 24)
    assert cert.pieces[1].value == sp.Integer(2)


def test_scale_enters_as_power():
    # R=2, m=1, monomial z^2 (e=(2,)): moment = 2^(1+2) * 2! / 3! = 8*2/6 = 8/3.
    cert = polytope_moment_certificate(
        [(2, 1, [(1, (2,))])], sp.Rational(8, 3))
    assert cert.total == sp.Rational(8, 3)


# --------------------------------------------------------------------------- #
# 3. certify point + emit the theorem directly and lint it                    #
# --------------------------------------------------------------------------- #


def _build_certified_family(fam, pts):
    """Certify the given points via the arm's point function and wrap them in a
    CertifiedFamily under certify.py's construction guard (the global dispatch is
    not wired for this kind)."""
    instances = []
    checks = 0
    for pt in pts:
        inst, n = certify_polytope_moment_point(fam, pt, fam.lean_name(pt))
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
    text, n = PolytopeMomentEmitter().emit_body(cf, LeanProfile(namespace=("PM",)))
    return text, n


def test_certify_point_n_checks():
    fam = polytope_moment_family(
        "PM", GridSpec([("_", [0])]), lambda pt: "pm_inst",
        spec=lambda pt: ([(1, 2, [(1, (1, 1))]), (1, 1, [(2, ())])],
                         sp.Rational(49, 24)))
    pt = next(iter(fam.grid.points()))
    inst, n = certify_polytope_moment_point(fam, pt, "pm_inst")
    # 2 monomial terms + 1 total check
    assert n == 3
    assert inst.payload.total == sp.Rational(49, 24)


def test_emit_lint_clean_and_deterministic():
    fam = polytope_moment_family(
        "PM", GridSpec([("_", [0])]), lambda pt: "polytope_moment_inst",
        spec=lambda pt: ([(1, 2, [(1, (1, 1))])], sp.Rational(1, 24)))
    pts = list(fam.grid.points())
    text, n = _emit_text(fam, pts)
    assert n == 1
    assert "theorem polytope_moment_inst" in text
    assert "simplexMoment" in text
    assert "norm_num" in text
    # the claimed rational appears in the emitted equality
    assert "1 / 24" in text
    # the prelude closed form is emitted exactly once
    assert text.count("def simplexMoment") == 1
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic
    text2, _ = _emit_text(fam, pts)
    assert text2 == text


def test_emit_multi_piece_text():
    fam = polytope_moment_family(
        "PM2", GridSpec([("_", [0])]), lambda pt: "polytope_moment_multi",
        spec=lambda pt: ([(1, 2, [(1, (1, 1))]), (1, 1, [(2, ())])],
                         sp.Rational(49, 24)))
    pts = list(fam.grid.points())
    text, _ = _emit_text(fam, pts)
    assert "theorem polytope_moment_multi" in text
    assert "49 / 24" in text
    # two simplexMoment applications in the summed LHS
    assert text.count("simplexMoment") >= 3  # 1 in def + 2 in the sum
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors

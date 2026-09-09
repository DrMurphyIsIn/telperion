"""RayleighGram emitter tests (offline, self-contained).

The global certify()/emit() dispatch is NOT wired for kind ``rayleigh_gram``
(the parent session owns the registry wiring), so these tests drive the emitter
DIRECTLY: build the certificate, construct a CertifiedFamily under certify.py's
construction guard, and call ``RayleighGramEmitter().emit_body`` — then lint the
emitted Lean text.

Shape: concrete-instance shadow of Axiom Math bgp212 Thm 11.1's generalized-
eigenvalue bound ``cᵀJc − θ·cᵀIc > 0`` (and ``cᵀIc > 0``).  The builder REFUSES
any bad or false configuration (honest refusal); the emitted theorem is a true,
non-vacuous, norm_num-decidable rational statement about the concrete pencil,
NOT the variational lemma (the Gram semantics is the trust seam).
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import (  # noqa: E402
    CertifiedFamily,
    _construction_guard,
)
from telperion.emit_rayleigh_gram import (  # noqa: E402
    RayleighGramEmitter,
    certify_rayleigh_gram_point,
    rayleigh_gram_certificate,
    rayleigh_gram_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _refused(**kw) -> bool:
    try:
        rayleigh_gram_certificate(**kw)
        return False
    except ValueError:
        return True


# --------------------------------------------------------------------------- #
# 1. builder: accepts a valid pencil, refuses each bad case                   #
# --------------------------------------------------------------------------- #


def test_accepts_valid_instance():
    # J = diag(10,1), I = identity, c = (1,0), θ = 4:
    # cᵀJc = 10, cᵀIc = 1, gap = 10 − 4·1 = 6 > 0.
    cert = rayleigh_gram_certificate([[10, 0], [0, 1]], [[1, 0], [0, 1]], [1, 0], 4)
    assert cert.dim == 2
    assert cert.qJ == sp.Integer(10)
    assert cert.qI == sp.Integer(1)
    assert cert.theta == sp.Integer(4)
    assert cert.gap == sp.Integer(6)


def test_theta_defaults_to_four():
    cert = rayleigh_gram_certificate([[10, 0], [0, 1]], [[1, 0], [0, 1]], [1, 0])
    assert cert.theta == sp.Integer(4)
    assert cert.gap == sp.Integer(6)


def test_off_diagonal_and_rational_entries():
    # Symmetric J with off-diagonal coupling, rational vector.
    # J = [[2,1],[1,3]], I = id, c = (1/2, 1):
    # cᵀJc = 2·(1/4) + 2·1·(1/2)·1 + 3·1 = 1/2 + 1 + 3 = 9/2.
    # cᵀIc = 1/4 + 1 = 5/4.  gap = 9/2 − 4·(5/4) = 9/2 − 5 = -1/2 < 0 → REFUSE.
    assert _refused(J=[[2, 1], [1, 3]], I=[[1, 0], [0, 1]], c=[sp.Rational(1, 2), 1], theta=4)
    # Same J/I/c but θ small enough that the gap is positive: θ = 2.
    # gap = 9/2 − 2·(5/4) = 9/2 − 5/2 = 2 > 0.
    cert = rayleigh_gram_certificate(
        [[2, 1], [1, 3]], [[1, 0], [0, 1]], [sp.Rational(1, 2), 1], 2)
    assert cert.qJ == sp.Rational(9, 2)
    assert cert.qI == sp.Rational(5, 4)
    assert cert.gap == sp.Integer(2)


def test_refuses_asymmetric_matrix():
    assert _refused(J=[[1, 2], [3, 4]], I=[[1, 0], [0, 1]], c=[1, 1], theta=1)  # J asym
    assert _refused(J=[[1, 0], [0, 1]], I=[[1, 2], [3, 4]], c=[1, 1], theta=1)  # I asym


def test_refuses_nonpositive_theta():
    assert _refused(J=[[10, 0], [0, 1]], I=[[1, 0], [0, 1]], c=[1, 0], theta=0)
    assert _refused(J=[[10, 0], [0, 1]], I=[[1, 0], [0, 1]], c=[1, 0], theta=-1)


def test_refuses_zero_vector():
    assert _refused(J=[[10, 0], [0, 1]], I=[[1, 0], [0, 1]], c=[0, 0], theta=4)


def test_refuses_nonpositive_denominator():
    # I not PSD in direction c: c = (1,0), I = diag(-1, 1) → cᵀIc = -1 ≤ 0.
    assert _refused(J=[[10, 0], [0, 1]], I=[[-1, 0], [0, 1]], c=[1, 0], theta=4)


def test_refuses_failing_inequality():
    # cᵀJc = 3, cᵀIc = 1, θ = 4 → gap = 3 − 4 = -1 ≤ 0.  False inequality.
    assert _refused(J=[[3, 0], [0, 1]], I=[[1, 0], [0, 1]], c=[1, 0], theta=4)
    # Tie (gap = 0) is also refused (strict > 0 required): cᵀJc = 4, θ·cᵀIc = 4.
    assert _refused(J=[[4, 0], [0, 1]], I=[[1, 0], [0, 1]], c=[1, 0], theta=4)


def test_refuses_dimension_mismatch():
    assert _refused(J=[[1, 0], [0, 1]], I=[[1]], c=[1, 0], theta=1)          # dim(J)≠dim(I)
    assert _refused(J=[[1, 0], [0, 1]], I=[[1, 0], [0, 1]], c=[1], theta=1)  # len(c)≠dim
    assert _refused(J=[[1, 2, 3], [1, 2]], I=[[1, 0], [0, 1]], c=[1, 1], theta=1)  # non-square


def test_refuses_over_dimension_cap():
    n = 26
    big = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    Jbig = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
    c = [1] + [0] * (n - 1)
    assert _refused(J=Jbig, I=big, c=c, theta=1)


def test_accepts_sympy_matrix_input():
    # sympy Matrix input is coerced the same as nested sequences.
    J = sp.Matrix([[10, 0], [0, 1]])
    I = sp.eye(2)
    cert = rayleigh_gram_certificate(J, I, [1, 0], 4)
    assert cert.gap == sp.Integer(6)


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
        inst, n = certify_rayleigh_gram_point(fam, pt, fam.lean_name(pt))
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
    text, n = RayleighGramEmitter().emit_body(cf, LeanProfile(namespace=("RG",)))
    return text, n


def test_emit_lint_clean_and_deterministic():
    fam = rayleigh_gram_family(
        "RG", GridSpec([("_", [0])]), lambda pt: "rayleigh_gram_concrete",
        spec=lambda pt: ([[10, 1], [1, 3]], [[1, 0], [0, 1]], [1, 1], 2))
    pts = list(fam.grid.points())
    text, n = _emit_text(fam, pts)
    assert n == 1
    assert "theorem rayleigh_gram_concrete" in text
    assert "norm_num" in text
    assert "> 0" in text
    # both contractions are spelled out as explicit rational-literal products
    assert "10 * 1 * 1" in text          # J[0][0]·c0·c1 term
    assert "conjecture1_proved = False" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic
    text2, _ = _emit_text(fam, pts)
    assert text2 == text


def test_emit_renders_theta_and_conjunction():
    fam = rayleigh_gram_family(
        "RG2", GridSpec([("_", [0])]), lambda pt: "rayleigh_gram_diag",
        spec=lambda pt: ([[10, 0], [0, 1]], [[1, 0], [0, 1]], [1, 0], 4))
    pts = list(fam.grid.points())
    text, _ = _emit_text(fam, pts)
    assert "theorem rayleigh_gram_diag" in text
    assert "4 * (" in text          # θ = 4 multiplies the I-form
    assert "∧" in text              # the conjunction (gap > 0) ∧ (denom > 0)
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors

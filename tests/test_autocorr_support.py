"""AutocorrSupport emitter (kind ``autocorr_support``) — offline, self-contained.

Ported shape: anthropics/zeta-23-lean ``Taper/Decay.autocorr_le_of_support`` —
for a box-supported nonneg step taper ``v = Σ c_i·1_[i,i+1)`` on ``[0, 2M)``, the
integer-shift autocorrelation ``Σ_i c_i c_{i+|k|}`` is bounded by the support
triangle ``(2M − |k|)₊``, strict where the taper drops below the box.

Dispatch is NOT wired (the parent session owns the registry), so the emitter is
tested DIRECTLY: the certificate builder's accept/refuse behaviour, and a
hand-assembled ``CertifiedFamily`` fed straight to ``emit_body``.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import (  # noqa: E402
    CertifiedFamily,
    _construction_guard,
)
from telperion.emit_autocorr_support import (  # noqa: E402
    AutocorrSupportEmitter,
    autocorr_support_certificate,
    autocorr_support_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


# --------------------------------------------------------------------------- #
# helpers                                                                      #
# --------------------------------------------------------------------------- #

def _certified(fam, name):
    """Certify the single-point family directly (dispatch is unwired), returning
    a guard-constructed CertifiedFamily ready for emit_body."""
    pt = next(iter(fam.grid.points()))
    M, coeffs, shifts = fam.special[1](pt)
    from telperion.certify import CertifiedInstance
    cert = autocorr_support_certificate(M, coeffs, shifts)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    _construction_guard.open = True
    try:
        return CertifiedFamily(family=fam, instances=(inst,), checks_passed=len(cert.samples))
    finally:
        _construction_guard.open = False


# --------------------------------------------------------------------------- #
# (1) certificate builder: accept + honest refusals                            #
# --------------------------------------------------------------------------- #

def test_builder_accepts_valid_instance():
    # M=2 -> width 2M=4 cells; a taper that drops below the box at two cells.
    cert = autocorr_support_certificate(
        2, [sp.Rational(1), sp.Rational(1, 2), sp.Rational(1), sp.Rational(3, 4)],
        [-3, -2, -1, 0, 1, 2, 3])
    assert cert.M == 2 and len(cert.coeffs) == 4
    # every sample obeys lhs <= rhs, with the peak (shift 0) strictly below 2M=4
    for s, lhs, rhs in cert.samples:
        assert lhs <= rhs
    peak = next(lhs for s, lhs, rhs in cert.samples if s == 0)
    assert peak == sp.Rational(45, 16) and peak < 4       # strict: taper < box


def test_lhs_is_exact_discrete_autocorrelation():
    # Σ_i c_i c_{i+|k|} recomputed independently.
    coeffs = [sp.Rational(1), sp.Rational(1, 2), sp.Rational(1), sp.Rational(3, 4)]
    cert = autocorr_support_certificate(2, coeffs, [0, 1, 2, 3])
    for s, lhs, rhs in cert.samples:
        k = abs(int(s))
        want = sum(coeffs[i] * coeffs[i + k] for i in range(len(coeffs) - k))
        assert lhs == want
        assert rhs == max(sp.Integer(0), 2 * cert.M - abs(int(s)))


def test_refuses_nonpositive_M():
    for bad in (0, -1, sp.Rational(-1, 2)):
        try:
            autocorr_support_certificate(bad, [], [0])
            raised = False
        except ValueError:
            raised = True
        assert raised, f"M={bad} must be refused"


def test_refuses_width_mismatch():
    # 2M = 4 but only 3 coefficients supplied.
    try:
        autocorr_support_certificate(2, [sp.Rational(1)] * 3, [0])
        raised = False
    except ValueError:
        raised = True
    assert raised, "len(coeffs) != 2M must be refused"


def test_refuses_coefficient_out_of_unit_interval():
    for bad in (sp.Rational(3, 2), sp.Rational(-1, 4)):
        try:
            autocorr_support_certificate(1, [bad, sp.Rational(1, 2)], [0])
            raised = False
        except ValueError:
            raised = True
        assert raised, f"coefficient {bad} outside [0,1] must be refused"


def test_refuses_all_equality_box_case():
    # the box (all c_i = 1) saturates the triangle at every shift -> X <= X,
    # vacuous; the builder refuses it (deferred to the analytic lemma).
    try:
        autocorr_support_certificate(2, [sp.Rational(1)] * 4, [-1, 0, 1])
        raised = False
    except ValueError:
        raised = True
    assert raised, "the all-equality box case must be refused as vacuous"


def test_refusal_message_is_honest_on_impossible_false_claim():
    # A LHS can never exceed the RHS for an admissible taper, so the false-claim
    # branch is unreachable via the public API by construction — but the
    # all-equality refusal proves the builder does gate on slack.  Confirm the
    # accepted certificate is genuinely two-sided (>=1 strict sample).
    cert = autocorr_support_certificate(
        1, [sp.Rational(1, 2), sp.Rational(1)], [-1, 0, 1])
    assert any(lhs < rhs for _, lhs, rhs in cert.samples)


# --------------------------------------------------------------------------- #
# (2) emit_body directly: theorem + triangle bound + tactic, lint clean         #
# --------------------------------------------------------------------------- #

def _emit(fam, name):
    cf = _certified(fam, name)
    text, n = AutocorrSupportEmitter().emit_body(cf, LeanProfile(namespace=("AC",)))
    return text, n


def test_emit_body_has_theorem_triangle_bound_and_tactic():
    fam = autocorr_support_family(
        "AC", GridSpec([("_", [0])]), lambda pt: "autocorr_box_step",
        spec=lambda pt: (2, [sp.Rational(1), sp.Rational(1, 2),
                             sp.Rational(1), sp.Rational(3, 4)],
                         [-3, -2, -1, 0, 1, 2, 3]))
    text, n = _emit(fam, "autocorr_box_step")
    assert n == 1
    assert "theorem autocorr_box_step" in text
    # the support-triangle bound (2M − |y|)₊ rendered as max 0 (2*M − |·|)
    assert "max 0 (2 * (2) - |p.1|)" in text
    assert "List (ℚ × ℚ)" in text
    assert "fin_cases hp" in text and "norm_num" in text
    # the exact peak autocorrelation value (45/16) is present and < box (4)
    assert "(45 / 16)" in text
    # honest provenance + RH stance in the comment
    assert "autocorr_le_of_support" in text
    assert "RH: no" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emit_body_deterministic():
    fam = autocorr_support_family(
        "AC", GridSpec([("_", [0])]), lambda pt: "autocorr_det",
        spec=lambda pt: (1, [sp.Rational(1, 2), sp.Rational(1)], [-1, 0, 1]))
    a, _ = _emit(fam, "autocorr_det")
    b, _ = _emit(fam, "autocorr_det")
    assert a == b


def test_emit_body_is_nonvacuous():
    # at least one emitted sample is a STRICT inequality (LHS textually distinct
    # from RHS), so the body is not the reflexive X <= X tautology.
    from telperion.nonvacuity import check_nonvacuous
    fam = autocorr_support_family(
        "AC", GridSpec([("_", [0])]), lambda pt: "autocorr_nonvac",
        spec=lambda pt: (2, [sp.Rational(1), sp.Rational(1, 2),
                             sp.Rational(1), sp.Rational(3, 4)],
                         [0, 1, 2]))
    text, _ = _emit(fam, "autocorr_nonvac")
    check_nonvacuous(text)  # raises if wholly vacuous

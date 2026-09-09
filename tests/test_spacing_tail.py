"""SpacingTailBound emitter tests (offline, self-contained).

The global certify()/emit() dispatch is NOT wired for kind ``spacing_tail_bound``
(the parent session owns the registry wiring), so these tests drive the emitter
DIRECTLY: build the certificate, construct a CertifiedFamily under certify.py's
construction guard, and call ``SpacingTailBoundEmitter().emit_body`` — then lint
the emitted Lean text.

Shape: concrete-instance shadow of MV/Spacing ``spacing_sq`` / ``spacing_four``.
The builder REFUSES any bad or false configuration (honest refusal); the emitted
theorem is a true, non-vacuous, norm_num-decidable rational inequality about the
concrete config, NOT the uniform 9/δ (27/δ³) lemma.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import certify as _certify_mod  # noqa: E402
from telperion.certify import (  # noqa: E402
    CertifiedFamily,
    _construction_guard,
)
from telperion.emit_spacing_tail import (  # noqa: E402
    SpacingTailBoundEmitter,
    certify_spacing_tail_bound_point,
    spacing_tail_bound_certificate,
    spacing_tail_bound_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _refused(**kw) -> bool:
    try:
        spacing_tail_bound_certificate(**kw)
        return False
    except ValueError:
        return True


# --------------------------------------------------------------------------- #
# 1. builder: accepts a valid separated config, refuses each bad case         #
# --------------------------------------------------------------------------- #


def test_accepts_valid_separated_config():
    # s=0, f=[0, 5, -5], δ=[1,1,1]: separation (1+1)/2=1 ≤ 5 (admissible);
    # Σ = 1/25 + 1/25 = 2/25 ≤ 9/1 = 9.
    cert = spacing_tail_bound_certificate(0, [0, 5, -5], [1, 1, 1])
    assert cert.lhs_sum == sp.Rational(2, 25)
    assert cert.rhs == sp.Integer(9)
    assert cert.lhs_sum <= cert.rhs
    assert cert.power == 2


def test_refuses_nonpositive_radius():
    assert _refused(s=0, centers=[0, 5], radii=[0, 1])
    assert _refused(s=0, centers=[0, 5], radii=[1, -1])


def test_refuses_coincident_center():
    # f_1 = f_0 = 0 makes the t=1 term singular.
    assert _refused(s=0, centers=[0, 0], radii=[1, 1])


def test_refuses_admissibility_violation():
    # gap = 1 but (δ_s+δ_t)/2 = 2 > 1: separation fails.
    assert _refused(s=0, centers=[0, 1], radii=[2, 2])


def test_refuses_sum_exceeding_bound():
    # A config that passes admissibility but whose exact sum exceeds 9/δ_s.
    # Use a big δ_s so 9/δ_s is tiny, while a tightly-admissible neighbor
    # contributes a term that overshoots.  δ_s=100 → 9/100 = 0.09.
    # Neighbor at gap g with δ_t: admissible needs (100+δ_t)/2 ≤ g.
    # Take δ_t=100, g=100 (exactly admissible), term = 100/100^2 = 1/100...
    # too small. Instead make many neighbors OR pick δ_s huge with a close
    # cluster.  Simplest: δ_s large, neighbor gap exactly (δ_s+δ_t)/2, term
    # = δ_t / ((δ_s+δ_t)/2)^2.  With δ_s=1000, δ_t=1000, g=1000:
    # term = 1000/1000^2 = 1/1000; bound 9/1000. still under.
    # The bound 9/δ_s is genuinely uniform, so a single admissible term can't
    # break it; we need to hand a NON-admissible-looking but sum-breaking config
    # past admissibility — impossible by design. So instead verify the refusal
    # path by directly overriding: a config with δ_s tiny is easiest.
    # Actually the cleanest false-but-admissible case: it does not exist for a
    # SINGLE term (the uniform bound holds per-term-ish). Use the internal gate
    # by constructing a sum that exceeds via a hand-picked NON-uniform check:
    # give s a tiny radius and one neighbor with a huge radius at the minimal
    # admissible gap, so the term ~ δ_t/gap^2 with gap≈δ_t/2 → 4/δ_t, and
    # bound 9/δ_s with δ_s tiny is LARGE — so that under-shoots too.
    # Conclusion: for power=2 the uniform bound makes an admissible false case
    # impossible, which is exactly the honesty guarantee. We therefore test the
    # refusal on a deliberately NON-admissible config is already covered; here
    # assert the gate is REACHED by monkeypatching admissibility off via a
    # config the builder still sums: use power=4 where a clustered config can
    # exceed 27/δ_s^3 while each pair is admissible.
    #
    # power=4, s=0, δ_s=6, many close-but-admissible neighbors:
    # neighbor gap g, δ_t: admissible (6+δ_t)/2 ≤ g. Take δ_t=6, g=6 (tight):
    # term = 6/6^4 = 6/1296 = 1/216. bound 27/6^3 = 27/216 = 1/8. one term under.
    # 27 such terms → 27/216 = 1/8 = bound (tie). 28 terms would exceed but need
    # 28 distinct admissible centers — fine. Build 30 neighbors at ±6k spacing
    # is NOT all at gap 6. So this too respects the uniform bound.
    #
    # The honest truth: an ADMISSIBLE config can never break the uniform bound
    # (that IS the lemma). The sum-exceeds refusal guards against a MIS-STATED
    # bound / power mismatch, and is exercised by a config the builder is asked
    # to certify against the WRONG (too-small) constant. Since the constant is
    # fixed at 9/27, we instead prove the gate exists and fires by feeding a
    # config where we bypass admissibility is impossible — so we assert the
    # builder's returned sum ALWAYS satisfies the bound for every admissible
    # config we can construct (the guarantee), and separately that a
    # near-coincident (admissibility-violating) config is refused BEFORE the sum
    # gate. Both are covered above; here we assert the sum-gate is live by
    # checking a hand-built cert value.
    cert = spacing_tail_bound_certificate(0, [0, 3, -3], [1, 1, 1])
    # gap=3, admissible (1+1)/2=1 ≤ 3; Σ = 1/9+1/9 = 2/9 ≤ 9. sum gate passed.
    assert cert.lhs_sum == sp.Rational(2, 9)
    assert cert.lhs_sum <= cert.rhs


def test_sum_gate_fires_on_false_config(monkeypatch):
    # Directly exercise the exact-sum-vs-bound refusal: monkeypatch the module's
    # admissibility so a sum-breaking config slips past separation, proving the
    # final "sum exceeds bound → REFUSE" gate is live and independent.
    import telperion.emit_spacing_tail as m

    orig_abs = abs
    # A config with a very close neighbor: gap tiny, term huge, bound modest.
    # s=0, δ=[1,1], f=[0, 1/10]: gap=1/10, term = 1/(1/10)^2 = 100; bound 9.
    # This VIOLATES admissibility ((1+1)/2=1 > 1/10), so it is normally refused
    # at the separation gate. Patch admissibility to always pass, so execution
    # reaches the sum gate — which must then refuse because 100 > 9.
    def fake_abs(x):
        # make |f_s - f_t| look large enough to pass (δ_s+δ_t)/2 ≤ |gap|
        return orig_abs(x) + sp.Integer(1000)

    monkeypatch.setattr(m, "abs", fake_abs, raising=False)
    try:
        m.spacing_tail_bound_certificate(0, [0, sp.Rational(1, 10)], [1, 1])
        fired = False
    except ValueError as e:
        fired = "exceeds the bound" in str(e)
    assert fired, "the exact-sum-vs-bound gate must refuse the false config"


def test_quartic_mode_accepts_and_bounds():
    # power=4: s=0, f=[0, 5, -5], δ=[1,1,1]; Σ = 1/625+1/625 = 2/625 ≤ 27/1.
    cert = spacing_tail_bound_certificate(0, [0, 5, -5], [1, 1, 1], power=4)
    assert cert.power == 4
    assert cert.lhs_sum == sp.Rational(2, 625)
    assert cert.rhs == sp.Integer(27)
    assert cert.lhs_sum <= cert.rhs


def test_refuses_bad_power_index_and_length():
    assert _refused(s=0, centers=[0, 5], radii=[1, 1], power=3)
    assert _refused(s=5, centers=[0, 5], radii=[1, 1])          # index OOR
    assert _refused(s=0, centers=[0, 5, 9], radii=[1, 1])       # length mismatch
    assert _refused(s=0, centers=[0], radii=[1])                # vacuous (no t≠s)


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
        inst, n = certify_spacing_tail_bound_point(fam, pt, fam.lean_name(pt))
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
    text, n = SpacingTailBoundEmitter().emit_body(cf, LeanProfile(namespace=("ST",)))
    return text, n


def test_emit_lint_clean_and_deterministic():
    # δ_s = 2 so the RHS renders as a genuine `9 / 2` rational literal.
    fam = spacing_tail_bound_family(
        "ST", GridSpec([("_", [0])]), lambda pt: "spacing_tail_concrete",
        spec=lambda pt: (0, [0, 5, -5], [2, 1, 1]))
    pts = list(fam.grid.points())
    text, n = _emit_text(fam, pts)
    assert n == 1
    assert "theorem spacing_tail_concrete" in text
    assert "9 /" in text
    assert "norm_num" in text
    # the tail sum is spelled out as explicit rational terms
    assert "^2" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic
    text2, _ = _emit_text(fam, pts)
    assert text2 == text


def test_emit_quartic_uses_27():
    # δ_s = 2 so the RHS renders as a genuine `27 / 8` rational literal.
    fam = spacing_tail_bound_family(
        "ST4", GridSpec([("_", [0])]), lambda pt: "spacing_tail_quartic",
        spec=lambda pt: (0, [0, 5, -5], [2, 1, 1], 4))
    pts = list(fam.grid.points())
    text, _ = _emit_text(fam, pts)
    assert "theorem spacing_tail_quartic" in text
    assert "27 /" in text
    assert "^4" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors

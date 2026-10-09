"""scaled_interval_eval emitter -- kernel-computable fixed-point interval evaluation.

The shape (Part C, C1; prior art: OpenAI openai/math `WaveIntervals.lean`, Apache-2.0): real
intervals are integer pairs at a fixed scale S, every operation is computable integer
arithmetic with floor division and a one-ulp outward round, each operation's `mem_*` lemma is
proved ONCE in the `ScaledInterval` prelude, and per instance the kernel only re-runs the
integer arithmetic (`decide +kernel` on a Bool subset check) on literal boxes.

These tests pin, in order: the Python mirror of the integer semantics (it must agree with the
Lean definitions bit for bit, and it must enclose the true real value); the DAG builder; the
certify-time refusals; the emitted text; the sensitivity-registry classification and the
negative-control adapter; and, Lean-gated, an end-to-end kernel check of three instances plus
the two-sided negative control.

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

import mpmath
import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_scaled_interval_eval import (  # noqa: E402
    ScaledIntervalEvalEmitter,
    scaled_interval_eval_certificate,
    scaled_interval_eval_family,
    scaled_interval_prelude_lean,
    sie_add,
    sie_divnat,
    sie_exp,
    sie_mul,
    sie_neg,
    sie_of_frac,
    sie_of_range,
    sie_square,
    sie_sub,
    sie_taylor,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

mpmath.mp.dps = 120
x = sp.Symbol("x")
S30 = 10 ** 30

# The three worked instances (shared with the Lean-gated end-to-end test).
EX_EXP = sp.exp(sp.Rational(1, 3)) * sp.Rational(1, 7) + sp.Rational(2, 9)
EX_POLY = x ** 3 - 2 * x + sp.Rational(1, 3)          # over x in [1/3, 1/2]
EX_EXP_BIG = sp.exp(sp.Rational(5, 2)) - sp.exp(-sp.Rational(5, 2))   # argument reduction


def _contains(box, S, value):
    """lo <= S*value <= hi, with value an mpmath number (120 digits)."""
    v = mpmath.mpf(S) * value
    return mpmath.mpf(box[0]) <= v <= mpmath.mpf(box[1])


# --- 1. the integer semantics (must mirror the Lean definitions exactly) -----

def test_of_frac_floor_and_plus_one():
    assert sie_of_frac(10 ** 6, 1, 3) == (333333, 333334)
    # negative numerator: floor, not truncation (Lean `Int` `/` is Euclidean = floor for q > 0)
    assert sie_of_frac(10 ** 6, -1, 3) == (-333334, -333333)
    assert sie_of_range(10 ** 6, 1, 3, 1, 2) == (333333, 500001)


def test_add_neg_sub():
    a, b = (10, 20), (-3, 5)
    assert sie_add(a, b) == (7, 25)
    assert sie_neg(b) == (-5, 3)
    assert sie_sub(a, b) == sie_add(a, sie_neg(b)) == (5, 23)


def test_mul_corners_floor_plus_one():
    S = 100
    # [-1.5, 2.0] * [0.3, 0.7]: corners -45, -105, 60, 140 (scaled S^2) -> floor/S, max//S + 1
    assert sie_mul(S, (-150, 200), (30, 70)) == (-10500 // 100, 14000 // 100 + 1)


def test_divnat_and_square():
    assert sie_divnat((7, 9), 2) == (3, 5)
    assert sie_divnat((-7, -5), 2) == (-4, -2)
    S = 1000
    assert sie_square(S, (1500, 1501), 1) == sie_mul(S, (1500, 1501), (1500, 1501))


@pytest.mark.parametrize("p,q", [(1, 3), (-2, 7), (5, 11), (0, 1)])
def test_mul_encloses_true_product(p, q):
    S = 10 ** 12
    a = sie_of_frac(S, p, q)
    b = sie_of_frac(S, 3, 13)
    assert _contains(sie_mul(S, a, b), S, mpmath.mpf(p) / q * mpmath.mpf(3) / 13)


def test_taylor_sum_encloses_partial_sum():
    S = 10 ** 20
    a = sie_of_frac(S, 1, 3)
    term, total = sie_taylor(S, a, 10)
    y = Fraction(1, 3)
    from math import factorial
    exact = sum(y ** j / factorial(j) for j in range(11))
    assert _contains(total, S, mpmath.mpf(exact.numerator) / exact.denominator)


@pytest.mark.parametrize("p,q", [(1, 3), (-1, 3), (5, 2), (-5, 2), (7, 1), (0, 1)])
def test_exp_encloses_true_value(p, q):
    S = S30
    box, (k, n, r) = sie_exp(S, sie_of_frac(S, p, q))
    assert _contains(box, S, mpmath.exp(mpmath.mpf(p) / q))
    assert box[1] - box[0] < S // 10 ** 12  # still a tight box after reduction
    if abs(Fraction(p, q)) <= 1:
        assert k == 0
    else:
        assert k >= 1
    assert r >= 1 and n >= 1


# --- 2. the DAG builder -------------------------------------------------------

def test_dag_shares_common_subtrees():
    expr = x * sp.exp(x) + sp.exp(x)              # exp(x) occurs twice
    cert = scaled_interval_eval_certificate(expr, vars={"x": ("1/3", "1/2")}, scale=S30)
    exps = [nd for nd in cert.nodes if nd.op == "exp"]
    assert len(exps) == 1, "exp(x) must be built once and shared"


def test_dag_handles_subtraction_and_negation():
    cert = scaled_interval_eval_certificate(EX_POLY, vars={"x": ("1/3", "1/2")}, scale=S30)
    ops = {nd.op for nd in cert.nodes}
    assert "sub" in ops                           # -2*x becomes a subtraction of 2*x
    assert {"var", "const", "mul"} <= ops


# --- 3. certification and refusals ---------------------------------------------

def test_certify_exp_example_encloses_true_value():
    cert = scaled_interval_eval_certificate(EX_EXP, scale=S30)
    true = mpmath.exp(mpmath.mpf(1) / 3) / 7 + mpmath.mpf(2) / 9
    root = cert.nodes[cert.root]
    assert _contains(root.box, cert.scale, true)
    assert cert.claim_lo <= sp.Rational(root.box[0], cert.scale)
    assert sp.Rational(root.box[1], cert.scale) <= cert.claim_hi


def test_certify_polynomial_over_a_range_is_sound():
    cert = scaled_interval_eval_certificate(EX_POLY, vars={"x": ("1/3", "1/2")}, scale=S30)
    for t in [Fraction(1, 3), Fraction(2, 5), Fraction(9, 20), Fraction(1, 2)]:
        v = t ** 3 - 2 * t + Fraction(1, 3)
        assert cert.claim_lo <= sp.Rational(v.numerator, v.denominator) <= cert.claim_hi


def test_user_claim_is_accepted_when_it_contains_the_box():
    cert = scaled_interval_eval_certificate(EX_EXP, scale=S30, lo="21/50", hi="11/25")
    assert cert.claim_lo == sp.Rational(21, 50) and cert.claim_hi == sp.Rational(11, 25)


def test_refuses_claim_one_ulp_too_tight():
    """The design's TDD-1 test 3: a claim 1 ulp inside the computed box is refused in Python."""
    honest = scaled_interval_eval_certificate(EX_EXP, scale=S30)
    lo_b, hi_b = honest.nodes[honest.root].box
    with pytest.raises(ValueError, match="REFUSED"):
        scaled_interval_eval_certificate(
            EX_EXP, scale=S30, lo=sp.Rational(lo_b, S30), hi=sp.Rational(hi_b - 1, S30))
    with pytest.raises(ValueError, match="REFUSED"):
        scaled_interval_eval_certificate(
            EX_EXP, scale=S30, lo=sp.Rational(lo_b + 1, S30), hi=sp.Rational(hi_b, S30))


@pytest.mark.parametrize("bad", [
    sp.sin(sp.Rational(1, 3)),                 # unsupported function
    sp.Float(0.25) + 1,                        # float literal
    sp.pi + 1,                                 # irrational constant
    x ** -1,                                   # negative power
    sp.sqrt(x),                                # fractional power
])
def test_refuses_unsupported_expressions(bad):
    with pytest.raises(ValueError, match="REFUSED"):
        scaled_interval_eval_certificate(bad, vars={"x": ("1/3", "1/2")}, scale=S30)


def test_refuses_bad_inputs():
    with pytest.raises(ValueError, match="REFUSED"):
        scaled_interval_eval_certificate(EX_POLY, vars={"x": ("1/2", "1/3")}, scale=S30)
    with pytest.raises(ValueError, match="REFUSED"):       # undeclared symbol
        scaled_interval_eval_certificate(EX_POLY, scale=S30)
    with pytest.raises(ValueError, match="REFUSED"):       # declared but unused binder
        scaled_interval_eval_certificate(EX_EXP, vars={"x": ("0", "1")}, scale=S30)
    with pytest.raises(ValueError, match="REFUSED"):       # scale too small
        scaled_interval_eval_certificate(EX_EXP, scale=1)
    with pytest.raises(ValueError, match="REFUSED"):       # inverted claim
        scaled_interval_eval_certificate(EX_EXP, scale=S30, lo="1", hi="0")
    with pytest.raises(ValueError, match="REFUSED"):       # exp argument out of range
        scaled_interval_eval_certificate(sp.exp(sp.Integer(10) ** 30), scale=S30)


def test_certify_propagates_the_refusal():
    fam = scaled_interval_eval_family(
        "Bad", GridSpec([("i", [0])]), lambda pt: "bad",
        spec=lambda pt: dict(expr=EX_EXP, scale=S30, lo="1", hi="0"))
    with pytest.raises(Exception, match="REFUSED"):
        certify(fam)


# --- 4. emission ---------------------------------------------------------------

def _emit_text(expr, name="sie_t", **kw):
    fam = scaled_interval_eval_family(
        "ScaledIntervalEvalTest", GridSpec([("i", [0])]), lambda pt: name,
        spec=lambda pt: dict(expr=expr, **kw))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ScaledIntervalEvalTest",),
                    imports=("Mathlib", "ScaledInterval")),
        [ScaledIntervalEvalEmitter()],
        ValidationReport(checks=(("scaled_interval_eval", True),)),
    )
    return next(iter(report.files.values()))


def test_kind_and_emitter_for():
    fam = scaled_interval_eval_family("T", GridSpec([("i", [0])]), lambda pt: "t",
                                      spec=lambda pt: dict(expr=EX_EXP, scale=S30))
    assert fam.kind == "scaled_interval_eval"
    assert emitter_for("scaled_interval_eval").kind == "scaled_interval_eval"


def test_emit_shape_is_deterministic_and_lint_clean():
    txt = _emit_text(EX_EXP, scale=S30)
    assert txt == _emit_text(EX_EXP, scale=S30), "emission is not byte-deterministic"
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == [], errs
    for banned in ("sorry", "admit", "native_decide", "axiom ", "maxHeartbeats"):
        assert banned not in txt, banned
    assert "decide +kernel" in txt
    assert "_calc" in txt and "_mem" in txt
    assert "RI.mem_expR" in txt and "RI.mem_of_subset" in txt
    assert "Real.exp" in txt
    assert "conjecture1_proved = False" in txt
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_emit_polynomial_binds_the_variable():
    txt = _emit_text(EX_POLY, vars={"x": ("1/3", "1/2")}, scale=S30)
    assert "∀ x : ℝ" in txt
    assert "RI.mem_ofRange" in txt


def test_prelude_is_attributed_and_clean():
    pre = scaled_interval_prelude_lean()
    assert pre.startswith("/-")
    assert "openai/math" in pre and "Apache-2.0" in pre and "WaveIntervals.lean" in pre
    assert "import Mathlib" in pre
    for banned in ("sorry", "native_decide", "admit"):
        assert banned not in pre
    assert "theorem RI.mem_expR" in pre and "theorem RI.mem_mul" in pre


def test_example_prelude_file_matches_the_generator():
    """The island's ScaledInterval.lean is written from the SAME string (drift check)."""
    p = (Path(__file__).resolve().parents[1] / "examples" / "scaled_interval_eval" / "lean"
         / "ScaledInterval.lean")
    assert p.read_text(encoding="utf-8") == scaled_interval_prelude_lean()


# --- 5. registry and negative-control wiring -----------------------------------

def test_emitter_is_classified_structurally_nonvacuous_with_adapter():
    from telperion.emitter_sensitivity import (
        NEG_CONTROL_ADAPTER, REGISTRY, STRUCTURALLY_NONVACUOUS)
    from telperion.negative_control_harness import registered_adapters
    stance = REGISTRY["ScaledIntervalEvalEmitter"]
    assert stance.stance == STRUCTURALLY_NONVACUOUS
    assert stance.reason.strip()
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "ScaledIntervalEvalEmitter" in registered_adapters()


def test_adapter_twins_differ_by_one_ulp_only():
    from telperion.negative_control_harness import registered_adapters
    ad = registered_adapters()["ScaledIntervalEvalEmitter"]
    f, t = ad.make_false_cert(), ad.make_true_cert()
    fr, tr = f.nodes[f.root].box, t.nodes[t.root].box
    assert fr[0] == tr[0] and fr[1] == tr[1] - 1
    ft, tt = ad.emit_call(f, "twin"), ad.emit_call(t, "twin")
    diff = [(a, b) for a, b in zip(ft.splitlines(), tt.splitlines()) if a != b]
    assert len(diff) == 1, diff
    assert str(tr[1]) in diff[0][1] and str(tr[1] - 1) in diff[0][0]


# --- 6. Lean end to end (gated on a built env) ----------------------------------

_ENV = Path(__file__).resolve().parents[1] / "examples" / "scaled_interval_eval" / "lean"


def _env_ready():
    from lean_env import lean_env_ready
    olean = _ENV / ".lake" / "build" / "lib" / "lean" / "ScaledInterval.olean"
    return lean_env_ready(_ENV) and olean.is_file()


lean = pytest.mark.skipif(not _env_ready(),
                          reason="scaled_interval_eval Lean env not built -- skipped")


@lean
def test_lean_end_to_end_three_instances_axiom_clean():
    from telperion.verify import verify_lean
    cases = [
        ("sie_exp_third", EX_EXP, {}),
        ("sie_cubic", EX_POLY, {"x": ("1/3", "1/2")}),
        ("sie_sinh_reduced", EX_EXP_BIG, {}),
    ]
    for name, expr, vs in cases:
        txt = _emit_text(expr, name=name, vars=vs, scale=S30)
        r = verify_lean(txt, env_dir=_ENV, decls=[f"ScaledIntervalEvalTest.{name}"])
        assert r.okay and r.axioms_clean, (name, r.summary(), r.errors[:2])
        assert set(r.axioms[f"ScaledIntervalEvalTest.{name}"]) <= {
            "propext", "Classical.choice", "Quot.sound"}


@lean
def test_lean_negative_control_one_ulp():
    from telperion.negative_control_harness import (
        generic_negative_control, registered_adapters)
    res = generic_negative_control(registered_adapters()["ScaledIntervalEvalEmitter"],
                                   env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail


@lean
def test_lean_rejects_a_genuinely_false_enclosure():
    """A hand-forged claim whose upper end sits BELOW the true value (Layer 1 bypassed):
    the `upperOK` decide is false, so the kernel rejects the theorem."""
    from dataclasses import replace

    from telperion.negative_control import assert_kernel_rejects
    from telperion.negative_control_harness import emit_via_single_instance_family
    cert = scaled_interval_eval_certificate(EX_EXP, scale=S30)
    true = mpmath.exp(mpmath.mpf(1) / 3) / 7 + mpmath.mpf(2) / 9
    bad_hi = sp.Rational(int(mpmath.floor(true * 10 ** 20)) - 1, 10 ** 20)
    assert mpmath.mpf(bad_hi.p) / bad_hi.q < true
    forged = replace(cert, claim_hi=bad_hi)
    body = emit_via_single_instance_family(
        ScaledIntervalEvalEmitter(), lean_name="sie_false_hi",
        instance_kwargs={"payload": forged})
    assert assert_kernel_rejects(f"import Mathlib\nimport ScaledInterval\n{body}\n",
                                 "sie_false_hi", env_dir=_ENV)

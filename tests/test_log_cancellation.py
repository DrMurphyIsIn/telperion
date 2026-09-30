"""log_combination EXACT-CANCELLATION face (routes ``exact`` / ``mixed``).

Layer 1: the generation-time self-check refuses a combination whose rational
identity ∏ rᵢ^{D·cᵢ} = 1 fails, and a mixed bound the tangent enclosure cannot
carry.  Layer 2 (Lean-gated): a hand-forged certificate of a FALSE equality /
FALSE mixed bound is kernel-REJECTED while the true twin compiles (the generic
two-sided negative-control engine, face-specific adapters defined here because
the registry holds one adapter per emitter and LogCombinationEmitter's is the
monotone-route control).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from lean_env import lean_env_ready  # noqa: E402
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_log_combination import (  # noqa: E402
    LogCancellationCertificate,
    LogCombinationEmitter,
    log_cancellation_certificate,
    log_combination_family,
)
from telperion.lean_lint import check_lean_text  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    NegativeControlAdapter,
    generic_negative_control,
)

R = sp.Rational
_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"


# --- Layer 1 -----------------------------------------------------------------

def test_exact_identity_log12():
    c = log_cancellation_certificate(route="exact", exact_terms=[(1, 12), (-2, 2), (-1, 3)])
    assert c.exact_scale == 1
    assert c.exact_pos == ((12, 1),) and c.exact_neg == ((2, 2), (3, 1))


def test_exact_rational_coefficients_scale_to_lcm():
    c = log_cancellation_certificate(
        route="exact", exact_terms=[(R(1, 2), R(9, 4)), (R(1, 3), R(8, 27))])
    assert c.exact_scale == 6
    assert c.exact_pos == ((R(9, 4), 3), (R(8, 27), 2)) and c.exact_neg == ()


def test_exact_tie_value_is_forced_zero():
    """The motivating tie shape: 11·(log B / 11) = 5 log(3/2) + log(23/18) with
    B = (3/2)^5·(23/18); an enclosure check would have zero margin here."""
    B = R(3, 2) ** 5 * R(23, 18)
    c = log_cancellation_certificate(
        route="exact", exact_terms=[(1, B), (-5, R(3, 2)), (-1, R(23, 18))])
    assert c.route == "exact"


@pytest.mark.parametrize("terms", [
    [(1, 12), (-2, 2), (-1, 5)],                  # log 12 ≠ 2 log 2 + log 5
    [(R(1, 2), R(9, 4)), (R(1, 3), R(8, 25))],    # perturbed argument
    [(R(1, 2), R(9, 4)), (R(1, 4), R(8, 27))],    # perturbed coefficient
])
def test_exact_refuses_non_cancelling(terms):
    with pytest.raises(ValueError, match="does not cancel"):
        log_cancellation_certificate(route="exact", exact_terms=terms)


def test_refuses_nonpositive_argument_and_zero_coeff():
    with pytest.raises(ValueError, match="> 0"):
        log_cancellation_certificate(route="exact", exact_terms=[(1, 0), (-1, 1)])
    with pytest.raises(ValueError, match="zero coefficient"):
        log_cancellation_certificate(route="exact", exact_terms=[(0, 2), (1, 1)])


def test_mixed_enclosure_and_refusals():
    base = dict(route="mixed", exact_terms=[(1, 12), (-2, 2), (-1, 3)],
                rem_terms=[(1, R(101, 100))])
    c = log_cancellation_certificate(**base, lo=0, hi=R(1, 100))
    assert c.rem_fold == R(101, 100)
    # true value log(1.01) ≈ 0.00995 < 1/100 = tangent bound; hi below it is refused
    with pytest.raises(ValueError, match="upper enclosure fails"):
        log_cancellation_certificate(**base, hi=R(99, 10000))
    with pytest.raises(ValueError, match="lower enclosure fails"):
        log_cancellation_certificate(**base, lo=R(1, 100))
    # a non-cancelling exact group is refused even in mixed mode
    with pytest.raises(ValueError, match="does not cancel"):
        log_cancellation_certificate(
            route="mixed", exact_terms=[(1, 12), (-2, 2), (-1, 5)],
            rem_terms=[(1, R(101, 100))], hi=1)
    with pytest.raises(ValueError, match="at least one of lo / hi"):
        log_cancellation_certificate(**base)


def test_mixed_opaque_remainder():
    c = log_cancellation_certificate(
        route="mixed", exact_terms=[(R(1, 2), R(9, 4)), (-1, R(3, 2))],
        rem_terms=[(R(1, 3), R(5, 4))], opaque=(R(-1, 100), R(1, 100)),
        lo=R(1, 20), hi=R(1, 10))
    assert c.opaque == (R(-1, 100), R(1, 100))
    with pytest.raises(ValueError, match="upper enclosure fails"):
        log_cancellation_certificate(
            route="mixed", exact_terms=[(R(1, 2), R(9, 4)), (-1, R(3, 2))],
            rem_terms=[(R(1, 3), R(5, 4))], opaque=(R(-1, 100), R(1, 50)),
            hi=R(1, 10))


def test_family_emits_clean_lean():
    specs = {
        0: {"route": "exact", "terms": [(1, "12"), (-2, "2"), (-1, "3")]},
        1: {"route": "mixed", "exact_terms": [(1, "12"), (-2, "2"), (-1, "3")],
            "rem_terms": [(1, "101/100")], "lo": "0", "hi": "1/100"},
    }
    fam = log_combination_family(
        "LCancel", GridSpec([("case", [0, 1])]), lambda pt: f"lc{pt['case']}",
        spec=lambda pt: specs[pt["case"]])
    rep = emit(certify(fam), LeanProfile(namespace=("LCancel",)),
               [LogCombinationEmitter()], ValidationReport(checks=(("x", True),)))
    text = next(iter(rep.files.values()))
    assert "theorem lc0 :" in text and "= 0 := by" in text
    assert "Real.one_sub_inv_le_log_of_pos" in text and "Real.log_le_sub_one_of_pos" in text
    assert "sorry" not in text and "native_decide" not in text
    check_lean_text(text)  # raises on any error-severity lint issue


def test_dogfood_generate_check():
    import importlib.util
    p = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "generate.py"
    spec = importlib.util.spec_from_file_location("lc_gen", p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert mod.main(check=True) == 0


# --- Layer 2 (kernel) --------------------------------------------------------

def _exact_cert(terms, pos, neg):
    return LogCancellationCertificate(
        route="exact", exact_terms=tuple((R(c), R(r)) for c, r in terms),
        exact_scale=sp.Integer(1), exact_pos=pos, exact_neg=neg)


def _exact_adapter():
    em = LogCombinationEmitter()
    return NegativeControlAdapter(
        emitter_name="LogCombinationEmitter[exact]",
        # FALSE: log 12 = 2 log 2 + log 5 (forged split; e_num 12 = 2^2·5 is false)
        make_false_cert=lambda: _exact_cert(
            [(1, 12), (-2, 2), (-1, 5)], ((R(12), 1),), ((R(2), 2), (R(5), 1))),
        make_true_cert=lambda: _exact_cert(
            [(1, 12), (-2, 2), (-1, 3)], ((R(12), 1),), ((R(2), 2), (R(3), 1))),
        emit_call=lambda cert, name: em._emit_cancellation(cert, name),
        label="log 12 = 2 log 2 + log 5 is FALSE (12 ≠ 20)",
    )


def _mixed_adapter():
    em = LogCombinationEmitter()

    def cert(hi):
        return LogCancellationCertificate(
            route="mixed", exact_terms=((R(1), R(12)), (R(-2), R(2)), (R(-1), R(3))),
            exact_scale=sp.Integer(1), exact_pos=((R(12), 1),),
            exact_neg=((R(2), 2), (R(3), 1)), rem_terms=((R(1), R(101, 100)),),
            rem_scale=sp.Integer(1), rem_pos=((R(101, 100), 1),), rem_neg=(),
            rem_fold=R(101, 100), hi=hi)

    return NegativeControlAdapter(
        emitter_name="LogCombinationEmitter[mixed]",
        # FALSE: log 12 − 2 log 2 − log 3 + log(101/100) ≤ 1/200 (true value ≈ 0.00995)
        make_false_cert=lambda: cert(R(1, 200)),
        make_true_cert=lambda: cert(R(1, 100)),
        emit_call=lambda c, name: em._emit_cancellation(c, name),
        label="exact part + log(101/100) ≤ 1/200 is FALSE (log 1.01 ≈ 0.00995)",
    )


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="log_combination Lean env not built")
@pytest.mark.parametrize("make", [_exact_adapter, _mixed_adapter], ids=["exact", "mixed"])
def test_kernel_negative_control(make):
    res = generic_negative_control(make(), env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay

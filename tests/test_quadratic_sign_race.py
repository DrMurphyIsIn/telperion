"""eventual_threshold QUADRATIC SIGN RACE face.

Layer 1: exact self-check refusals (wrong switch point, vertex past m0, wrong
leading sign, endpoint sign).  Layer 2 (Lean-gated): the registered
EventualThresholdEmitter adapter forges the switch one step late and the kernel
rejects it, while the true twin compiles.  Also pins the arity face unchanged and
the dogfood drift check.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from lean_env import lean_env_ready  # noqa: E402
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_eventual_threshold import (  # noqa: E402
    EventualThresholdEmitter,
    QuadraticSignRaceCert,
    eventual_threshold_certificate,
    eventual_threshold_family,
    quadratic_sign_race_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.lean_lint import check_lean_text  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)

R = sp.Rational
_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"


def _P(a, b, c, m):
    return a * m * m + b * m + c


def test_switch_certificate_literals():
    c = quadratic_sign_race_certificate(1, -10, -7, 5, "switch", 10)
    assert (c.anchor, c.slope, c.value, c.head_value) == (11, 12, 4, -7)


@pytest.mark.parametrize("a,b,c", [(1, -10, -7), (R(1, 2), R(-7, 2), -20), (3, -2, -100)])
def test_switch_matches_brute_force(a, b, c):
    """The certified pattern agrees with direct evaluation on a long integer range."""
    a, b, c = R(a), R(b), R(c)
    m0 = int(sp.ceiling(-b / (2 * a)))
    r = max(m for m in range(m0, 200) if _P(a, b, c, m) < 0)
    cert = quadratic_sign_race_certificate(a, b, c, m0, "switch", r)
    for m in range(m0, 400):
        v = _P(a, b, c, m)
        assert (v < 0) if m <= cert.r else (v > 0)


@pytest.mark.parametrize("r", [9, 11])
def test_refuses_wrong_switch_point(r):
    with pytest.raises(ValueError, match="REFUSED"):
        quadratic_sign_race_certificate(1, -10, -7, 5, "switch", r)


def test_refuses_vertex_past_m0():
    # vertex 5 > m0 = 4: P is not monotone on [4, oo)
    with pytest.raises(ValueError, match="vertex"):
        quadratic_sign_race_certificate(1, -10, -7, 4, "switch", 10)


def test_refuses_wrong_modes_and_signs():
    with pytest.raises(ValueError, match="a > 0"):
        quadratic_sign_race_certificate(-1, 0, -1, 0, "positive")
    with pytest.raises(ValueError, match="a < 0"):
        quadratic_sign_race_certificate(1, 0, -1, 0, "negative")
    with pytest.raises(ValueError, match="a = 0"):
        quadratic_sign_race_certificate(0, 1, -1, 0, "positive")
    with pytest.raises(ValueError, match="not > 0"):
        quadratic_sign_race_certificate(1, -3, 1, 2, "positive")   # P(2) = -1
    with pytest.raises(ValueError, match="not < 0"):
        quadratic_sign_race_certificate(-1, -8, -15, -3, "negative")  # P(-3) = 0
    with pytest.raises(ValueError, match="r >= m0"):
        quadratic_sign_race_certificate(1, -10, -7, 5, "switch", 4)


def test_arity_face_unchanged():
    assert eventual_threshold_certificate(3).n == 3
    fam = eventual_threshold_family("ET", GridSpec([("k", [2])]), lambda pt: "et2",
                                    spec=lambda pt: pt["k"])
    text = next(iter(emit(certify(fam), LeanProfile(namespace=("ET",)),
                          [EventualThresholdEmitter()],
                          ValidationReport(checks=(("x", True),))).files.values()))
    assert "∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p → (a1 < p * c1 ∧ a2 < p * c2)" in text


def test_family_emits_clean_lean():
    spec = {"quadratic": (1, -10, -7), "m0": 5, "mode": "switch", "r": 10}
    fam = eventual_threshold_family("QR", GridSpec([("k", [0])]), lambda pt: "qr",
                                    spec=lambda pt: spec)
    cf = certify(fam)
    assert isinstance(cf.instances[0].payload, QuadraticSignRaceCert)
    text = next(iter(emit(cf, LeanProfile(namespace=("QR",)), [EventualThresholdEmitter()],
                          ValidationReport(checks=(("x", True),))).files.values()))
    assert "(∀ m : ℤ, 11 ≤ m → 0 <" in text and "≠ 0)" in text
    assert "sorry" not in text and "native_decide" not in text
    check_lean_text(text)


def test_dogfood_generate_check():
    import importlib.util
    p = Path(__file__).resolve().parents[1] / "examples" / "quadratic_sign_race" / "generate.py"
    spec = importlib.util.spec_from_file_location("qsr_gen", p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert mod.main(check=True) == 0


# --- negative control -------------------------------------------------------

def _adapter():
    ad = registered_adapters().get("EventualThresholdEmitter")
    assert ad is not None
    return ad


def test_registry_declares_wired_adapter():
    assert REGISTRY["EventualThresholdEmitter"].neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_false_and_refused_by_layer_one():
    cert = _adapter().make_false_cert()
    assert cert.r == 11 and _P(cert.a, cert.b, cert.c, 11) == 4   # claimed < 0
    with pytest.raises(ValueError, match="REFUSED"):
        quadratic_sign_race_certificate(cert.a, cert.b, cert.c, cert.m0, "switch", cert.r)
    t = _adapter().make_true_cert()
    assert quadratic_sign_race_certificate(t.a, t.b, t.c, t.m0, "switch", t.r) == t


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="Lean env not built")
def test_kernel_negative_control():
    res = generic_negative_control(_adapter(), env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay

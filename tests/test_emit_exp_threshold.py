"""exp_threshold emitter -- threshold-to-exponential domination via `1 + t <= e^t`.

The shape (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 5; B N2, C 4.5): a bundle reads a
nested-max threshold hypothesis (the `eventual_threshold` witness with its `max 1` guard folded in)
and returns each exponential consequence `Q <= K exp(s lam a)`, by the linear route
(`div_le_iff0` + `Real.add_one_le_exp` + `linarith`) or the log route (`Real.exp_log` +
`Real.exp_le_exp`); plus the product / inverse / shifted-rate atoms.

Acceptance is pinned on the two dogfood sites (E6Bridge7.lean:554-590, E6Bridge14.lean:66-86)
and the emitted Lean is compared, tactic line by tactic line, against the island source it
mirrors.  Every refusal has its own test.  The Lean kernel is the arbiter (the lead compiles
`examples/rvm_bridge/lean/Probes/Dogfood_exp_threshold.lean` on the island); these are the
pre-CI self-checks.

conjecture1_proved = False.
"""
import importlib.util
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    ExpThresholdEmitter,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    exp_threshold_certificate,
    exp_threshold_family,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_ROOT = Path(__file__).resolve().parents[1]
_E6B7 = _ROOT / "examples" / "rvm_bridge" / "lean" / "E6Bridge7.lean"
_E6B14 = _ROOT / "examples" / "rvm_bridge" / "lean" / "E6Bridge14.lean"
_DOGFOOD_GEN = _ROOT / "examples" / "rvm_bridge" / "dogfood_exp_threshold.py"
_DOGFOOD_LEAN = _ROOT / "examples" / "rvm_bridge" / "lean" / "Probes" / "Dogfood_exp_threshold.lean"

# the two dogfood sites, as the audit cites them
_E6B7_BUNDLE = dict(mode="linear", guard=True, steps=[
    dict(Q="A", a="eta", K="K", scale=2),
    dict(Q="B", a="M", K="K", scale=2, strict=True),
])
_E6B14_LOG = dict(mode="log", Q="Q", a="a", scale=2)
_E6B14_BUNDLE = dict(mode="log", guard=True, steps=[
    dict(Q="Q1", a="a1", scale=2),
    dict(Q="Q2", a="a2", scale=2),
])


def _fam(spec, name="t_inst", fam_name="ExpThresholdTest"):
    return exp_threshold_family(fam_name, GridSpec([("i", [0])]), lambda pt: name,
                                spec=lambda pt: dict(spec))


def _emit_text(spec, name="t_inst"):
    report = emit(
        certify(_fam(spec, name)),
        LeanProfile(namespace=("ExpThresholdTest",), imports=("Mathlib",)),
        [ExpThresholdEmitter()],
        ValidationReport(checks=(("exp_threshold", True),)),
    )
    return next(iter(report.files.values()))


def _sym(*names):
    return [sp.Symbol(n) for n in names]


# --- registry wiring --------------------------------------------------------

def test_kind_is_exp_threshold():
    assert _fam(_E6B14_LOG).kind == "exp_threshold"


def test_emitter_for_round_trips():
    assert emitter_for("exp_threshold").kind == "exp_threshold"


def test_emitter_is_classified_with_a_wired_adapter():
    from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY
    from telperion.negative_control_harness import ADAPTERS
    assert "ExpThresholdEmitter" in REGISTRY
    stance = REGISTRY["ExpThresholdEmitter"]
    assert stance.reason.strip()
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "ExpThresholdEmitter" in ADAPTERS


# --- acceptance: the dogfood instances ---------------------------------------

def test_e6bridge7_bundle_certificate():
    """E6Bridge7.lean:568-590: guard + two linear K-cleared steps, the second strict."""
    cert = exp_threshold_certificate(**_E6B7_BUNDLE)
    assert cert.mode == "linear" and cert.guard and cert.is_bundle
    assert cert.n_conjuncts == 3 and len(cert.steps) == 2
    A, eta, K, B, M = _sym("A", "eta", "K", "B", "M")
    s1, s2 = cert.steps
    assert (s1.Q, s1.a, s1.K, s1.scale, s1.strict) == (A, eta, K, 2, False)
    assert (s2.Q, s2.a, s2.K, s2.scale, s2.strict) == (B, M, K, 2, True)
    assert s1.symbolic and s2.symbolic
    # the exact threshold each hypothesis states
    assert sp.simplify(s1.threshold - A / (2 * eta * K)) == 0
    assert sp.simplify(s2.threshold - B / (2 * M * K)) == 0


def test_e6bridge14_log_step_certificate():
    """E6Bridge14.lean:78-86 (le_exp_of_log_le): one unguarded log step, scale 2."""
    cert = exp_threshold_certificate(**_E6B14_LOG)
    assert cert.mode == "log" and not cert.guard and cert.n_conjuncts == 1
    Q, a = _sym("Q", "a")
    (st,) = cert.steps
    assert st.K is None and st.symbolic
    assert sp.simplify(st.threshold - sp.log(sp.Max(1, Q)) / (2 * a)) == 0


def test_e6bridge14_effective_threshold_bundle_certificate():
    cert = exp_threshold_certificate(**_E6B14_BUNDLE)
    assert cert.mode == "log" and cert.guard and cert.n_conjuncts == 3


def test_mixed_bundle_is_labelled_mixed():
    cert = exp_threshold_certificate(mode="linear", steps=[
        dict(Q="A", a="b"), dict(mode="log", Q="C", a="d")])
    assert cert.mode == "mixed" and [s.mode for s in cert.steps] == ["linear", "log"]


# --- exact arithmetic on rational instances -----------------------------------

def test_rational_linear_threshold_is_exact_and_matches_declared():
    cert = exp_threshold_certificate(mode="linear", Q="3", a="1/2", K="1", scale=2, threshold="3")
    (st,) = cert.steps
    assert st.threshold == sp.Integer(3)
    assert not st.symbolic
    # Fraction / sp.Rational inputs are accepted exactly
    cert2 = exp_threshold_certificate(mode="linear", Q=Fraction(3), a=sp.Rational(1, 2),
                                      K=1, scale=sp.Integer(2), threshold=Fraction(3))
    assert cert2.steps[0].threshold == 3


def test_rational_log_threshold_is_the_exact_log_expression():
    cert = exp_threshold_certificate(mode="log", Q="5", a="3", scale=2, threshold="log(5)/6")
    assert sp.simplify(cert.steps[0].threshold - sp.log(5) / 6) == 0
    # Q <= 1: max 1 Q = 1, log 1 = 0, the threshold is EXACTLY 0 (the trivial face)
    cert0 = exp_threshold_certificate(mode="log", Q="1/2", a="3", scale=2, threshold=0)
    assert cert0.steps[0].threshold == 0


def test_declared_threshold_matches_up_to_rewriting():
    """(A/K)/(2 eta) and A/(2 eta K) are the same exact expression."""
    cert = exp_threshold_certificate(mode="linear", Q="A", a="eta", K="K", scale=2,
                                     threshold="(A/K)/(2*eta)")
    assert cert.steps[0].K == sp.Symbol("K")


def test_shifted_rate_emits_the_certified_minimum_constant():
    """y e^-y <= 1: P = y, r = 1, r' = 0 -> K = max(0, 1/1, 0) = 1 (E6Bridge16.lean:315-317)."""
    cert = exp_threshold_certificate(mode="shifted_rate", c0=0, c1=1, r=1, r_prime=0)
    assert cert.K == 1
    cert2 = exp_threshold_certificate(mode="shifted_rate", c0="1", c1="3", r="2", r_prime="1/2")
    assert cert2.K == sp.Integer(2)  # max(1, 3/(3/2), 0) = 2
    # a declared K at least the minimum is accepted verbatim
    assert exp_threshold_certificate(mode="shifted_rate", c0="1", c1="3", r="2",
                                     r_prime="1/2", K="5/2").K == sp.Rational(5, 2)


def test_inv_floor_defaults_to_one_over_x0():
    """E6Bridge11.lean:1084-1095: exp(-x) <= 1/x at x >= 64000."""
    cert = exp_threshold_certificate(mode="inv", x0=64000)
    assert cert.x0 == 64000 and cert.bound == sp.Rational(1, 64000)
    assert exp_threshold_certificate(mode="inv").x0 is None


# --- anti-phantom refusals (one test each) ----------------------------------

def test_refuses_rational_a_nonpositive():
    """THE audit phantom: a <= 0 makes the implication false at lam = 0."""
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="linear", Q="3", a="-1", scale=2)
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="log", Q="3", a="0", scale=2)


def test_refuses_rational_K_nonpositive():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="linear", Q="3", a="1", K="0", scale=2)


def test_refuses_nonpositive_scale():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="linear", Q="A", a="b", scale=0)
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="linear", Q="A", a="b", scale="-2")


def test_refuses_declared_threshold_mismatch_linear():
    """Q/a does not match the declared threshold: 3/(2 * 1/2) = 3, not 2."""
    with pytest.raises(ValueError, match="does not match"):
        exp_threshold_certificate(mode="linear", Q="3", a="1/2", scale=2, threshold="2")


def test_refuses_declared_threshold_mismatch_log():
    """log(max 1 Q)/a does not match a rational claim (log 5 / 6 is not 1/2)."""
    with pytest.raises(ValueError, match="does not match"):
        exp_threshold_certificate(mode="log", Q="5", a="3", scale=2, threshold="1/2")
    with pytest.raises(ValueError, match="does not match"):
        exp_threshold_certificate(mode="log", Q="Q", a="a", scale=2, threshold="log(Q)/(2*a)")


def test_refuses_strict_in_log_mode():
    with pytest.raises(ValueError, match="strict"):
        exp_threshold_certificate(mode="log", Q="Q", a="a", strict=True)


def test_refuses_unknown_mode_and_unknown_step_key():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="sinh", Q="Q", a="a")
    with pytest.raises(ValueError, match="unknown keys"):
        exp_threshold_certificate(mode="linear", steps=[dict(Q="Q", a="a", bogus=1)])


def test_refuses_floats_everywhere():
    with pytest.raises(ValueError, match="float"):
        exp_threshold_certificate(mode="linear", Q="3", a=0.5, scale=2)
    with pytest.raises(ValueError, match="float"):
        exp_threshold_certificate(mode="linear", Q="3", a=sp.Float(0.5), scale=2)
    with pytest.raises(ValueError, match="float"):
        exp_threshold_certificate(mode="linear", Q="3", a="1/2", scale=2, threshold=3.0)
    with pytest.raises(ValueError, match="float"):
        exp_threshold_certificate(mode="shifted_rate", c0=0.0, c1=1, r=1, r_prime=0)
    with pytest.raises(ValueError, match="float"):
        exp_threshold_certificate(mode="inv", x0=1.5)


def test_refuses_bad_symbol_names():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="linear", Q="2x", a="a")      # neither ident nor rational
    with pytest.raises(ValueError, match="reserved"):
        exp_threshold_certificate(mode="linear", Q="max", a="a")     # shadows the vocabulary
    with pytest.raises(ValueError, match="scale variable"):
        exp_threshold_certificate(mode="linear", Q="lam", a="a")     # named like lam
    with pytest.raises(ValueError, match="collide"):
        exp_threshold_certificate(mode="linear", Q="hK0", a="a", K="K")  # hypothesis-name clash


def test_refuses_every_block_local_name():
    """A symbol may not shadow ANY name the emitted bodies bind.

    The first collision set covered only the per-symbol positivity hypotheses, the
    guard and the per-step thresholds; the step and atom renderers also bind h1, h2,
    h3, hmax, hsplit and hx0.  Shadowing one of those would silently point the
    emitted proof at the wrong term, so each is refused at certify time.
    """
    for shadow in ("h1", "h2", "h3", "hmax", "hsplit", "hx0"):
        with pytest.raises(ValueError, match="collide"):
            exp_threshold_certificate(mode="linear", Q=shadow, a="a", K="K")
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="product", y="1y")
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(mode="linear", Q="Q", a="a", lam="2lam")


def test_refuses_bundling_an_atom():
    with pytest.raises(ValueError, match="standalone"):
        exp_threshold_certificate(mode="linear", steps=[dict(mode="product")])
    with pytest.raises(ValueError, match="standalone atom"):
        exp_threshold_certificate(mode="product", guard=True)
    with pytest.raises(ValueError, match="standalone atom"):
        exp_threshold_certificate(mode="inv", steps=[dict(Q="Q", a="a")])
    with pytest.raises(ValueError, match="takes no K"):
        exp_threshold_certificate(mode="product", K="2")


def test_refuses_empty_or_oversized_bundle_and_double_spec():
    with pytest.raises(ValueError, match="empty"):
        exp_threshold_certificate(mode="linear", steps=[])
    with pytest.raises(ValueError, match="arity"):
        exp_threshold_certificate(mode="linear",
                                  steps=[dict(Q=f"Q{i}", a=f"a{i}") for i in range(7)])
    with pytest.raises(ValueError, match="not both"):
        exp_threshold_certificate(mode="linear", Q="Q", a="a", steps=[dict(Q="Q", a="a")])


def test_refuses_inv_phantoms():
    with pytest.raises(ValueError, match="x0"):
        exp_threshold_certificate(mode="inv", x0=0)
    with pytest.raises(ValueError, match="x0"):
        exp_threshold_certificate(mode="inv", x0="-3")
    # e^-1 = 0.3678... > 1/3: a claimed bound BELOW 1/x0 is a false (and unprovable) claim
    with pytest.raises(ValueError, match="BELOW"):
        exp_threshold_certificate(mode="inv", x0=1, bound="1/3")
    with pytest.raises(ValueError, match="floor"):
        exp_threshold_certificate(mode="inv", bound="1/3")


def test_refuses_shifted_rate_phantoms():
    with pytest.raises(ValueError, match="r' ="):
        exp_threshold_certificate(mode="shifted_rate", c0=0, c1=1, r=1, r_prime=1)
    with pytest.raises(ValueError, match="r' ="):
        exp_threshold_certificate(mode="shifted_rate", c0=0, c1=1, r=1, r_prime=2)
    with pytest.raises(ValueError, match="below the certified minimum"):
        exp_threshold_certificate(mode="shifted_rate", c0="1", c1="3", r="2", r_prime="1/2", K="1")
    with pytest.raises(ValueError, match="below the certified minimum"):
        exp_threshold_certificate(mode="shifted_rate", c0=0, c1=1, r=1, r_prime=0, K="-1")


def test_certify_propagates_the_refusal():
    fam = _fam(dict(mode="linear", Q="3", a="-1", scale=2), name="bad")
    with pytest.raises(Exception, match="REFUSED"):
        certify(fam)


# --- emission: the tactic skeleton, pinned by substring ------------------------

def test_emit_e6bridge7_bundle_pins_the_hand_proof_skeleton():
    txt = _emit_text(_E6B7_BUNDLE, name="gaussian_dominance_thresholds")
    for line in (
        "theorem gaussian_dominance_thresholds (A eta K B M lam : ℝ)",
        "(heta0 : 0 < eta) (hK0 : 0 < K) (hM0 : 0 < M)",
        "(h : max 1 (max (A / (2 * eta * K)) (B / (2 * M * K))) ≤ lam) :",
        "1 ≤ lam ∧ A ≤ K * Real.exp (2 * lam * eta) ∧ B < K * Real.exp (2 * lam * M) := by",
        "have hlam1 : 1 ≤ lam := (le_max_left _ _).trans h",
        "have ht1 : A / (2 * eta * K) ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans h",
        "have ht2 : B / (2 * M * K) ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans h",
        "refine ⟨hlam1, ?_, ?_⟩",
        "· have h1 : A / K ≤ 2 * lam * eta := by",
        "rw [div_le_iff₀ hK0]",
        "have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * eta * K)).mp ht1",
        "have h2 : 2 * lam * eta + 1 ≤ Real.exp (2 * lam * eta) := Real.add_one_le_exp _",
        "have h3 : A / K ≤ Real.exp (2 * lam * eta) := by linarith",
        "rwa [div_le_iff₀ hK0, mul_comm] at h3",
        "have h3 : B / K < Real.exp (2 * lam * M) := by linarith",
        "rwa [div_lt_iff₀ hK0, mul_comm] at h3",
    ):
        assert line in txt, line
    assert txt.count("Real.add_one_le_exp _") == 2


def test_e6bridge7_skeleton_lines_are_verbatim_island_lines():
    """The emitted step blocks are the island's hexpeta / hexpM blocks with eta spelled out:
    every tactic line that does not mention the extracted-threshold name appears verbatim in
    E6Bridge7.lean (the audit's 'mirror the hand proof' contract, pinned to the source)."""
    src = _E6B7.read_text(encoding="utf-8")
    txt = _emit_text(_E6B7_BUNDLE).replace("eta", "η")
    for line in (
        "      rw [div_le_iff₀ hK0]",
        "    have h2 : 2 * lam * η + 1 ≤ Real.exp (2 * lam * η) := Real.add_one_le_exp _",
        "    have h3 : A / K ≤ Real.exp (2 * lam * η) := by linarith",
        "    rwa [div_le_iff₀ hK0, mul_comm] at h3",
        "    have h2 : 2 * lam * M + 1 ≤ Real.exp (2 * lam * M) := Real.add_one_le_exp _",
        "    have h3 : B / K < Real.exp (2 * lam * M) := by linarith",
        "    rwa [div_lt_iff₀ hK0, mul_comm] at h3",
        "max 1 (max (A / (2 * η * K)) (B / (2 * M * K)))",
    ):
        assert line in txt, f"emitted text lacks {line!r}"
        assert line in src, f"E6Bridge7.lean lacks {line!r}"


def test_emit_e6bridge14_log_step_is_the_island_lemma_verbatim():
    """le_exp_of_log_le: statement and every proof line appear verbatim in E6Bridge14.lean."""
    src = _E6B14.read_text(encoding="utf-8")
    txt = _emit_text(_E6B14_LOG, name="le_exp_of_log_le")
    for line in (
        "(h : Real.log (max 1 Q) / (2 * a) ≤ lam) :",
        "    Q ≤ Real.exp (2 * lam * a) := by",
        "  have hmax : 0 < max 1 Q := lt_max_of_lt_left one_pos",
        "  have h1 : Real.log (max 1 Q) ≤ 2 * lam * a := by",
        "    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp h",
        "    linarith",
        "  calc Q ≤ max 1 Q := le_max_right _ _",
        "    _ = Real.exp (Real.log (max 1 Q)) := (Real.exp_log hmax).symm",
        "    _ ≤ Real.exp (2 * lam * a) := Real.exp_le_exp.mpr h1",
    ):
        assert line in txt, f"emitted text lacks {line!r}"
        assert line in src, f"E6Bridge14.lean lacks {line!r}"


def test_emit_effective_threshold_bundle():
    txt = _emit_text(_E6B14_BUNDLE, name="effectiveThreshold_consequences")
    assert ("(h : max 1 (max (Real.log (max 1 Q1) / (2 * a1)) (Real.log (max 1 Q2) / (2 * a2))) "
            "≤ lam) :") in txt
    assert "1 ≤ lam ∧ Q1 ≤ Real.exp (2 * lam * a1) ∧ Q2 ≤ Real.exp (2 * lam * a2) := by" in txt
    # long extraction lines break before `:=` (E6Bridge14's hthr1 / hthr2 style), the
    # continuation two columns deeper than the `have`
    assert ("  have ht1 : Real.log (max 1 Q1) / (2 * a1) ≤ lam :=\n"
            "    ((le_max_left _ _).trans (le_max_right _ _)).trans h\n") in txt
    assert ("  have ht2 : Real.log (max 1 Q2) / (2 * a2) ≤ lam :=\n"
            "    ((le_max_right _ _).trans (le_max_right _ _)).trans h\n") in txt
    assert txt.count("have hmax : 0 < max 1 Q") == 2


def test_emit_linear_without_K_and_scale_one():
    txt = _emit_text(dict(mode="linear", Q="A", a="eta", scale=1))
    assert "(h : A / eta ≤ lam) :\n    A ≤ Real.exp (lam * eta) := by" in txt
    assert "have := (div_le_iff₀ (by positivity : (0 : ℝ) < eta)).mp h" in txt
    assert "have h2 : lam * eta + 1 ≤ Real.exp (lam * eta) := Real.add_one_le_exp _" in txt
    assert "mul_comm" not in txt  # nothing to clear


def test_emit_log_with_K_clears_K_after_the_calc():
    txt = _emit_text(dict(mode="log", Q="A", a="eta", K="K", scale=2))
    assert "(h : Real.log (max 1 (A / K)) / (2 * eta) ≤ lam) :" in txt
    assert "A ≤ K * Real.exp (2 * lam * eta) := by" in txt
    assert "have h3 : A / K ≤ Real.exp (2 * lam * eta) := by" in txt
    assert "rwa [div_le_iff₀ hK0, mul_comm] at h3" in txt


def test_emit_rational_instance_pins_literals_and_redecides_signs():
    txt = _emit_text(dict(mode="linear", Q="3", a="1/2", K="1", scale=2, threshold="3"))
    assert "(h : (3 : ℝ) / (2 * ((1 / 2) : ℝ) * (1 : ℝ)) ≤ lam) :" in txt
    assert "(3 : ℝ) ≤ (1 : ℝ) * Real.exp (2 * lam * ((1 / 2) : ℝ)) := by" in txt
    assert "have hK10 : (0 : ℝ) < (1 : ℝ) := by norm_num" in txt
    assert "(by positivity : (0 : ℝ) < 2 * ((1 / 2) : ℝ) * (1 : ℝ))" in txt
    # no symbolic binder besides lam
    assert "theorem t_inst (lam : ℝ)" in txt


def test_emit_product_atom_both_faces():
    txt = _emit_text(dict(mode="product"))
    assert "theorem t_inst (y : ℝ) : y * Real.exp (-y) ≤ 1 := by" in txt
    assert "rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]" in txt
    assert "theorem t_inst_comm (y : ℝ) : Real.exp (-y) * y ≤ 1 := by" in txt
    assert "rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]" in txt
    assert txt.count("linarith [Real.add_one_le_exp y]") == 2


def test_product_atom_lines_are_verbatim_island_lines():
    """bumpR_le (E6Bridge11.lean:910-925) and hexpkappa (E6Bridge12.lean:311-316)."""
    e11 = (_ROOT / "examples" / "rvm_bridge" / "lean" / "E6Bridge11.lean").read_text(encoding="utf-8")
    e12 = (_ROOT / "examples" / "rvm_bridge" / "lean" / "E6Bridge12.lean").read_text(encoding="utf-8")
    assert "rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]" in e11
    assert "rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]" in e12


def test_emit_inv_atom_both_faces():
    txt = _emit_text(dict(mode="inv"))
    assert "theorem t_inst (x : ℝ) (hx0 : 0 < x) : Real.exp (-x) ≤ 1 / x := by" in txt
    assert "exact inv_anti₀ hx0 (by linarith [Real.add_one_le_exp x])" in txt
    txt2 = _emit_text(dict(mode="inv", x0=64000))
    assert "(hx : (64000 : ℝ) ≤ x) : Real.exp (-x) ≤ ((1 / 64000) : ℝ) := by" in txt2
    assert "one_div_le_one_div_of_le (by norm_num) hx" in txt2
    assert "have h3 : 1 / (64000 : ℝ) ≤ ((1 / 64000) : ℝ) := by norm_num" in txt2


def test_emit_shifted_rate_atom():
    txt = _emit_text(dict(mode="shifted_rate", c0="1", c1="3", r="2", r_prime="1/2"))
    assert "(3 * y + 1) * Real.exp (-(2 * y)) ≤ 2 * Real.exp (-((1 / 2) * y)) := by" in txt
    assert "have hδ : 1 + (3 / 2) * y ≤ Real.exp ((3 / 2) * y) := by" in txt
    assert "mul_le_mul_of_nonneg_left hδ (by norm_num)" in txt
    assert "mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le" in txt
    assert "rw [← Real.exp_add]" in txt and "rw [mul_assoc, hsplit]" in txt


def test_emit_is_lint_clean_deterministic_and_honest():
    for spec in (_E6B7_BUNDLE, _E6B14_LOG, _E6B14_BUNDLE, dict(mode="product"),
                 dict(mode="inv", x0=64000), dict(mode="shifted_rate", c0=0, c1=1, r=1, r_prime=0)):
        txt = _emit_text(spec)
        assert txt == _emit_text(spec), "emission is not byte-deterministic"
        errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
        assert errs == [], errs
        assert "sorry" not in txt and "admit" not in txt and "decide" not in txt
        assert "conjecture1_proved = False" in txt
        assert "Real.add_one_le_exp" in txt
        for ch in txt:
            assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_theorem_counts():
    fam = exp_threshold_family(
        "Counts", GridSpec([("i", [0, 1, 2])]), lambda pt: f"c{pt['i']}",
        spec=lambda pt: [dict(mode="product"), _E6B7_BUNDLE, dict(mode="inv")][pt["i"]])
    report = emit(certify(fam), LeanProfile(namespace=("Counts",)), [ExpThresholdEmitter()],
                  ValidationReport(checks=(("x", True),)))
    assert report.n_theorems == 4  # product emits both faces


# --- the dogfood file ---------------------------------------------------------

def _load_generator():
    spec = importlib.util.spec_from_file_location("dogfood_exp_threshold", _DOGFOOD_GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_dogfood_file_is_regenerable_byte_for_byte():
    """The checked-in probe is exactly what the generator writes: banner + frozen emitter
    output + the kernel cross-checks -- the emitter cannot drift from the island file."""
    gen = _load_generator()
    assert gen.OUT == _DOGFOOD_LEAN
    assert _DOGFOOD_LEAN.is_file(), "run examples/rvm_bridge/dogfood_exp_threshold.py"
    assert _DOGFOOD_LEAN.read_text(encoding="utf-8") == gen.build_text()


def test_dogfood_file_regenerates_the_two_sites_under_new_names():
    txt = _DOGFOOD_LEAN.read_text(encoding="utf-8")
    assert txt.startswith("/-\n  Dogfood_exp_threshold")
    assert "conjecture1_proved = False" in txt and "Nothing here bears on RH" in txt
    assert "import E6Bridge7\nimport E6Bridge14" in txt
    assert "namespace DogfoodExpThreshold" in txt and "end DogfoodExpThreshold" in txt
    for nm in ("gaussian_dominance_thresholds", "le_exp_of_log_le_regen",
               "effectiveThreshold_consequences"):
        assert f"theorem {nm} " in txt
        assert f"#print axioms DogfoodExpThreshold.{nm}" in txt
    # the originals are consumed, never redefined
    assert "RvMBridge14.le_exp_of_log_le ha0 h" in txt
    assert "RvMBridge14.effectiveThreshold y0 xmin N B D ≤ lam" in txt
    assert "theorem le_exp_of_log_le " not in txt
    assert "sorry" not in txt and "admit" not in txt
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the dogfood file"

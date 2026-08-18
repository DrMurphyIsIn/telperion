"""Interval-bracket emitter: rigorous rational enclosures of transcendental constants.

Promotes exp_bracket's one-off template into a first-class Emitter for
two-sided rational enclosures  lo <= exp(-theta) <= hi  at a rational
point theta, via the CI-green Mathlib scaffold:

    UPPER (exp_neg_theta_le): Taylor lower bound on exp(theta) gives
        hi * Taylor_nterms(theta) - 1 >= 0  (Polya-certified)
    =>  1/Taylor <= hi  =>  exp(-theta) = 1/exp(theta) <= hi
    Lean tactics: Real.sum_le_exp_of_nonneg + one_div_le_one_div_of_le.

    LOWER (exp_neg_theta_ge): convexity companion  1 - theta <= exp(-theta)
    Lean tactics: Real.add_one_le_exp + linarith.

The rational Taylor heart is Polya-certified via certify(); the transcendental
wrapping is the emitted assembly.  Only func="exp" is implemented; func="log"
is deferred (no CI-verified Mathlib chain available to emit safely).

HONEST SCOPE: rigorous rational ENCLOSURES of transcendental constants.  This
does NOT close the g1 Real.log bridge (origin's G1Kernel owns it).
conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp

from .certify import CertifiedInstance, polya_certify
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _taylor(x: Fraction, nterms: int) -> Fraction:
    """Exact rational Taylor partial sum  sum_{k=0}^{nterms-1} x^k / k!"""
    s, term = Fraction(0), Fraction(1)
    for k in range(nterms):
        s += term
        term = term * x / (k + 1)
    return s


def _rat(q) -> sp.Rational:
    """Coerce a Fraction or int to sympy Rational."""
    if isinstance(q, Fraction):
        return sp.Rational(q.numerator, q.denominator)
    return sp.Rational(q)


@dataclass(frozen=True)
class BracketSpec:
    """A two-sided rational enclosure of exp(-theta) at a rational point theta.

    Fields:
        func      only "exp" is supported (func="log" deferred — no CI-safe chain).
        theta_num / theta_den   theta = theta_num / theta_den  (theta > 0)
        nterms    number of Taylor terms used (i.e. sum for i in range(nterms))
        hi_num / hi_den         HI = hi_num / hi_den >= exp(-theta)
        lo_num / lo_den         LO = lo_num / lo_den <= exp(-theta)  (LO = 1 - theta)
        tf_num / tf_den         TFLOOR = tf_num / tf_den <= Taylor_nterms(theta)
    """

    func: str
    theta_num: int
    theta_den: int
    nterms: int
    hi_num: int
    hi_den: int
    lo_num: int
    lo_den: int
    tf_num: int
    tf_den: int

    @property
    def theta(self) -> Fraction:
        return Fraction(self.theta_num, self.theta_den)

    @property
    def hi(self) -> Fraction:
        return Fraction(self.hi_num, self.hi_den)

    @property
    def lo(self) -> Fraction:
        return Fraction(self.lo_num, self.lo_den)

    @property
    def taylor_floor(self) -> Fraction:
        return Fraction(self.tf_num, self.tf_den)


def certify_bracket_point(family, pt, name):
    """Certify one bracket instance: (CertifiedInstance, n_checks).

    Retrieves the BracketSpec from family.bracket(pt), then EXACTLY verifies
    (in Fraction arithmetic) the three rational conditions that make the
    transcendental tactic sequence sound:

      (1)  taylor_floor  <=  Taylor_nterms(theta)
      (2)  hi * Taylor_nterms(theta) - 1  >=  0
               => 1/Taylor <= hi  => exp(-theta) = 1/exp(theta) <= 1/Taylor <= hi
      (3)  lo  ==  1 - theta   (the convexity companion)

    Condition (2) is also Polya-certified via polya_certify so the pipeline's
    certification machinery accepts it.  Raises ValueError (a refusal, the
    negative control) on any violation.
    """
    if family.kind != "bracket":
        raise ValueError(f"certify_bracket_point requires kind='bracket', got {family.kind!r}")

    spec = family.bracket(pt)
    if not isinstance(spec, BracketSpec):
        raise ValueError(f"family.bracket(pt) must return a BracketSpec, got {type(spec)}")
    if spec.func != "exp":
        raise NotImplementedError(
            f"func={spec.func!r} is not implemented; only func='exp' is supported. "
            "func='log' is deferred — no CI-verified Mathlib tactic chain is available."
        )

    theta = spec.theta
    hi = spec.hi
    lo = spec.lo
    tf = spec.taylor_floor

    # Check (1): taylor_floor is a valid lower bound on Taylor_nterms(theta)
    T = _taylor(theta, spec.nterms)
    if not (tf <= T):
        raise ValueError(
            f"REFUSED: taylor_floor ({tf}) > Taylor_{spec.nterms}({theta}) = {T}; "
            "the Taylor lower bound is not valid"
        )

    # Check (2): hi * taylor_floor - 1 >= 0.
    # The emitted Lean's final step proves `1/tf <= hi` (`hi` bounds `1/tf`,
    # and `tf <= exp(theta)` gives `1/exp(theta) <= 1/tf <= hi`).  That step
    # closes iff hi * tf >= 1 — using taylor_floor (tf), NOT the full Taylor
    # sum T.  Since tf <= T, checking hi*T here would be WEAKER than the Lean
    # requires: a spec with hi*T >= 1 but hi*tf < 1 would pass certification and
    # then fail `lake build`.  The gate must verify exactly what the proof needs.
    margin = hi * tf - Fraction(1)
    if margin < 0:
        raise ValueError(
            f"REFUSED: hi * taylor_floor - 1 = {float(margin):.6g} < 0; "
            f"hi={float(hi):.6g} cannot close `1/tf <= hi` "
            f"(tf={float(tf):.6g}) to upper-bound exp(-{float(theta):.6g})"
        )

    # Polya-certify the rational heart so the pipeline's certification logic is satisfied.
    # The margin is a positive rational constant (no symbols).
    margin_sym = _rat(margin)
    cert = polya_certify(margin_sym, syms=(), lift_max=0)

    # Check (3): lo must equal 1 - theta (the convexity companion identity)
    expected_lo = Fraction(1) - theta
    if lo != expected_lo:
        raise ValueError(
            f"REFUSED: lo = {lo} != 1 - theta = {expected_lo}; "
            "the lower bound must be the convexity companion (1 - theta)"
        )

    n_checks = 3  # taylor_floor valid, margin >= 0, lo identity
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(cert,),
        bracket=spec,
    )
    return inst, n_checks


# ---------------------------------------------------------------------------
# Lean template: the EXACT tactic sequence from the CI-green ExpBracket.lean.
# Substitution placeholders use «name» syntax; we render manually (not via
# lean.render()) so we can handle multi-theorem output cleanly.
# ---------------------------------------------------------------------------

_LE_TEMPLATE = """\
theorem {name}_le :
    Real.exp (-({theta_num} / {theta_den} : ℝ)) ≤ {hi_num} / {hi_den} := by
  rw [Real.exp_neg, ← one_div]
  have hlow : ({tf_num} / {tf_den} : ℝ) ≤ Real.exp ({theta_num} / {theta_den}) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) {nterms})
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < {tf_num} / {tf_den} := by norm_num
  calc 1 / Real.exp ({theta_num} / {theta_den})
      ≤ 1 / ({tf_num} / {tf_den} : ℝ) := one_div_le_one_div_of_le hpos hlow
    _ ≤ {hi_num} / {hi_den} := by norm_num
"""

_GE_TEMPLATE = """\
theorem {name}_ge :
    (1 - {theta_num} / {theta_den} : ℝ) ≤ Real.exp (-({theta_num} / {theta_den})) := by
  have h := Real.add_one_le_exp (-({theta_num} / {theta_den} : ℝ))
  linarith
"""


def _render_instance(lean_name: str, spec: BracketSpec) -> str:
    """Render the two theorems for one BracketSpec instance."""
    d = {
        "name": lean_name,
        "theta_num": str(spec.theta_num),
        "theta_den": str(spec.theta_den),
        "hi_num": str(spec.hi_num),
        "hi_den": str(spec.hi_den),
        "tf_num": str(spec.tf_num),
        "tf_den": str(spec.tf_den),
        "nterms": str(spec.nterms),
    }
    le_part = _LE_TEMPLATE.format(**d)
    ge_part = _GE_TEMPLATE.format(**d)
    return le_part + "\n" + ge_part


@dataclass
class IntervalBracketEmitter(Emitter):
    """Two theorems per instance (<name>_le and <name>_ge) from a BracketSpec.

    The tactic sequence is copied verbatim from the CI-green ExpBracket.lean:
      _le: Real.sum_le_exp_of_nonneg + one_div_le_one_div_of_le + norm_num
      _ge: Real.add_one_le_exp + linarith

    Only func='exp' is supported.  func='log' is deferred — no CI-verified
    Mathlib chain is available; emitting speculative Lean would be unsound."""

    def __post_init__(self):
        self.kind = "bracket"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts: list[str] = []
        for inst in fam.instances:
            spec = inst.bracket
            if not isinstance(spec, BracketSpec):
                raise ValueError(
                    f"instance {inst.lean_name!r} missing BracketSpec on .bracket"
                )
            parts.append(_render_instance(inst.lean_name, spec))
        return "\n".join(parts), 2 * len(fam.instances)


def bracket_family(
    name: str,
    grid,
    lean_name,
    spec,
    *,
    constants=None,
) -> InequalityFamily:
    """Convenience constructor for an interval-bracket family (kind='bracket').

    Args:
        name:       family name (string)
        grid:       GridSpec over the parameter axes
        lean_name:  callable  pt -> Lean theorem base name
        spec:       callable  pt -> BracketSpec  (the enclosure for that grid point)
        constants:  optional mapping of symbolic constants (forwarded to InequalityFamily)

    Returns an InequalityFamily with kind='bracket', ready for certify() -> emit().
    """
    if not callable(spec):
        raise ValueError("spec must be a callable pt -> BracketSpec")
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        bracket=spec,
        constants=constants or {},
    )

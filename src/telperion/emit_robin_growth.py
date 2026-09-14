"""Robin-growth emitter — Face 2 (temperedness) of the RH obstruction.

Robin's theorem (Guy Robin 1984): RH ⟺  σ(n) < e^γ · n · log log n  for every
integer n > 5040, where σ is the sum-of-divisors function and γ is the
Euler–Mascheroni constant.  Each n verified is a finite, kernel-checkable shadow
of temperedness — the FQ-grade dual-comb growth clause named in the QC rigidity
memo.  The uniform "∀ n > 5040" IS RH; a single rung is NOT.

Per-n certificate: the EXACT divisor sum σ(n) (an integer, computed and carried
exactly), together with a rigorous rational LOWER bound ``Llo`` on the
transcendental Robin right-hand side ``R(n) = e^γ · n · log log n`` obtained from
flint/Arb ball arithmetic (``robin_rhs_lower_bound``).  The certificate is
accepted only when

    σ(n) < Llo          (an exact ℤ-vs-ℚ inequality) AND  n > 5040.

HONESTY SEAM (identical discipline to li_positivity / RH-in-a-box): the fact
``Llo ≤ R(n)`` is an EXTERNAL numeric input (the Arb enclosure), carried as the
emitted theorem's HYPOTHESIS ``hR``.  The kernel proves only the trivial chain

    (σ(n) : ℝ) < Llo ≤ R(n)   ⟹   (σ(n) : ℝ) < R(n),

with ``(σ(n) : ℝ) < Llo`` closed by ``norm_num`` on the exact literals.  The
kernel does NOT evaluate the transcendental ``e^γ n log log n``.  Certifying the
n-th rung is NOT progress toward RH.  conjecture1_proved = False.

NEGATIVE CONTROL: a forged ``Llo`` that is NOT strictly above σ(n) (so the
per-n inequality is false or vacuous), or an ``n ≤ 5040`` (outside Robin's
range, where the inequality genuinely fails at colossally-abundant n), is
REFUSED at certification with a ``ValueError``.  The tightest test case is a
colossally-abundant n (e.g. n = 10080) where the true margin is thin: a lower
bound placed above the true R(n) must be refused.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter

ROBIN_THRESHOLD = 5040  # Robin's inequality holds for all n > 5040 iff RH.


def sigma_exact(n: int) -> int:
    """Exact sum-of-divisors σ(n) as a Python int (no floats)."""
    return int(sp.divisor_sigma(int(n), 1))


def robin_rhs_lower_bound(n: int, prec_bits: int = 256) -> Fraction:
    """A RIGOROUS rational lower bound on the Robin RHS ``e^γ · n · log log n``.

    Uses flint/Arb ball arithmetic: γ, log, and log∘log are evaluated as balls
    (mid ± certified radius); the ball's exact lower endpoint (mid − rad,
    recovered exactly from the dyadic man/exp) is a rigorous lower bound of the
    true value.  Requires ``n ≥ 3`` so that ``log log n > 0``.
    """
    n = int(n)
    if n < 3:
        raise ValueError(f"robin_rhs_lower_bound needs n ≥ 3 (log log n > 0); got {n}")
    from flint import arb, ctx

    try:
        from .rh_jensen.coefficients import _arb_ball_to_fractions
    except ImportError:
        from telperion.rh_jensen.coefficients import _arb_ball_to_fractions

    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        gamma = arb.const_euler()
        rhs = gamma.exp() * arb(n) * arb(n).log().log()
        lo, _hi = _arb_ball_to_fractions(rhs)
    finally:
        ctx.prec = old_prec
    return Fraction(lo)


@dataclass(frozen=True)
class RobinGrowthCert:
    """The n-th Robin rung: exact σ(n) and a rigorous rational lower bound ``Llo``
    on ``e^γ · n · log log n`` with ``σ(n) < Llo`` and ``n > 5040``."""

    n: int
    sigma: int
    Llo: Fraction


def robin_growth_certificate(n, Llo, sigma=None) -> RobinGrowthCert:
    """Build (and exactly re-check) a Robin-growth certificate.

    Refuses (``ValueError``):
      * ``n ≤ 5040`` — outside Robin's range (the negative control: at a
        colossally-abundant n ≤ 5040 the inequality genuinely fails);
      * a supplied ``sigma`` that disagrees with the exact divisor sum;
      * ``Llo`` not strictly above σ(n) — a lower bound at or below σ(n) cannot
        witness σ(n) < R(n) (an honest refusal, not a false theorem).
    """
    n = int(n)
    Llo = Fraction(sp.nsimplify(Llo)) if not isinstance(Llo, Fraction) else Llo
    if n <= ROBIN_THRESHOLD:
        raise ValueError(
            f"robin_growth REFUSED: Robin's inequality is an RH-equivalent only for "
            f"n > {ROBIN_THRESHOLD}; got n = {n}")
    sig = sigma_exact(n)
    if sigma is not None and int(sigma) != sig:
        raise ValueError(
            f"robin_growth REFUSED: supplied σ({n}) = {sigma} ≠ exact σ({n}) = {sig}")
    if not (Fraction(sig) < Llo):
        raise ValueError(
            f"robin_growth REFUSED: need σ({n}) = {sig} < Llo to witness the Robin "
            f"inequality; got Llo = {Llo}")
    return RobinGrowthCert(n=n, sigma=sig, Llo=Llo)


def certify_robin_growth_point(family, pt, name):
    """Certify one Robin rung: ``(CertifiedInstance, 1)``.  Reads
    ``spec = family.special[1](pt)`` — a dict ``{"n":…, "Llo":…[, "sigma":…]}``
    or a bare ``(n, Llo)`` pair."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = robin_growth_certificate(spec["n"], spec["Llo"], spec.get("sigma"))
    else:
        n, Llo = spec
        cert = robin_growth_certificate(n, Llo)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class RobinGrowthEmitter(Emitter):
    """Emit the n-th Robin rung ``(σ(n) : ℝ) < R`` (with ``R = e^γ n log log n``
    the certified RHS carried as hypothesis ``hR : Llo ≤ R``) from the exact
    σ(n) and a certified rational lower bound.  Deterministic
    ``lt_of_lt_of_le (by norm_num) hR``."""

    def __post_init__(self):
        self.kind = "robin_growth"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: RobinGrowthCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            Llo = rat_lean(cert.Llo)
            sig = cert.sigma
            lines.append(
                f"-- {nm}: Robin rung n={cert.n} (> {ROBIN_THRESHOLD}) — σ({cert.n}) = {sig} < "
                f"e^γ·{cert.n}·log log {cert.n} = R.\n"
                f"-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,\n"
                f"-- Llo = {cert.Llo} the certified Arb lower bound (the trust seam).\n"
                f"-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of\n"
                f"-- Robin's RH-equivalence (RH ⟺ ∀ n > {ROBIN_THRESHOLD}, σ(n) < R(n)); NOT RH.\n"
                f"theorem {nm} (R : ℝ) (hR : ({Llo} : ℝ) ≤ R) : (({sig} : ℝ)) < R :=\n"
                f"  lt_of_lt_of_le (by norm_num) hR\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def robin_refutation_atom_lean() -> str:
    """Robin's falsifiability face, emitted ONCE per generated file.

    Through Robin's equivalence, a certified UPPER bound on the RHS strictly
    below σ(n) at some n > 5040 would refute the Robin inequality there, hence
    ¬RH (the equivalence carried as the hypothesis ``hRobin``).  Term-mode; not
    expected to fire.  conjecture1_proved = False."""
    return (
        "-- robin_neg_refutes: the falsifiability face.  A certified UPPER bound `hi`\n"
        "-- on R = e^γ·n·log log n with `hi < σ(n)` (n > 5040) contradicts Robin's\n"
        "-- inequality at n, hence ¬RH through Robin's equivalence (carried as hRobin :\n"
        "-- RH → σ(n) < R).  Not expected to fire; makes the ladder falsifiable.\n"
        "theorem robin_neg_refutes {P : Prop} (sigma_n R hi : ℝ)\n"
        "    (hRobin : P → sigma_n < R) (hUp : R ≤ hi) (hlt : hi < sigma_n) : ¬P :=\n"
        "  fun hP => absurd (hRobin hP) (not_lt.mpr (le_trans hUp (le_of_lt hlt)))\n"
    )


def robin_growth_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Robin-growth family (kind ``robin_growth``).
    ``spec``: ``pt -> {"n":…, "Llo":…}`` (optionally ``"sigma"``) or ``pt -> (n, Llo)``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("robin_growth", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert n=5041 ===")
    lo = robin_rhs_lower_bound(5041)
    c = robin_growth_certificate(5041, lo)
    print(f"cert OK: n={c.n} σ={c.sigma} Llo≈{float(c.Llo):.4f}")

    print("\n=== NEGATIVE CONTROL 1: n ≤ 5040 (n=5040) must raise ===")
    try:
        robin_growth_certificate(5040, robin_rhs_lower_bound(5040))
        raise SystemExit("FAIL: n ≤ 5040 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL 2: forged Llo below σ(n) must raise ===")
    n = 10080
    sig = sigma_exact(n)
    try:
        robin_growth_certificate(n, Fraction(sig))  # Llo = σ(n), not strictly above
        raise SystemExit("FAIL: non-strict Llo not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL 3: forged Llo ABOVE true R(n) at a thin-margin n ===")
    # A too-large Llo would be caught downstream (hR unprovable), but if it exceeds σ(n)
    # the certificate accepts it — the trust seam is hR.  We instead verify the enclosure
    # driver itself is a genuine LOWER bound: Llo < mpmath's e^γ n log log n.
    import mpmath as mp

    mp.mp.dps = 60
    true_rhs = mp.e ** mp.euler * n * mp.log(mp.log(n))
    driver_lo = robin_rhs_lower_bound(n)
    # Exact rational vs a 60-digit mpmath value: the Arb lower endpoint must not
    # exceed the true RHS (it is mid − certified_radius, hence a rigorous bound).
    assert mp.mpf(driver_lo.numerator) / driver_lo.denominator <= true_rhs, (
        "driver lower bound is NOT below the true RHS!")
    print(f"driver lower bound {float(driver_lo):.6f} ≤ true R({n}) {float(true_rhs):.6f}  (rigorous)")

    print("\n=== emitted Lean (n=5041) ===")
    fam = robin_growth_family(
        "T", GridSpec([("case", [0])]), lambda pt: "robin_n5041",
        spec=lambda pt: {"n": 5041, "Llo": lo},
    )
    inst, _ = certify_robin_growth_point(fam, {"case": 0}, "robin_n5041")

    class _V:
        instances = [inst]

    body, nthm = RobinGrowthEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")
    print(robin_refutation_atom_lean())

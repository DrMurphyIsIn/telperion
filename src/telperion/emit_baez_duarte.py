"""Báez-Duarte emitter — Face 6 (spectral / approximation) of the RH obstruction.

The Nyman–Beurling–Báez-Duarte criterion: RH ⟺ d²_N → 0, where

    d²_N = inf_c ‖ 1 − Σ_{k=2}^{N} c_k · ρ_{1/k} ‖²_{L²(0,1)},   ρ_a(x) = {a/x},

the L²(0,1) distance from the constant 1 to the span of the dilated fractional
parts {(1/k)/x}.  A DECREASING certified upper-bound sequence d²_N ≤ U_N is
finite, kernel-checkable evidence of the spectral face (the Hilbert-space "Bragg
box").  The uniform d²_N → 0 IS RH; a single N is NOT.

Per-N certificate: an EXPLICIT rational coefficient vector c gives the quadratic
form value

    Q(c) = 1 − 2·Σ_k c_k·b_k + Σ_{j,k} c_j c_k·A_{jk},
    b_k = ∫₀¹ ρ_{1/k},   A_{jk} = ∫₀¹ ρ_{1/j} ρ_{1/k},

and since d²_N is an INFIMUM, d²_N ≤ Q(c) for every c.  The Gram/linear
integrals are computed RIGOROUSLY: on x ∈ (0,1) the integrand is piecewise
(a/x − m)(b/x − n) with elementary antiderivative
−ab/x − (a·n + b·m)·ln x + mn·x; we integrate exactly on [δ, 1] (finitely many
breakpoints a/m, b/m) and bound the tail [0, δ] by [0, δ] (the integrand lies in
[0,1)).  The ln-values are enclosed with flint/Arb.  This yields a rigorous
rational OUTER enclosure of each integral, hence a rigorous rational UPPER bound
``U`` on Q(c) ≥ d²_N.

HONESTY SEAM (Arb-trust class, like winding_box / li_positivity): the fact
``d²_N ≤ Uexact`` — combining the analytic inf-inequality with the certified
enclosure of Q(c) — is the EXTERNAL numeric input, carried as the emitted
theorem's hypothesis ``hval : dN2 ≤ Uexact``.  The kernel proves only the trivial
rounding ``Uexact ≤ U`` (norm_num) and chains ``dN2 ≤ Uexact ≤ U``.  Certifying
one N is NOT progress toward RH.  conjecture1_proved = False.

NEGATIVE CONTROL: a claimed upper bound ``U`` BELOW the certified enclosure's
own upper endpoint (so the bound is not actually established), or a degenerate N
< 2 / empty coefficient vector, is REFUSED at certification with a ``ValueError``.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

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


def _gram_integral_enclose(a: Fraction, b: Fraction, delta: Fraction,
                           prec_bits: int = 256) -> tuple[Fraction, Fraction]:
    """Rigorous rational OUTER enclosure (lo, hi) of ∫₀¹ {a/x}{b/x} dx.

    Exact on [δ, 1] via the piecewise antiderivative (rational part + a rational
    combination of ln(x) values, the ln values enclosed by flint/Arb); the tail
    [0, δ] is bounded by [0, δ] since 0 ≤ {a/x}{b/x} < 1.  Requires 0 < δ ≤ min(a,b)
    small enough (a, b ∈ (0, 1/2]).
    """
    from flint import arb, ctx

    try:
        from .rh_jensen.coefficients import _arb_ball_to_fractions
    except ImportError:
        from telperion.rh_jensen.coefficients import _arb_ball_to_fractions

    a = Fraction(a)
    b = Fraction(b)
    delta = Fraction(delta)
    # unified breakpoints a/m, b/m in [δ, 1]
    bset = {delta, Fraction(1)}
    for c in (a, b):
        m = 1
        while c / m >= delta:
            v = c / m
            if delta <= v <= 1:
                bset.add(v)
            m += 1
    pts = sorted(bset)
    rat = Fraction(0)
    ln_terms: list[tuple[Fraction, Fraction]] = []  # (coeff, x) meaning coeff·ln(x)
    for i in range(len(pts) - 1):
        p, q = pts[i], pts[i + 1]
        xm = (p + q) / 2
        m = int(a / xm)  # floor(a/x) constant on (p,q)
        n = int(b / xm)  # floor(b/x)
        # antiderivative F(x) = −ab/x − (a·n + b·m)·ln x + mn·x
        rat += (-(a * b) / q + m * n * q) - (-(a * b) / p + m * n * p)
        c = -(a * n + b * m)
        ln_terms.append((c, q))
        ln_terms.append((-c, p))
    # enclose the ln part rigorously with Arb
    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        lo_ln = Fraction(0)
        hi_ln = Fraction(0)
        for c, x in ln_terms:
            lnx = arb(x.numerator).log() - arb(x.denominator).log()  # ln(num)-ln(den)=ln(x)
            lx_lo, lx_hi = _arb_ball_to_fractions(lnx)
            if c >= 0:
                lo_ln += c * lx_lo
                hi_ln += c * lx_hi
            else:
                lo_ln += c * lx_hi
                hi_ln += c * lx_lo
    finally:
        ctx.prec = old_prec
    lo = rat + lo_ln            # tail ≥ 0 -> lower endpoint stays
    hi = rat + hi_ln + delta    # tail ≤ δ -> add to upper endpoint
    return (lo, hi)


def _linear_integral_enclose(a: Fraction, delta: Fraction,
                             prec_bits: int = 256) -> tuple[Fraction, Fraction]:
    """Rigorous enclosure of ∫₀¹ {a/x} dx = b_k (with a = 1/k).  Same machinery
    as the Gram entry with the second factor ≡ 1 (i.e. b ≡ 'infinite', floor 0):
    integrand is (a/x − m), antiderivative a·ln x + ... — reuse via a small direct
    computation."""
    from flint import arb, ctx

    try:
        from .rh_jensen.coefficients import _arb_ball_to_fractions
    except ImportError:
        from telperion.rh_jensen.coefficients import _arb_ball_to_fractions

    a = Fraction(a)
    delta = Fraction(delta)
    bset = {delta, Fraction(1)}
    m = 1
    while a / m >= delta:
        v = a / m
        if delta <= v <= 1:
            bset.add(v)
        m += 1
    pts = sorted(bset)
    rat = Fraction(0)
    ln_terms: list[tuple[Fraction, Fraction]] = []
    for i in range(len(pts) - 1):
        p, q = pts[i], pts[i + 1]
        xm = (p + q) / 2
        m = int(a / xm)
        # ∫ (a/x − m) dx = a·ln x − m·x
        rat += (-m * q) - (-m * p)
        ln_terms.append((a, q))
        ln_terms.append((-a, p))
    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        lo_ln = Fraction(0)
        hi_ln = Fraction(0)
        for c, x in ln_terms:
            lnx = arb(x.numerator).log() - arb(x.denominator).log()
            lx_lo, lx_hi = _arb_ball_to_fractions(lnx)
            if c >= 0:
                lo_ln += c * lx_lo
                hi_ln += c * lx_hi
            else:
                lo_ln += c * lx_hi
                hi_ln += c * lx_lo
    finally:
        ctx.prec = old_prec
    return (rat + lo_ln, rat + hi_ln + delta)


def baez_duarte_upper_bound(coeffs: dict[int, Fraction], delta: Fraction | None = None,
                            prec_bits: int = 256) -> tuple[Fraction, int]:
    """A RIGOROUS rational upper bound on d²_N ≤ Q(c) for the explicit coefficient
    vector ``coeffs`` (a dict k -> c_k, k ≥ 2).  Returns ``(Uexact, N)`` where N is
    max(k) and ``Uexact`` is the enclosure's UPPER endpoint of Q(c) (so
    d²_N ≤ Q(c) ≤ Uexact rigorously)."""
    ks = sorted(coeffs)
    if not ks or min(ks) < 2:
        raise ValueError("baez_duarte needs coefficients indexed by k ≥ 2")
    N = max(ks)
    if delta is None:
        delta = Fraction(1, 4) / N  # δ ≤ min(a) = 1/N, comfortably inside
    # Q(c) = 1 − 2 Σ c_k b_k + Σ_{j,k} c_j c_k A_{jk}; propagate outward enclosure.
    lo = Fraction(1)
    hi = Fraction(1)
    for k in ks:
        ck = coeffs[k]
        blo, bhi = _linear_integral_enclose(Fraction(1, k), delta, prec_bits)
        term_lo, term_hi = (-2 * ck * bhi, -2 * ck * blo) if ck >= 0 else (-2 * ck * blo, -2 * ck * bhi)
        lo += term_lo
        hi += term_hi
    for j in ks:
        for k in ks:
            cj, ck = coeffs[j], coeffs[k]
            Alo, Ahi = _gram_integral_enclose(Fraction(1, j), Fraction(1, k), delta, prec_bits)
            w = cj * ck  # sign of the weight sets which endpoint is the upper one
            if w >= 0:
                lo += w * Alo
                hi += w * Ahi
            else:
                lo += w * Ahi
                hi += w * Alo
    return (hi, N)


@dataclass(frozen=True)
class BaezDuarteCert:
    """The N-th Báez-Duarte rung: a rigorous rational upper bound ``U`` on d²_N,
    established by the coefficient vector ``coeffs`` (whose form value Q encloses to
    ``Uexact ≤ U``)."""

    N: int
    coeffs: tuple           # ((k, c_k), …)
    Uexact: Fraction        # certified enclosure upper endpoint of Q(c) ≥ d²_N
    U: Fraction             # readable rational bound emitted, Uexact ≤ U


def baez_duarte_certificate(coeffs, U=None, delta=None, prec_bits: int = 256) -> BaezDuarteCert:
    """Build (and exactly re-check) a Báez-Duarte rung certificate.

    ``coeffs``: dict k -> c_k (k ≥ 2).  ``U``: the readable rational bound to emit;
    defaults to ``Uexact``.  Refuses (``ValueError``): fewer than one coefficient /
    k < 2 (degenerate), or a supplied ``U`` BELOW the certified ``Uexact`` (the
    negative control — such a U is NOT actually established by the enclosure)."""
    coeffs = {int(k): (Fraction(sp.nsimplify(v)) if not isinstance(v, Fraction) else v)
              for k, v in dict(coeffs).items()}
    Uexact, N = baez_duarte_upper_bound(coeffs, delta=delta, prec_bits=prec_bits)
    if U is None:
        U = Uexact
    U = Fraction(sp.nsimplify(U)) if not isinstance(U, Fraction) else U
    if U < Uexact:
        raise ValueError(
            f"baez_duarte REFUSED: emitted bound U = {U} is below the certified "
            f"enclosure upper endpoint Uexact = {Uexact}; U is not established")
    return BaezDuarteCert(
        N=N, coeffs=tuple(sorted(coeffs.items())), Uexact=Uexact, U=U)


def certify_baez_duarte_point(family, pt, name):
    """Certify one Báez-Duarte rung.  Reads ``spec = family.special[1](pt)`` — a
    dict ``{"coeffs":{k:c_k}, "U":…}`` (U optional)."""
    spec = family.special[1](pt)
    cert = baez_duarte_certificate(spec["coeffs"], spec.get("U"), spec.get("delta"))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BaezDuarteEmitter(Emitter):
    """Emit the N-th Báez-Duarte rung ``dN2 ≤ U`` (with ``dN2`` the L²(0,1)
    infimum carried abstractly, hypothesis ``hval : dN2 ≤ Uexact`` the Arb-enclosed
    form value ≥ d²_N) from an explicit coefficient vector.  Deterministic
    ``le_trans hval (by norm_num)``."""

    def __post_init__(self):
        self.kind = "baez_duarte"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: BaezDuarteCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            Ue = rat_lean(cert.Uexact)
            U = rat_lean(cert.U)
            cvec = ", ".join(f"c_{k}={c}" for k, c in cert.coeffs)
            lines.append(
                f"-- {nm}: Báez-Duarte rung N={cert.N} — d²_N ≤ {cert.U}.\n"
                f"-- d²_N = inf_c ‖1 − Σ c_k·{{(1/k)/x}}‖²_{{L²(0,1)}} (RH ⟺ d²_N → 0).\n"
                f"-- Witnessing coefficient vector: {cvec}.  Its form value Q(c) ≥ d²_N is\n"
                f"-- Arb-enclosed to Uexact = {cert.Uexact} (the trust seam, hypothesis hval).\n"
                f"-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.\n"
                f"theorem {nm} (dN2 : ℝ) (hval : dN2 ≤ ({Ue} : ℝ)) : dN2 ≤ ({U} : ℝ) :=\n"
                f"  le_trans hval (by norm_num)\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def baez_duarte_refutation_atom_lean() -> str:
    """The Báez-Duarte falsifiability face, emitted ONCE per generated file.

    RH forces d²_N → 0; a certified persistent LOWER bound d²_N ≥ L with the RH
    tolerance ε ≤ L would refute RH (the equivalence carried as ``hRH``).
    Term-mode; not expected to fire.  conjecture1_proved = False."""
    return (
        "-- bd_neg_refutes: the falsifiability face.  RH forces d²_N → 0; a certified\n"
        "-- LOWER bound L ≤ d²_N with the RH-tolerance ε ≤ L contradicts d²_N < ε,\n"
        "-- hence ¬RH through the Báez-Duarte equivalence (carried as hRH : RH →\n"
        "-- d²_N < ε).  Not expected to fire; makes the sequence falsifiable.\n"
        "theorem bd_neg_refutes {P : Prop} (dN2 L eps : ℝ)\n"
        "    (hRH : P → dN2 < eps) (hLo : L ≤ dN2) (hbad : eps ≤ L) : ¬P :=\n"
        "  fun hP => absurd (hRH hP) (not_lt.mpr (le_trans hbad hLo))\n"
    )


def baez_duarte_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Báez-Duarte family (kind ``baez_duarte``).
    ``spec``: ``pt -> {"coeffs": {k: c_k}, "U": …}`` (U optional)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("baez_duarte", spec),
        constants=dict(constants or {}),
    )


def optimal_coeffs(N: int, prec_bits: int = 256) -> dict[int, Fraction]:
    """A near-optimal rational coefficient vector for the N-th rung, from solving
    the (numerically-computed) normal equations A c = b and rationalizing.  The
    RESULT feeds the RIGOROUS enclosure — its optimality is only a heuristic for a
    tight bound; the certificate's rigor comes from the exact enclosure of Q(c),
    not from c being the true minimizer."""
    import mpmath as mp

    old = mp.mp.dps
    try:
        mp.mp.dps = max(30, prec_bits // 6)
        ks = list(range(2, N + 1))
        d = Fraction(1, 4 * N)

        def _mid(pair):
            lo, hi = pair
            return (mp.mpf(lo.numerator) / lo.denominator + mp.mpf(hi.numerator) / hi.denominator) / 2

        def _num_gram(j, k):
            return _mid(_gram_integral_enclose(Fraction(1, j), Fraction(1, k), d, prec_bits))

        def _num_lin(k):
            return _mid(_linear_integral_enclose(Fraction(1, k), d, prec_bits))

        A = mp.matrix([[_num_gram(j, k) for k in ks] for j in ks])
        bvec = mp.matrix([_num_lin(k) for k in ks])
        c = mp.lu_solve(A, bvec)
        return {k: Fraction(str(mp.nstr(c[i], 12))).limit_denominator(10**6)
                for i, k in enumerate(ks)}
    finally:
        mp.mp.dps = old


if __name__ == "__main__":
    from fractions import Fraction as F

    print("=== positive cert N=4 (optimal-ish coeffs) ===")
    cs = optimal_coeffs(4)
    print("coeffs:", {k: str(v) for k, v in cs.items()})
    cert = baez_duarte_certificate(cs)
    print(f"cert OK: N={cert.N} Uexact≈{float(cert.Uexact):.6f}")

    print("\n=== decreasing sequence check (d²_N upper bounds should shrink) ===")
    for N in (2, 3, 4, 5):
        c = optimal_coeffs(N)
        ct = baez_duarte_certificate(c)
        print(f"N={N}: d²_N ≤ {float(ct.Uexact):.6f}")

    print("\n=== NEGATIVE CONTROL: U below the certified Uexact must raise ===")
    try:
        baez_duarte_certificate(cs, U=F(1, 1000))
        raise SystemExit("FAIL: too-small U not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL 2: degenerate (k<2) must raise ===")
    try:
        baez_duarte_certificate({1: F(1, 2)})
        raise SystemExit("FAIL: k<2 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean (N=4) ===")
    fam = baez_duarte_family(
        "T", GridSpec([("case", [0])]), lambda pt: "bd_N4",
        spec=lambda pt: {"coeffs": cs, "U": None},
    )
    inst, _ = certify_baez_duarte_point(fam, {"case": 0}, "bd_N4")

    class _V:
        instances = [inst]

    body, nthm = BaezDuarteEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")
    print(baez_duarte_refutation_atom_lean())

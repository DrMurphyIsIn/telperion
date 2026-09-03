"""Separable-convex extremum emitter — the extremum of a separable convex sum
on a fixed-sum box is at the homogeneous point (MIN) or a vertex (MAX).

For a separable objective ``Σᵢ φ(xᵢ)`` over the fixed-sum box slice

    {x : Σxᵢ = S,  lᵢ ≤ xᵢ ≤ uᵢ}

with ``φ`` CONVEX, the two extrema are structurally different (see
``proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md``, the vertex lemma and
the knee/kink discussion):

  * the MINIMUM is at the HOMOGENEOUS point ``xᵢ = S/n`` — this is Jensen, and it
    is EASY: ``n·φ(S/n) ≤ Σφ(xᵢ)`` for convex ``φ``.  It is exactly the
    tangent-line trick (``emit_tangent``): the tangent line ``L`` at ``a = S/n``
    under-estimates ``φ`` everywhere, so ``Σφ(xᵢ) ≥ ΣL(xᵢ) = n·φ(a)`` using
    ``Σxᵢ = S``.  The per-term surplus ``φ(x) − L(x)`` has a double root at ``a``
    and an EXACT RATIONAL sum-of-squares form, so each per-term inequality is the
    robust, search-free ``have … = Σcⱼ·bⱼ² := by ring; positivity`` and the whole
    claim assembles by ``linarith`` over the ``hᵢ`` and ``Σxᵢ = S``.

  * the MAXIMUM is at a VERTEX (all-but-one coordinate at a box bound) — this is
    the genuinely HARD direction, requiring the two-point spreading-exchange
    induction with the two-region (below-knee / above-knee) kink bookkeeping of
    the design doc.  **This emitter does NOT attempt the max/vertex direction**:
    the sum-preserving spreading-exchange induction (``glemma_spread`` /
    ``glemma_push_to_bound`` / ``vertex_bound_cons`` list induction) does not
    reduce to a search-free per-term SOS + ``linarith`` shape, so it is NOT a
    reliably-green single-instance certificate.  It is honestly reported as
    NAMED-OPEN below and in the module report.

So this emitter certifies the MIN / homogeneous direction only — a first-class,
reliably-green ``n·φ(S/n) ≤ Σφ(xᵢ)`` on the fixed-sum box.  Relative to the bare
``emit_tangent``, it additionally carries the BOX ``lᵢ ≤ xᵢ ≤ uᵢ`` in the
certificate (the design-doc slice) and emits the box hypotheses as binders — the
homogeneous point ``S/n`` must lie inside the box (else the bound is vacuous /
mis-stated), which is checked at certification.  The box hypotheses are present
but unused by ``linarith`` for the min direction (Jensen needs only the
sum-constraint); they scope the statement to the design-doc slice and set up the
vertex/max companion.

NEGATIVE CONTROL: a NON-CONVEX ``φ`` (surplus ``φ−L`` lacks a nonnegative rational
SOS form) is refused at certification with ``ValueError``.  Also refused: the
homogeneous point ``S/n`` outside the box ``[min lᵢ, max uᵢ]`` (mis-stated slice),
``n < 2``, or a linear ``φ``.

HONEST SCOPE: this proves ONLY the min/homogeneous face of the separable-convex
extremum problem.  The vertex/max face is named-open (heavy spreading-exchange
induction).  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import expr_lean, rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_separable_convex.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import expr_lean, rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# ---------------------------------------------------------------------------
# Exact univariate rational SOS (shared shape with emit_tangent; kept local so
# this module is self-contained and directly runnable).
# ---------------------------------------------------------------------------

def _univariate_rational_sos(p, x):
    """Exact rational SOS of a univariate ``p ≥ 0``: returns ``[(coeff, base),
    ...]`` with every ``coeff > 0`` rational and ``p = Σ coeff·base²``, or None
    when no such factorization exists (odd-multiplicity real root → sign change,
    or an irreducible factor of degree ≥ 3 → named-open Pourchet SOS).

    Same exact, sympy-only method as ``emit_tangent._univariate_rational_sos``:
    factor ``p`` over ℚ; a nonnegative ``p`` is a positive constant times even
    powers of real-linear factors and (any powers of) positive-definite
    irreducible quadratics, distributed term-by-term."""
    p = sp.expand(p)
    if p == 0:
        return None  # a constant-zero surplus is not a real bound
    const, facs = sp.factor_list(p)
    const = sp.nsimplify(const)
    if const <= 0:
        return None
    sos = [(const, sp.Integer(1))]  # const · 1²

    def _distribute(A, B):
        return [(sp.nsimplify(ca * cb), sp.expand(sa * sb))
                for ca, sa in A for cb, sb in B]

    for fac, mult in facs:
        fp = sp.Poly(fac, x)
        d = fp.degree()
        if d == 1:
            if mult % 2:
                return None  # odd-multiplicity real root → sign change
            fsos = [(sp.Integer(1), sp.expand(fac ** (mult // 2)))]
        elif d == 2:
            a2 = fp.coeff_monomial(x**2)
            a1 = fp.coeff_monomial(x)
            a0 = fp.coeff_monomial(1)
            if a2 <= 0 or a1**2 - 4 * a2 * a0 >= 0:
                return None  # not a positive-definite irreducible quadratic
            h = sp.Rational(-a1, 2 * a2)
            k = a0 - a2 * h**2
            base = [(a2, sp.expand(x - h)), (k, sp.Integer(1))]
            if mult % 2 == 0:
                fsos = [(sp.Integer(1), sp.expand(fac ** (mult // 2)))]
            else:
                carry = sp.expand(fac ** ((mult - 1) // 2))
                fsos = [(c, sp.expand(s * carry)) for c, s in base]
        else:
            return None  # irreducible degree ≥ 3: named-open
        sos = _distribute(sos, fsos)

    merged: dict = {}
    for c, base in sos:
        merged[base] = merged.get(base, sp.Integer(0)) + c
    return [(c, base) for base, c in merged.items() if c != 0]


# ---------------------------------------------------------------------------
# Certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SeparableConvexCertificate:
    """A verified separable-convex MIN (homogeneous-point) certificate.

    For a convex polynomial ``φ`` over the fixed-sum box slice
    ``{Σxᵢ = S, lᵢ ≤ xᵢ ≤ uᵢ}``, the minimum of ``Σφ(xᵢ)`` is the homogeneous
    value ``B = n·φ(S/n)`` (Jensen).  Certified by the tangent-line surplus
    ``φ(x) − L(x) = Σ coeff·base²`` at ``a = S/n`` (``L`` the tangent line),
    assembled by ``linarith`` with ``Σxᵢ = S``.  The box bounds are carried for
    scope (homogeneous point ``a`` lies inside) and emitted as binders; they are
    unused by ``linarith`` for this (min) direction.
    """

    n: int
    phi: sp.Expr
    x: sp.Symbol
    degree: int
    lowers: tuple            # (l₁, …, lₙ) rational lower box bounds
    uppers: tuple            # (u₁, …, uₙ) rational upper box bounds
    S: sp.Rational
    a: sp.Rational           # homogeneous / tangent point S/n
    slope: sp.Rational       # φ'(a)
    intercept: sp.Rational   # φ(a) − slope·a, so L(x) = intercept + slope·x
    B: sp.Rational           # n·φ(a) — the homogeneous minimum
    sos_terms: tuple         # ((coeff, base), ...): φ − L = Σ coeff·base²


def separable_convex_certificate(*, phi, x, n, S, box=None) -> SeparableConvexCertificate:
    """Build and EXACTLY self-check a separable-convex MIN certificate for a
    convex polynomial ``φ`` over the fixed-sum box ``{Σxᵢ = S, lᵢ ≤ xᵢ ≤ uᵢ}``.

    ``box`` is ``None`` (unbounded — the pure Jensen face) or a sequence of ``n``
    ``(lᵢ, uᵢ)`` rational pairs.  Refuses (``ValueError``): a non-convex ``φ``
    (surplus lacks a rational SOS — the negative control), a linear ``φ``,
    ``n < 2``, a box with ``lᵢ > uᵢ``, or the homogeneous point ``S/n`` outside
    the overall box range (mis-stated slice → vacuous bound)."""
    phi = sp.expand(sp.sympify(phi))
    S = sp.nsimplify(S)
    n = int(n)
    if n < 2:
        raise ValueError("separable-convex extremum needs n ≥ 2 terms")
    deg = sp.Poly(phi, x).degree()
    if deg < 2:
        raise ValueError(
            f"separable-convex needs a non-linear (curved) φ; got degree {deg}"
        )

    if box is None:
        lowers = tuple(sp.Integer(0) for _ in range(n))  # placeholder; not emitted
        uppers = tuple(sp.Integer(0) for _ in range(n))
        have_box = False
    else:
        box = list(box)
        if len(box) != n:
            raise ValueError(f"box must have n={n} (lᵢ,uᵢ) pairs; got {len(box)}")
        lowers = tuple(sp.nsimplify(lo) for lo, _ in box)
        uppers = tuple(sp.nsimplify(hi) for _, hi in box)
        for i in range(n):
            if lowers[i] > uppers[i]:
                raise ValueError(
                    f"REFUSED: box coordinate {i} has lᵢ={lowers[i]} > uᵢ={uppers[i]}"
                )
        have_box = True

    a = sp.Rational(S, n)
    if have_box:
        # homogeneous point must sit inside the overall box range, else the
        # slice is mis-stated and the "minimum at S/n" claim is vacuous.
        lo_all, hi_all = min(lowers), max(uppers)
        if not (lo_all <= a <= hi_all):
            raise ValueError(
                f"REFUSED: homogeneous point S/n = {a} lies outside the box range "
                f"[{lo_all}, {hi_all}] — mis-stated slice"
            )

    fa = phi.subs(x, a)
    m = sp.diff(phi, x).subs(x, a)
    intercept = sp.nsimplify(fa - m * a)
    slope = sp.nsimplify(m)
    B = sp.nsimplify(n * fa)
    fL = sp.expand(phi - (intercept + slope * x))
    sos = _univariate_rational_sos(fL, x)
    if sos is None:
        raise ValueError(
            "REFUSED: tangent surplus φ−L is not a certifiable rational SOS — φ is "
            "NOT convex (or its surplus has an irreducible factor of degree ≥ 3, "
            "named-open) — negative control"
        )
    # exact SOS self-check
    if sp.expand(fL - sum(c * base**2 for c, base in sos)) != 0:
        raise ValueError("separable-convex SOS self-check failed — certificate rejected")
    # exact assembly self-check: Σφ − B = Σ(φ−L) + slope·(Σx − S)
    xs = sp.symbols(f"x1:{n + 1}")
    lhs = sum(phi.subs(x, xi) for xi in xs) - B
    rhs = sum(fL.subs(x, xi) for xi in xs) + slope * (sum(xs) - S)
    if sp.expand(lhs - rhs) != 0:
        raise ValueError("separable-convex assembly self-check failed — certificate rejected")

    return SeparableConvexCertificate(
        n=n, phi=phi, x=x, degree=deg,
        lowers=lowers if have_box else (),
        uppers=uppers if have_box else (),
        S=S, a=a, slope=slope, intercept=intercept, B=B, sos_terms=tuple(sos),
    )


def certify_separable_convex_point(family, pt, name):
    """Certify one separable-convex MIN instance from
    ``family.special[1](pt) -> spec``.

    ``spec`` is ``((φ, x), n, S)`` or ``((φ, x), n, S, box)`` where ``box`` is a
    sequence of ``n`` ``(lᵢ, uᵢ)`` rational pairs (or ``None``).  Returns
    ``(CertifiedInstance, n)``."""
    spec = family.special[1](pt)
    (phi, x), n, S = spec[0], spec[1], spec[2]
    box = spec[3] if len(spec) > 3 else None
    cert = separable_convex_certificate(phi=phi, x=x, n=n, S=S, box=box)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, cert.n


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class SeparableConvexExtremumEmitter(Emitter):
    """Emit the separable-convex MIN (homogeneous-point) bound
    ``n·φ(S/n) ≤ Σφ(xᵢ)`` on the fixed-sum box — one theorem per instance,
    per-term surplus ``φ(xᵢ)−L(xᵢ) = Σcⱼ·bⱼ²`` by ``ring``+``positivity``,
    assembled by ``linarith`` over the ``hᵢ`` and the sum-constraint ``hsum``.

    The box bounds ``lᵢ ≤ xᵢ ≤ uᵢ`` are emitted as binders (the design-doc
    slice) but are unused by ``linarith`` for this direction — Jensen needs only
    ``Σxᵢ = S``.  The vertex/MAX direction is NAMED-OPEN (heavy spreading-exchange
    induction) and is NOT emitted."""

    def __post_init__(self):
        self.kind = "separable_convex"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: SeparableConvexCertificate = inst.payload  # type: ignore[assignment]
            n = cert.n
            x = cert.x
            have_box = bool(cert.lowers)

            def xi(i):
                return sp.Symbol(f"x{i}")

            def phi_at(i):
                return expr_lean(cert.phi.subs(x, xi(i)), (xi(i),))

            def L_at(i):
                return f"({rat_lean(cert.intercept)} + {rat_lean(cert.slope)} * x{i})"

            def sos_at(i):
                return " + ".join(
                    f"{rat_lean(c)} * ({expr_lean(sp.expand(base.subs(x, xi(i))), (xi(i),))})^2"
                    for c, base in cert.sos_terms
                )

            binders = " ".join(f"x{i}" for i in range(1, n + 1))
            hsum_lhs = " + ".join(f"x{i}" for i in range(1, n + 1))
            phiterms = " + ".join(f"({phi_at(i)})" for i in range(1, n + 1))

            # box hypotheses (scope to the design-doc slice; unused by linarith)
            box_hyps = ""
            if have_box:
                box_hyps = "".join(
                    f" (hlo{i} : ({rat_lean(cert.lowers[i-1])} : ℝ) ≤ x{i})"
                    f" (hhi{i} : x{i} ≤ {rat_lean(cert.uppers[i-1])})"
                    for i in range(1, n + 1)
                )

            haves = "".join(
                f"  have h{i} : (0:ℝ) ≤ ({phi_at(i)}) - {L_at(i)} := by\n"
                f"    have e{i} : ({phi_at(i)}) - {L_at(i)} = {sos_at(i)} := by ring\n"
                f"    rw [e{i}]; positivity\n"
                for i in range(1, n + 1)
            )
            hint_names = ", ".join(f"h{i}" for i in range(1, n + 1))

            note = (
                "-- Separable-convex MINIMUM at the homogeneous point S/n (Jensen); "
                "box bounds scope the slice.\n"
            )
            lines.append(
                note
                + f"theorem {inst.lean_name} ({binders} : ℝ){box_hyps} "
                f"(hsum : {hsum_lhs} = {rat_lean(cert.S)}) :\n"
                f"    ({rat_lean(cert.B)} : ℝ) ≤ {phiterms} := by\n"
                f"{haves}"
                f"  linarith [{hint_names}, hsum]\n"
            )
            nthm += 1
        return "".join(lines), nthm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def separable_convex_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a separable-convex MIN family (kind='separable_convex').

    ``spec``: a callable ``pt -> ((φ, x), n, S)`` or ``pt -> ((φ, x), n, S, box)``
    where ``φ`` is a convex polynomial (degree ≥ 2) in ``x``, ``n ≥ 2``, ``S`` the
    sum-constraint ``Σxᵢ = S``, and ``box`` an optional sequence of ``n``
    ``(lᵢ, uᵢ)`` rational bound-pairs.  Refuses (at certification) a non-convex φ,
    a linear φ, a box with ``lᵢ > uᵢ``, or a homogeneous point ``S/n`` outside the
    box range (no Lean for a non-member)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("separable_convex", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid certs, negative controls, print emitted Lean --------
    _x = sp.Symbol("x")

    print("=== positive: Jensen for squares, x1+x2+x3=3 on box [0,3]^3 => 3 <= Σx² ===")
    cert = separable_convex_certificate(
        phi=_x**2, x=_x, n=3, S=sp.Integer(3),
        box=[(0, 3), (0, 3), (0, 3)],
    )
    print(f"  cert OK: n={cert.n}, B={cert.B}, a={cert.a}, "
          f"{len(cert.sos_terms)} SOS term(s), box={bool(cert.lowers)}")

    print("\n=== positive: convex quartic φ=x⁴, x1+x2=2 on box [1/2,3/2]² => 2 <= Σx⁴ ===")
    cert2 = separable_convex_certificate(
        phi=_x**4, x=_x, n=2, S=sp.Integer(2),
        box=[(sp.Rational(1, 2), sp.Rational(3, 2)),
             (sp.Rational(1, 2), sp.Rational(3, 2))],
    )
    print(f"  cert OK: n={cert2.n}, B={cert2.B}, deg={cert2.degree}, box={bool(cert2.lowers)}")

    print("\n=== positive: unbounded (pure Jensen face) φ=2x²-3x+5, x1+x2=4 ===")
    cert3 = separable_convex_certificate(
        phi=2 * _x**2 - 3 * _x + 5, x=_x, n=2, S=sp.Integer(4), box=None,
    )
    print(f"  cert OK: n={cert3.n}, B={cert3.B}, box={bool(cert3.lowers)}")

    print("\n=== NEGATIVE CONTROL: NON-CONVEX φ=x³-x (surplus not SOS) — expect ValueError ===")
    try:
        separable_convex_certificate(
            phi=_x**3 - _x, x=_x, n=2, S=sp.Integer(0), box=None,
        )
        raise SystemExit("FAIL: non-convex φ was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: concave φ=-x² (surplus negative) — expect ValueError ===")
    try:
        separable_convex_certificate(
            phi=-_x**2, x=_x, n=2, S=sp.Integer(2), box=None,
        )
        raise SystemExit("FAIL: concave φ was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: homogeneous point outside box — expect ValueError ===")
    try:
        separable_convex_certificate(
            phi=_x**2, x=_x, n=2, S=sp.Integer(10),  # a = 5, box max 3
            box=[(0, 3), (0, 3)],
        )
        raise SystemExit("FAIL: mis-stated slice was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (three instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="sepconv_jensen_sq3",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="sepconv_quartic_box",
                          corners=(), payload=cert2),
        CertifiedInstance(point={"case": 2}, lean_name="sepconv_quad_unbounded",
                          corners=(), payload=cert3),
    ]

    class _View:
        instances = insts

    body, nthm = SeparableConvexExtremumEmitter().emit_body(
        _View(), LeanProfile(namespace=("SeparableConvex",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

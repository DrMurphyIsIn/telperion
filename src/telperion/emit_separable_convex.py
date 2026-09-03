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

  * the MAXIMUM is at a VERTEX (all-but-one coordinate at the common box bound
    ``u``, the last coordinate carrying the residual) — the genuinely
    STRUCTURAL direction.  The engine is the two-point spreading exchange
    ``φ(a) + φ(b) ≤ φ(a + b − u) + φ(u)`` (push one coordinate up to the bound,
    the other carries the excess), assembled by the vertex list-induction.  This
    is EXACTLY the proven, sorry-free development
    ``proof/formalization/R3Cert/VertexLemma.lean`` (``glemma_two_point_spread``)
    + ``VertexLemmaFull.lean`` (``glemma_spread`` / ``glemma_push_to_bound`` /
    ``sum_le_half_length`` / ``vertex_bound`` / ``vertex_bound_cons``), with the
    specific ``glemma`` family and cap ``1/2`` replaced by the certificate's
    convex polynomial ``φ`` and common upper bound ``u``.  This emitter
    PARAMETERIZES that proven structure in a ``mode="max"`` face — a fixed-``n``
    UNROLLED vertex bound (``n − 1`` push-to-bound exchanges chained, each an
    exact ``nlinarith`` fact ``φ(a) + φ(b) ≤ φ(a+b−u) + φ(u)`` from the box
    slacks ``0 ≤ u − a``, ``0 ≤ u − b``, per ``glemma_push_to_bound``), then the
    residual-substitution + ``nlinarith`` assembly.

So this emitter ships BOTH faces of the separable-convex extremum on the
fixed-sum box:

  * ``mode="min"`` (default): the homogeneous-point bound ``n·φ(S/n) ≤ Σφ(xᵢ)``
    (Jensen), search-free per-term SOS + ``linarith``.  Relative to the bare
    ``emit_tangent``, it additionally carries the BOX ``lᵢ ≤ xᵢ ≤ uᵢ`` in the
    certificate (the design-doc slice) and emits the box hypotheses as binders —
    the homogeneous point ``S/n`` must lie inside the box (else the bound is
    vacuous / mis-stated), which is checked at certification.  The box
    hypotheses are present but unused by ``linarith`` for the min direction.

  * ``mode="max"`` (vertex): the vertex bound
    ``Σφ(xᵢ) ≤ (n−1)·φ(u) + φ(S − (n−1)·u)`` over the UNIFORM box
    ``{Σxᵢ = S, l ≤ xᵢ ≤ u}`` (common ``l``, ``u``), the residual
    ``S − (n−1)·u`` required to lie in ``[l, u]`` (else the stated vertex is not
    a box member).  The per-pair push-to-bound exchange
    ``φ(a) + φ(b) ≤ φ(a+b−u) + φ(u)`` is the parameterized ``glemma_push_to_bound``;
    every exchange's two box slacks are ``linarith``-derivable from the box
    binders, so the chained proof is reliably green.  Restricted to convex
    polynomials of even degree ``≤ 6`` (the ``nlinarith`` per-pair exchange is
    empirically robust there; degree 8+ is named-open as the ``nlinarith`` hint
    set stops closing it).

NEGATIVE CONTROL: a NON-CONVEX ``φ`` is refused at certification with
``ValueError`` — for ``min`` because the tangent surplus ``φ−L`` lacks a
nonnegative rational SOS, for ``max`` because ``φ''`` lacks a nonnegative
rational SOS (convexity fails, so the spreading exchange is false).  Also
refused: ``min`` with the homogeneous point ``S/n`` outside the box (mis-stated
slice); ``max`` with a non-uniform box, a residual ``S − (n−1)·u`` outside
``[l, u]`` (the stated vertex is not a box member), or degree ``> 6`` /
odd-degree (named-open ``nlinarith`` range).  Also for both: ``n < 2`` or a
linear ``φ``.

HONEST SCOPE: both faces are exact, kernel-checkable single-instance
certificates.  The ``max`` face is a fixed-``n`` UNROLLED vertex bound (not the
general list induction of ``vertex_bound_cons`` — that stays in the proven Lean
development this parameterizes), restricted to convex even-degree-``≤6``
polynomials on a uniform box.  conjecture1_proved=False.
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


def _is_convex(phi, x) -> bool:
    """True iff ``φ`` is convex on ℝ, i.e. ``φ'' ≥ 0`` everywhere.

    A univariate polynomial is ``≥ 0`` everywhere iff it is the zero polynomial's
    complement — concretely: positive leading coefficient, even degree, and every
    real root of even multiplicity (an odd-multiplicity real root is a sign
    change).  Exact over ℚ via ``Poly.real_roots`` with multiplicity.  Returns
    False on a non-convex ``φ`` (the max-mode NEGATIVE CONTROL) and on a linear
    ``φ`` (``φ'' = 0``, no genuine curvature)."""
    d2 = sp.expand(sp.diff(phi, x, 2))
    if d2 == 0:
        return False  # linear φ — no curvature, not a genuine convex bound
    p = sp.Poly(d2, x)
    if p.degree() == 0:
        return sp.nsimplify(p.LC()) > 0  # constant φ'' (quadratic φ)
    if p.degree() % 2 == 1 or sp.nsimplify(p.LC()) < 0:
        return False
    from collections import Counter
    mult = Counter(p.real_roots())
    return all(m % 2 == 0 for m in mult.values())


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


@dataclass(frozen=True)
class SeparableConvexMaxCertificate:
    """A verified separable-convex MAX (vertex) certificate.

    For a convex polynomial ``φ`` (even degree ``≤ 6``) over the UNIFORM
    fixed-sum box ``{Σxᵢ = S, l ≤ xᵢ ≤ u}``, the maximum of ``Σφ(xᵢ)`` is the
    vertex value ``B = (n−1)·φ(u) + φ(residual)`` with ``residual = S − (n−1)·u``
    (push ``n−1`` coordinates to the common upper bound ``u``, the last carries
    the residual).  Certified by the chained push-to-bound exchanges
    ``φ(a) + φ(b) ≤ φ(a+b−u) + φ(u)`` (the parameterized
    ``VertexLemmaFull.glemma_push_to_bound``), each an exact ``nlinarith`` fact
    from the box slacks, then residual substitution + ``nlinarith`` assembly.
    ``residual ∈ [l, u]`` is enforced at certification (else the vertex is not a
    box member)."""

    n: int
    phi: sp.Expr
    x: sp.Symbol
    degree: int
    l: sp.Rational           # common lower box bound
    u: sp.Rational           # common upper box bound
    S: sp.Rational
    residual: sp.Rational    # S − (n−1)·u — the free coordinate at the vertex
    half_deg: int            # degree // 2 (drives the nlinarith hint set size)
    B: sp.Rational           # (n−1)·φ(u) + φ(residual) — the vertex maximum


def separable_convex_max_certificate(*, phi, x, n, S, box) -> SeparableConvexMaxCertificate:
    """Build and EXACTLY self-check a separable-convex MAX (vertex) certificate.

    ``box`` is a sequence of ``n`` ``(lᵢ, uᵢ)`` rational pairs that MUST be
    uniform (a common ``(l, u)``).  Refuses (``ValueError`` — the negative
    control): a non-convex ``φ`` (``φ''`` lacks a rational SOS), a linear ``φ``,
    ``n < 2``, an odd or ``> 6`` degree (outside the robust ``nlinarith`` range),
    a non-uniform box, ``l > u``, or a residual ``S − (n−1)·u`` outside
    ``[l, u]`` (the stated vertex is not a box member — mis-stated slice)."""
    phi = sp.expand(sp.sympify(phi))
    S = sp.nsimplify(S)
    n = int(n)
    if n < 2:
        raise ValueError("separable-convex vertex extremum needs n ≥ 2 terms")
    deg = sp.Poly(phi, x).degree()
    if deg < 2:
        raise ValueError(
            f"separable-convex (max) needs a non-linear (curved) φ; got degree {deg}"
        )
    if deg % 2 == 1 or deg > 6:
        raise ValueError(
            f"REFUSED: max/vertex mode is restricted to even degree ≤ 6 (the robust "
            f"nlinarith per-pair exchange range); got degree {deg} — named-open"
        )
    if not _is_convex(phi, x):
        raise ValueError(
            "REFUSED: φ'' takes negative values — φ is NOT convex, so the "
            "spreading-exchange (φ(a)+φ(b) ≤ φ(a+b−u)+φ(u)) is FALSE — negative control"
        )

    box = list(box)
    if len(box) != n:
        raise ValueError(f"box must have n={n} (lᵢ,uᵢ) pairs; got {len(box)}")
    lowers = tuple(sp.nsimplify(lo) for lo, _ in box)
    uppers = tuple(sp.nsimplify(hi) for _, hi in box)
    l, u = lowers[0], uppers[0]
    if any(ll != l for ll in lowers) or any(uu != u for uu in uppers):
        raise ValueError(
            "REFUSED: max/vertex mode needs a UNIFORM box (a common (l,u) across "
            "coordinates — the common bound the spreading exchange pushes to)"
        )
    if l > u:
        raise ValueError(f"REFUSED: box has l={l} > u={u}")

    residual = sp.nsimplify(S - (n - 1) * u)
    if not (l <= residual <= u):
        raise ValueError(
            f"REFUSED: residual S − (n−1)·u = {residual} lies outside the box "
            f"[{l}, {u}] — the stated vertex is not a box member (mis-stated slice)"
        )

    fu = phi.subs(x, u)
    fres = phi.subs(x, residual)
    B = sp.nsimplify((n - 1) * fu + fres)

    # exact assembly self-check: the chained push-to-bound exchanges telescope to
    # Σφ(xᵢ) ≤ B when Σxᵢ = S.  Verify the exact per-pair surplus identity
    # φ(a+b−u)+φ(u)−φ(a)−φ(b) = (u−a)(u−b)·Q with Q ≥ 0 on the box (⇐ convexity),
    # and that the telescoped vertex value equals B at Σxᵢ = S.
    a_, b_ = sp.symbols("a_ b_")
    surplus = sp.expand(
        phi.subs(x, a_ + b_ - u) + fu - phi.subs(x, a_) - phi.subs(x, b_)
    )
    q = sp.cancel(surplus / ((u - a_) * (u - b_)))
    if sp.expand(surplus - (u - a_) * (u - b_) * q) != 0:
        raise ValueError("separable-convex-max surplus factorization self-check failed")
    # symbolic telescope: Σφ(xᵢ) − B = Σ per-pair surpluses (all ≥ 0) with the
    # running free coordinate carrying the residual; verify the endpoint value.
    xs = sp.symbols(f"x1:{n + 1}")
    # push x2..xn to u one at a time; running low coordinate r starts at x1.
    r = xs[0]
    total_surplus = sp.Integer(0)
    for k in range(1, n):
        # exchange (r, x_{k+1}) -> (r + x_{k+1} - u, u)
        s_k = sp.expand(
            phi.subs(x, r + xs[k] - u) + fu - phi.subs(x, r) - phi.subs(x, xs[k])
        )
        total_surplus += s_k
        r = sp.expand(r + xs[k] - u)
    # after n−1 pushes: r = Σxᵢ − (n−1)u ; Σφ(xᵢ) + total_surplus = (n−1)φ(u) + φ(r)
    lhs = sum(phi.subs(x, xi) for xi in xs) + total_surplus
    rhs = (n - 1) * fu + phi.subs(x, r)
    if sp.expand(lhs - rhs) != 0:
        raise ValueError("separable-convex-max telescope self-check failed")
    # and at Σxᵢ = S the endpoint φ(r) = φ(residual), so rhs = B.
    r_at_S = sp.nsimplify(S - (n - 1) * u)
    if sp.expand(((n - 1) * fu + phi.subs(x, r_at_S)) - B) != 0:
        raise ValueError("separable-convex-max endpoint value self-check failed")

    return SeparableConvexMaxCertificate(
        n=n, phi=phi, x=x, degree=deg, l=l, u=u, S=S,
        residual=residual, half_deg=deg // 2, B=B,
    )


def certify_separable_convex_point(family, pt, name):
    """Certify one separable-convex instance from ``family.special[1](pt) -> spec``.

    ``spec`` selects the FACE by an optional trailing ``mode`` field:

      * MIN (default): ``((φ, x), n, S)`` or ``((φ, x), n, S, box)`` — the
        homogeneous-point bound; ``box`` is a sequence of ``n`` ``(lᵢ, uᵢ)``
        pairs (or ``None``).
      * MAX (vertex): ``((φ, x), n, S, box, "max")`` — the vertex bound over the
        uniform ``box``.

    Returns ``(CertifiedInstance, n_theorems)``."""
    spec = family.special[1](pt)
    (phi, x), n, S = spec[0], spec[1], spec[2]
    box = spec[3] if len(spec) > 3 else None
    mode = spec[4] if len(spec) > 4 else "min"
    if mode == "max":
        cert = separable_convex_max_certificate(phi=phi, x=x, n=n, S=S, box=box)
    else:
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
    slice) but are unused by ``linarith`` for the MIN direction — Jensen needs
    only ``Σxᵢ = S``.

    The MAX / vertex direction (``mode="max"`` certificate) emits the vertex
    bound ``Σφ(xᵢ) ≤ (n−1)·φ(u) + φ(S−(n−1)·u)`` over the uniform box: ``n − 1``
    chained push-to-bound exchanges ``φ(a)+φ(b) ≤ φ(a+b−u)+φ(u)`` (each an
    ``nlinarith`` fact seeded by the box slacks, per the proven
    ``VertexLemmaFull.glemma_push_to_bound``), residual substitution, then an
    ``nlinarith`` assembly.  Here the box binders ARE load-bearing (every
    exchange's slacks are ``linarith``-derived from them)."""

    def __post_init__(self):
        self.kind = "separable_convex"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            if isinstance(inst.payload, SeparableConvexMaxCertificate):
                block, k = self._emit_max_instance(inst)
            else:
                block, k = self._emit_min_instance(inst)
            lines.append(block)
            nthm += k
        return "".join(lines), nthm

    def _emit_min_instance(self, inst) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in (inst,):
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

    def _emit_max_instance(self, inst) -> tuple[str, int]:
        """Emit one separable-convex MAX (vertex) theorem — the fixed-``n``
        UNROLLED parameterization of the proven ``vertex_bound`` push-to-bound
        chain (``VertexLemmaFull``), with ``glemma`` replaced by the convex
        polynomial ``φ`` and the cap ``1/2`` by the common upper bound ``u``."""
        cert: SeparableConvexMaxCertificate = inst.payload  # type: ignore[assignment]
        n = cert.n
        x = cert.x
        u = cert.u
        l = cert.l
        m = cert.half_deg  # degree // 2

        # φ's rational monomials, once — used to render φ(<Lean atom>) WITHOUT
        # expanding the atom (so the final low coordinate stays a rewrite target).
        phi_poly = sp.Poly(cert.phi, x)
        phi_terms = sorted(
            ((int(mono[0]), sp.Rational(coeff))
             for mono, coeff in zip(phi_poly.monoms(), phi_poly.coeffs())
             if coeff != 0),
            key=lambda t: t[0],
        )

        def phi_at_str(atom: str) -> str:
            """φ rendered at a Lean expression string ``atom`` (kept UNexpanded)."""
            parts = []
            for deg, c in phi_terms:
                if deg == 0:
                    parts.append(rat_lean(c))
                elif deg == 1:
                    parts.append(f"{rat_lean(c)} * ({atom})")
                else:
                    parts.append(f"{rat_lean(c)} * ({atom})^{deg}")
            return " + ".join(parts) if parts else "0"

        xs = sp.symbols(f"x1:{n + 1}")
        binders = " ".join(f"x{i}" for i in range(1, n + 1))
        hsum_lhs = " + ".join(f"x{i}" for i in range(1, n + 1))
        box_hyps = "".join(
            f" (hlo{i} : ({rat_lean(l)} : ℝ) ≤ x{i}) (hhi{i} : x{i} ≤ {rat_lean(u)})"
            for i in range(1, n + 1)
        )
        phiterms = " + ".join(f"({phi_at_str(f'x{i}')})" for i in range(1, n + 1))
        phi_u = rat_lean(cert.phi.subs(x, u))

        def exchange_hints(a_str: str, b_str: str) -> str:
            """nlinarith hints for φ(a)+φ(b) ≤ φ(a+b−u)+φ(u): the box-slack product
            times the pairwise even SOS bases (a^j ± b^j)², j = 1..m−1 (mirrors
            the ``(1/2−a)(1/2−b) ≥ 0`` product feeding ``glemma_push_to_bound``)."""
            slack_a = f"(by linarith : (0:ℝ) ≤ {rat_lean(u)} - ({a_str}))"
            slack_b = f"(by linarith : (0:ℝ) ≤ {rat_lean(u)} - ({b_str}))"
            base = f"mul_nonneg {slack_a} {slack_b}"
            hints = [base]
            for j in range(1, m):
                aj = f"({a_str})^{j}" if j > 1 else f"({a_str})"
                bj = f"({b_str})^{j}" if j > 1 else f"({b_str})"
                hints.append(f"mul_nonneg ({base}) (sq_nonneg ({aj} + {bj}))")
                hints.append(f"mul_nonneg ({base}) (sq_nonneg ({aj} - {bj}))")
            return ",\n               ".join(hints)

        # chained push-to-bound exchanges: running low coordinate (a Lean STRING,
        # kept unexpanded) starts at x1; each step pushes the next coord to u.
        haves: list[str] = []
        r_str = "x1"
        ename: list[str] = []
        for k in range(1, n):
            a_str = r_str
            b_str = f"x{k + 1}"
            low_next = f"({a_str}) + {b_str} - {rat_lean(u)}"
            lhs = f"({phi_at_str(a_str)}) + ({phi_at_str(b_str)})"
            rhs = f"({phi_at_str(low_next)}) + ({phi_u})"
            nm = f"e{k}"
            ename.append(nm)
            haves.append(
                f"  have {nm} : {lhs} ≤ {rhs} := by\n"
                f"    nlinarith [{exchange_hints(a_str, b_str)}]\n"
            )
            r_str = low_next

        # r_str is now (Σxᵢ − (n−1)·u) as an unexpanded atom; rewrite it to the
        # residual constant inside the last exchange, simplify, and assemble.
        last = ename[-1]
        hres = (
            f"  have hres : ({r_str}) = {rat_lean(cert.residual)} := by linarith\n"
        )
        rw_and_simp = (
            f"  rw [hres] at {last}\n"
            f"  norm_num at {last}\n"
        )
        assembly = f"  linarith [{', '.join(ename)}]\n"

        note = (
            "-- Separable-convex MAXIMUM at the VERTEX (push n−1 coords to the common "
            "bound u; last carries the residual).\n"
            "-- Parameterizes the proven VertexLemmaFull.glemma_push_to_bound "
            "spreading exchange + vertex_bound chain.\n"
        )
        body = (
            note
            + f"theorem {inst.lean_name} ({binders} : ℝ){box_hyps} "
            f"(hsum : {hsum_lhs} = {rat_lean(cert.S)}) :\n"
            f"    {phiterms} ≤ ({rat_lean(cert.B)} : ℝ) := by\n"
            + "".join(haves)
            + hres
            + rw_and_simp
            + assembly
        )
        return body, 1


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
    """Build a separable-convex family (kind='separable_convex') — MIN or MAX face.

    ``spec``: a callable ``pt -> ((φ, x), n, S[, box[, mode]])`` where ``φ`` is a
    convex polynomial (degree ≥ 2) in ``x``, ``n ≥ 2``, ``S`` the sum-constraint
    ``Σxᵢ = S``, ``box`` an optional sequence of ``n`` ``(lᵢ, uᵢ)`` rational
    bound-pairs, and ``mode`` optionally ``"max"`` (vertex face) vs the default
    ``"min"`` (homogeneous face).

      * MIN: refuses a non-convex φ, a linear φ, a box with ``lᵢ > uᵢ``, or a
        homogeneous point ``S/n`` outside the box range.
      * MAX: refuses a non-convex φ, a linear φ, an odd or ``> 6`` degree, a
        non-uniform box, or a residual ``S − (n−1)·u`` outside ``[l, u]`` (the
        stated vertex is not a box member)."""
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

    # ---- MAX / vertex mode --------------------------------------------------
    print("\n=== positive (MAX): φ=x², n=3, S=6 on box [0,3]³ => Σx² <= 18 (vertex) ===")
    certM1 = separable_convex_max_certificate(
        phi=_x**2, x=_x, n=3, S=sp.Integer(6),
        box=[(0, 3), (0, 3), (0, 3)],
    )
    print(f"  cert OK: n={certM1.n}, u={certM1.u}, residual={certM1.residual}, "
          f"B(max)={certM1.B}")

    print("\n=== positive (MAX): convex quartic φ=x⁴, n=3, S=5 on box [0,2]³ "
          "=> Σx⁴ <= 33 (vertex) ===")
    certM2 = separable_convex_max_certificate(
        phi=_x**4, x=_x, n=3, S=sp.Integer(5),
        box=[(0, 2), (0, 2), (0, 2)],
    )
    print(f"  cert OK: n={certM2.n}, deg={certM2.degree}, residual={certM2.residual}, "
          f"B(max)={certM2.B}")

    print("\n=== positive (MAX): degree-6 φ=x⁶+x², n=2, S=3 on box [1,2]² "
          "=> Σφ <= vertex ===")
    certM3 = separable_convex_max_certificate(
        phi=_x**6 + _x**2, x=_x, n=2, S=sp.Integer(3),
        box=[(1, 2), (1, 2)],
    )
    print(f"  cert OK: n={certM3.n}, deg={certM3.degree}, residual={certM3.residual}, "
          f"B(max)={certM3.B}")

    print("\n=== NEGATIVE CONTROL (MAX): NON-CONVEX φ=x⁴-4x² "
          "(φ'' sign-changes) — expect ValueError ===")
    try:
        separable_convex_max_certificate(
            phi=_x**4 - 4 * _x**2, x=_x, n=3, S=sp.Integer(5),
            box=[(0, 2), (0, 2), (0, 2)],
        )
        raise SystemExit("FAIL: non-convex φ was NOT refused (max)")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL (MAX): residual outside box "
          "(S too small) — expect ValueError ===")
    try:
        separable_convex_max_certificate(
            phi=_x**2, x=_x, n=3, S=sp.Integer(2),  # residual = 2 - 6 = -4 ∉ [0,3]
            box=[(0, 3), (0, 3), (0, 3)],
        )
        raise SystemExit("FAIL: bad residual was NOT refused (max)")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL (MAX): non-uniform box — expect ValueError ===")
    try:
        separable_convex_max_certificate(
            phi=_x**2, x=_x, n=2, S=sp.Integer(3),
            box=[(0, 2), (0, 3)],
        )
        raise SystemExit("FAIL: non-uniform box was NOT refused (max)")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL (MAX): odd degree φ=x³ — expect ValueError ===")
    try:
        separable_convex_max_certificate(
            phi=_x**3, x=_x, n=2, S=sp.Integer(2),
            box=[(0, 2), (0, 2)],
        )
        raise SystemExit("FAIL: odd degree was NOT refused (max)")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (three MIN + three MAX instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="sepconv_jensen_sq3",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="sepconv_quartic_box",
                          corners=(), payload=cert2),
        CertifiedInstance(point={"case": 2}, lean_name="sepconv_quad_unbounded",
                          corners=(), payload=cert3),
        CertifiedInstance(point={"case": 3}, lean_name="sepconv_max_sq3",
                          corners=(), payload=certM1),
        CertifiedInstance(point={"case": 4}, lean_name="sepconv_max_quartic",
                          corners=(), payload=certM2),
        CertifiedInstance(point={"case": 5}, lean_name="sepconv_max_deg6",
                          corners=(), payload=certM3),
    ]

    class _View:
        instances = insts

    body, nthm = SeparableConvexExtremumEmitter().emit_body(
        _View(), LeanProfile(namespace=("SeparableConvex",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

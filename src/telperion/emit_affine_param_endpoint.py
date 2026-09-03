"""BG SCLStep "affine-in-parameter endpoint" emitter — the price-interval collapse.

In the Brualdi–Goldwasser proof the value functional ``bV μ b = bell b + μ·bY b``
is AFFINE in the price ``μ``, and the SCL obligation is

    bV μ (node cs) ≤ bV μ cherry     for all μ in I = [456/3703, 3/7].

Because the gap

    G(μ) = [bell(node cs) − bell cherry] + μ·[bY(node cs) − bY cherry]
         = A + μ·B

is AFFINE in μ, it is ``≥ 0`` on ``[lo,hi]`` IFF it is ``≥ 0`` at the two
endpoints.  The load-bearing identity is

    (hi − lo)·(A + μ·B) = (hi − μ)·(A + lo·B) + (μ − lo)·(A + hi·B),

both summands nonnegative when ``lo ≤ μ ≤ hi`` and both endpoint values are
``≥ 0``.  This COLLAPSES the price-continuum ``I`` to the two rational checks
``μ = 456/3703`` and ``μ = 3/7``.

HONEST SCOPE.  This emitter reduces an AFFINE-in-parameter interval inequality
to its two endpoints — for SCLStep it collapses the price interval ``I`` to two
rational endpoint checks.  It does NOT prove the endpoint inequalities
themselves (``bell``/``bY`` are opaque function arguments), nor the affinity of
``bV`` (that is an input hypothesis).  The emitted file is self-contained
(only ``import Mathlib``; ``bell``/``bY`` appear as abstract ``α → ℝ`` maps).

conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# ---- the real SCLStep price interval I = [456/3703, 3/7] ---------------------
_I_LO = sp.Rational(456, 3703)
_I_HI = sp.Rational(3, 7)


def _lean_rat(q) -> str:
    """Render an exact rational as a Lean ℝ literal fragment (n or n/d)."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"{q.p}"
    return f"{q.p}/{q.q}"


@dataclass(frozen=True)
class AffineParamEndpointCertificate:
    """A verified affine-in-parameter endpoint-collapse certificate.

    The gap ``G(μ) = A + μ·B`` is affine in the price ``μ`` (checked exactly:
    degree ``≤ 1`` in μ — a μ² or higher term is REFUSED), and both endpoint
    values ``A + lo·B`` and ``A + hi·B`` are ``≥ 0`` (a negative endpoint is
    REFUSED).  ``mu_test`` is a specific rational in ``[lo,hi]`` at which the
    concrete sanity ``example`` is emitted; ``gap_test = A + mu_test·B ≥ 0`` by
    the abstract collapse.

    Fields are exact ``sympy`` rationals.
    """

    A: object          # intercept  bell(node cs) − bell cherry
    B: object          # slope      bY(node cs) − bY cherry
    lo: object         # interval lower endpoint (456/3703)
    hi: object         # interval upper endpoint (3/7)
    mu_test: object    # concrete μ in [lo,hi] for the rational sanity example
    endpoint_lo: object  # A + lo·B  (≥ 0)
    endpoint_hi: object  # A + hi·B  (≥ 0)
    gap_test: object   # A + mu_test·B  (≥ 0)


def affine_param_endpoint_certificate(
    *, A, B, lo=None, hi=None, mu_test=None
) -> AffineParamEndpointCertificate:
    """Build and EXACTLY self-check (over ℚ) an affine-endpoint collapse cert.

    Self-check (both must hold, else ``ValueError``):

    1. AFFINITY.  The gap ``G(μ) = A + μ·B`` must be affine in ``μ`` — degree
       ``≤ 1`` in the symbol.  We build ``G`` symbolically as ``A + μ·B`` with
       ``A, B`` treated as the given constants and REFUSE if the polynomial in
       ``μ`` carries a ``μ²`` or higher term.  (NEGATIVE CONTROL (a): pass a
       gap that already contains a ``μ²`` term via a nonconstant ``B`` — refused.)
    2. ENDPOINT NONNEGATIVITY.  Both ``A + lo·B ≥ 0`` and ``A + hi·B ≥ 0`` must
       hold exactly over ℚ.  (NEGATIVE CONTROL (b): an affine gap with one
       endpoint value ``< 0`` — refused.)

    ``lo``/``hi`` default to the real SCLStep interval endpoints ``456/3703`` and
    ``3/7``.  ``mu_test`` defaults to the interior point ``1/4 ∈ (lo,hi)``.
    """
    lo = _I_LO if lo is None else sp.Rational(lo)
    hi = _I_HI if hi is None else sp.Rational(hi)
    if not (lo < hi):
        raise ValueError(f"REFUSED: degenerate interval [{lo},{hi}] (need lo < hi)")

    mu = sp.Symbol("mu")
    A_s = sp.nsimplify(A)
    B_s = sp.nsimplify(B)

    # (1) AFFINITY: build the gap and confirm degree <= 1 in μ.
    gap = sp.expand(A_s + mu * B_s)
    poly = sp.Poly(gap, mu)
    if poly.degree() > 1:
        raise ValueError(
            f"REFUSED: gap G(μ) = {gap} is NOT affine in μ — it carries a "
            f"degree-{poly.degree()} term in μ (negative control (a))"
        )

    # (2) both endpoint values must be nonnegative over ℚ.
    e_lo = sp.nsimplify(A_s + lo * B_s)
    e_hi = sp.nsimplify(A_s + hi * B_s)
    if not (e_lo.is_number and e_lo >= 0):
        raise ValueError(
            f"REFUSED: lower-endpoint value A + lo·B = {e_lo} < 0 at μ = {lo} "
            f"(negative control (b))"
        )
    if not (e_hi.is_number and e_hi >= 0):
        raise ValueError(
            f"REFUSED: upper-endpoint value A + hi·B = {e_hi} < 0 at μ = {hi} "
            f"(negative control (b))"
        )

    mu_t = sp.Rational(1, 4) if mu_test is None else sp.Rational(mu_test)
    if not (lo <= mu_t <= hi):
        raise ValueError(
            f"REFUSED: mu_test = {mu_t} is not in the interval [{lo},{hi}]"
        )
    gap_t = sp.nsimplify(A_s + mu_t * B_s)
    if not (gap_t.is_number and gap_t >= 0):  # pragma: no cover — implied by collapse
        raise ValueError(
            f"REFUSED: interior test value A + mu_test·B = {gap_t} < 0 (impossible "
            f"if both endpoints nonneg and affine — internal check)"
        )

    return AffineParamEndpointCertificate(
        A=A_s, B=B_s, lo=lo, hi=hi, mu_test=mu_t,
        endpoint_lo=e_lo, endpoint_hi=e_hi, gap_test=gap_t,
    )


def certify_affine_param_endpoint_point(family, pt, name):
    """Certify one affine-param-endpoint instance from ``family.special[1](pt)``.

    ``spec`` is a dict ``{"A": ..., "B": ..., "lo": ..., "hi": ...,
    "mu_test": ...}`` (``A``/``B`` required; ``lo``/``hi``/``mu_test`` optional —
    default to the real SCLStep interval ``[456/3703, 3/7]`` and interior
    ``μ = 1/4``)."""
    spec = family.special[1](pt)
    cert = affine_param_endpoint_certificate(
        A=spec["A"], B=spec["B"],
        lo=spec.get("lo"), hi=spec.get("hi"), mu_test=spec.get("mu_test"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class AffineParamEndpointEmitter(Emitter):
    """Emit the BG SCLStep affine-in-parameter endpoint-collapse theorems.

    Each instance emits THREE self-contained theorems (only ``import Mathlib``):

    1. ``affine_endpoint_nonneg`` — the abstract core: an affine ``A + μ·B`` that
       is ``≥ 0`` at both endpoints of ``[lo,hi]`` is ``≥ 0`` throughout.
    2. ``bV_interval_of_endpoints`` — the bV-shaped SCLStep application
       (``f = bell``, ``g = bY`` opaque; ``x = node cs``, ``c = cherry``):
       endpoint-wise ``≤`` at ``lo`` and ``hi`` lifts to ``≤`` at every interior
       ``μ``, by reduction to theorem 1 with ``A = f c − f x``, ``B = g c − g x``.
    3. a CONCRETE rational sanity ``example`` instantiating theorem 1 at the real
       interval endpoints ``lo = 456/3703``, ``hi = 3/7`` and the specific
       interior ``μ = mu_test``.

    HONEST SCOPE: this reduces the affine-in-parameter interval inequality to two
    endpoints — for SCLStep it collapses the price interval ``I``.  It does NOT
    prove the endpoint inequalities themselves.  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "affine_param_endpoint"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        # The two abstract theorems are identical across instances; emit them
        # once (from the first instance) then one concrete example per instance.
        abstract_emitted = False
        for inst in fam.instances:
            cert: AffineParamEndpointCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            if not abstract_emitted:
                lines.append(self._emit_abstract())
                abstract_emitted = True
                nthm += 2
            lines.append(self._emit_concrete(cert, name))
            nthm += 1
        return "\n".join(lines), nthm

    def _emit_abstract(self) -> str:
        return (
            "-- (1) ABSTRACT CORE.  An affine map `A + μ·B` that is nonneg at both\n"
            "-- endpoints of `[lo,hi]` is nonneg throughout, via the identity\n"
            "--   (hi−lo)(A+μB) = (hi−μ)(A+loB) + (μ−lo)(A+hiB),  both summands ≥ 0.\n"
            "theorem affine_endpoint_nonneg (A B lo hi μ : ℝ)\n"
            "    (hlo : lo ≤ μ) (hhi : μ ≤ hi)\n"
            "    (hL : 0 ≤ A + lo * B) (hH : 0 ≤ A + hi * B) :\n"
            "    0 ≤ A + μ * B := by\n"
            "  -- (hi−μ)(A+loB) ≥ 0 and (μ−lo)(A+hiB) ≥ 0; their sum is\n"
            "  -- (hi−lo)(A+μB).  Case-split on the interval being nondegenerate.\n"
            "  have hprodL : 0 ≤ (hi - μ) * (A + lo * B) :=\n"
            "    mul_nonneg (sub_nonneg.mpr hhi) hL\n"
            "  have hprodH : 0 ≤ (μ - lo) * (A + hi * B) :=\n"
            "    mul_nonneg (sub_nonneg.mpr hlo) hH\n"
            "  rcases (le_trans hlo hhi).lt_or_eq with hlt | heq\n"
            "  · -- lo < hi: divide the summed identity by (hi − lo) > 0.\n"
            "    nlinarith [hprodL, hprodH, sub_pos.mpr hlt]\n"
            "  · -- lo = hi forces μ = lo = hi, so A + μB = A + lo·B ≥ 0.\n"
            "    have hμlo : μ = lo := le_antisymm (heq ▸ hhi) hlo\n"
            "    rw [hμlo]; exact hL\n"
            "\n"
            "-- (2) bV-SHAPED SCLStep APPLICATION.  With `f = bell`, `g = bY` opaque,\n"
            "-- `x = node cs`, `c = cherry`: endpoint-wise `≤` at `lo` and `hi` lifts\n"
            "-- to `≤` at every interior price `μ`.  Reduces to (1) with\n"
            "-- `A = f c − f x`, `B = g c − g x` (the affine gap G(μ) = A + μ·B).\n"
            "theorem bV_interval_of_endpoints {α : Type*} (f g : α → ℝ) (x c : α)\n"
            "    (lo hi μ : ℝ) (hlo : lo ≤ μ) (hhi : μ ≤ hi)\n"
            "    (hL : (f x + lo * g x) ≤ (f c + lo * g c))\n"
            "    (hH : (f x + hi * g x) ≤ (f c + hi * g c)) :\n"
            "    (f x + μ * g x) ≤ (f c + μ * g c) := by\n"
            "  have hL' : 0 ≤ (f c - f x) + lo * (g c - g x) := by nlinarith [hL]\n"
            "  have hH' : 0 ≤ (f c - f x) + hi * (g c - g x) := by nlinarith [hH]\n"
            "  have hcore : 0 ≤ (f c - f x) + μ * (g c - g x) :=\n"
            "    affine_endpoint_nonneg (f c - f x) (g c - g x) lo hi μ hlo hhi hL' hH'\n"
            "  nlinarith [hcore]\n"
        )

    def _emit_concrete(self, cert: AffineParamEndpointCertificate, name: str) -> str:
        A = _lean_rat(cert.A)
        B = _lean_rat(cert.B)
        lo = _lean_rat(cert.lo)
        hi = _lean_rat(cert.hi)
        mu = _lean_rat(cert.mu_test)
        return (
            f"-- (3) CONCRETE RATIONAL SANITY INSTANCE `{name}`.  Instantiates the\n"
            f"-- abstract core at the REAL SCLStep interval endpoints lo = {lo},\n"
            f"-- hi = {hi} and the interior price μ = {mu}: with A = {A}, B = {B}\n"
            f"-- both endpoint values are ≥ 0, so the gap A + μ·B ≥ 0.\n"
            f"example : (0 : ℝ) ≤ ({A}) + ({mu}) * ({B}) :=\n"
            f"  affine_endpoint_nonneg ({A}) ({B}) ({lo}) ({hi}) ({mu})\n"
            f"    (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n"
        )


def affine_param_endpoint_family(name, grid, lean_name, spec, constants=None):
    """Build a BG SCLStep affine-param-endpoint family (kind='affine_param_endpoint').

    ``spec``: a callable ``pt -> {"A": ..., "B": ..., "lo": ..., "hi": ...,
    "mu_test": ...}`` (``A``/``B`` required; the rest default to the real SCLStep
    interval ``[456/3703, 3/7]`` and interior ``μ = 1/4``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("affine_param_endpoint", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive: SCLStep interval I=[456/3703, 3/7], A=1, B=2, μ=1/4 ===")
    c = affine_param_endpoint_certificate(A=1, B=2)
    print(f"  cert OK: A={c.A}, B={c.B}, I=[{c.lo},{c.hi}], μ_test={c.mu_test}; "
          f"endpoints [{c.endpoint_lo}, {c.endpoint_hi}] ≥ 0, gap={c.gap_test} ≥ 0")

    print("\n=== positive: descending affine gap A=1, B=-1 (still ≥0 on I) ===")
    c2 = affine_param_endpoint_certificate(A=1, B=-1)
    print(f"  cert OK: endpoints [{c2.endpoint_lo}, {c2.endpoint_hi}] ≥ 0")

    print("\n=== NEGATIVE CONTROL (a): gap carries a μ² term (non-affine) ===")
    mu = sp.Symbol("mu")
    try:
        # B nonconstant in μ makes A + μ·B carry μ² — must be refused.
        affine_param_endpoint_certificate(A=1, B=mu)
        raise SystemExit("FAIL: non-affine (μ²) gap was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

    print("\n=== NEGATIVE CONTROL (b): affine gap with a NEGATIVE endpoint ===")
    try:
        # A=0, B=-1: lower endpoint A+lo·B = -456/3703 < 0 — must be refused.
        affine_param_endpoint_certificate(A=0, B=-1)
        raise SystemExit("FAIL: negative-endpoint gap was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

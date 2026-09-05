"""Mossinghoff–Trudgian-style OPTIMAL nonnegative-cosine polynomials, with an exact,
search-free Fejér–Riesz sum-of-squares certificate.

`emit_zero_free_cosine` realizes only the de la Vallée-Poussin slice `(1+cosθ)^n` of the
nonnegative-cosine cone.  The zero-free-region functional
`F(P) = (√a₁ − √a₀)² / Σ_{k≥1} a_k` is NOT maximized on that slice — Mossinghoff and
Trudgian optimize it over the whole admissible cone `{a_k ≥ 0, P(θ) ≥ 0, a₁ ≥ a₀}` to get
a wider region.  This module supplies (i) the exact SOS certificate for any such optimized
polynomial, and (ii) the verified degree-4 optimum that beats the VP slice.

THE CERTIFICATE (exact, no Positivstellensatz search).  A nonnegative trig polynomial
factors Fejér–Riesz as `P(θ) = |Q(e^{iθ})|²`, `Q(z) = Σ_{j=0}^d b_j z^j`.  Writing
`Q(e^{iθ}) = A(cosθ) + i·sinθ·B(cosθ)` with

    A(x) = Σ_{j=0}^d b_j T_j(x),     B(x) = Σ_{j=1}^d b_j U_{j-1}(x)

(`T`,`U` the Chebyshev polynomials of the 1st/2nd kind) and `sin²θ = 1 − x²`, one gets the
EXACT identity, in `x = cosθ`,

    p(x) := Σ_{k=0}^d a_k T_k(x)  =  A(x)²  +  (1 − x²)·B(x)²,

so `p ≥ 0` on `[−1,1]` by construction — a Putinar/SOS witness on `{1 − x² ≥ 0}` obtained
directly from `b`, with NO search and NO floating point in the certificate.  The Lean
discharge is a one-line `nlinarith [sq_nonneg A, mul_nonneg h_(1−x²) (sq_nonneg B)]`.

`fejer_riesz_sos` builds `(A, B, p, a)` from a rational `b` and asserts the identity; the
UNTRUSTED emitter ships Lean the kernel re-checks.  The optimization that FINDS a
region-improving `b` is a separate numeric step (scipy) recorded in the module docstring —
the shipped constant `MT_DEG4` is its verified rational output.  conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

__all__ = ["fejer_riesz_sos", "mt_cosine_cert_lean", "f_functional_exact", "MT_DEG4"]

_X = sp.Symbol("x")


def f_functional_exact(a) -> sp.Expr:
    """`F = (√a₁ − √a₀)² / Σ_{k≥1} a_k`, exact (with sympy surds)."""
    a = list(a)
    tail = sum(a[1:])
    return (sp.sqrt(a[1]) - sp.sqrt(a[0])) ** 2 / tail


def fejer_riesz_sos(b, x: sp.Symbol = _X):
    """From a Fejér–Riesz coefficient vector `b = (b_0,…,b_d)` (rationals), return
    `(A, B, p, a)` where

      * `A = Σ b_j T_j(x)`, `B = Σ_{j≥1} b_j U_{j-1}(x)` — the SOS half-witnesses,
      * `p = A² + (1−x²)B²` (expanded) — nonnegative on `[−1,1]` by construction,
      * `a = (a_0,…,a_d)` — the cosine coefficients, i.e. `p = Σ a_k T_k(x)`.

    Asserts the exact identity `p = Σ a_k T_k` and that `deg p = d` (the high powers from
    `A²` and `(1−x²)B²` cancel), so the returned `a` is the genuine cosine spectrum.
    """
    b = [sp.nsimplify(bj) for bj in b]
    d = len(b) - 1
    A = sp.expand(sum(b[j] * sp.chebyshevt(j, x) for j in range(d + 1)))
    B = sp.expand(sum(b[j] * sp.chebyshevu(j - 1, x) for j in range(1, d + 1)))
    p = sp.expand(A ** 2 + (1 - x ** 2) * B ** 2)
    if sp.Poly(p, x).degree() > d:
        raise ValueError(f"fejer_riesz_sos: p has degree {sp.Poly(p, x).degree()} > {d}; b is inconsistent")
    # recover cosine coefficients by matching the T-basis (upper-triangular, exact).
    a = []
    q = p
    for k in range(d, -1, -1):
        Tk = sp.Poly(sp.chebyshevt(k, x), x)
        lead = Tk.LC()
        ck = sp.Poly(q, x).coeff_monomial(x ** k) / lead if k > 0 else sp.Poly(q, x).coeff_monomial(1)
        a.append((k, ck))
        q = sp.expand(q - ck * sp.chebyshevt(k, x))
    a = [c for _, c in sorted(a)]
    if sp.expand(p - sum(a[k] * sp.chebyshevt(k, x) for k in range(d + 1))) != 0:
        raise ValueError("fejer_riesz_sos: SOS != Σ a_k T_k — identity failed")
    return A, B, p, a


def mt_cosine_cert_lean(name: str, b, *, doc: str | None = None, x_name: str = "x") -> str:
    """Emit a Lean theorem: the degree-`d` Chebyshev polynomial `p(x) = Σ a_k T_k(x)`
    built from Fejér–Riesz `b` is `≥ 0` on `[−1,1]`, via the exact SOS `A² + (1−x²)B²`.

    The proof is `nlinarith [sq_nonneg A, mul_nonneg (0 ≤ 1−x²) (sq_nonneg B)]` — the goal
    equals the sum of those two nonnegative terms as a ring identity, so it closes with
    unit coefficients.  Admissibility (`a_k ≥ 0`, `a₁ ≥ a₀`) is asserted here and surfaced
    in the docstring; a violation raises before emitting.
    """
    A, B, p, a = fejer_riesz_sos(b)
    if any(c < 0 for c in a):
        raise ValueError(f"{name}: cosine coefficient negative — not an admissible tuple")
    if a[1] < a[0]:
        raise ValueError(f"{name}: a₁ < a₀ — degenerate branch, not a zero-free polynomial")
    x = sp.Symbol(x_name)
    A = A.subs(_X, x); B = B.subs(_X, x); p = p.subs(_X, x)
    # sympy's str printer uses `**` for powers; Lean uses `^`.
    def _lean(e):
        return sp.printing.str.sstr(e).replace("**", "^")
    A_s, B_s, p_s = _lean(A), _lean(B), _lean(p)
    docblock = f"/-- {doc} -/\n" if doc else ""
    return (
        f"{docblock}"
        f"theorem {name} ({x_name} : ℝ) (h1 : -1 ≤ {x_name}) (h2 : {x_name} ≤ 1) :\n"
        f"    (0:ℝ) ≤ {p_s} := by\n"
        f"  have hsq : (0:ℝ) ≤ 1 - {x_name}^2 := by nlinarith [h1, h2]\n"
        f"  nlinarith [sq_nonneg ({A_s}), mul_nonneg hsq (sq_nonneg ({B_s}))]"
    )


# ── Verified degree-4 optimum ────────────────────────────────────────────────
# Found by maximizing F over the Fejér cone (scipy SLSQP over b with a_k ≥ 0, a₁ ≥ a₀),
# then rationalizing b at denominator 8.  Cosine spectrum a = (65/64, 7/4, 9/8, 1/2, 1/8),
# F = 2(√7/2 − √65/8)²/7 ≈ 0.028367 vs the VP-degree-4 slice's ≈ 0.026411 (a 7.4% wider
# region functional).  `b` here reproduces A = -2x⁴-2x³+¾x²+x+⅛, B = -2x³-2x²-x/4.
MT_DEG4 = {
    "b": [sp.Rational(-1, 4), sp.Rational(-1, 2), sp.Rational(-5, 8), sp.Rational(-1, 2), sp.Rational(-1, 4)],
    "a": [sp.Rational(65, 64), sp.Rational(7, 4), sp.Rational(9, 8), sp.Rational(1, 2), sp.Rational(1, 8)],
}

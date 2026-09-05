"""Fejér–Riesz spectral factorization: ANY nonnegative trig polynomial → exact SOS.

`emit_mt_cosine.fejer_riesz_sos` goes the easy way (`b → A²+(1−x²)B²`, a factorization is
given).  This module supplies the missing front-end — the SPECTRAL FACTORIZATION
`a → b` — so a caller who has only the target nonnegative cosine polynomial
`P(θ) = Σ_{k=0}^d a_k cos kθ ≥ 0` (not its factorization) gets the exact
`p(x) = Σ a_k T_k(x) = A(x)² + (1−x²)B(x)² ≥ 0` certificate on `[−1,1]`, `x = cosθ`.

ALGORITHM (`spectral_factor`).  Form the palindromic associated polynomial
`g(z) = Σ_{j=0}^{2d} c_{j−d} z^j`, `c_0 = a_0`, `c_{±k} = a_k/2`.  Its roots come in
conjugate-reciprocal pairs; take the `d` roots in the closed unit disk (smallest modulus),
set `Q(z) = ∏(z − r_in)`, and scale so `Σ b_j² = a_0`.  Then `|Q(e^{iθ})|² = P(θ)`.

SCOPE / TRUST.  Unlike `emit_mt_cosine` (which gates on the zero-free-region admissibility
`a₁ ≥ a₀`), this emitter is GENERAL: it certifies nonnegativity ONLY, for any nonnegative
trig polynomial.  Because `P = |Q|²` for any real `b`, a RATIONALIZED `b` yields an EXACT
rational SOS for the nearby tuple `a' = autocorr(b')` (`target='nearby'`, always succeeds,
`a' ≈ a`); the sweet spot is certifying an optimizer's or a constructed polynomial.  To
certify a SPECIFIC arbitrary rational `a` exactly, that is the domain of `emit_rational_sos`
/ `find_handelman_certificate` (a general SDP-rationalized SOS) — this module raises for
`target='exact'` when the factorization is not exactly rational, rather than shipping a
tuple `≠ a`.  UNTRUSTED like every emitter: the kernel re-checks; a mis-shape raises here.
conjecture1_proved = False.
"""
from __future__ import annotations

import numpy as np
import sympy as sp

from .emit_mt_cosine import fejer_riesz_sos

__all__ = ["spectral_factor", "rationalize_factor", "emit_spectral_sos_cert"]

_X = sp.Symbol("x")


def spectral_factor(a, *, tol: float = 1e-6):
    """Numeric Fejér–Riesz factor `b = (b_0,…,b_d)` of the cosine tuple `a` (with
    `P(θ) = Σ a_k cos kθ ≥ 0`), so `|Σ b_j e^{ijθ}|² = P(θ)`.  Raises if `P` dips
    negative on a dense circle sample (not a nonnegative trig polynomial)."""
    d = len(a) - 1
    af = [float(v) for v in a]
    thetas = np.linspace(0, np.pi, 400)
    Pvals = af[0] + sum(af[k] * np.cos(k * thetas) for k in range(1, d + 1))
    if Pvals.min() < -tol * max(1.0, af[0]):
        raise ValueError(f"spectral_factor: P(θ) dips to {Pvals.min():.3e} — not nonnegative")
    c = [0.0] * (2 * d + 1)
    c[d] = af[0]
    for k in range(1, d + 1):
        c[d + k] = c[d - k] = af[k] / 2
    roots = np.roots(c[::-1])
    roots = sorted(roots, key=lambda r: abs(r))[:d]
    Q = np.poly(roots)                       # highest-first
    b = Q[::-1].real                         # b_0..b_d
    nb = np.dot(b, b)
    if nb <= 0:
        raise ValueError("spectral_factor: degenerate factorization")
    return b * np.sqrt(af[0] / nb)


def rationalize_factor(a, *, denom: int = 16):
    """Factor `a`, rationalize `b` at `denom`, and return `(b_rat, a_exact)` where
    `a_exact = autocorr(b_rat)` is the EXACT rational cosine spectrum actually certified
    (`a_exact ≈ a`).  Fixes the leading sign so `b_rat[0] ≥ 0` (unimodular freedom)."""
    b = spectral_factor(a)
    if b[0] < 0:
        b = -b
    b_rat = [sp.Rational(round(v * denom), denom) for v in b]
    _, _, _, a_exact = fejer_riesz_sos(b_rat)
    return b_rat, a_exact


def emit_spectral_sos_cert(
    name: str,
    a,
    *,
    denom: int = 16,
    target: str = "nearby",
    doc: str | None = None,
    x_name: str = "x",
) -> tuple[str, list]:
    """Emit a Lean theorem `0 ≤ Σ a'_k T_k(x)` on `[−1,1]` via the exact Fejér–Riesz SOS,
    and return `(lean, a_exact)`.

    `target='nearby'` certifies the exact rational `a_exact` from a rationalized factor
    (`a_exact ≈ a`).  `target='exact'` requires `a_exact == a` (raises otherwise, so a
    tuple `≠ a` is never silently shipped).  No admissibility gate — nonnegativity only.
    """
    b_rat, a_exact = rationalize_factor(a, denom=denom)
    if target == "exact":
        a_in = [sp.nsimplify(v) for v in a]
        if list(a_exact) != a_in:
            raise ValueError(
                f"{name}: exact rational factorization not found at denom={denom} "
                f"(got {a_exact}, want {a_in}); use target='nearby' or emit_rational_sos"
            )
    A, B, p, _ = fejer_riesz_sos(b_rat)
    x = sp.Symbol(x_name)
    A, B, p = A.subs(_X, x), B.subs(_X, x), p.subs(_X, x)

    def _lean(e):
        return sp.printing.str.sstr(e).replace("**", "^")

    docblock = f"/-- {doc} -/\n" if doc else ""
    lean = (
        f"{docblock}"
        f"theorem {name} ({x_name} : ℝ) (h1 : -1 ≤ {x_name}) (h2 : {x_name} ≤ 1) :\n"
        f"    (0:ℝ) ≤ {_lean(p)} := by\n"
        f"  have hsq : (0:ℝ) ≤ 1 - {x_name}^2 := by nlinarith [h1, h2]\n"
        f"  nlinarith [sq_nonneg ({_lean(A)}), mul_nonneg hsq (sq_nonneg ({_lean(B)}))]"
    )
    return lean, list(a_exact)

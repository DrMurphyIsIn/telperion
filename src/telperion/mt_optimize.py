"""Mossinghoff–Trudgian cosine optimizer: the pipeline that DISCOVERS a region-improving
nonnegative-cosine polynomial at any degree, then hands it to the exact SOS certificate.

`emit_mt_cosine` ships one hand-found flagship (`MT_DEG4`).  This module codifies how it was
found, for arbitrary degree `d`:

  1. maximize the zero-free-region functional `F = (√a₁ − √a₀)² / Σ_{k≥1} a_k` over the
     Fejér cone, parametrized by the factor `b` (so `a = autocorr(b)` and `P = |Q|² ≥ 0`
     automatically), subject to the ADMISSIBILITY constraints `a_k ≥ 0` and `a₁ ≥ a₀`
     — WITHOUT which the maximization is degenerate (it drives `a₁ → 0` or `a_k < 0`);
  2. rationalize `b` at a chosen denominator (any rational `b` keeps `P = |Q|² ≥ 0` exactly);
  3. verify the resulting exact rational spectrum `a` is admissible and beats the de la
     Vallée-Poussin slice at the same degree.

The returned `b` feeds `emit_mt_cosine.mt_cosine_cert_lean` for the exact, search-free
`A² + (1−x²)B²` certificate.  Numerics (scipy) are used ONLY to DISCOVER `b`; the shipped
certificate is exact rational and kernel-checked — the optimizer is untrusted scaffolding.
SciPy is imported lazily so this module never breaks the core import graph.
conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from .emit_mt_cosine import fejer_riesz_sos, f_functional_exact
from .emit_zero_free_cosine import vallee_poussin_coeffs, f_functional

__all__ = ["optimize_cosine"]


def _require_scipy():
    try:
        import numpy as np
        from scipy.optimize import minimize
        return np, minimize
    except ImportError as e:  # pragma: no cover
        raise RuntimeError(
            "mt_optimize.optimize_cosine needs numpy+scipy (the discovery step). "
            "Install them, or use the pre-optimized emit_mt_cosine.MT_DEG4."
        ) from e


def optimize_cosine(d: int, *, trials: int = 120, denom: int = 8):
    """Find a degree-`d` nonnegative-cosine polynomial that BEATS the de la Vallée-Poussin
    slice on the functional `F`, and return a dict with the exact rational data:

        {"b": [Rational…], "a": [Rational…], "F": Rational-ish, "F_vp": float,
         "gain": float, "beats_vp": bool}

    `b` is the (rationalized) Fejér–Riesz factor; `a = autocorr(b)` is the certified exact
    cosine spectrum.  Raises if no admissible rational improvement is found at `denom`
    (try a larger `denom`).  `beats_vp` is guaranteed True on a successful return.
    """
    np, minimize = _require_scipy()

    def a_from_b(b):
        m = len(b) - 1
        a = np.zeros(m + 1)
        a[0] = np.dot(b, b)
        for k in range(1, m + 1):
            a[k] = 2 * np.sum(b[: m + 1 - k] * b[k:])
        return a

    def negF(b):
        a = a_from_b(b)
        tail = a[1:].sum()
        if tail <= 0:
            return 1e6
        return -((np.sqrt(max(a[1], 0)) - np.sqrt(max(a[0], 0))) ** 2 / tail)

    best = None
    for t in range(trials):
        b0 = np.random.RandomState(t).randn(d + 1)
        cons = [{"type": "ineq", "fun": (lambda b, k=k: a_from_b(b)[k])} for k in range(1, d + 1)]
        cons.append({"type": "ineq", "fun": lambda b: a_from_b(b)[1] - a_from_b(b)[0]})  # a1>=a0
        r = minimize(negF, b0, constraints=cons, method="SLSQP",
                     options={"maxiter": 800, "ftol": 1e-14})
        if r.success:
            a = a_from_b(r.x)
            if a[0] > 0 and (a[1:] >= -1e-9).all() and a[1] >= a[0] - 1e-9:
                if best is None or -r.fun > best[0]:
                    best = (-r.fun, r.x)
    if best is None:
        raise RuntimeError(f"optimize_cosine(d={d}): no admissible optimum found")

    b = best[1]
    if b[0] < 0:
        b = -b
    # Robust rationalization: the numeric optimum is a continuum, so a single round() can land
    # on a poor rational.  Search every floor/ceil rounding of b·denom and keep the admissible
    # one with the largest exact F (this is how the MT_DEG4 flagship rounds nicely).
    import itertools
    # b comes from scipy.optimize as a numpy array. Coerce each entry to a Python
    # float before it reaches sympy: under numpy>=2 the repr is "np.float64(...)"
    # and sympy 1.12 converts numpy scalars by stringifying, so sp.floor(np.float64)
    # raises "invalid literal for int()". float(v) is an exact, value-preserving
    # conversion; newer sympy masks the bug but this keeps both matrix legs green.
    lo = [int(sp.floor(float(v) * denom)) for v in b]
    b_rat, a_exact, F = None, None, None
    for bump in itertools.product((0, 1), repeat=d + 1):
        cand = [sp.Rational(lo[j] + bump[j], denom) for j in range(d + 1)]
        if all(c == 0 for c in cand):
            continue
        try:
            _, _, _, a_c = fejer_riesz_sos(cand)
        except ValueError:
            continue
        if any(c < 0 for c in a_c) or a_c[1] < a_c[0] or a_c[0] <= 0:
            continue
        Fc = f_functional_exact(a_c)
        if F is None or float(Fc) > float(F):
            b_rat, a_exact, F = cand, a_c, Fc
    if b_rat is None:
        raise RuntimeError(
            f"optimize_cosine(d={d}): no admissible rational factor at denom={denom}; "
            f"try a larger denom"
        )
    F_vp = float(f_functional(vallee_poussin_coeffs(d)))
    if not (float(F) > F_vp):
        raise RuntimeError(
            f"optimize_cosine(d={d}): rationalized F={float(F):.5f} does not beat VP={F_vp:.5f}; "
            f"try a larger denom or more trials"
        )
    return {
        "b": b_rat,
        "a": list(a_exact),
        "F": F,
        "F_vp": F_vp,
        "gain": float(F) / F_vp,
        "beats_vp": True,
    }

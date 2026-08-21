"""SDP-based FINDER for the SOS-Positivstellensatz REFUTATION emitter — the
free-multiplier companion to the Putinar finder in `sos_sdp`.

The Putinar finder (`sos_sdp.find_putinar_certificate`) proves `0 ≤ p` on a set
by searching SOS multipliers.  Its refutation dual needs the same SDP plus FREE
(not-necessarily-SOS) multipliers for the equality constraints:

  * `find_sos_refutation` — `−1 = σ₀ + Σ σᵢ·gᵢ + Σ λⱼ·hⱼ` (SOS σ, free λ),
    which certifies ℝ-unsatisfiability of `{gᵢ ≥ 0, hⱼ = 0}` and automatically
    closes the real-only gap (e.g. finds `σ₀ = x²`, `λ = −1` for `x² + 1 = 0`).

The shared solver puts a PSD Gram block on each `σ` and a free coefficient vector
on each `λ`, minimizes total trace (steering toward lower-rank, rationalizable
solutions), rationalizes the numerical solution over a denominator ladder, and
VERIFIES the reconstruction EXACTLY.  UNTRUSTED — the emitter re-verifies every
result — so a numerically-unrationalizable solution is a refusal, never a wrong
certificate.

HONEST SCOPE: numerical SDP → exact rational is inherently incomplete — a valid
certificate whose SDP solution does not rationalize over the tried denominators
is refused (the same limitation as `sos_sdp`).  Needs cvxpy (the `sdp` CI group);
the emitted Lean is compile-gated regardless.
"""
from __future__ import annotations

from itertools import combinations_with_replacement

import sympy as sp

_DENOMS = (1, 2, 3, 4, 6, 8, 12, 24, 48, 120, 720, 5040)


def _monomials_upto(syms, deg: int):
    mons = [sp.Integer(1)]
    for d in range(1, deg + 1):
        for combo in combinations_with_replacement(syms, d):
            mons.append(sp.prod(combo))
    return mons


def _sos_terms_from_psd(Q, mons):
    """Exact rational LDLᵀ that skips zero pivots (PSD-singular safe) →
    list of (coef, base) with `Σ coef·base² = mᵀ Q m`, or None if not PSD-exact."""
    n = Q.rows
    M = sp.Matrix(Q)
    terms = []
    for i in range(n):
        d = M[i, i]
        if d < 0:
            return None
        if d == 0:
            continue
        ell = [M[i, j] / d for j in range(n)]
        terms.append((sp.Rational(d),
                      sp.expand(sum(ell[j] * mons[j] for j in range(n)))))
        for a in range(n):
            if ell[a] == 0:
                continue
            for b in range(n):
                M[a, b] = M[a, b] - d * ell[a] * ell[b]
    if any(M[a, b] != 0 for a in range(n) for b in range(n)):
        return None
    return terms


def _solve(target, sos_blocks, free_blocks, syms):
    """Find PSD Grams (sos_blocks) + free coefficient vectors (free_blocks) with
    ``Σ mult·(mᵀQm) + Σ mult·(cᵀ·mons) = target``.  Returns
    ``(list-of-SOS-term-lists, list-of-free-polys)`` or None."""
    import cvxpy as cp
    import numpy as np

    target = sp.expand(target)
    Qs = [cp.Variable((len(m), len(m)), symmetric=True) for _m, m in sos_blocks]
    Cs = [cp.Variable(len(m)) for _m, m in free_blocks]
    form = sp.Integer(0)
    symmap, allq = {}, {}
    for k, (mult, mons) in enumerate(sos_blocks):
        n = len(mons)
        qs = sp.Matrix(n, n, lambda i, j: sp.Symbol(f"q{k}_{min(i,j)}_{max(i,j)}"))
        form += sp.expand(mult * (sp.Matrix(mons).T * qs * sp.Matrix(mons))[0])
        for i in range(n):
            for j in range(i, n):
                s = sp.Symbol(f"q{k}_{i}_{j}")
                allq[s] = 0
                symmap[s] = Qs[k][i, j]
    for k, (mult, mons) in enumerate(free_blocks):
        cvec = [sp.Symbol(f"c{k}_{i}") for i in range(len(mons))]
        form += sp.expand(mult * sum(cvec[i] * mons[i] for i in range(len(mons))))
        for i, s in enumerate(cvec):
            allq[s] = 0
            symmap[s] = Cs[k][i]

    diff = sp.Poly(sp.expand(form - target), *syms)
    cons = [Q >> 0 for Q in Qs]
    for _mono, coef in diff.terms():
        row = 0.0
        for s, cvar in symmap.items():
            c = coef.coeff(s)
            if c != 0:
                row = row + float(c) * cvar
        cons.append(row + float(coef.subs(allq)) == 0)

    obj = cp.Minimize(sum(cp.trace(Q) for Q in Qs)) if Qs else cp.Minimize(0)
    prob = cp.Problem(obj, cons)
    try:
        prob.solve()
    except Exception:
        return None
    if prob.status not in ("optimal", "optimal_inaccurate"):
        return None
    if any(Q.value is None or not np.all(np.isfinite(Q.value)) for Q in Qs):
        return None
    if any(C.value is None or not np.all(np.isfinite(C.value)) for C in Cs):
        return None

    # Rationalization: two strategies per attempt — a fixed-denominator ladder,
    # and per-entry continued-fraction rounding (`limit_denominator`) which snaps
    # an entry like 0.333… to 1/3 without needing 3 to be on the ladder.  After
    # rounding, the reconstruction is verified EXACTLY over ℚ; only an exact match
    # (and a PSD-exact Gram) is accepted, so a bad rounding is simply skipped.
    from fractions import Fraction

    def _fixed(D):
        return (lambda v: sp.Rational(round(v * D), D))

    def _cf(limit):
        return (lambda v: sp.Rational(Fraction(float(v)).limit_denominator(limit)))

    strategies = [_fixed(D) for D in _DENOMS] + [_cf(L) for L in (12, 60, 360, 5040)]
    for rnd in strategies:
        Qrs = [sp.Matrix(len(m), len(m), lambda i, j: rnd(Q.value[i, j]))
               for Q, (_mult, m) in zip(Qs, sos_blocks)]
        Crs = [[rnd(C.value[i]) for i in range(len(m))]
               for C, (_mult, m) in zip(Cs, free_blocks)]
        tot = sp.Integer(0)
        for Qr, (mult, mons) in zip(Qrs, sos_blocks):
            tot += mult * (sp.Matrix(mons).T * Qr * sp.Matrix(mons))[0]
        for Cr, (mult, mons) in zip(Crs, free_blocks):
            tot += mult * sum(Cr[i] * mons[i] for i in range(len(mons)))
        if sp.expand(tot - target) != 0:
            continue
        sos_out, ok = [], True
        for Qr, (_mult, mons) in zip(Qrs, sos_blocks):
            t = _sos_terms_from_psd(Qr, mons)
            if t is None:
                ok = False
                break
            sos_out.append(t)
        if not ok:
            continue
        free_out = [sp.expand(sum(Cr[i] * mons[i] for i in range(len(mons))))
                    for Cr, (_mult, mons) in zip(Crs, free_blocks)]
        return sos_out, free_out
    return None


def find_real_nullstellensatz(p, gens, syms, m_max: int = 3, half_deg: int = 1):
    """Search for a Real-Nullstellensatz certificate ``p^{2m} + s ∈ ⟨gₖ⟩`` with
    `s` a sum of squares — proving `p = 0` on the REAL variety of `⟨gₖ⟩`.

    Reuses the shared SDP: find SOS `s` and free cofactors `cₖ` with
    ``s = −p^{2m} − Σ cₖ·gₖ`` (so ``p^{2m} + s = −Σ cₖ·gₖ ∈ ⟨gₖ⟩``), raising the
    multiplicity `m` until a certificate is found.  Returns ``(m, s_terms)`` (the
    multiplicity and the SOS term list for `s`) or None; the emitter recomputes
    the ideal cofactors by Gröbner reduction of ``p^{2m} + s``."""
    p = sp.expand(sp.sympify(p))
    gens = [sp.expand(sp.sympify(g)) for g in gens]
    syms = tuple(syms)
    dp = sp.Poly(p, *syms).total_degree() if p != 0 else 0
    for m in range(1, m_max + 1):
        target = sp.expand(-(p ** (2 * m)))
        s_deg = max(m * dp, 1) + half_deg          # room for the SOS block
        sos_blocks = [(sp.Integer(1), _monomials_upto(syms, s_deg))]
        free_blocks = [(g, _monomials_upto(syms, half_deg)) for g in gens]
        res = _solve(target, sos_blocks, free_blocks, syms)
        if res is None:
            continue
        sos_out, _free = res
        return m, sos_out[0]
    return None


def find_sos_refutation(ineq_exprs, eq_exprs, syms, half_deg: int = 1):
    """Search for an SOS-Positivstellensatz refutation
    ``−1 = σ₀ + Σ σᵢ·gᵢ + Σ λⱼ·hⱼ`` (SOS σ, free λ) of the ℝ-infeasibility of
    ``{gᵢ ≥ 0, hⱼ = 0}``.  Returns ``(sigma0_terms, [(g_i, sigma_i_terms)],
    [(h_j, lambda_j)])`` or None."""
    ineqs = [sp.expand(sp.sympify(g)) for g in ineq_exprs]
    eqs = [sp.expand(sp.sympify(h)) for h in eq_exprs]
    syms = tuple(syms)
    sos_blocks = [(sp.Integer(1), _monomials_upto(syms, half_deg))]
    sos_blocks += [(g, _monomials_upto(syms, half_deg)) for g in ineqs]
    free_blocks = [(h, _monomials_upto(syms, half_deg)) for h in eqs]
    res = _solve(sp.Integer(-1), sos_blocks, free_blocks, syms)
    if res is None:
        return None
    sos_out, free_out = res
    return sos_out[0], list(zip(ineqs, sos_out[1:])), list(zip(eqs, free_out))

"""SDP-based SOS certificates with complementary-slackness duality — the LP -> SDP
upgrade of Telperion's certifier.

Polya certificates are the LP-feasibility special case: a nonnegative combination
of known-nonnegative forms.  The established extremal-combinatorics toolkit (the
occupancy method; flag algebras; "SOS for limits of trees") is the SDP layer:
certify `p >= 0` by a POSITIVE-SEMIDEFINITE Gram matrix, `p = mᵀ Q m` over a
monomial basis `m`, with two things the LP layer cannot give:

  * REACH: an SDP finds Gram matrices with off-diagonal coupling, so it certifies
    polynomials that vanish at INTERIOR points (the tie shapes) -- exactly the
    class Polya lifting provably cannot handle;
  * DUALITY / COMPLEMENTARY SLACKNESS: the kernel of the optimal `Q` is the tight
    monomial relation, so the equality variety (`p = 0`) is read off the
    certificate AUTOMATICALLY -- the SDP dual "lands on the tie" for free.

This solves the SDP numerically (cvxpy), rationalizes the Gram matrix, verifies
`p = mᵀ Q m` EXACTLY over the rationals (refusing if rationalization is inexact --
the trust model is unchanged: a bad certificate fails, never lies), LDLᵀ-factors
`Q` into an exact rational SOS, and reports the tight variety from `ker Q`.

HONEST SCOPE: this is the certificate LAYER the occupancy / SOS-for-trees method
runs on.  Applying it to the ∏deg-normalized matching functional's recursive tree
profile -- so the dual lands on the integer tie s=5 -- is the named research
program (unbounded degree + arithmetic tie), not a one-shot emission.

FINDER ROUTE DECISION (2026-08-20).  `find_putinar_certificate` upgrades the
Putinar/constrained-SOS emitter from CHECKER to SEARCHER.  We took ROUTE A (numeric
SDP -> exact rational rounding), which the local toolchain supports: cvxpy 1.7.5 is
installed with the CLARABEL and SCS solvers (no `csdp` binary on PATH, but cvxpy's
own interior-point solvers stand in for it), and sympy 1.14 gives exact rational
LDLᵀ / identity checking.  This mirrors leanprover/sos's own pipeline -- reify ->
SDP -> round the float Gram matrix to rationals (a denominator ladder) -> LDLᵀ
decomposition -> a certificate re-checked INDEPENDENTLY of the solver -- but entirely
inside Telperion's own exact-rational stack (`certify_putinar_point` is the kernel-
independent gate, exactly as `Certificate.checks` is on the Lean side).  Route B
(a DSOS/diagonally-dominant LP fallback, fully exact and numerics-free) was NOT
needed since Route A is runnable today; it remains the honest degradation path if
the SDP stack ever disappears.  As with `find_handelman_certificate`, the finder is
UNTRUSTED: every certificate it returns is re-verified EXACTLY by the existing
`certify_putinar_point` before any Lean is emitted, and a search miss is a REFUSAL,
never a wrong theorem.

sos_witness BRIDGE ASSESSMENT.  leanprover/sos exposes a `by sos?` mode that reports
its witness as a frozen `sos_witness` invocation; emitting `sos_witness`-compatible
goals would mean taking leanprover/sos as a `lake` dependency (Mathlib4 + hex-mv-poly
+ csdp-ffi + a system BLAS/LAPACK runtime) and letting THEIR tactic close the goal at
audit-compile time.  That imports a native-FFI toolchain (the `csdp-ffi` linking work
their `investigations/native-linking-repro/` tree documents) into our audit-compiles
gate, which currently needs only Mathlib -- a real portability and reproducibility
cost.  The self-contained path built here avoids that entirely: we emit ordinary
`ring`/`positivity`/`linarith` Lean that any plain-Mathlib checkout compiles, and keep
the SDP strictly on the (untrusted, Python-side) FINDER, never in the trusted checker.
Recommendation: stay self-contained; revisit the `sos_witness` bridge only if a target
goal is out of reach of our exact rounding but within leanprover/sos's rank-deficient
facial-reduction path.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from .sos import SOSCertificate


def _monomials_upto(syms, deg: int):
    from itertools import combinations_with_replacement
    mons = [sp.Integer(1)]
    for d in range(1, deg + 1):
        for combo in combinations_with_replacement(syms, d):
            mons.append(sp.prod(combo))
    return mons


def gram_sdp(p: sp.Expr, syms, half_deg: int = 1):
    """Solve the SOS SDP for `p = mᵀ Q m`, m = monomials up to half_deg, Q ⪰ 0.
    Returns an EXACT rational PSD Gram matrix (sympy Matrix) verified against p,
    or None (refusal: infeasible, or numeric Q not exactly rationalizable)."""
    import cvxpy as cp
    import numpy as np

    mons = _monomials_upto(syms, half_deg)
    n = len(mons)
    Q = cp.Variable((n, n), symmetric=True)
    mvec = sp.Matrix(mons)
    qsym = sp.Matrix(n, n, lambda i, j: sp.Symbol(f"q_{min(i,j)}_{max(i,j)}"))
    form = sp.expand((mvec.T * qsym * mvec)[0])
    diff = sp.Poly(sp.expand(form - sp.expand(p)), *syms)
    cons = [Q >> 0]
    allq = {sp.Symbol(f"q_{i}_{j}"): 0 for i in range(n) for j in range(i, n)}
    for _, coef in diff.terms():
        row = 0.0
        # each DISTINCT symbol q_{i}_{j} (i<=j) maps once to Q[i,j]; the symbolic
        # coefficient already carries the off-diagonal multiplicity of 2.
        for i in range(n):
            for j in range(i, n):
                c = coef.coeff(sp.Symbol(f"q_{i}_{j}"))
                if c != 0:
                    row = row + float(c) * Q[i, j]
        const = float(coef.subs(allq))
        cons.append(row + const == 0)
    prob = cp.Problem(cp.Minimize(0), cons)
    prob.solve()
    if prob.status not in ("optimal", "optimal_inaccurate") or Q.value is None:
        return None, mons
    if not np.all(np.isfinite(Q.value)):          # degenerate SDP -> refuse
        return None, mons
    Qr = sp.Matrix(n, n, lambda i, j: sp.nsimplify(round(Q.value[i, j] * 5040) / 5040,
                                                   rational=True))
    # exact verification: p == mᵀ Qr m
    if sp.expand((mvec.T * Qr * mvec)[0] - sp.expand(p)) != 0:
        return None, mons
    return Qr, mons


def sos_from_gram(Q: sp.Matrix, mons) -> SOSCertificate | None:
    """LDLᵀ of a PSD rational Gram matrix -> exact SOS: p = Σ dᵢ·(ℓᵢᵀ m)²."""
    try:
        L, D = Q.LDLdecomposition(hermitian=False)
    except Exception:
        return None
    mvec = sp.Matrix(mons)
    forms = L.T * mvec
    terms = []
    for i in range(Q.rows):
        d = sp.Rational(D[i, i])
        if d < 0:
            return None
        if d != 0:
            terms.append((d, sp.expand(forms[i])))
    return SOSCertificate(terms=tuple(terms))


def tight_variety(cert: SOSCertificate):
    """Complementary slackness: p = Σ dᵢ·ℓᵢ² = 0 iff EVERY square base ℓᵢ = 0.
    Returns the square bases (ℓᵢ); their common zero locus is the equality
    variety -- the tie, read off the certificate for free (the SDP dual)."""
    return tuple(s for _, s in cert.terms)


def sos_sdp_certificate(p: sp.Expr, syms, half_deg: int = 1):
    """Full pipeline: SDP Gram -> exact SOS + tight variety.  Returns
    (SOSCertificate, tight_relations) or None."""
    Q, mons = gram_sdp(p, syms, half_deg)
    if Q is None:
        return None
    cert = sos_from_gram(Q, mons)
    if cert is None or sp.expand(cert.as_expr() - sp.expand(p)) != 0:
        return None
    return cert, tight_variety(cert)


def lean_certificate(name: str, p: sp.Expr, syms, half_deg: int = 1) -> str | None:
    res = sos_sdp_certificate(p, syms, half_deg)
    if res is None:
        return None
    cert, tight = res

    def _l(e):
        return sp.printing.sstr(e).replace("**", "^")

    sos = " + ".join(f"({_l(c)}) * ({_l(s)})^2" for c, s in cert.terms)
    binder = " ".join(str(s) for s in syms)
    tightdoc = " ∧ ".join(f"{_l(t)} = 0" for t in tight) or "(none)"
    return (
        f"-- {name}: SDP-SOS certificate (PSD Gram, off-diagonal coupling).\n"
        f"-- Complementary slackness / tight variety (p = 0 iff): {tightdoc}\n"
        f"theorem {name} : ∀ {binder} : ℝ, (0:ℝ) ≤ {_l(sp.expand(p))} := by\n"
        f"  intro {binder}\n"
        f"  have hsos : ({_l(sp.expand(p))} : ℝ) = {sos} := by ring\n"
        f"  rw [hsos]; positivity\n"
    )


# --------------------------------------------------------------------------- #
# Putinar (constrained-SOS) FINDER: numeric SDP -> exact rational rounding.    #
# --------------------------------------------------------------------------- #

# Denominator ladder for rounding float Gram entries to Q.  Highly composite
# denominators (products of small primes) so that a Gram matrix whose true
# entries are simple rationals rounds EXACTLY at some rung; we walk it low->high
# and accept the first rung whose rounded Grams reproduce `p` exactly.
_DENOM_LADDER = (1, 2, 3, 4, 6, 12, 24, 60, 120, 360, 720, 5040, 55440, 720720)


def _round_matrix(M, denom: int):
    """Round a float numpy matrix to an exact rational sympy Matrix on 1/denom."""
    n = M.shape[0]
    return sp.Matrix(n, n, lambda i, j: sp.Rational(round(M[i, j] * denom), denom))


def _robust_ldlt(Q):
    """Exact rational LDLᵀ for a symmetric PSD matrix, tolerant of ZERO pivots
    (rank-deficient Grams — the class sympy's built-in LDL and Cholesky reject).

    Standard outer-product LDLᵀ: at each pivot `d = Q[k,k]`, if `d = 0` the whole
    remaining k-th row/column must be zero for a PSD matrix (else a 2×2 minor is
    indefinite) — we verify that and skip.  If `d < 0` the matrix is not PSD.
    Returns ``(L, D)`` (both sympy Matrices, L unit-lower-triangular) or ``None``
    if not PSD.  This mirrors, in exact arithmetic, the rank-deficiency handling
    leanprover/sos does with facial reduction."""
    n = Q.rows
    A = [[sp.Rational(Q[i, j]) for j in range(n)] for i in range(n)]
    L = [[sp.Integer(1) if i == j else sp.Integer(0) for j in range(n)] for i in range(n)]
    D = [sp.Integer(0)] * n
    for k in range(n):
        d = A[k][k]
        if d < 0:
            return None
        D[k] = d
        if d == 0:
            # PSD => the entire trailing k-column must already be zero.
            if any(A[i][k] != 0 for i in range(k + 1, n)):
                return None
            continue
        for i in range(k + 1, n):
            L[i][k] = A[i][k] / d
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = A[i][j] - L[i][k] * d * L[j][k]
    return sp.Matrix(L), sp.Matrix(n, n, lambda i, j: D[i] if i == j else 0)


def _gram_terms(Q, mons):
    """Robust LDLᵀ of a PSD rational Gram -> [(coef, base)] sum-of-squares terms
    in the (coef, base) shape the Putinar certifier consumes, or None if not PSD.

    A rounded Gram need NOT be PSD, and even when PSD it may be rank-deficient;
    `_robust_ldlt` handles both, and we re-check `Q = L D Lᵀ` EXACTLY so any
    numerical-rounding artifact is caught rather than trusted."""
    if Q.rows == 0 or Q == sp.zeros(*Q.shape):
        return []                                    # σ ≡ 0 is a valid multiplier
    res = _robust_ldlt(Q)
    if res is None:
        return None
    L, D = res
    if sp.expand(sp.Matrix(L * D * L.T) - Q) != sp.zeros(*Q.shape):
        return None                                  # LDL did not reconstruct Q
    forms = L.T * sp.Matrix(mons)
    terms = []
    for i in range(Q.rows):
        d = sp.Rational(D[i, i])
        if d < 0:
            return None
        if d != 0:
            terms.append((d, sp.expand(forms[i])))
    return terms


def _round_vector(v, denom: int):
    """Round a float numpy vector to an exact rational sympy list on 1/denom."""
    return [sp.Rational(round(float(x) * denom), denom) for x in v]


def find_putinar_certificate(p, constraints, syms, half_deg: int | None = None,
                             equalities=()):
    """SEARCH for a Positivstellensatz certificate on `{g_i ≥ 0} ∩ {h_j = 0}`:

        p = σ_0 + Σ_i σ_i·g_i + Σ_j λ_j·h_j

    with every `σ_j` a sum of squares (PSD Gram) and every `λ_j` a FREE
    polynomial multiplier (arbitrary real coefficients — NOT constrained SOS or
    nonnegative), the standard ideal-membership augmentation for equality
    constraints (Route A: numeric SDP -> EXACT rational rounding).  ``constraints``
    is a list of ``(g_i, hyp_name)`` pairs (inequalities `g_i ≥ 0`); ``equalities``
    is a list of ``(h_j, hyp_name)`` pairs (equalities `h_j = 0`, e.g. the cavity
    recursion `h·(1+Σ…) − 1 = 0`).

    Returns ``(sigma0, out_constraints, out_equalities)`` where ``sigma0`` is a
    list of ``(coef, base)`` SOS terms for σ_0, ``out_constraints`` a list of
    ``(g_i, sigma_i, hyp)``, and ``out_equalities`` a list of ``(h_j, lambda_j,
    hyp)`` with ``lambda_j`` a sympy polynomial (the free multiplier) — the exact
    shape `certify_putinar_point` re-verifies — or ``None`` (a REFUSAL, not a
    claim of non-existence).

    On the variety every `h_j = 0`, so `Σ_j λ_j·h_j = 0` there and the certificate
    reduces to `p = σ_0 + Σ σ_i g_i ≥ 0` on `{g_i ≥ 0} ∩ {h_j = 0}` — a
    nonnegativity certificate over the RECURSION-CONSTRAINED (reachable) field set,
    exactly what excludes the free-box cheaters.  The finder is untrusted: the
    caller re-verifies via `certify_putinar_point`.
    """
    import cvxpy as cp
    import numpy as np

    p = sp.expand(sp.sympify(p))
    syms = tuple(syms)
    gens = [sp.expand(sp.sympify(g)) for g, _h in constraints]
    hyps = [h for _g, h in constraints]
    heqs = [sp.expand(sp.sympify(h)) for h, _hn in equalities]
    ehyps = [hn for _h, hn in equalities]

    if half_deg is None:
        pdeg = sp.Poly(p, *syms).total_degree() if p != 0 else 0
        half_deg = max(1, -(-pdeg // 2))            # ceil(deg p / 2)

    # σ_0 lives on monomials up to half_deg; σ_i (multiplying g_i) on monomials
    # up to half_deg - ceil(deg g_i / 2), so σ_i·g_i stays within total degree.
    def _half_for(g):
        gd = sp.Poly(g, *syms).total_degree() if g != 0 else 0
        return max(0, half_deg - -(-gd // 2))

    bases = [(_monomials_upto(syms, half_deg), None)]     # (mons, g) for σ_0
    for g in gens:
        bases.append((_monomials_upto(syms, _half_for(g)), g))

    # One symmetric PSD Gram per block; symbolic Gram symbols to read off the
    # exact affine (coefficient-matching) constraints p = Σ_block g·(mᵀQm).
    Qvars, sym_forms = [], []
    for bidx, (mons, g) in enumerate(bases):
        n = len(mons)
        Qvars.append(cp.Variable((n, n), symmetric=True))
        qsym = sp.Matrix(n, n, lambda i, j: sp.Symbol(f"q{bidx}_{min(i,j)}_{max(i,j)}"))
        mvec = sp.Matrix(mons)
        form = (mvec.T * qsym * mvec)[0]
        if g is not None:
            form = g * form
        sym_forms.append(sp.expand(form))

    # FREE multiplier blocks λ_j·h_j: λ_j = Σ_α l{j}_α · m_α over monomials up to
    # `2·half_deg − deg h_j` (so λ_j·h_j stays within total degree 2·half_deg).
    # The l-coefficients are UNCONSTRAINED cvxpy scalars (any sign) — no PSD, no
    # nonnegativity; this is the ideal (equality) part of the Positivstellensatz.
    Lvars, lam_monlists = [], []
    for jidx, h in enumerate(heqs):
        hd = sp.Poly(h, *syms).total_degree() if h != 0 else 0
        lam_half = max(0, 2 * half_deg - hd)
        lmons = _monomials_upto(syms, lam_half)
        lam_monlists.append(lmons)
        Lvars.append(cp.Variable(len(lmons)))
        lsym = [sp.Symbol(f"l{jidx}_{a}") for a in range(len(lmons))]
        lam_form = sum((lsym[a] * lmons[a] for a in range(len(lmons))), sp.Integer(0))
        sym_forms.append(sp.expand(h * lam_form))

    total = sp.expand(sum(sym_forms, sp.Integer(0)))
    diff = sp.Poly(sp.expand(total - p), *syms)

    def _qsymbol(bidx, i, j):
        return sp.Symbol(f"q{bidx}_{min(i,j)}_{max(i,j)}")

    allq = {}
    for bidx, (mons, _g) in enumerate(bases):
        n = len(mons)
        for i in range(n):
            for j in range(i, n):
                allq[_qsymbol(bidx, i, j)] = 0
    for jidx, lmons in enumerate(lam_monlists):
        for a in range(len(lmons)):
            allq[sp.Symbol(f"l{jidx}_{a}")] = 0

    cons = [Q >> 0 for Q in Qvars]
    for _mono, coef in diff.terms():
        row = 0.0
        for bidx, (mons, _g) in enumerate(bases):
            n = len(mons)
            for i in range(n):
                for j in range(i, n):
                    c = coef.coeff(_qsymbol(bidx, i, j))
                    if c != 0:
                        row = row + float(c) * Qvars[bidx][i, j]
        for jidx, lmons in enumerate(lam_monlists):
            for a in range(len(lmons)):
                c = coef.coeff(sp.Symbol(f"l{jidx}_{a}"))
                if c != 0:
                    row = row + float(c) * Lvars[jidx][a]
        const = float(coef.subs(allq))
        cons.append(row + const == 0)

    # Minimize total trace (+ a tiny ridge on the free multipliers so the SDP has
    # a unique, well-conditioned optimum that rounds cleanly).  Deterministic.
    obj = sum(cp.trace(Q) for Q in Qvars)
    for Lv in Lvars:
        obj = obj + 1e-6 * cp.sum_squares(Lv)
    prob = cp.Problem(cp.Minimize(obj), cons)
    try:
        # Pin the solver and a tight tolerance so the returned Gram (hence the
        # rounded certificate) is deterministic and clean enough to round to
        # simple rationals; SCS is the reliable SDP backend in the cvxpy set.
        prob.solve(solver=cp.SCS, eps=1e-9, max_iters=200000)
    except Exception:
        return None
    if prob.status not in ("optimal", "optimal_inaccurate"):
        return None
    if any(Q.value is None or not np.all(np.isfinite(Q.value)) for Q in Qvars):
        return None
    if any(Lv.value is None or not np.all(np.isfinite(Lv.value)) for Lv in Lvars):
        return None

    # Symmetrize away solver asymmetry noise before rounding (Q is theoretically
    # symmetric; SCS returns it up to ~1e-5, which would defeat exact rounding).
    Qsym = [(np.asarray(Q.value) + np.asarray(Q.value).T) / 2 for Q in Qvars]
    Lval = [np.asarray(Lv.value).reshape(-1) for Lv in Lvars]

    # Exact rational rounding on the denominator ladder: accept the first rung
    # whose rounded Grams (a) LDLᵀ-decompose PSD and (b) reconstruct p exactly.
    for denom in _DENOM_LADDER:
        rounded = [_round_matrix(Qv, denom) for Qv in Qsym]
        term_lists = [_gram_terms(Qr, mons) for Qr, (mons, _g) in zip(rounded, bases)]
        if any(t is None for t in term_lists):
            continue
        lam_polys = []
        for jidx, lmons in enumerate(lam_monlists):
            coeffs = _round_vector(Lval[jidx], denom)
            lam_polys.append(sp.expand(sum((coeffs[a] * lmons[a]
                                            for a in range(len(lmons))), sp.Integer(0))))
        # reconstruct σ_0 + Σ σ_i g_i + Σ λ_j h_j and check the identity over ℚ
        recon = sp.Integer(0)
        for (coef, base) in term_lists[0]:
            recon += coef * base ** 2
        for k, g in enumerate(gens, start=1):
            for (coef, base) in term_lists[k]:
                recon += g * coef * base ** 2
        for jidx, h in enumerate(heqs):
            recon += lam_polys[jidx] * h
        if sp.expand(recon - p) != 0:
            continue
        sigma0 = [(sp.Rational(c), sp.expand(b)) for c, b in term_lists[0]]
        out_constraints = [
            (gens[k - 1], [(sp.Rational(c), sp.expand(b)) for c, b in term_lists[k]],
             hyps[k - 1])
            for k in range(1, len(bases))
        ]
        out_equalities = [
            (heqs[jidx], lam_polys[jidx], ehyps[jidx]) for jidx in range(len(heqs))
        ]
        if out_equalities:
            return sigma0, out_constraints, out_equalities
        return sigma0, out_constraints
    return None

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

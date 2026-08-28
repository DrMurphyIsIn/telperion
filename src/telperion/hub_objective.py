"""Exact symbolic `Aobj` of hub/caterpillar configs + Polya domination certificates.

The reusable engine behind a `hub_dom_family` capability: the Brualdi-Goldwasser
objective `Aobj = per(L)/prod-deg = Ztot(dtRealize)` of any hub/caterpillar
configuration is an EXACT rational function of its structural parameters (leg
counts, cherry counts, hub sizes), via the cavity / `Matched_factor` recursion

    Ztot(node) = Popen * (1 + qSum),
    qSum = sum_children  (1 / (deg * udeg_child)) * (Zopen_child / Ztot_child),

where children are given by their `dtSub` triples `(Zopen, Ztot, udeg)` (degree =
#children + 1), and the ROOT uses `dtRealize` (degree = #children).  Leg counts may
be sympy Symbols, so a whole FAMILY is one symbolic expression.

Domination `Aobj(A) <= Aobj(B)` across a family is certified via the RATIO `B/A`:
the exponential growth (`(3/2)^k` etc.) cancels, leaving a rational function of the
parameter whose `>= 1` is a Polya certificate (all-nonnegative coefficients after a
shift `param -> dom_lo + t`, `t >= 0`) -- exactly the per-cell `positivity`/`norm_num`
shape the Telperion unimodal/Bernstein backends emit.

This mechanizes the recurring BG primitive "compare Aobj of two hub configs": the
cherry-parity single-vs-multi-hub domination, the single-hub Hdom cells, and the
star-merge comparisons.  It does NOT touch the asymptotic convergence (analysis) or
the tree->hub structural reduction (no clean certificate).  conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

# --- dtSub triples (Zopen, Ztot, udeg) of the primitive legs ----------------
CHERRY = (sp.Integer(1), sp.Rational(3, 2), 2)       # cherryU  (length-2 leg)
LONG3 = (sp.Rational(3, 2), sp.Rational(7, 4), 2)    # armU 1   (length-3 leg)


def arm(j: int):
    """dtSub triple of a load-`j` arm `armU j` (`j` concrete)."""
    zt = sp.Rational(3, 2) ** j * (1 + sp.Rational(j, 1) / (3 * (j + 1)))
    zo = sp.Rational(3, 2) ** j
    return (zo, zt, j + 1)


def _node(children, root: bool):
    """(Zopen, Ztot, udeg) of a node.

    children: list of (count, (Zopen, Ztot, udeg)); count may be symbolic.
    root=True -> dtRealize (degree = #children); else dtSub (degree = #children + 1).
    """
    numch = sum(c for c, _ in children)
    d = numch if root else numch + 1
    popen = sp.prod([zt ** c for c, (zo, zt, ud) in children])
    qsum = sum(c * sp.Rational(1) / (d * ud) * (zo / zt) for c, (zo, zt, ud) in children)
    return sp.simplify(popen), sp.simplify(popen * (1 + qsum)), d


def hub_dtSub(legs, spine_child=None):
    """dtSub triple of a hub with the given legs (and one optional spine child)."""
    ch = list(legs) + ([(1, spine_child)] if spine_child else [])
    return _node(ch, root=False)


def hub_Aobj(legs, spine_child=None):
    """`Aobj` (root objective) of a hub with the given legs (and optional spine child)."""
    ch = list(legs) + ([(1, spine_child)] if spine_child else [])
    return _node(ch, root=True)[1]


def caterpillar_Aobj(hubs):
    """`Aobj` of a caterpillar: `hubs` is a list of leg-lists, spine chained left-to-right.

    hubs[-1] is the deepest hub (no further spine); hubs[0] is the root.
    """
    child = None
    for legs in reversed(hubs[1:]):
        child = hub_dtSub(legs, spine_child=child)
    return hub_Aobj(hubs[0], spine_child=child)


# --- domination certificate --------------------------------------------------
def hub_dom_cert(a_expr, b_expr, param, dom_lo):
    """Certify `Aobj(A) <= Aobj(B)` for integer `param >= dom_lo`.

    Via the ratio `r = B/A` (exponentials cancel -> rational in `param`):
    `r - 1 = num/den`; substitute `param -> dom_lo + t` (`t >= 0`) and check that
    the numerator and denominator polynomials in `t` have all-nonnegative
    coefficients (a Polya certificate on `[dom_lo, inf)`), so `r - 1 >= 0`.

    Returns `(ok: bool, cert: dict)`.
    """
    r = sp.simplify(b_expr / a_expr)
    num, den = sp.fraction(sp.together(r - 1))
    t = sp.Symbol("t", nonnegative=True)
    num_t = sp.expand(sp.expand(num).subs(param, dom_lo + t))
    den_t = sp.expand(sp.expand(den).subs(param, dom_lo + t))
    try:
        cn = sp.Poly(num_t, t).all_coeffs()
        cd = sp.Poly(den_t, t).all_coeffs()
    except sp.PolynomialError as e:
        return False, {"error": str(e), "ratio": r}
    # normalize denominator to positive leading coefficient
    if cd[0] < 0:
        cn = [-c for c in cn]
        cd = [-c for c in cd]
    ok = all(c >= 0 for c in cn) and all(c >= 0 for c in cd)
    return ok, {
        "ratio_B_over_A": sp.factor(r),
        "num_shifted": sp.factor(num_t),
        "num_coeffs": cn,
        "den_coeffs": cd,
    }

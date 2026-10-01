"""anchored_monotone_extension emitter -- a normalized parametric tree recursion is antitone past a
threshold, so an anchor value bounds the whole half-line.

conjecture1_proved = False.  This module certifies, for one explicitly given recursion and one
explicitly given normalizer, an inequality that holds on EVERY finite rooted tree.  It says nothing
about any open conjecture; downstream consumers state their own scope.

THE SHAPE
---------
Finite rooted trees (a node has ``k >= 0`` children; ``k = 0`` is a leaf).  A PARAMETRIC
RECURSION in a real parameter ``x`` (written ``lam`` in specs):

    A_b  = prod_c y_c   (mode "prod")      or      A_b = sum_c y_c   (mode "sum")
    T_b(x) = (prod_c T_c(x)) * g(x, A_b)
    y_b(x) = h(x, A_b)

with ``g``, ``h`` rational functions of ``(x, A)`` with rational coefficients.  The NORMALIZER is
``N(x, n) = psi(x) ** (rho * n)`` with ``psi`` rational in ``x`` and ``rho > 0`` rational, so that
``x d/dx log N(x, n) = n * c(x)`` with the per-vertex budget ``c = rho x psi' / psi``.

Certified, kernel-checked, for every tree ``b`` (``n_b`` = number of vertices):

(1) THE DERIVATIVE PRELUDE (generic Lean, once per file).  On ``[x0, oo)`` every ``T_b`` is
    positive and differentiable; its log-derivative ``D_b`` satisfies the explicit recursion

        D_b = sum_c D_c + (g_x + g_A A') / g,     E_b = (h_x + h_A A') / h,
        A' = A * sum_c E_c  (prod)   or   A' = sum_c y_c E_c  (sum),

    where ``E_b`` is the log-derivative of the message; ``D_b`` is DEFINED by this recursion and
    PROVED equal to ``d/dx log T_b`` (``hasDeriv_rec``, ``hasDerivAt_log_T``; mutual induction
    with ``HasDerivAt`` combinators: ``hasDerivAt_p2`` for a two-variable polynomial along
    ``t -> (t, A(t))``, ``HasDerivAt.fun_div``, ``HasDerivAt.fun_finsetProd``, ``HasDerivAt.fun_sum``).
(2) THE MONOTONICITY STEP.  ``x D_b <= n_b c(x)`` on ``[x0, oo)``, by an INDUCTIVE INVARIANT of
    two rows,

        row 0 (target):     x D_b                    <= n_b c(x)
        row 1 (auxiliary):  x D_b + mu(x) * x E_b    <= n_b c(x) + kappa(x),

    with ``mu > 0`` and ``kappa`` rational in ``x`` (supplied by the certificate).  The step
    writes a child's coefficient ``m`` on ``x E_c`` as the convex combination ``(1 - m/mu)``
    row 0 ``+ (m/mu)`` row 1, so the per-node content is FINITELY MANY POLYNOMIAL INEQUALITIES in
    ``(x, A[, k])`` (``k`` the child count): positivity of the four node polynomials, the weight
    window ``0 <= m <= mu``, and one cleared residual per row.  Hence ``log T_b - rho n_b log psi``
    and ``T_b / N(., n_b)`` are ANTITONE on ``[x0, oo)``
    (``antitoneOn_of_hasDerivWithinAt_nonpos``).
(3) THE ANCHOR + EXTENSION.  From ``T_b(xa) <= N(xa, n_b)`` for all ``b`` (``xa >= x0``), conclude
    ``T_b(x) <= N(x, n_b)`` for every ``x >= xa``.  The anchor is either a NODE CHECK at ``x0``
    (``g(x0, A)^q <= psi(x0)^p`` on the aggregate range, ``rho = p/q``; the anchor then follows
    by induction) or a HYPOTHESIS passed through to the final theorem (``hanchor``), for an
    anchor certified elsewhere.

Every polynomial inequality is certified by an exact product-basis expansion (Taylor at the
left end of an unbounded variable, Bernstein on a bounded one) with nonnegative coefficients,
with bisection into cells when needed; in Lean each cell is one ``linarith`` over the
product facts.

ANTI-PHANTOM REFUSALS
---------------------
``anchored_monotone_extension_certificate`` refuses: floats; symbols other than ``lam`` / ``A``;
a mode other than "prod" / "sum"; ``lam0 < 0``; ``rho <= 0``; an anchor point below ``lam0``;
a node polynomial not certified positive on ``[lam0, oo) x range(A)`` (product mode also needs
``h <= 1``); ``psi``, ``mu`` or the denominator of ``kappa`` not certified positive; a weight
window violated (the convex combination does not exist); a residual with a negative
coefficient at the subdivision limit (a too-small normalizer is refused HERE, with a located
exact violation when one is found); a failed anchor node check; degree caps.
``check=False`` is for hand-forged negative controls ONLY: it builds the same certificate
algebra with every sign check skipped, so the Lean kernel is the arbiter.

HONEST SCOPE: the two-row invariant is a sufficient condition.  Product mode needs messages in
``(0, 1]`` (so ``A`` ranges over ``[0, 1]``); sum mode lets ``A`` range over ``[0, oo)`` and
treats the child count as free (a relaxation, sound).  The dogfood instances are classical (the
hard-core / independent-set recursion) or synthetic (a matching-type sum recursion); nothing here
is specific to any open problem.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from math import comb

import sympy as sp

from .certify import CertifiedInstance
from .emit_concave_pooled_induction import _q
from .family import InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

conjecture1_proved = False

X_SYM = sp.Symbol("x")
A_SYM = sp.Symbol("a")
K_SYM = sp.Symbol("k")
_LOCALS = {"lam": X_SYM, "x": X_SYM, "A": A_SYM, "a": A_SYM}

#: total-degree cap for a single obligation polynomial (Lean cost of the product facts)
_MAX_DEGREE = 16
#: bisection depth for an obligation's cell cover
_MAX_DEPTH = 8
#: cap on product-basis terms in one cell (one linarith fact each)
_MAX_TERMS = 160


class AnchoredMonotoneRefusal(ValueError):
    """Raised when the certificate cannot be built or verified."""


def _refuse(msg: str) -> AnchoredMonotoneRefusal:
    return AnchoredMonotoneRefusal(f"anchored_monotone_extension REFUSED: {msg}")


# ---------------------------------------------------------------------------
# exact input handling
# ---------------------------------------------------------------------------

def _rat(v, what: str) -> sp.Rational:
    if isinstance(v, (bool, float)):
        raise _refuse(f"{what} = {v!r}: floats/bools are not exact; pass a Rational or a string")
    try:
        r = sp.Rational(sp.sympify(v)) if isinstance(v, str) else sp.Rational(v)
    except (TypeError, ValueError, sp.SympifyError):
        raise _refuse(f"{what} = {v!r} is not an exact rational") from None
    return r


def _expr(e, what: str, allowed: set) -> sp.Expr:
    if isinstance(e, float):
        raise _refuse(f"{what} = {e!r}: floats are not exact")
    ex = sp.sympify(e, locals=_LOCALS) if isinstance(e, str) else sp.sympify(e)
    ex = ex.subs({sp.Symbol("lam"): X_SYM, sp.Symbol("A"): A_SYM})
    if ex.has(sp.Float):
        raise _refuse(f"{what} = {ex}: contains a float")
    extra = ex.free_symbols - allowed
    if extra:
        names = {X_SYM: "lam", A_SYM: "A"}
        ok = ", ".join(sorted(names[s] for s in allowed))
        raise _refuse(f"{what} = {ex}: only the symbols {ok} are allowed "
                      f"(got {sorted(map(str, extra))})")
    return ex


def _ratfun(e, what: str, allowed: set) -> tuple[sp.Poly, sp.Poly]:
    """(numerator, denominator) polynomials in (x, a) over QQ, common factors cancelled, the
    denominator normalised to a positive leading coefficient."""
    ex = _expr(e, what, allowed)
    num, den = sp.fraction(sp.cancel(sp.together(ex)))
    try:
        pn = sp.Poly(num, X_SYM, A_SYM, domain="QQ")
        pd = sp.Poly(den, X_SYM, A_SYM, domain="QQ")
    except sp.PolynomialError:
        raise _refuse(f"{what} = {ex} is not a rational function") from None
    if pd.is_zero:
        raise _refuse(f"{what} has a zero denominator")
    if pd.LC() < 0:
        pn, pd = -pn, -pd
    return pn, pd


def _P(e) -> sp.Poly:
    return sp.Poly(sp.expand(e), X_SYM, A_SYM, K_SYM, domain="QQ")


# ---------------------------------------------------------------------------
# multivariate product-basis positivity (Taylor on [s, oo), Bernstein on [s, t])
# ---------------------------------------------------------------------------

_VARS = (X_SYM, A_SYM, K_SYM)


@dataclass(frozen=True)
class MCell:
    """A box ``((s, t|None) per variable x, a, k)`` and the product-basis coefficients of the
    obligation polynomial on it: ``P = sum_c c * prod_v basis_v(i_v)`` with
    ``basis_v(i) = (v - s)^i`` (unbounded) or ``(v - s)^i (t - v)^(d_v - i)`` (bounded)."""

    box: tuple
    degs: tuple
    coeffs: tuple          # ((i_x, i_a, i_k), c), every c != 0

    def ok(self, strict: bool) -> bool:
        if any(c < 0 for _, c in self.coeffs):
            return False
        if not strict:
            return True
        # strict: every product-basis index whose unbounded-variable part is zero must carry a
        # positive coefficient (their sum is a positive constant on the box)
        d = dict(self.coeffs)
        grids = []
        for (s, t), dv in zip(self.box, self.degs):
            grids.append(range(dv + 1) if t is not None else (0,))
        import itertools
        return all(d.get(ix, 0) > 0 for ix in itertools.product(*grids))


@dataclass(frozen=True)
class MCert:
    """``0 <= P`` (``0 < P`` when ``strict``) on the box ``dom``; ``tree`` is a cell or a split
    ``("split", var_index, point, left, right)``."""

    poly: tuple            # ((e_x, e_a, e_k), c) of P
    dom: tuple
    strict: bool
    tree: object

    def leaves(self) -> list:
        out, stack = [], [self.tree]
        while stack:
            n = stack.pop()
            if isinstance(n, MCell):
                out.append(n)
            else:
                stack.extend([n[4], n[3]])
        return out

    def ok(self) -> bool:
        return all(c.ok(self.strict) for c in self.leaves())

    def polynomial(self) -> sp.Poly:
        return sp.Poly(sum(c * X_SYM ** e[0] * A_SYM ** e[1] * K_SYM ** e[2]
                           for e, c in self.poly) if self.poly else 0,
                       *_VARS, domain="QQ")


def _poly_items(P: sp.Poly) -> tuple:
    return tuple(sorted((tuple(m), sp.Rational(c)) for m, c in P.terms() if c != 0))


def _expand_cell(P: sp.Poly, box) -> MCell:
    """Exact product-basis coefficients of ``P`` on ``box``."""
    u = sp.symbols("u0:3")
    sub = {}
    degs = []
    for v, uv, (s, t) in zip(_VARS, u, box):
        if t is not None and s == t:          # a fixed variable: substitute its value
            degs.append(0)
            sub[v] = s
            continue
        dv = max(P.degree(v), 0) if not P.is_zero else 0
        degs.append(dv)
        sub[v] = s + uv if t is None else s + (t - s) * uv
    Q = sp.Poly(sp.expand(P.as_expr().subs(sub, simultaneous=True)), *u, domain="QQ")
    coeffs = {tuple(m): sp.Rational(c) for m, c in Q.terms()}
    for axis, ((s, t), dv) in enumerate(zip(box, degs)):
        if t is None or s == t:
            continue
        w = (t - s) ** dv
        grouped: dict = {}
        for m, c in coeffs.items():
            rest = m[:axis] + (0,) + m[axis + 1:]
            grouped.setdefault(rest, [sp.Rational(0)] * (dv + 1))[m[axis]] += c
        new = {}
        for rest, p in grouped.items():
            for i in range(dv + 1):
                beta = sum(sp.Rational(comb(i, j), comb(dv, j)) * p[j] for j in range(i + 1))
                ci = beta * comb(dv, i) / w
                if ci != 0:
                    new[rest[:axis] + (i,) + rest[axis + 1:]] = ci
        coeffs = new
    return MCell(box=tuple(box), degs=tuple(degs),
                 coeffs=tuple(sorted((m, c) for m, c in coeffs.items() if c != 0)))


def cell_identity_holds(P: sp.Poly, cell: MCell) -> bool:
    """Re-expand a cell's certificate and compare with ``P`` exactly."""
    tot = 0
    for ix, c in cell.coeffs:
        term = c
        for v, i, (s, t), dv in zip(_VARS, ix, cell.box, cell.degs):
            term *= (v - s) ** i if t is None else (v - s) ** i * (t - v) ** (dv - i)
        tot += term
    return sp.expand(tot - P.as_expr()) == 0


def _split_point(s, t):
    if t is None:
        return 2 * s + 1 if s >= 0 else sp.Rational(0)
    return (s + t) / 2


def _probe(P: sp.Poly, box, strict: bool):
    """A located exact violation of the claim on ``box``, or None (a coarse grid search)."""
    pts = []
    for (s, t) in box:
        hi = t if t is not None else s + 64
        pts.append(sorted({s, hi, (s + hi) / 2, s + (hi - s) / 8, s + (hi - s) / 64,
                           s + (hi - s) * 7 / 8}))
    import itertools
    worst = None
    for pt in itertools.product(*pts):
        v = P.eval(dict(zip(_VARS, pt))) if not P.is_zero else 0
        if (v < 0) or (strict and v == 0):
            if worst is None or v < worst[0]:
                worst = (v, pt)
    return worst


def _mcert(P: sp.Poly, dom, strict: bool, *, check: bool, what: str) -> MCert:
    deg = P.total_degree() if not P.is_zero else 0
    if deg > _MAX_DEGREE:
        raise _refuse(f"{what}: obligation polynomial of total degree {deg} > {_MAX_DEGREE}")
    split_vars = [i for i, (s, t) in enumerate(dom) if i < 2 and not (t is not None and s == t)]

    def rec(box, depth):
        cell = _expand_cell(P, box)
        if len(cell.coeffs) > _MAX_TERMS:
            raise _refuse(f"{what}: {len(cell.coeffs)} product-basis terms > {_MAX_TERMS}")
        if cell.ok(strict) or not check:
            return cell
        if depth >= _MAX_DEPTH or not split_vars:
            bad = _probe(P, box, strict)
            loc = ("" if bad is None else
                   f"; FALSE at (lam, A, k) = {tuple(str(v) for v in bad[1])}: value {bad[0]}")
            raise _refuse(f"{what}: no nonnegative product-basis certificate for "
                          f"{'0 < ' if strict else '0 <= '}{P.as_expr()} on the box "
                          f"{_box_txt(box)} down to the subdivision limit{loc}")
        vi = split_vars[depth % len(split_vars)]
        s, t = box[vi]
        m = _split_point(s, t)
        lb = list(box)
        rb = list(box)
        lb[vi] = (s, m)
        rb[vi] = (m, t)
        return ("split", vi, m, rec(tuple(lb), depth + 1), rec(tuple(rb), depth + 1))

    bad = _probe(P, dom, strict) if check else None
    if bad is not None:
        raise _refuse(f"{what}: the claim {'0 < ' if strict else '0 <= '}{P.as_expr()} is FALSE "
                      f"at (lam, A, k) = {tuple(str(v) for v in bad[1])}: value {bad[0]}")
    return MCert(poly=_poly_items(P), dom=tuple(dom), strict=strict, tree=rec(tuple(dom), 0))


def _box_txt(box) -> str:
    names = ("lam", "A", "k")
    return " x ".join(f"{n} in [{s}, {'oo' if t is None else t}]"
                      for n, (s, t) in zip(names, box) if not (t is not None and s == t))


# ---------------------------------------------------------------------------
# the certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Obligation:
    """One named polynomial obligation and its certificate."""

    name: str
    cert: MCert


@dataclass(frozen=True)
class AnchoredMonotoneCert:
    """A verified anchored-monotone-extension certificate (all fields exact)."""

    mode: str                  # "prod" | "sum"
    lam0: sp.Rational
    g: tuple                   # (num Poly, den Poly) in (x, a)
    h: tuple
    psi: tuple                 # (num, den) in x
    rho: sp.Rational
    mu: tuple
    kappa: tuple
    anchor: dict               # {"kind": "node", "p": p, "q": q} | {"kind": "hypothesis", "at": xa}
    obligations: tuple         # Obligation
    exprs: dict = field(default_factory=dict, compare=False)   # human-readable inputs
    checked: bool = True       # False only for hand-forged (negative-control) certificates

    @property
    def prod(self) -> bool:
        return self.mode == "prod"

    def obligation(self, name: str) -> Obligation:
        for o in self.obligations:
            if o.name == name:
                return o
        raise KeyError(name)


def _d(P: sp.Poly, v) -> sp.Poly:
    return sp.Poly(sp.diff(P.as_expr(), v), X_SYM, A_SYM, domain="QQ")


def obligation_polynomials(mode, lam0, g, h, psi, rho, mu, kappa, anchor) -> list:
    """The obligations as ``(name, polynomial, domain, strict)``; the polynomial is exactly the
    cleared form the Lean generic layer consumes (``Rec.KN``, ``Rec.Q``, ...)."""
    gN, gD = g
    hN, hD = h
    pN, pD = psi
    mN, mD = mu
    kN, kD = kappa
    prod = mode == "prod"
    ex = lambda P: P.as_expr()  # noqa: E731
    Gx = ex(_d(gN, X_SYM)) * ex(gD) - ex(gN) * ex(_d(gD, X_SYM))
    Gq = ex(_d(gN, A_SYM)) * ex(gD) - ex(gN) * ex(_d(gD, A_SYM))
    Dg = ex(gN) * ex(gD)
    Hx = ex(_d(hN, X_SYM)) * ex(hD) - ex(hN) * ex(_d(hD, X_SYM))
    Hq = ex(_d(hN, A_SYM)) * ex(hD) - ex(hN) * ex(_d(hD, A_SYM))
    Dh = ex(hN) * ex(hD)
    Px = ex(_d(pN, X_SYM)) * ex(pD) - ex(pN) * ex(_d(pD, X_SYM))
    x = X_SYM
    a = A_SYM
    W = K_SYM * a if prod else a
    arng = (sp.Rational(0), sp.Rational(1)) if prod else (sp.Rational(0), None)
    xr = (lam0, None)
    k0 = (sp.Rational(0), sp.Rational(0))
    dom2 = (xr, arng, k0)
    dom1 = (xr, k0, k0)
    dom3 = (xr, arng, (sp.Rational(0), None)) if prod else dom2
    out = [
        ("gN", ex(gN), dom2, True), ("gD", ex(gD), dom2, True),
        ("hN", ex(hN), dom2, True), ("hD", ex(hD), dom2, True),
    ]
    if prod:
        out.append(("hle", ex(hD) - ex(hN), dom2, False))
    out += [("pN", ex(pN), dom1, True), ("pD", ex(pD), dom1, True),
            ("mN", ex(mN), dom1, True), ("mD", ex(mD), dom1, True),
            ("kD", ex(kD), dom1, True)]
    for iota in (0, 1):
        KN = ex(mD) * Dh * Gq + iota * ex(mN) * Dg * Hq
        Q = (rho * x * Px * Dg * Dh * ex(mD) * ex(mN) * ex(kD)
             + iota * ex(kN) * Dg * Dh * ex(mD) * ex(mN) * ex(pN) * ex(pD)
             - x * Gx * Dh * ex(mD) * ex(mN) * ex(kD) * ex(pN) * ex(pD)
             - iota * ex(mN) ** 2 * x * Hx * Dg * ex(kD) * ex(pN) * ex(pD)
             - ex(kN) * ex(mD) * KN * W * ex(pN) * ex(pD))
        out.append((f"K{iota}", KN, dom2, False))
        out.append((f"K{iota}le", ex(mN) * Dg * Dh - a * KN, dom2, False))
        out.append((f"res{iota}", Q, dom3, False))
    if anchor["kind"] == "node":
        p, q = anchor["p"], anchor["q"]
        sub = {x: lam0}
        P = (ex(pN).subs(sub) ** p * ex(gD).subs(sub) ** q
             - ex(gN).subs(sub) ** q * ex(pD).subs(sub) ** p)
        out.append(("anchor", P, ((lam0, lam0), arng, k0), False))
    return [(n, _P(P), dom, st) for n, P, dom, st in out]


def anchored_monotone_extension_certificate(*, mode: str, g, h, psi, rho, lam0, mu, kappa,
                                            anchor, check: bool = True) -> AnchoredMonotoneCert:
    """Build and (unless ``check=False``) verify the certificate.

    ``g``, ``h``: rational functions of ``lam`` and ``A`` (node factor and message);
    ``psi``: rational function of ``lam``; ``rho``: the normalizer exponent per vertex;
    ``lam0``: the threshold; ``mu``, ``kappa``: the auxiliary invariant row (rational in
    ``lam``); ``anchor``: ``{"kind": "node"}`` (checked at ``lam0``) or
    ``{"kind": "hypothesis", "at": xa}`` (passed through as a Lean hypothesis)."""
    if mode not in ("prod", "sum"):
        raise _refuse(f"mode = {mode!r}: must be 'prod' or 'sum'")
    lam0 = _rat(lam0, "lam0")
    if lam0 < 0:
        raise _refuse(f"lam0 = {lam0} < 0: the threshold must be >= 0")
    rho = _rat(rho, "rho")
    if rho <= 0:
        raise _refuse(f"rho = {rho} <= 0")
    both = {X_SYM, A_SYM}
    gq = _ratfun(g, "g", both)
    hq = _ratfun(h, "h", both)
    psiq = _ratfun(psi, "psi", {X_SYM})
    muq = _ratfun(mu, "mu", {X_SYM})
    kq = _ratfun(kappa, "kappa", {X_SYM})
    anchor = dict(anchor)
    if anchor.get("kind") == "node":
        anchor = {"kind": "node", "p": int(rho.p), "q": int(rho.q)}
    elif anchor.get("kind") == "hypothesis":
        xa = _rat(anchor.get("at"), "anchor point")
        if xa < lam0:
            raise _refuse(f"anchor point {xa} < lam0 = {lam0}: the extension runs from the "
                          f"anchor rightwards inside [lam0, oo)")
        anchor = {"kind": "hypothesis", "at": xa}
    else:
        raise _refuse(f"anchor = {anchor!r}: kind must be 'node' or 'hypothesis'")
    obs = []
    for name, P, dom, strict in obligation_polynomials(mode, lam0, gq, hq, psiq, rho, muq, kq,
                                                       anchor):
        obs.append(Obligation(name, _mcert(P, dom, strict, check=check,
                                           what=f"obligation {name}")))
    exprs = {"g": sp.sstr(_expr(g, "g", both)), "h": sp.sstr(_expr(h, "h", both)),
             "psi": sp.sstr(_expr(psi, "psi", {X_SYM})), "mu": sp.sstr(_expr(mu, "mu", {X_SYM})),
             "kappa": sp.sstr(_expr(kappa, "kappa", {X_SYM}))}
    cert = AnchoredMonotoneCert(mode=mode, lam0=lam0, g=gq, h=hq, psi=psiq, rho=rho, mu=muq,
                                kappa=kq, anchor=anchor, obligations=tuple(obs), exprs=exprs,
                                checked=check)
    if check:
        verify_certificate(cert)
    return cert


def verify_certificate(cert: AnchoredMonotoneCert) -> None:
    """Independent exact re-check: every obligation is recomputed from the recursion data and
    every cell's product-basis expansion is re-expanded and sign-checked."""
    want = obligation_polynomials(cert.mode, cert.lam0, cert.g, cert.h, cert.psi, cert.rho,
                                  cert.mu, cert.kappa, cert.anchor)
    if [w[0] for w in want] != [o.name for o in cert.obligations]:
        raise _refuse("the obligation list does not match the recursion data")
    for (name, P, dom, strict), o in zip(want, cert.obligations):
        if _poly_items(P) != o.cert.poly or tuple(dom) != o.cert.dom or strict != o.cert.strict:
            raise _refuse(f"obligation {name}: stored polynomial does not match its recomputation")
        _check_tree(P, o.cert.tree, o.cert.dom, name)
        if not o.cert.ok():
            raise _refuse(f"obligation {name}: a cell has a negative product-basis coefficient")


def _check_tree(P, node, box, name):
    if isinstance(node, MCell):
        if tuple(node.box) != tuple(box) or not cell_identity_holds(P, node):
            raise _refuse(f"obligation {name}: a cell's expansion does not re-expand to P")
        return
    _, vi, m, left, right = node
    s, t = box[vi]
    if not (m > s and (t is None or m < t)):
        raise _refuse(f"obligation {name}: a split point lies outside its cell")
    lb, rb = list(box), list(box)
    lb[vi] = (s, m)
    rb[vi] = (m, t)
    _check_tree(P, left, tuple(lb), name)
    _check_tree(P, right, tuple(rb), name)


def certify_anchored_monotone_extension_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``, a dict of the keyword arguments of
    :func:`anchored_monotone_extension_certificate` (plus optional ``sanity``)."""
    spec = dict(family.special[1](pt))
    spec.pop("sanity", None)
    cert = anchored_monotone_extension_certificate(**spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.obligations)


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

_GENERIC = r"""set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Generic anchored monotone extension (emitted once per file)

A parametric recursion on finite rooted trees, its log-derivative recursion (the derivative
prelude), a two-row inductive invariant whose per-node content is finitely many polynomial
checks, the antitone normalized ratio, and the anchored extension.  Everything here is
re-derived from Mathlib; per instance only the polynomial checks remain.
conjecture1_proved = False. -/

namespace AnchoredMonotone

set_option linter.unusedVariables false

/-- Finite rooted trees: a node with `k ≥ 0` children (`k = 0` is a leaf). -/
inductive RTree : Type
  | node (k : ℕ) (cs : Fin k → RTree) : RTree

namespace RTree

/-- Number of vertices. -/
def size : RTree → ℕ
  | node _ cs => 1 + ∑ i, size (cs i)

end RTree

/-! ### Two-variable polynomials as coefficient lists `[(i, j, c), ...] ↦ Σ c x^i a^j`. -/

noncomputable def p2 : List (ℕ × ℕ × ℝ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | t :: L, x, a => t.2.2 * x ^ t.1 * a ^ t.2.1 + p2 L x a

/-- The `x`-partial derivative's coefficient list. -/
def p2dx : List (ℕ × ℕ × ℝ) → List (ℕ × ℕ × ℝ)
  | [] => []
  | t :: L => (t.1 - 1, t.2.1, t.2.2 * t.1) :: p2dx L

/-- The `a`-partial derivative's coefficient list. -/
def p2da : List (ℕ × ℕ × ℝ) → List (ℕ × ℕ × ℝ)
  | [] => []
  | t :: L => (t.1, t.2.1 - 1, t.2.2 * t.2.1) :: p2da L

/-- Chain rule for a two-variable polynomial along `t ↦ (t, U t)`. -/
theorem hasDerivAt_p2 (L : List (ℕ × ℕ × ℝ)) {U : ℝ → ℝ} {u' x : ℝ}
    (hU : HasDerivAt U u' x) :
    HasDerivAt (fun t => p2 L t (U t)) (p2 (p2dx L) x (U x) + p2 (p2da L) x (U x) * u') x := by
  induction L with
  | nil => simpa [p2, p2dx, p2da] using hasDerivAt_const x (0 : ℝ)
  | cons t L ih =>
    obtain ⟨i, j, c⟩ := t
    have h1 := ((hasDerivAt_pow i x).const_mul c).mul (hU.fun_pow j)
    have h2 : HasDerivAt (fun t => c * t ^ i * U t ^ j + p2 L t (U t)) _ x := h1.add ih
    refine h2.congr_deriv ?_
    simp only [p2, p2dx, p2da]
    ring

/-- The quotient `N / D` of two coefficient lists and its two partial derivatives. -/
noncomputable def rq (N D : List (ℕ × ℕ × ℝ)) (x a : ℝ) : ℝ := p2 N x a / p2 D x a

noncomputable def rqx (N D : List (ℕ × ℕ × ℝ)) (x a : ℝ) : ℝ :=
  (p2 (p2dx N) x a * p2 D x a - p2 N x a * p2 (p2dx D) x a) / p2 D x a ^ 2

noncomputable def rqa (N D : List (ℕ × ℕ × ℝ)) (x a : ℝ) : ℝ :=
  (p2 (p2da N) x a * p2 D x a - p2 N x a * p2 (p2da D) x a) / p2 D x a ^ 2

theorem hasDerivAt_rq (N D : List (ℕ × ℕ × ℝ)) {U : ℝ → ℝ} {u' x : ℝ}
    (hU : HasDerivAt U u' x) (hD : p2 D x (U x) ≠ 0) :
    HasDerivAt (fun t => rq N D t (U t)) (rqx N D x (U x) + rqa N D x (U x) * u') x := by
  have h := (hasDerivAt_p2 N hU).fun_div (hasDerivAt_p2 D hU) hD
  refine h.congr_deriv ?_
  simp only [rqx, rqa]
  field_simp
  ring

/-- A product of positive functions, from the log-derivatives of the factors. -/
theorem hasDerivAt_prod_log {k : ℕ} (F : Fin k → ℝ → ℝ) (e : Fin k → ℝ) {x : ℝ}
    (hF : ∀ i, HasDerivAt (F i) (F i x * e i) x) :
    HasDerivAt (fun t => ∏ i, F i t) ((∏ i, F i x) * ∑ i, e i) x := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hF i)
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ hi]
  ring

/-! ### The parametric tree recursion and its log-derivative recursion -/

/-- A parametric recursion on rooted trees.  At a node with children `c`, the aggregate
`A = ∏ y_c` (`prod = true`) or `A = Σ y_c` (`prod = false`); the node value is
`T = (∏ T_c) · g(x, A)` and the message is `y = h(x, A)`, with `g = gN / gD`, `h = hN / hD`. -/
structure Rec where
  prod : Bool
  gN : List (ℕ × ℕ × ℝ)
  gD : List (ℕ × ℕ × ℝ)
  hN : List (ℕ × ℕ × ℝ)
  hD : List (ℕ × ℕ × ℝ)

namespace Rec

noncomputable def agg (R : Rec) {k : ℕ} (f : Fin k → ℝ) : ℝ :=
  if R.prod then ∏ i, f i else ∑ i, f i

/-- The derivative of the aggregate, from the children's values `f` and log-derivatives `e`. -/
noncomputable def aggD (R : Rec) {k : ℕ} (f e : Fin k → ℝ) : ℝ :=
  if R.prod then (∏ i, f i) * ∑ i, e i else ∑ i, f i * e i

/-- The aggregate's range: `0 ≤ a ≤ 1` for a product of messages in the unit interval, `0 ≤ a`
for a sum. -/
def inA (R : Rec) (a : ℝ) : Prop := 0 ≤ a ∧ (R.prod = true → a ≤ 1)

/-- The message. -/
noncomputable def y (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x => rq R.hN R.hD x (R.agg fun i => y R (cs i) x)

/-- The tree value. -/
noncomputable def T (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x => (∏ i, T R (cs i) x) * rq R.gN R.gD x (R.agg fun i => y R (cs i) x)

/-- The log-derivative of the message, by recursion. -/
noncomputable def E (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x =>
      (rqx R.hN R.hD x (R.agg fun i => y R (cs i) x) +
        rqa R.hN R.hD x (R.agg fun i => y R (cs i) x) *
          R.aggD (fun i => y R (cs i) x) (fun i => E R (cs i) x)) /
      rq R.hN R.hD x (R.agg fun i => y R (cs i) x)

/-- The log-derivative of the tree value, by recursion. -/
noncomputable def D (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x =>
      (∑ i, D R (cs i) x) +
      (rqx R.gN R.gD x (R.agg fun i => y R (cs i) x) +
        rqa R.gN R.gD x (R.agg fun i => y R (cs i) x) *
          R.aggD (fun i => y R (cs i) x) (fun i => E R (cs i) x)) /
      rq R.gN R.gD x (R.agg fun i => y R (cs i) x)

/-- Pointwise well-posedness at `x`: the four node polynomials are positive on the aggregate
range, and in product mode the message stays `≤ 1`. -/
def Good (R : Rec) (x : ℝ) : Prop :=
  ∀ a, R.inA a → 0 < p2 R.gN x a ∧ 0 < p2 R.gD x a ∧ 0 < p2 R.hN x a ∧ 0 < p2 R.hD x a ∧
    (R.prod = true → p2 R.hN x a ≤ p2 R.hD x a)

theorem agg_inA (R : Rec) {k : ℕ} (f : Fin k → ℝ) (hpos : ∀ i, 0 < f i)
    (hle : R.prod = true → ∀ i, f i ≤ 1) : R.inA (R.agg f) := by
  unfold agg inA
  cases hp : R.prod
  · simp only [Bool.false_eq_true, if_false, false_implies, and_true]
    exact Finset.sum_nonneg (fun i _ => (hpos i).le)
  · simp only [if_true, forall_const]
    exact ⟨Finset.prod_nonneg (fun i _ => (hpos i).le),
      Finset.prod_le_one (fun i _ => (hpos i).le) (fun i _ => hle hp i)⟩

theorem hasDerivAt_agg (R : Rec) {k : ℕ} (F : Fin k → ℝ → ℝ) (e : Fin k → ℝ) {x : ℝ}
    (hF : ∀ i, HasDerivAt (F i) (F i x * e i) x) :
    HasDerivAt (fun t => R.agg fun i => F i t) (R.aggD (fun i => F i x) e) x := by
  unfold agg aggD
  cases R.prod
  · simp only [Bool.false_eq_true, if_false]
    exact HasDerivAt.fun_sum (fun i _ => hF i)
  · simp only [if_true]
    exact hasDerivAt_prod_log F e hF

/-- THE DERIVATIVE PRELUDE: under pointwise well-posedness, every message is positive (and
`≤ 1` in product mode), every tree value is positive, and the recursively
defined `E`, `D` are the log-derivatives of the message and of the tree value. -/
theorem hasDeriv_rec (R : Rec) {x : ℝ} (hG : R.Good x) :
    ∀ b : RTree, 0 < R.y b x ∧ (R.prod = true → R.y b x ≤ 1) ∧ 0 < R.T b x ∧
      HasDerivAt (R.y b) (R.y b x * R.E b x) x ∧ HasDerivAt (R.T b) (R.T b x * R.D b x) x := by
  intro b
  induction b with
  | node k cs ih =>
    set A := R.agg fun i => R.y (cs i) x with hA
    have hAin : R.inA A := R.agg_inA _ (fun i => (ih i).1) (fun hp i => (ih i).2.1 hp)
    obtain ⟨hgN, hgD, hhN, hhD, hle⟩ := hG A hAin
    have hAd := R.hasDerivAt_agg (fun i => R.y (cs i)) (fun i => R.E (cs i) x)
      (fun i => (ih i).2.2.2.1)
    have hyv : R.y (.node k cs) x = rq R.hN R.hD x A := by simp only [y, hA]
    have hTv : R.T (.node k cs) x = (∏ i, R.T (cs i) x) * rq R.gN R.gD x A := by
      simp only [T, hA]
    have hq : 0 < rq R.hN R.hD x A := div_pos hhN hhD
    have hg : 0 < rq R.gN R.gD x A := div_pos hgN hgD
    have hP : 0 < ∏ i, R.T (cs i) x := Finset.prod_pos (fun i _ => (ih i).2.2.1)
    refine ⟨hyv ▸ hq, fun hp => ?_, hTv ▸ mul_pos hP hg, ?_, ?_⟩
    · rw [hyv, rq, div_le_one hhD]; exact hle hp
    · have h := hasDerivAt_rq R.hN R.hD hAd hhD.ne'
      have hfun : R.y (.node k cs) = fun t => rq R.hN R.hD t (R.agg fun i => R.y (cs i) t) := by
        funext t; simp only [y]
      rw [hfun]
      refine h.congr_deriv ?_
      simp only [E, ← hA]
      field_simp
    · have h1 := hasDerivAt_prod_log (fun i => R.T (cs i)) (fun i => R.D (cs i) x)
        (fun i => (ih i).2.2.2.2)
      have h2 := hasDerivAt_rq R.gN R.gD hAd hgD.ne'
      have h := h1.mul h2
      have hfun : R.T (.node k cs) =
          fun t => (∏ i, R.T (cs i) t) * rq R.gN R.gD t (R.agg fun i => R.y (cs i) t) := by
        funext t; simp only [T]
      rw [hfun]
      refine h.congr_deriv ?_
      simp only [D, ← hA]
      field_simp

/-- `D` is the derivative of `log T`. -/
theorem hasDerivAt_log_T (R : Rec) {x : ℝ} (hG : R.Good x) (b : RTree) :
    HasDerivAt (fun t => Real.log (R.T b t)) (R.D b x) x := by
  obtain ⟨-, -, hT, -, hd⟩ := R.hasDeriv_rec hG b
  have := hd.log hT.ne'
  refine this.congr_deriv ?_
  field_simp

end Rec

/-! ### The normalizer, the auxiliary invariant row and the cleared node checks -/

/-- The normalizer `N(x, n) = ψ(x) ^ (ρ n)` with `ψ = pN / pD` (lists in `x` alone). -/
structure Norm where
  pN : List (ℕ × ℕ × ℝ)
  pD : List (ℕ × ℕ × ℝ)
  rho : ℝ

/-- The auxiliary invariant row `x D + μ (x E) ≤ n C + κ`, `μ = mN / mD`, `κ = kN / kD`. -/
structure Aux where
  mN : List (ℕ × ℕ × ℝ)
  mD : List (ℕ × ℕ × ℝ)
  kN : List (ℕ × ℕ × ℝ)
  kD : List (ℕ × ℕ × ℝ)

noncomputable def Norm.psi (N : Norm) (x : ℝ) : ℝ := p2 N.pN x 0 / p2 N.pD x 0
/-- `ψ'(x) pN pD / ψ = pN' pD - pN pD'`. -/
noncomputable def Norm.Px (N : Norm) (x : ℝ) : ℝ :=
  p2 (p2dx N.pN) x 0 * p2 N.pD x 0 - p2 N.pN x 0 * p2 (p2dx N.pD) x 0
/-- The per-vertex budget `C(x) = ρ x ψ'(x) / ψ(x)`, so that `x ∂ₓ log N(x, n) = n C(x)`. -/
noncomputable def Norm.C (N : Norm) (x : ℝ) : ℝ :=
  N.rho * x * N.Px x / (p2 N.pN x 0 * p2 N.pD x 0)
noncomputable def Aux.mu (I : Aux) (x : ℝ) : ℝ := p2 I.mN x 0 / p2 I.mD x 0
noncomputable def Aux.kap (I : Aux) (x : ℝ) : ℝ := p2 I.kN x 0 / p2 I.kD x 0

namespace Rec

/-- Cleared partials: `x gₓ/g = x Gx / Dg`, `g_a/g = Gq / Dg`, same for `h`. -/
noncomputable def Gx (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2dx R.gN) x a * p2 R.gD x a - p2 R.gN x a * p2 (p2dx R.gD) x a
noncomputable def Gq (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2da R.gN) x a * p2 R.gD x a - p2 R.gN x a * p2 (p2da R.gD) x a
noncomputable def Dg (R : Rec) (x a : ℝ) : ℝ := p2 R.gN x a * p2 R.gD x a
noncomputable def Hx (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2dx R.hN) x a * p2 R.hD x a - p2 R.hN x a * p2 (p2dx R.hD) x a
noncomputable def Hq (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2da R.hN) x a * p2 R.hD x a - p2 R.hN x a * p2 (p2da R.hD) x a
noncomputable def Dh (R : Rec) (x a : ℝ) : ℝ := p2 R.hN x a * p2 R.hD x a

/-- `K_ι · Dg · Dh · mD`, where `K_ι = g_a/g + ι μ h_a/h` is the coefficient of a child's
`x E` in row `ι` (row 0: `x D ≤ n C`; row 1: the auxiliary row). -/
noncomputable def KN (R : Rec) (I : Aux) (ι x a : ℝ) : ℝ :=
  p2 I.mD x 0 * R.Dh x a * R.Gq x a + ι * p2 I.mN x 0 * R.Dg x a * R.Hq x a

/-- The children's weight total: `k·A` (product mode) or `A` (sum mode). -/
noncomputable def wt (R : Rec) (k : ℕ) (a : ℝ) : ℝ := if R.prod then (k : ℝ) * a else a

/-- The cleared residual of row `ι` (must be `≥ 0`):
`(C + ικ − α − ιμγ − (κ/μ) K_ι W) · Dg Dh mD mN kD pN pD`. -/
noncomputable def Q (R : Rec) (N : Norm) (I : Aux) (ι x a w : ℝ) : ℝ :=
  N.rho * x * N.Px x * R.Dg x a * R.Dh x a * p2 I.mD x 0 * p2 I.mN x 0 * p2 I.kD x 0
  + ι * p2 I.kN x 0 * R.Dg x a * R.Dh x a * p2 I.mD x 0 * p2 I.mN x 0 * p2 N.pN x 0 * p2 N.pD x 0
  - x * R.Gx x a * R.Dh x a * p2 I.mD x 0 * p2 I.mN x 0 * p2 I.kD x 0 * p2 N.pN x 0 * p2 N.pD x 0
  - ι * p2 I.mN x 0 ^ 2 * x * R.Hx x a * R.Dg x a * p2 I.kD x 0 * p2 N.pN x 0 * p2 N.pD x 0
  - p2 I.kN x 0 * p2 I.mD x 0 * R.KN I ι x a * w * p2 N.pN x 0 * p2 N.pD x 0

end Rec

/-- The cleared residual, generically: one `field_simp` for every instance. -/
theorem resid_of_Q (ρ x Gx Gq Dg Hx Hq Dh mN mD kN kD pN pD Px ι W : ℝ)
    (hDg : 0 < Dg) (hDh : 0 < Dh) (hmN : 0 < mN) (hmD : 0 < mD) (hkD : 0 < kD)
    (hpN : 0 < pN) (hpD : 0 < pD)
    (hQ : 0 ≤ ρ * x * Px * Dg * Dh * mD * mN * kD
      + ι * kN * Dg * Dh * mD * mN * pN * pD
      - x * Gx * Dh * mD * mN * kD * pN * pD
      - ι * mN ^ 2 * x * Hx * Dg * kD * pN * pD
      - kN * mD * (mD * Dh * Gq + ι * mN * Dg * Hq) * W * pN * pD) :
    x * Gx / Dg + ι * (mN / mD) * (x * Hx / Dh)
      + (kN / kD) / (mN / mD) * ((Gq / Dg + ι * (mN / mD) * (Hq / Dh)) * W)
      ≤ ρ * x * Px / (pN * pD) + ι * (kN / kD) := by
  rw [← sub_nonneg]
  have hM : 0 < Dg * Dh * mD * mN * kD * pN * pD := by positivity
  have key : ρ * x * Px / (pN * pD) + ι * (kN / kD) - (x * Gx / Dg + ι * (mN / mD) * (x * Hx / Dh)
      + (kN / kD) / (mN / mD) * ((Gq / Dg + ι * (mN / mD) * (Hq / Dh)) * W)) =
      (ρ * x * Px * Dg * Dh * mD * mN * kD
      + ι * kN * Dg * Dh * mD * mN * pN * pD
      - x * Gx * Dh * mD * mN * kD * pN * pD
      - ι * mN ^ 2 * x * Hx * Dg * kD * pN * pD
      - kN * mD * (mD * Dh * Gq + ι * mN * Dg * Hq) * W * pN * pD) /
        (Dg * Dh * mD * mN * kD * pN * pD) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg hQ hM.le

/-- `K_ι = KN_ι / (Dg Dh mD)` in semantic form. -/
theorem K_eq (Gq Dg Hq Dh mN mD ι : ℝ) (hDg : 0 < Dg) (hDh : 0 < Dh) (hmD : 0 < mD) :
    Gq / Dg + ι * (mN / mD) * (Hq / Dh) = (mD * Dh * Gq + ι * mN * Dg * Hq) / (Dg * Dh * mD) := by
  field_simp

namespace Rec

/-- The per-instance obligations: finitely many polynomial inequalities in `(x, a[, k])`. -/
structure Checks (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) : Prop where
  x0_nonneg : 0 ≤ x0
  good : ∀ x, x0 ≤ x → R.Good x
  pos1 : ∀ x, x0 ≤ x → 0 < p2 N.pN x 0 ∧ 0 < p2 N.pD x 0 ∧ 0 < p2 I.mN x 0 ∧
    0 < p2 I.mD x 0 ∧ 0 < p2 I.kD x 0
  K0 : ∀ x a, x0 ≤ x → R.inA a → 0 ≤ R.KN I 0 x a
  K0le : ∀ x a, x0 ≤ x → R.inA a → a * R.KN I 0 x a ≤ p2 I.mN x 0 * R.Dg x a * R.Dh x a
  K1 : ∀ x a, x0 ≤ x → R.inA a → 0 ≤ R.KN I 1 x a
  K1le : ∀ x a, x0 ≤ x → R.inA a → a * R.KN I 1 x a ≤ p2 I.mN x 0 * R.Dg x a * R.Dh x a
  res0 : ∀ x a (k : ℕ), x0 ≤ x → R.inA a → 0 ≤ R.Q N I 0 x a (R.wt k a)
  res1 : ∀ x a (k : ℕ), x0 ≤ x → R.inA a → 0 ≤ R.Q N I 1 x a (R.wt k a)

/-- One child's contribution: from the two rows at the child and a weight `m ∈ [0, μ]`. -/
theorem child_step (d σ nC μ κ m : ℝ) (hμ : 0 < μ) (hm0 : 0 ≤ m) (hm1 : m ≤ μ)
    (r0 : d ≤ nC) (r1 : d + μ * σ ≤ nC + κ) : d + m * σ ≤ nC + m / μ * κ := by
  set θ := m / μ with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hm0 hμ.le
  have hθ1 : θ ≤ 1 := (div_le_one hμ).2 hm1
  have hm : m = θ * μ := by rw [hθ]; field_simp
  have e1 := mul_le_mul_of_nonneg_left r0 (sub_nonneg.2 hθ1)
  have e2 := mul_le_mul_of_nonneg_left r1 hθ0
  rw [hm]
  nlinarith [e1, e2]

/-- THE INDUCTIVE INVARIANT: for `x ≥ x0`, every tree satisfies the target row
`x D_b ≤ n_b C(x)` and the auxiliary row `x D_b + μ (x E_b) ≤ n_b C(x) + κ`. -/
theorem invariant (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0) :
    ∀ b : RTree, ∀ x, x0 ≤ x → x * R.D b x ≤ b.size * N.C x ∧
      x * R.D b x + I.mu x * (x * R.E b x) ≤ b.size * N.C x + I.kap x := by
  intro b
  induction b with
  | node k cs ih =>
    intro x hx
    have hG := hc.good x hx
    obtain ⟨hpN, hpD, hmN, hmD, hkD⟩ := hc.pos1 x hx
    have hch := fun i => R.hasDeriv_rec hG (cs i)
    set A := R.agg fun i => R.y (cs i) x with hA
    set Ad := R.aggD (fun i => R.y (cs i) x) (fun i => R.E (cs i) x) with hAd
    have hAin : R.inA A := R.agg_inA _ (fun i => (hch i).1) (fun hp i => (hch i).2.1 hp)
    obtain ⟨hgN, hgD, hhN, hhD, -⟩ := hG A hAin
    have hDg : 0 < R.Dg x A := mul_pos hgN hgD
    have hDh : 0 < R.Dh x A := mul_pos hhN hhD
    have hμ : 0 < I.mu x := div_pos hmN hmD
    -- the weights `w i` and the aggregate derivative
    let w : Fin k → ℝ := fun i => if R.prod then A else R.y (cs i) x
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i; simp only [w]; split_ifs
      · exact hAin.1
      · exact (hch i).1.le
    have hwA : ∀ i, w i ≤ A := by
      intro i; simp only [w]; split_ifs with hp
      · exact le_rfl
      · simp only [hA, agg, hp, Bool.false_eq_true, if_false]
        exact Finset.single_le_sum (f := fun j => R.y (cs j) x)
          (fun j _ => (hch j).1.le) (Finset.mem_univ i)
    have hwsum : ∑ i, w i = R.wt k A := by
      simp only [w, wt]; split_ifs
      · simp
      · simp only [hA, agg]; split_ifs; rfl
    have hxAd : x * Ad = ∑ i, w i * (x * R.E (cs i) x) := by
      simp only [hAd, aggD, w, hA, agg]
      split_ifs
      · simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have k1 : x * R.D (.node k cs) x = (∑ i, x * R.D (cs i) x) + x * R.Gx x A / R.Dg x A
        + R.Gq x A / R.Dg x A * (x * Ad) := by
      simp only [D, ← hA, ← hAd]
      rw [← Finset.mul_sum]
      simp only [rqx, rqa, rq, Gx, Gq, Dg]
      field_simp
      ring
    have k2 : x * R.E (.node k cs) x = x * R.Hx x A / R.Dh x A
        + R.Hq x A / R.Dh x A * (x * Ad) := by
      simp only [E, ← hA, ← hAd]
      simp only [rqx, rqa, rq, Hx, Hq, Dh]
      field_simp
    have hsize : ((RTree.node k cs).size : ℝ) = 1 + ∑ i, ((cs i).size : ℝ) := by
      simp [RTree.size]
    -- one row, uniformly in `ι ∈ {0, 1}`
    have row : ∀ ι : ℝ, (ι = 0 ∨ ι = 1) → 0 ≤ R.KN I ι x A →
        A * R.KN I ι x A ≤ p2 I.mN x 0 * R.Dg x A * R.Dh x A →
        0 ≤ R.Q N I ι x A (R.wt k A) →
        x * R.D (.node k cs) x + ι * I.mu x * (x * R.E (.node k cs) x) ≤
          (RTree.node k cs).size * N.C x + ι * I.kap x := by
      intro ι hι hK hKA hQ
      set K := R.Gq x A / R.Dg x A + ι * I.mu x * (R.Hq x A / R.Dh x A) with hK'
      have hKeq : K = R.KN I ι x A / (R.Dg x A * R.Dh x A * p2 I.mD x 0) := by
        rw [hK', Aux.mu, KN]; field_simp
      have hK0 : 0 ≤ K := by rw [hKeq]; positivity
      have hKA' : A * K ≤ I.mu x := by
        rw [hKeq, Aux.mu, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hmD]
        nlinarith [hKA, mul_pos (mul_pos hDg hDh) hmD]
      have hchild : ∀ i, x * R.D (cs i) x + K * w i * (x * R.E (cs i) x) ≤
          ((cs i).size : ℝ) * N.C x + K * w i / I.mu x * I.kap x := by
        intro i
        obtain ⟨r0, r1⟩ := ih i x hx
        exact child_step _ _ _ _ _ _ hμ (mul_nonneg hK0 (hw0 i))
          (le_trans (mul_le_mul_of_nonneg_left (hwA i) hK0) (by linarith [hKA'])) r0 r1
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hchild i)
      have hL : ∑ i, (x * R.D (cs i) x + K * w i * (x * R.E (cs i) x)) =
          (∑ i, x * R.D (cs i) x) + K * (x * Ad) := by
        rw [Finset.sum_add_distrib, hxAd, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      have hR : ∑ i, (((cs i).size : ℝ) * N.C x + K * w i / I.mu x * I.kap x) =
          (∑ i, ((cs i).size : ℝ)) * N.C x + I.kap x / I.mu x * (K * R.wt k A) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, ← hwsum, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      rw [hL, hR] at hsum
      have hres := resid_of_Q N.rho x (R.Gx x A) (R.Gq x A) (R.Dg x A) (R.Hx x A) (R.Hq x A)
        (R.Dh x A) (p2 I.mN x 0) (p2 I.mD x 0) (p2 I.kN x 0) (p2 I.kD x 0)
        (p2 N.pN x 0) (p2 N.pD x 0) (N.Px x) ι (R.wt k A) hDg hDh hmN hmD hkD hpN hpD
        (by simpa only [Q, KN] using hQ)
      have hC : N.C x = N.rho * x * N.Px x / (p2 N.pN x 0 * p2 N.pD x 0) := rfl
      rw [← hC] at hres
      simp only [Aux.mu, Aux.kap] at hres hsum ⊢
      rw [k1, k2, hsize]
      simp only [hK', Aux.mu] at hsum
      nlinarith [hres, hsum]
    refine ⟨?_, ?_⟩
    · have := row 0 (Or.inl rfl) (hc.K0 x A hx hAin) (hc.K0le x A hx hAin) (hc.res0 x A k hx hAin)
      simpa using this
    · have := row 1 (Or.inr rfl) (hc.K1 x A hx hAin) (hc.K1le x A hx hAin) (hc.res1 x A k hx hAin)
      simpa using this

end Rec

namespace Rec

theorem hasDerivAt_log_psi (N : Norm) {x : ℝ} (hpN : 0 < p2 N.pN x 0) (hpD : 0 < p2 N.pD x 0) :
    HasDerivAt (fun t => Real.log (N.psi t)) (N.Px x / (p2 N.pN x 0 * p2 N.pD x 0)) x := by
  have hU : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  have h := (hasDerivAt_rq N.pN N.pD hU hpD.ne').log (div_pos hpN hpD).ne'
  refine (show HasDerivAt (fun t => Real.log (N.psi t)) _ x from h).congr_deriv ?_
  simp only [rqx, rqa, rq, Norm.Px]
  field_simp
  ring

/-- THE MONOTONICITY STEP: `log T_b − ρ n_b log ψ` is antitone on `Set.Ici x0`. -/
theorem logratio_antitone (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0)
    (b : RTree) :
    AntitoneOn (fun t => Real.log (R.T b t) - N.rho * b.size * Real.log (N.psi t)) (Set.Ici x0) := by
  have hd : ∀ x ∈ Set.Ici x0, HasDerivAt
      (fun t => Real.log (R.T b t) - N.rho * b.size * Real.log (N.psi t))
      (R.D b x - N.rho * b.size * (N.Px x / (p2 N.pN x 0 * p2 N.pD x 0))) x := by
    intro x hx
    obtain ⟨hpN, hpD, -⟩ := hc.pos1 x hx
    exact (R.hasDerivAt_log_T (hc.good x hx) b).sub
      ((hasDerivAt_log_psi N hpN hpD).const_mul (N.rho * b.size))
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => ?_)
  rw [interior_Ici] at hx
  have hxpos : 0 < x := lt_of_le_of_lt hc.x0_nonneg hx
  have hinv := (R.invariant N I x0 hc b x (le_of_lt hx)).1
  simp only [Norm.C] at hinv
  by_contra hneg
  rw [not_le] at hneg
  have := mul_pos hxpos hneg
  have key : x * (R.D b x - N.rho * b.size * (N.Px x / (p2 N.pN x 0 * p2 N.pD x 0))) =
      x * R.D b x - b.size * (N.rho * x * N.Px x / (p2 N.pN x 0 * p2 N.pD x 0)) := by ring
  linarith

theorem ratio_eq_exp (R : Rec) (N : Norm) {x r : ℝ} (b : RTree) (hT : 0 < R.T b x)
    (hψ : 0 < N.psi x) :
    R.T b x / N.psi x ^ r = Real.exp (Real.log (R.T b x) - r * Real.log (N.psi x)) := by
  rw [Real.exp_sub, Real.exp_log hT, Real.rpow_def_of_pos hψ, mul_comm r]

/-- `T_b / N(·, n_b)` is antitone on `Set.Ici x0` (`N = ψ ^ (ρ n)`, a real power). -/
theorem ratio_antitone (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0)
    (b : RTree) :
    AntitoneOn (fun t => R.T b t / N.psi t ^ (N.rho * b.size)) (Set.Ici x0) := by
  have hpos : ∀ x ∈ Set.Ici x0, 0 < R.T b x ∧ 0 < N.psi x := by
    intro x hx
    obtain ⟨hpN, hpD, -⟩ := hc.pos1 x hx
    exact ⟨(R.hasDeriv_rec (hc.good x hx) b).2.2.1, div_pos hpN hpD⟩
  intro u hu v hv huv
  have hΦ := R.logratio_antitone N I x0 hc b hu hv huv
  simp only at hΦ ⊢
  rw [ratio_eq_exp R N b (hpos u hu).1 (hpos u hu).2,
    ratio_eq_exp R N b (hpos v hv).1 (hpos v hv).2]
  exact Real.exp_le_exp.2 (by linarith)

/-- THE ANCHORED EXTENSION: an anchor at `xa ≥ x0` extends to every `x ≥ xa`. -/
theorem anchored_extension (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0)
    (xa : ℝ) (hxa : x0 ≤ xa) (hanchor : ∀ b : RTree, R.T b xa ≤ N.psi xa ^ (N.rho * b.size)) :
    ∀ b : RTree, ∀ x, xa ≤ x → R.T b x ≤ N.psi x ^ (N.rho * b.size) := by
  intro b x hx
  have hψ : ∀ t, x0 ≤ t → 0 < N.psi t ^ (N.rho * b.size) := by
    intro t ht
    obtain ⟨hpN, hpD, -⟩ := hc.pos1 t ht
    exact Real.rpow_pos_of_pos (div_pos hpN hpD) _
  have hmono := R.ratio_antitone N I x0 hc b (show xa ∈ Set.Ici x0 from hxa)
    (show x ∈ Set.Ici x0 from le_trans hxa hx) hx
  simp only at hmono
  have h1 : R.T b xa / N.psi xa ^ (N.rho * b.size) ≤ 1 :=
    (div_le_one (hψ xa hxa)).2 (hanchor b)
  exact (div_le_one (hψ x (le_trans hxa hx))).1 (le_trans hmono h1)

/-- THE ANCHOR FROM A NODE CHECK at `x0` (`ρ = p / q`): `g(x0, a)^q ≤ ψ(x0)^p` on the aggregate
range gives `T_b(x0) ≤ ψ(x0)^(ρ n_b)` for every tree. -/
theorem anchor_of_node (R : Rec) (N : Norm) (x0 : ℝ) (hG : R.Good x0)
    (hpN : 0 < p2 N.pN x0 0) (hpD : 0 < p2 N.pD x0 0) (p q : ℕ) (hq : 0 < q)
    (hρ : N.rho = p / q)
    (hnode : ∀ a, R.inA a → p2 R.gN x0 a ^ q * p2 N.pD x0 0 ^ p ≤
      p2 N.pN x0 0 ^ p * p2 R.gD x0 a ^ q) :
    ∀ b : RTree, R.T b x0 ≤ N.psi x0 ^ (N.rho * b.size) := by
  have hψ : 0 < N.psi x0 := div_pos hpN hpD
  have hlog : ∀ b : RTree, Real.log (R.T b x0) ≤ N.rho * b.size * Real.log (N.psi x0) := by
    intro b
    induction b with
    | node k cs ih =>
      have hch := fun i => R.hasDeriv_rec hG (cs i)
      set A := R.agg fun i => R.y (cs i) x0 with hA
      have hAin : R.inA A := R.agg_inA _ (fun i => (hch i).1) (fun hp i => (hch i).2.1 hp)
      obtain ⟨hgN, hgD, -⟩ := hG A hAin
      have hg : 0 < rq R.gN R.gD x0 A := div_pos hgN hgD
      have hTv : R.T (.node k cs) x0 = (∏ i, R.T (cs i) x0) * rq R.gN R.gD x0 A := by
        simp only [T, hA]
      have hgq : rq R.gN R.gD x0 A ^ q ≤ N.psi x0 ^ p := by
        simp only [rq, Norm.psi, div_pow]
        rw [div_le_div_iff₀ (pow_pos hgD q) (pow_pos hpD p)]
        linarith [hnode A hAin]
      have hlg : Real.log (rq R.gN R.gD x0 A) ≤ N.rho * Real.log (N.psi x0) := by
        have h1 := Real.log_le_log (pow_pos hg q) hgq
        rw [Real.log_pow, Real.log_pow] at h1
        rw [hρ, div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hq)]
        linarith
      rw [hTv, Real.log_mul (Finset.prod_pos (fun i _ => (hch i).2.2.1)).ne' hg.ne',
        Real.log_prod (fun i _ => (hch i).2.2.1.ne')]
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ih i)
      have hsize : ((RTree.node k cs).size : ℝ) = 1 + ∑ i, ((cs i).size : ℝ) := by
        simp [RTree.size]
      rw [hsize]
      have : ∑ i, N.rho * ((cs i).size : ℝ) * Real.log (N.psi x0) =
          N.rho * (∑ i, ((cs i).size : ℝ)) * Real.log (N.psi x0) := by
        rw [Finset.mul_sum, Finset.sum_mul]
      linarith
  intro b
  have hT := (R.hasDeriv_rec hG b).2.2.1
  rw [Real.rpow_def_of_pos hψ, ← Real.exp_log hT]
  exact Real.exp_le_exp.2 (by linarith [hlog b])

end Rec

end AnchoredMonotone

open AnchoredMonotone
"""


def _lean_list(P: sp.Poly) -> str:
    items = []
    for (i, j), c in sorted(P.terms()):
        if c != 0:
            items.append(f"({i}, {j}, {_q(c)})")
    return "[" + ", ".join(items) + "]"


def _lean_poly(P, *, kvar: bool = False) -> str:
    """A polynomial in x, a (and k, as ``(k : ℝ)``) as Lean real text."""
    if not isinstance(P, sp.Poly):
        P = _P(P)
    names = ["x", "a", "(k : ℝ)"]
    gens = P.gens
    terms = []
    for mon, c in sorted(P.terms()):
        c = sp.Rational(c)
        if c == 0:
            continue
        parts = []
        for g, e in zip(gens, mon):
            if e == 0:
                continue
            nm = names[_VARS.index(g)] if g in _VARS else str(g)
            parts.append(nm if e == 1 else f"{nm} ^ {e}")
        if c != 1 or not parts:
            parts.insert(0, _q(c))
        terms.append(" * ".join(parts))
    return "(" + (" + ".join(terms) if terms else "(0 : ℝ)") + ")"


_VAR_LEAN = ("x", "a", "(k : ℝ)")


def _factor(vi: int, i: int, d: int, bounded: bool, hs: str, ht: str) -> str:
    if bounded:
        return f"mul_nonneg (pow_nonneg {hs} {i}) (pow_nonneg {ht} {d - i})"
    return f"pow_nonneg {hs} {i}"


def _cell_tactic(cell: MCell, uid: str, active: tuple, ind: str) -> str:
    """Tactic text closing the obligation on one cell: the box bounds as ``0 ≤ v - s`` /
    ``0 ≤ t - v`` facts from context, then one linarith over the product facts."""
    lines = []
    hyps = []
    for vi in active:
        s, t = cell.box[vi]
        v = _VAR_LEAN[vi]
        hs = f"h{uid}{'xak'[vi]}s"
        lines.append(f"{ind}have {hs} : 0 ≤ {v} - {_q(s)} := by linarith")
        ht = None
        if t is not None:
            ht = f"h{uid}{'xak'[vi]}t"
            lines.append(f"{ind}have {ht} : 0 ≤ {_q(t)} - {v} := by linarith")
        hyps.append((vi, hs, ht))
    facts = []
    for ix, c in cell.coeffs:
        fs = []
        for vi, hs, ht in hyps:
            fs.append(_factor(vi, ix[vi], cell.degs[vi], ht is not None, hs, ht))
        if not fs:
            continue
        f = fs[0]
        for g in fs[1:]:
            f = f"mul_nonneg ({f}) ({g})"
        facts.append(f)
    lines.append(f"{ind}linarith [{', '.join(facts)}]" if facts else f"{ind}linarith")
    return "\n".join(lines)


def _tree_tactic(node, uid: str, active: tuple, ind: str) -> str:
    if isinstance(node, MCell):
        return _cell_tactic(node, uid, active, ind)
    _, vi, m, left, right = node
    v = _VAR_LEAN[vi]
    h = f"hsp{uid}"
    return (f"{ind}rcases le_or_gt {v} {_q(m)} with {h} | {h}\n"
            f"{ind}· " + _tree_tactic(left, uid + "l", active, ind + "  ").lstrip() + "\n"
            f"{ind}· " + _tree_tactic(right, uid + "r", active, ind + "  ").lstrip())


def _active(dom) -> tuple:
    return tuple(i for i, (s, t) in enumerate(dom) if not (t is not None and s == t))


@dataclass
class AnchoredMonotoneExtensionEmitter(Emitter):
    """Emit the generic anchored-monotone theory (tree recursion, derivative prelude, two-row
    invariant, antitone ratio, anchored extension) once, then per instance the recursion data,
    the evaluation lemmas, one lemma per polynomial obligation, the ``Checks`` record, and the
    capstone theorems.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "anchored_monotone_extension"

    def emit_units(self, fam, profile: LeanProfile):
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts = [_GENERIC]
        for inst in fam.instances:
            parts.append(self._emit_instance(inst.payload, inst.lean_name,
                                             _sanity_of(fam, inst)))
        body = "\n".join(parts)
        nthm = sum(1 for ln in body.split("\n") if ln.startswith("theorem "))
        return body, nthm

    # -- per instance -------------------------------------------------------------------
    def _emit_instance(self, c: AnchoredMonotoneCert, nm: str, sanity) -> str:
        L: list[str] = []
        prod = c.prod
        gN, gD = c.g
        hN, hD = c.h
        pN, pD = c.psi
        mN, mD = c.mu
        kN, kD = c.kappa
        x0 = _q(c.lam0)
        anchor_txt = ("node check at lam0" if c.anchor["kind"] == "node"
                      else f"hypothesis at lam = {c.anchor['at']}")
        L.append(f"/-! ## Instance `{nm}`\n\n"
                 f"In Lean `x` is the parameter `λ` and `a` the aggregate `A`.\n"
                 f"Recursion ({c.mode} mode): `T_b = (∏ T_c) · g(x, a)`, `y_b = h(x, a)`, "
                 f"`g = {c.exprs.get('g')}`, `h = {c.exprs.get('h')}`.\n"
                 f"Normalizer `ψ(x)^(ρ n)`, `ψ = {c.exprs.get('psi')}`, `ρ = {c.rho}`; "
                 f"threshold `λ0 = {c.lam0}`; auxiliary row `μ = {c.exprs.get('mu')}`, "
                 f"`κ = {c.exprs.get('kappa')}`; anchor: {anchor_txt}.\n"
                 f"conjecture1_proved = False. -/\n")
        L.append(f"noncomputable def {nm}_R : Rec :=\n"
                 f"  {{ prod := {'true' if prod else 'false'},\n"
                 f"    gN := {_lean_list(gN)},\n    gD := {_lean_list(gD)},\n"
                 f"    hN := {_lean_list(hN)},\n    hD := {_lean_list(hD)} }}\n")
        L.append(f"noncomputable def {nm}_N : Norm :=\n"
                 f"  {{ pN := {_lean_list(pN)},\n    pD := {_lean_list(pD)},\n"
                 f"    rho := {_q(c.rho)} }}\n")
        L.append(f"noncomputable def {nm}_I : Aux :=\n"
                 f"  {{ mN := {_lean_list(mN)},\n    mD := {_lean_list(mD)},\n"
                 f"    kN := {_lean_list(kN)},\n    kD := {_lean_list(kD)} }}\n")
        L.append(f"theorem {nm}_prod : {nm}_R.prod = {'true' if prod else 'false'} := rfl\n")
        L.append(f"theorem {nm}_rho : {nm}_N.rho = {_q(c.rho)} := rfl\n")
        # evaluation lemmas
        ev2 = []
        for fld, P in (("gN", gN), ("gD", gD), ("hN", hN), ("hD", hD)):
            for tag, Q, unf in (("", P, "p2"), ("_dx", _d(P, X_SYM), "p2, p2dx"),
                                ("_da", _d(P, A_SYM), "p2, p2da")):
                lhs = (f"p2 {nm}_R.{fld} x a" if not tag else
                       f"p2 ({'p2dx' if tag == '_dx' else 'p2da'} {nm}_R.{fld}) x a")
                n_ = f"{nm}_e_{fld}{tag}"
                ev2.append(n_)
                L.append(f"theorem {n_} (x a : ℝ) : {lhs} = {_lean_poly(Q)} := by\n"
                         f"  simp only [{nm}_R, {unf}]\n  push_cast\n  ring\n")
        ev1 = []
        for obj, fld, P, dx in ((f"{nm}_N", "pN", pN, True), (f"{nm}_N", "pD", pD, True),
                                (f"{nm}_I", "mN", mN, False), (f"{nm}_I", "mD", mD, False),
                                (f"{nm}_I", "kN", kN, False), (f"{nm}_I", "kD", kD, False)):
            n_ = f"{nm}_e_{fld}"
            ev1.append(n_)
            L.append(f"theorem {n_} (x : ℝ) : p2 {obj}.{fld} x 0 = {_lean_poly(P)} := by\n"
                     f"  simp only [{obj}, p2]\n  push_cast\n  ring\n")
            if dx:
                n_ = f"{nm}_e_{fld}_dx"
                ev1.append(n_)
                L.append(f"theorem {n_} (x : ℝ) : p2 (p2dx {obj}.{fld}) x 0 = "
                         f"{_lean_poly(_d(P, X_SYM))} := by\n"
                         f"  simp only [{obj}, p2, p2dx]\n  push_cast\n  ring\n")
        evs = ", ".join(ev2 + ev1)
        ob = {o.name: o.cert for o in c.obligations}

        def intro_a(ind="  "):
            s = f"{ind}obtain ⟨ha0, ha1⟩ := ha\n"
            if prod:
                s += f"{ind}have ha1 := ha1 {nm}_prod\n"
            return s

        def proof(name, ind="  "):
            mc = ob[name]
            return _tree_tactic(mc.tree, name, _active(mc.dom), ind)

        # well-posedness
        hle = (f"  · intro _\n    rw [{nm}_e_hN, {nm}_e_hD]\n" + proof("hle", "    ") + "\n"
               if prod else
               f"  · intro h\n    exact absurd h (by simp [{nm}_R])\n")
        L.append(f"/-- Well-posedness on `λ ≥ λ0`: the node polynomials are positive on the "
                 f"aggregate range{' and the message stays `≤ 1`' if prod else ''}. -/\n"
                 f"theorem {nm}_good : ∀ x, {x0} ≤ x → {nm}_R.Good x := by\n"
                 f"  intro x hx a ha\n" + intro_a() +
                 "  refine ⟨?_, ?_, ?_, ?_, ?_⟩\n" +
                 "".join(f"  · rw [{nm}_e_{f}]\n" + proof(f, "    ") + "\n"
                         for f in ("gN", "gD", "hN", "hD")) + hle)
        L.append(f"theorem {nm}_pos1 : ∀ x, {x0} ≤ x → 0 < p2 {nm}_N.pN x 0 ∧ "
                 f"0 < p2 {nm}_N.pD x 0 ∧\n    0 < p2 {nm}_I.mN x 0 ∧ 0 < p2 {nm}_I.mD x 0 ∧ "
                 f"0 < p2 {nm}_I.kD x 0 := by\n"
                 f"  intro x hx\n  refine ⟨?_, ?_, ?_, ?_, ?_⟩\n" +
                 "".join(f"  · rw [{nm}_e_{f}]\n" + proof(f, "    ") + "\n"
                         for f in ("pN", "pD", "mN", "mD", "kD")))
        unf = ("Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, "
               f"{nm}_rho, {evs}")
        for iota in (0, 1):
            L.append(f"/-- Row {iota}: the child weight is `≥ 0` "
                     f"(`K{iota} ≥ 0`). -/\n"
                     f"theorem {nm}_K{iota} : ∀ x a, {x0} ≤ x → {nm}_R.inA a → "
                     f"0 ≤ {nm}_R.KN {nm}_I {iota} x a := by\n"
                     f"  intro x a hx ha\n" + intro_a() +
                     f"  simp only [{unf}]\n" + proof(f"K{iota}") + "\n")
            L.append(f"/-- Row {iota}: the child weight is `≤ μ` (`A K{iota} ≤ μ`). -/\n"
                     f"theorem {nm}_K{iota}le : ∀ x a, {x0} ≤ x → {nm}_R.inA a →\n"
                     f"    a * {nm}_R.KN {nm}_I {iota} x a ≤ p2 {nm}_I.mN x 0 * {nm}_R.Dg x a * "
                     f"{nm}_R.Dh x a := by\n"
                     f"  intro x a hx ha\n" + intro_a() +
                     f"  simp only [{unf}]\n" + proof(f"K{iota}le") + "\n")
            wt = (f"Rec.wt, {nm}_prod, if_true" if prod else
                  f"Rec.wt, {nm}_prod, Bool.false_eq_true, if_false")
            L.append(f"/-- Row {iota}: the cleared residual of the inductive step is `≥ 0`. -/\n"
                     f"theorem {nm}_res{iota} : ∀ x a (k : ℕ), {x0} ≤ x → {nm}_R.inA a →\n"
                     f"    0 ≤ {nm}_R.Q {nm}_N {nm}_I {iota} x a ({nm}_R.wt k a) := by\n"
                     f"  intro x a k hx ha\n" + intro_a() +
                     f"  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k\n"
                     f"  simp only [Rec.Q, {wt}, {unf}]\n" + proof(f"res{iota}") + "\n")
        L.append(f"/-- The per-instance obligations, assembled. -/\n"
                 f"theorem {nm}_checks : {nm}_R.Checks {nm}_N {nm}_I {x0} where\n"
                 f"  x0_nonneg := by norm_num\n  good := {nm}_good\n  pos1 := {nm}_pos1\n"
                 f"  K0 := {nm}_K0\n  K0le := {nm}_K0le\n  K1 := {nm}_K1\n  K1le := {nm}_K1le\n"
                 f"  res0 := {nm}_res0\n  res1 := {nm}_res1\n")
        # capstones
        L.append(f"/-- (1) The derivative prelude: `D` is the log-derivative of `T` on "
                 f"`λ ≥ λ0`. -/\n"
                 f"theorem {nm}_logderiv : ∀ b : RTree, ∀ x, {x0} ≤ x →\n"
                 f"    HasDerivAt (fun t => Real.log ({nm}_R.T b t)) ({nm}_R.D b x) x :=\n"
                 f"  fun b x hx => {nm}_R.hasDerivAt_log_T ({nm}_good x hx) b\n")
        L.append(f"/-- (2) The derivative bound `λ D_b ≤ n_b c(λ)` on `λ ≥ λ0`. -/\n"
                 f"theorem {nm}_deriv_bound : ∀ b : RTree, ∀ x, {x0} ≤ x →\n"
                 f"    x * {nm}_R.D b x ≤ b.size * {nm}_N.C x :=\n"
                 f"  fun b x hx => (Rec.invariant _ _ _ _ {nm}_checks b x hx).1\n")
        L.append(f"/-- (2) `T_b / ψ^(ρ n_b)` is antitone on `λ ≥ λ0`. -/\n"
                 f"theorem {nm}_antitone : ∀ b : RTree,\n"
                 f"    AntitoneOn (fun t => {nm}_R.T b t / {nm}_N.psi t ^ ({nm}_N.rho * b.size)) "
                 f"(Set.Ici {x0}) :=\n"
                 f"  Rec.ratio_antitone _ _ _ _ {nm}_checks\n")
        if c.anchor["kind"] == "node":
            p, q = c.anchor["p"], c.anchor["q"]
            L.append(f"/-- The anchor node check at `λ0`: `g(λ0, A)^{q} ≤ ψ(λ0)^{p}`. -/\n"
                     f"theorem {nm}_node : ∀ a, {nm}_R.inA a → p2 {nm}_R.gN {x0} a ^ {q} * "
                     f"p2 {nm}_N.pD {x0} 0 ^ {p} ≤\n"
                     f"    p2 {nm}_N.pN {x0} 0 ^ {p} * p2 {nm}_R.gD {x0} a ^ {q} := by\n"
                     f"  intro a ha\n" + intro_a() +
                     f"  simp only [{evs}]\n" + proof("anchor") + "\n")
            L.append(f"/-- (3) The anchor: `T_b(λ0) ≤ ψ(λ0)^(ρ n_b)` for every tree. -/\n"
                     f"theorem {nm}_anchor : ∀ b : RTree, {nm}_R.T b {x0} ≤ "
                     f"{nm}_N.psi {x0} ^ ({nm}_N.rho * b.size) := by\n"
                     f"  obtain ⟨hpN, hpD, -⟩ := {nm}_pos1 {x0} le_rfl\n"
                     f"  exact Rec.anchor_of_node _ _ _ ({nm}_good _ le_rfl) hpN hpD {p} {q} "
                     f"(by norm_num) (by rw [{nm}_rho]; norm_num) {nm}_node\n")
            L.append(f"/-- (3) THE ANCHORED EXTENSION: `T_b(λ) ≤ ψ(λ)^(ρ n_b)` for every tree "
                     f"and every `λ ≥ λ0`. -/\n"
                     f"theorem {nm} : ∀ b : RTree, ∀ x, {x0} ≤ x →\n"
                     f"    {nm}_R.T b x ≤ {nm}_N.psi x ^ ({nm}_N.rho * b.size) :=\n"
                     f"  Rec.anchored_extension _ _ _ _ {nm}_checks {x0} le_rfl {nm}_anchor\n")
            hyp, xs = "", x0
        else:
            xa = _q(c.anchor["at"])
            L.append(f"/-- (3) THE ANCHORED EXTENSION from an anchor at `λ = {c.anchor['at']}` "
                     f"(a hypothesis, certified elsewhere): `T_b(λ) ≤ ψ(λ)^(ρ n_b)` for every "
                     f"tree and every `λ ≥ {c.anchor['at']}`. -/\n"
                     f"theorem {nm} (hanchor : ∀ b : RTree, {nm}_R.T b {xa} ≤ "
                     f"{nm}_N.psi {xa} ^ ({nm}_N.rho * b.size)) :\n"
                     f"    ∀ b : RTree, ∀ x, {xa} ≤ x → {nm}_R.T b x ≤ "
                     f"{nm}_N.psi x ^ ({nm}_N.rho * b.size) :=\n"
                     f"  Rec.anchored_extension _ _ _ _ {nm}_checks {xa} (by norm_num) hanchor\n")
            hyp, xs = "hanchor", xa
        # pretty corollaries when psi is a polynomial and rho = 1
        if c.rho == 1 and pD.is_ground:
            ptxt = _lean_poly(sp.Poly(pN.as_expr() / pD.as_expr(), X_SYM, A_SYM, domain="QQ"))
            L.append(f"theorem {nm}_psi (x : ℝ) : {nm}_N.psi x = {ptxt} := by\n"
                     f"  simp only [Norm.psi, {nm}_e_pN, {nm}_e_pD]\n  ring\n")
            at_val = (pN.as_expr() / pD.as_expr()).subs(X_SYM, c.anchor.get("at", c.lam0))
            hy = (f"(hanchor : ∀ b : RTree, {nm}_R.T b {xs} ≤ {_q(at_val)} ^ b.size) "
                  if hyp else "")
            L.append(f"/-- The extension with a natural-number power: "
                     f"`T_b(λ) ≤ {ptxt} ^ n_b`. -/\n"
                     f"theorem {nm}_pow {hy}:\n"
                     f"    ∀ b : RTree, ∀ x, {xs} ≤ x → {nm}_R.T b x ≤ {ptxt} ^ b.size := by\n"
                     f"  intro b x hx\n"
                     + (f"  have h := {nm} (fun b => by\n"
                        f"    rw [{nm}_psi, {nm}_rho, one_mul, Real.rpow_natCast]\n"
                        f"    convert hanchor b using 2 <;> norm_num) b x hx\n"
                        if hyp else f"  have h := {nm} b x hx\n") +
                     f"  rwa [{nm}_psi, {nm}_rho, one_mul, Real.rpow_natCast] at h\n")
            L.append(f"/-- The antitone ratio with a natural-number power: "
                     f"`T_b / {ptxt} ^ n_b`. -/\n"
                     f"theorem {nm}_antitone_pow : ∀ b : RTree,\n"
                     f"    AntitoneOn (fun t => {nm}_R.T b t / {ptxt.replace('x', 't')} ^ b.size) "
                     f"(Set.Ici {x0}) := by\n"
                     f"  intro b u hu v hv huv\n"
                     f"  have h := {nm}_antitone b hu hv huv\n"
                     f"  simp only [{nm}_psi, {nm}_rho, one_mul, Real.rpow_natCast] at h\n"
                     f"  exact h\n")
        for i, (tree, val) in enumerate(sanity or ()):
            L.append(f"/-- Sanity: the recursion on `{tree}`. -/\n"
                     f"theorem {nm}_sanity{i} (x : ℝ) (_hx : 0 ≤ x) : {nm}_R.T ({tree}) x = "
                     f"{val} := by\n"
                     f"  simp [Rec.T, Rec.y, Rec.agg, rq, p2, {nm}_R]\n"
                     f"  all_goals (try field_simp)\n  all_goals ring\n")
        return "\n".join(L)


def _sanity_of(fam, inst):
    try:
        spec = fam.family.special[1](inst.point)
    except Exception:  # noqa: BLE001 - a forged single-instance family has no spec callable
        return ()
    return tuple(spec.get("sanity", ())) if isinstance(spec, dict) else ()


def anchored_monotone_extension_family(name, grid, lean_name, spec, constants=None):
    """Build an anchored-monotone-extension family (kind='anchored_monotone_extension').

    ``spec``: a callable ``pt -> dict`` of :func:`anchored_monotone_extension_certificate`
    keyword arguments (``mode``, ``g``, ``h``, ``psi``, ``rho``, ``lam0``, ``mu``, ``kappa``,
    ``anchor``), plus an optional ``sanity`` list of ``(Lean tree, Lean value)`` pairs."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("anchored_monotone_extension", spec),
        constants=dict(constants or {}),
    )


#: (a) CLASSICAL: the hard-core (independent-set) partition function on rooted trees.  With
#: q_b = Z(b, root out)/Z(b) and P = prod_c q_c, Z_b = (prod_c Z_c) (1 + lam P) and
#: q_b = 1/(1 + lam P).  Claim: Z_b(lam)/(1+lam)^{n_b} is antitone on [0, oo), hence
#: Z_b(lam) <= (1+lam)^{n_b} from the anchor Z_b(0) = 1.  Auxiliary row: the root-deleted
#: forest, x D_b + x E_b = x d/dx log Z(b - root) <= (n_b - 1) c, i.e. mu = 1, kappa = -c.
HARDCORE_SPEC = dict(
    mode="prod", g="1 + lam*A", h="1/(1 + lam*A)", psi="1 + lam", rho=1, lam0=0,
    mu="1", kappa="-lam/(1 + lam)", anchor={"kind": "node"},
    sanity=[("RTree.node 0 Fin.elim0", "1 + x"),
            ("RTree.node 1 (fun _ => RTree.node 0 Fin.elim0)", "1 + 2 * x")],
)

#: (b) SYNTHETIC matching-type SUM recursion: R = sum_c y_c, T_b = (prod_c T_c)(1 + lam R),
#: y_b = 1/(1 + lam R), with our own normalizer (1 + lam)^n on [1, oo).  The anchor at lam = 1
#: is passed through as a Lean hypothesis (the node check fails there: R is unbounded).
MATCHING_SPEC = dict(
    mode="sum", g="1 + lam*A", h="1/(1 + lam*A)", psi="1 + lam", rho=1, lam0=1,
    mu="1", kappa="-lam/(1 + lam)", anchor={"kind": "hypothesis", "at": 1},
    sanity=[("RTree.node 0 Fin.elim0", "1"),
            ("RTree.node 1 (fun _ => RTree.node 0 Fin.elim0)", "1 + x")],
)

#: (a') the hard-core recursion with the normalizer written as ((1 + lam)^3)^(n/3): rho = 1/3,
#: exercising a rational exponent (a real power in Lean) and the anchor node check
#: g(0, A)^3 <= psi(0)^1.
HARDCORE_CUBE_SPEC = dict(HARDCORE_SPEC, psi="(1 + lam)**3", rho="1/3", sanity=[])

#: NEGATIVE CONTROL: the hard-core recursion against a TOO-SMALL normalizer (1 + 3 lam/4)^n.
#: Already a single vertex violates it (Z = 1 + lam > 1 + 3 lam/4 for lam > 0), and the
#: row-0 residual is negative at the leaf point (A = 1, k = 0): refused by Layer 1; the forged
#: certificate's residual cell carries a negative coefficient and its linarith cannot close.
HARDCORE_TOO_SMALL_SPEC = dict(
    HARDCORE_SPEC, psi="1 + 3*lam/4", kappa="-3*lam/(4 + 3*lam)", sanity=[],
)


if __name__ == "__main__":
    for nm, spec in (("hardcore", HARDCORE_SPEC), ("matching", MATCHING_SPEC)):
        s = dict(spec)
        s.pop("sanity")
        c = anchored_monotone_extension_certificate(**s)
        print(nm, [(o.name, len(o.cert.leaves())) for o in c.obligations])

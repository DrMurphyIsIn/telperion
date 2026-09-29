"""concave_pooled_induction emitter -- a bound on a BRANCHING (tree) recursion, certified by a
CONCAVE one-scalar witness checked at the POOLED MEAN of the children's messages.

conjecture1_proved = False.  Nothing in this module bears on the Brualdi-Goldwasser conjecture,
on RH, or on any other open problem.  It certifies, for one explicitly given recursion and one
explicitly given witness, a bound that holds on EVERY finite rooted tree; downstream consumers
state their own scope.

CREDIT
------
Method: concave-witness induction, from the draft "The maximum Laplacian ratio of a tree for all
n >= 303: concave witnesses and one-variable certificates" (28 September 2026), communicated to
us by Professor John L. Goldwasser (author: his London colleague; name to be added once
permission is given).  The draft uses this induction for the Brualdi-Goldwasser ceiling; this
module packages the METHOD generically.  Nothing from the draft's Sections 4-9 (the Laplacian-
ratio instance) is formalized here, and none of its data is used.

THE SETTING
-----------
Finite rooted trees.  A node `v` with `m >= 1` children `c_1..c_m` carries a scalar MESSAGE
`y_v` and a PROFIT `l(v)`:

    R   = y_{c_1} + ... + y_{c_m}
    y_v = h(m, R)
    l(v) = l(c_1) + ... + l(c_m) + g(m, R)

and a leaf carries the fixed pair `(y_leaf, l_leaf)`.  `h` and `g` are rational functions of
`(m, R)` with rational coefficients.  The CLAIM, for a witness `U` and a deficit `alpha`, is

    l(b) + alpha * |b|  <=  U(y_b)        for every finite rooted tree b,

where `|b|` is the number of vertices (`alpha = 0` is the plain bound; `alpha > 0` a
size-proportional deficit; `alpha < 0` a size-proportional allowance).  The deficit is a pure
reparametrisation: `l'(b) = l(b) + alpha |b|` satisfies the same recursion with `g + alpha` and
`l_leaf + alpha`, which is how it enters every obligation below.

THE WITNESS
-----------
`U` is concave piecewise-linear on `I = [lo, hi]` with rational nodes `x_0 < ... < x_K` and
values `v_0..v_K`; its slopes must be STRICTLY decreasing (a repeated slope is refused: merge
the node).  In Lean `U` is REPRESENTED as the MINIMUM of its `K` affine pieces
`p_j(x) = a_j x + b_j`, a function on all of R.  With strictly decreasing slopes the minimum
agrees with the interpolant on `I` (the emitted `*_node_j` lemmas re-check `U x_j = v_j` in the
kernel), and Jensen is free: a sum of minima is at most the minimum of the sums, and
`sum_i p_k(y_i) = m p_k(ybar)` because `p_k` is affine.  No concavity argument is needed in the
kernel; concavity is what makes the min-representation equal to the table.

THE CERTIFICATE (every obligation the Lean theorem consumes)
------------------------------------------------------------
(i)   concavity: slopes strictly decreasing (exact; refusal otherwise).
(ii)  base: `lo <= y_leaf <= hi` and `l_leaf + alpha <= U(y_leaf)` (exact).
(iii) for each child count `m = 1..M` and every mean `ybar` in `I`:
          m U(ybar) + g(m, m ybar) + alpha <= U(h(m, m ybar)),   lo <= h(m, m ybar) <= hi.
      Written in `R = m ybar in [m lo, m hi]`.  Since `U <= p_j` everywhere,
      `m U(ybar) <= a_j R + m b_j` for ANY piece `j`; the generator uses the piece active on the
      cell.  The right side `U(h)` is a minimum, so the certificate proves the inequality
      against EVERY piece `k`.  Each (cell, k) obligation is a one-variable rational inequality;
      multiplied by its certified-positive denominator it is a polynomial `N(R) >= 0` on the
      cell `[s, t]`, certified by its BERNSTEIN coefficients: `N = sum_i c_i (R-s)^i (t-R)^(d-i)`
      with every `c_i >= 0` (checked exactly, and the identity re-checked by expansion).  In
      Lean `linarith` closes it from the `d+1` product facts `0 <= (R-s)^i (t-R)^(d-i)`.
      Denominators are certified STRICTLY positive the same way (all `c_i > 0`).
(iv)  TAIL, all `m >= M + 1` at once (only when `h`, `g` do not depend on `m`, `lo >= 0` and
      `hi > 0`).  For a piece `j` with `b_j <= 0`, and `m >= M+1`, `R = m ybar <= m hi`:
          m U(ybar) <= a_j R + m b_j <= a_j R + (M+1) b_j            (mode "M1")
          m U(ybar) <= a_j R + m b_j <= (a_j + b_j / hi) R           (mode "Rhi")
      so it suffices that `LHS_mode(R) + g(R) + alpha <= U(h(R))` and `lo <= h(R) <= hi` for
      all `R >= (M+1) lo` -- ONE variable, no `m`.  The half-line is covered by finite cells and
      one unbounded cell `[s, oo)`, where the certificate is the Taylor expansion at `s`:
      `N(s + u) = sum_i c_i u^i` with every `c_i >= 0`.
      Without a tail (`tail=False`) the conclusion is stated for trees whose nodes all have at
      most `M` children (`PTree.AllDeg (fun m => m <= M)`); nothing is claimed beyond `M`.

This tail is NOT the node-condition tail of the draft's Lemma 3.4 (which uses `U = 0` near the
small messages that large `m` produces); it is a sufficient condition of our own that reduces
every `m >= M + 1` to one one-variable check.  Either is sound; this one is what is certified.

THE LEAN (self-contained; only `import Mathlib`)
------------------------------------------------
Generic, emitted once per file: the tree type `PTree` (`leaf` | `node m (cs : Fin (m+1) ->
PTree)`, so an internal node has at least one child), `size`, `msg`, `ell`, `AllDeg`, the
induction theorem `pooled_induction_core` (abstract `h g : N -> R -> R`, a CARRIED function `U`
and a POOLING function `V` with `U <= V` on `I` and Jensen for `V` as hypotheses), and
`minPieces` with `minPieces_le`, `le_minPieces`, `minPieces_jensen`.  Per instance: the pieces,
`U := minPieces A B`, the recursion `hh`/`gg`, the node table, one lemma per (cell, piece) and
per cell closure, one step lemma per `m <= M`, the tail lemma, and the final theorem plus the
uniform corollary `l(b) + alpha |b| <= max_j v_j`.

WHAT IS NOT SUPPORTED (stated plainly)
--------------------------------------
* "atom" children with exact (unpooled) values: not supported.
* a carried function `U` different from the pooling function `V`: the generic Lean theorem
  takes `U`, `V` and `U <= V`, but this emitter always instantiates `U = V`.
* non-rational `g`/`h` (logs, Mobius-log cells): out of scope here (see the sibling
  `mobius_tangent_cell` kind); use a rational upper bound for `g` and a separate lemma.
* an m-dependent recursion has no tail: the claim is then bounded-degree only.

ANTI-PHANTOM REFUSALS
---------------------
`concave_pooled_certificate` raises `ValueError("REFUSED: ...")` on: a float anywhere; fewer
than two nodes or non-increasing nodes; slopes not strictly decreasing (non-concave witness,
the negative control); `y_leaf` outside `I`; a failing base; `M < 1`; a denominator of `h` or
`g` not certified positive on a cell; any (cell, piece) or closure obligation whose Bernstein
coefficients stay negative down to the subdivision limit (with an exact counterexample point
when one of the probed points is one); a tail requested with `m` in `h`/`g`, with `lo < 0`,
with `hi <= 0` or with no piece `b_j <= 0`; a polynomial of degree above 12; and a supplied
cell layout that does not cover its domain exactly.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from math import comb

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter

conjecture1_proved = False

#: the recursion's symbols: child count and the sum of the children's messages
M_SYM = sp.Symbol("m")
R_SYM = sp.Symbol("R")

_MAX_DEGREE = 12
_MAX_DEPTH = 10


# ---------------------------------------------------------------------------
# exact helpers
# ---------------------------------------------------------------------------

def _rat(q, what: str) -> sp.Rational:
    """An exact rational; floats and non-rationals are refused."""
    if isinstance(q, float):
        raise ValueError(f"REFUSED: {what} = {q!r} is a float; pass an exact rational")
    if isinstance(q, Fraction):
        return sp.Rational(q.numerator, q.denominator)
    if isinstance(q, str):
        q = sp.Rational(q)
    q = sp.sympify(q)
    if isinstance(q, sp.Float) or not q.is_Rational:
        raise ValueError(f"REFUSED: {what} = {q} is not an exact rational")
    return sp.Rational(q)


def _ratfun(expr, what: str) -> tuple[sp.Poly, sp.Poly]:
    """Split a rational function of (m, R) into (numerator, denominator) polynomials with
    rational coefficients.  A constant denominator is folded into the numerator."""
    if isinstance(expr, str):
        expr = sp.sympify(expr, locals={"m": M_SYM, "R": R_SYM})
    expr = sp.sympify(expr)
    if expr.atoms(sp.Float):
        raise ValueError(f"REFUSED: {what} = {expr} contains a float")
    extra = expr.free_symbols - {M_SYM, R_SYM}
    if extra:
        raise ValueError(f"REFUSED: {what} depends on symbols {sorted(map(str, extra))} "
                         f"other than m, R")
    num, den = sp.fraction(sp.cancel(sp.together(expr)))
    try:
        pn = sp.Poly(num, R_SYM, M_SYM, domain="QQ")
        pd = sp.Poly(den, R_SYM, M_SYM, domain="QQ")
    except sp.PolynomialError as e:
        raise ValueError(f"REFUSED: {what} = {expr} is not a rational function of (m, R): "
                         f"{e}") from e
    if pd.is_zero:
        raise ValueError(f"REFUSED: {what} has a zero denominator")
    if pd.total_degree() == 0:
        c = pd.as_expr()
        pn = sp.Poly(sp.expand(pn.as_expr() / c), R_SYM, M_SYM, domain="QQ")
        pd = sp.Poly(1, R_SYM, M_SYM, domain="QQ")
    else:
        lc = pd.LC()
        if lc < 0:  # normalise the sign so a positive denominator is the natural reading
            pn, pd = -pn, -pd
    return pn, pd


def _at_m(p: sp.Poly, m) -> sp.Poly:
    """Specialise a (R, m) polynomial at an integer child count (or keep it m-free)."""
    e = p.as_expr()
    if m is not None:
        e = e.subs(M_SYM, m)
    return sp.Poly(sp.expand(e), R_SYM, domain="QQ")


def _bernstein(P: sp.Poly, s, t):
    """Coefficients c_i with P(R) = sum_i c_i (R-s)^i (t-R)^(d-i), d = deg P (d >= 0)."""
    d = max(P.degree(), 0)
    u = sp.Symbol("u")
    q = sp.Poly(sp.expand(P.as_expr().subs(R_SYM, s + (t - s) * u)), u, domain="QQ")
    p = [q.coeff_monomial(u ** k) for k in range(d + 1)]
    beta = [sum(sp.Rational(comb(i, k), comb(d, k)) * p[k] for k in range(i + 1))
            for i in range(d + 1)]
    w = (t - s) ** d
    return d, tuple(sp.Rational(beta[i] * comb(d, i)) / w for i in range(d + 1))


def _taylor(P: sp.Poly, s):
    """Coefficients c_i with P(R) = sum_i c_i (R-s)^i."""
    d = max(P.degree(), 0)
    u = sp.Symbol("u")
    q = sp.Poly(sp.expand(P.as_expr().subs(R_SYM, s + u)), u, domain="QQ")
    return d, tuple(sp.Rational(q.coeff_monomial(u ** k)) for k in range(d + 1))


@dataclass(frozen=True)
class PolyCert:
    """`0 <= P(R)` (or `0 < P(R)` when ``strict``) on `[s, t]` (`t is None`: `[s, oo)`).

    Bounded cell: Bernstein form `P = sum_i c_i (R-s)^i (t-R)^(d-i)`.
    Unbounded cell: Taylor form at `s`, `P = sum_i c_i (R-s)^i`.
    Nonneg needs every `c_i >= 0`; strict needs every `c_i > 0` (bounded) or `c_0 > 0` and every
    `c_i >= 0` (unbounded)."""

    poly: tuple            # coefficients of P in R, ascending degree (exact rationals)
    s: object
    t: object              # None = unbounded
    degree: int
    coeffs: tuple
    strict: bool

    def ok(self) -> bool:
        if self.strict:
            if self.t is None:
                return self.coeffs[0] > 0 and all(c >= 0 for c in self.coeffs)
            return all(c > 0 for c in self.coeffs)
        return all(c >= 0 for c in self.coeffs)

    def identity_holds(self) -> bool:
        """Re-expand the certificate and compare with P exactly."""
        R = R_SYM
        if self.t is None:
            rhs = sum(c * (R - self.s) ** i for i, c in enumerate(self.coeffs))
        else:
            d = self.degree
            rhs = sum(c * (R - self.s) ** i * (self.t - R) ** (d - i)
                      for i, c in enumerate(self.coeffs))
        lhs = sum(c * R ** i for i, c in enumerate(self.poly))
        return sp.expand(lhs - rhs) == 0


def _poly_tuple(P: sp.Poly) -> tuple:
    d = max(P.degree(), 0)
    return tuple(sp.Rational(P.coeff_monomial(R_SYM ** k)) for k in range(d + 1))


def _polycert(P: sp.Poly, s, t, strict: bool) -> PolyCert:
    if P.degree() > _MAX_DEGREE:
        raise ValueError(f"REFUSED: obligation polynomial of degree {P.degree()} > "
                         f"{_MAX_DEGREE} (Lean cost)")
    if t is None:
        d, cs = _taylor(P, s)
    else:
        d, cs = _bernstein(P, s, t)
    return PolyCert(poly=_poly_tuple(P), s=s, t=t, degree=d, coeffs=cs, strict=strict)


# ---------------------------------------------------------------------------
# certificate dataclasses
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Obligation:
    """One rational inequality `lhs <= rhs` on a cell, as `N / D >= 0` with `D > 0` and
    `N = (rhs - lhs) * D`.  ``k`` is the piece of `U(h)` it targets (None for closure);
    ``side`` is "piece", "lo" (`lo <= h`) or "hi" (`h <= hi`)."""

    side: str
    k: int | None
    num: PolyCert


@dataclass(frozen=True)
class Cell:
    """A cell `[s, t]` of the pooled sum `R` for child count ``m`` (None = the tail) on which
    the left side is bounded through piece ``j`` in ``mode`` ("fixed": `a_j R + m b_j`;
    "M1": `a_j R + (M+1) b_j`; "Rhi": `(a_j + b_j/hi) R`)."""

    m: int | None
    s: object
    t: object
    j: int
    mode: str
    dens: tuple            # PolyCert (strict) per distinct non-constant denominator
    dtot: object           # PolyCert (strict) of the common denominator, or None
    obligations: tuple     # Obligation, pieces first then closure lo/hi


@dataclass(frozen=True)
class ConcavePooledCert:
    """A verified concave-pooled-induction certificate (all fields exact)."""

    xs: tuple
    vs: tuple
    a: tuple               # piece slopes
    b: tuple               # piece intercepts
    h_num: object          # sp.Poly in (R, m)
    h_den: object
    g_num: object
    g_den: object
    y_leaf: object
    l_leaf: object
    alpha: object
    M: int
    tail: bool
    cells: tuple           # Cell
    checked: bool = True   # False only for hand-forged (negative-control) certificates

    @property
    def lo(self):
        return self.xs[0]

    @property
    def hi(self):
        return self.xs[-1]

    @property
    def K(self) -> int:
        return len(self.a)

    @property
    def umax(self):
        return max(self.vs)

    @property
    def m_dependent(self) -> bool:
        return any(M_SYM in p.as_expr().free_symbols
                   for p in (self.h_num, self.h_den, self.g_num, self.g_den))


def _U(a, b, x):
    return min(ai * x + bi for ai, bi in zip(a, b))


def _lhs_poly(cert_like, j: int, mode: str, m) -> sp.Poly:
    a, b = cert_like["a"][j], cert_like["b"][j]
    R = R_SYM
    if mode == "fixed":
        e = a * R + m * b
    elif mode == "M1":
        e = a * R + (cert_like["M"] + 1) * b
    elif mode == "Rhi":
        e = (a + b / cert_like["hi"]) * R
    else:  # pragma: no cover
        raise ValueError(f"unknown mode {mode}")
    return sp.Poly(sp.expand(e), R, domain="QQ")


def _build_cell(ctx, m, s, t, j, mode, *, check: bool) -> Cell:
    """Compute every obligation of one cell exactly; with ``check`` raise on a failure."""
    mm = m  # None in the tail (h, g are m-free there)
    hn, hd = _at_m(ctx["h_num"], mm), _at_m(ctx["h_den"], mm)
    gn, gd = _at_m(ctx["g_num"], mm), _at_m(ctx["g_den"], mm)
    den_list = []
    for D in (hd, gd):
        if D.degree() > 0 and all(D != E for E in den_list):
            den_list.append(D)
    dtot = sp.Poly(1, R_SYM, domain="QQ")
    for D in den_list:
        dtot = sp.Poly(sp.lcm(dtot.as_expr(), D.as_expr()), R_SYM, domain="QQ")
    if dtot.LC() < 0:
        dtot = -dtot
    dens = tuple(_polycert(D, s, t, True) for D in den_list)
    dtot_cert = _polycert(dtot, s, t, True) if den_list else None
    if check:
        for D, pc in zip(den_list, dens):
            if not pc.ok():
                raise ValueError(f"REFUSED: denominator {D.as_expr()} not certified positive on "
                                 f"[{s}, {'oo' if t is None else t}] (m = {m})")
        if dtot_cert is not None and not dtot_cert.ok():
            raise ValueError(f"REFUSED: common denominator {dtot.as_expr()} not certified "
                             f"positive on [{s}, {'oo' if t is None else t}] (m = {m})")
    H = hn.as_expr() / hd.as_expr()
    G = gn.as_expr() / gd.as_expr()
    lhs = _lhs_poly(ctx, j, mode, m).as_expr() + G + ctx["alpha"]
    obls = []
    for k in range(len(ctx["a"])):
        diff = ctx["a"][k] * H + ctx["b"][k] - lhs
        obls.append(("piece", k, diff))
    obls.append(("lo", None, H - ctx["lo"]))
    obls.append(("hi", None, ctx["hi"] - H))
    out = []
    for side, k, diff in obls:
        N = sp.cancel(sp.together(diff * dtot.as_expr()))
        num, den = sp.fraction(N)
        if sp.simplify(den) != 1:
            N = sp.cancel(N)
            num, den = sp.fraction(N)
            if den.free_symbols:  # pragma: no cover - dtot is a common multiple
                raise ValueError(f"internal: obligation not polynomial after clearing ({N})")
            num = num / den
        P = sp.Poly(sp.expand(num), R_SYM, domain="QQ")
        pc = _polycert(P, s, t, False)
        out.append(Obligation(side=side, k=k, num=pc))
    return Cell(m=m, s=s, t=t, j=j, mode=mode, dens=dens, dtot=dtot_cert,
                obligations=tuple(out))


def _cell_ok(cell: Cell) -> bool:
    return (all(pc.ok() for pc in cell.dens)
            and (cell.dtot is None or cell.dtot.ok())
            and all(o.num.ok() for o in cell.obligations))


def _probe_violation(ctx, m, s, t):
    """Search a few exact points for a GENUINE violation (to report, never to accept)."""
    pts = [s] if t is None else [s, t, (s + t) / 2, s + (t - s) / 4, s + 3 * (t - s) / 4]
    for R in pts:
        mm = m if m is not None else ctx["M"] + 1
        if mm == 0:
            continue
        yb = R / mm
        H = (_at_m(ctx["h_num"], mm).as_expr() / _at_m(ctx["h_den"], mm).as_expr()).subs(R_SYM, R)
        G = (_at_m(ctx["g_num"], mm).as_expr() / _at_m(ctx["g_den"], mm).as_expr()).subs(R_SYM, R)
        if not (ctx["lo"] <= yb <= ctx["hi"]):
            continue
        lhs = mm * _U(ctx["a"], ctx["b"], yb) + G + ctx["alpha"]
        if not (ctx["lo"] <= H <= ctx["hi"]):
            return f"closure fails: h({mm}, {R}) = {H} outside [{ctx['lo']}, {ctx['hi']}]"
        rhs = _U(ctx["a"], ctx["b"], H)
        if lhs > rhs:
            return (f"obligation FALSE at m = {mm}, R = {R}: "
                    f"m U(R/m) + g + alpha = {lhs} > U(h) = {rhs}")
    return None


def _cover(ctx, m, s, t, cands, depth, *, check=True) -> list:
    """Untrusted cell search: try each (j, mode) candidate, bisect on failure."""
    for j, mode in cands:
        cell = _build_cell(ctx, m, s, t, j, mode, check=False)
        if _cell_ok(cell):
            return [cell]
    if t is None:
        return None
    if depth >= _MAX_DEPTH:
        return None
    mid = (s + t) / 2
    left = _cover(ctx, m, s, mid, cands, depth + 1)
    if left is None:
        return None
    right = _cover(ctx, m, mid, t, cands, depth + 1)
    if right is None:
        return None
    return left + right


def _fixed_m_cells(ctx, m) -> list:
    cells = []
    xs = ctx["xs"]
    for j in range(len(xs) - 1):
        s, t = m * xs[j], m * xs[j + 1]
        cands = [(j, "fixed")] + [(i, "fixed") for i in range(len(xs) - 1) if i != j]
        got = _cover(ctx, m, s, t, cands, 0)
        if got is None:
            why = _probe_violation(ctx, m, s, t)
            raise ValueError(f"REFUSED: no certificate for m = {m} on R in [{s}, {t}] down to "
                             f"depth {_MAX_DEPTH}" + (f"; {why}" if why else ""))
        cells += got
    return cells


def _tail_cells(ctx, breaks) -> list:
    M1 = ctx["M"] + 1
    start = M1 * ctx["lo"]
    cands = []
    for j in range(len(ctx["a"])):
        if ctx["b"][j] <= 0:
            cands += [(j, "Rhi"), (j, "M1")]
    if not cands:
        raise ValueError("REFUSED: tail requested but no piece has intercept b_j <= 0")
    if breaks is None:
        # fewest cells first: the whole half-line, then one finite cell [start, B] (bisected
        # as needed) plus [B, oo) for growing B
        whole = _cover(ctx, None, start, None, cands, 0)
        if whole is not None:
            return whole
        for k in range(-2, 10):
            B = start + sp.Rational(2) ** k
            last = _cover(ctx, None, B, None, cands, 0)
            if last is None:
                continue
            first = _cover(ctx, None, start, B, cands, 0)
            if first is not None:
                return first + last
        breaks = []
    pts = [start] + sorted(sp.Rational(x) for x in breaks if sp.Rational(x) > start)
    cells = []
    for s, t in zip(pts, pts[1:]):
        got = _cover(ctx, None, s, t, cands, 0)
        if got is None:
            why = _probe_violation(ctx, None, s, t)
            raise ValueError(f"REFUSED: no tail certificate on R in [{s}, {t}]"
                             + (f"; {why}" if why else ""))
        cells += got
    last = _cover(ctx, None, pts[-1], None, cands, 0)
    if last is None:
        raise ValueError(f"REFUSED: no tail certificate on the unbounded cell R >= {pts[-1]}")
    return cells + last


def _check_cover(cells, m, start, stop):
    cur = start
    for c in cells:
        if c.s != cur:
            raise ValueError(f"REFUSED: cells for m = {m} do not cover the domain (gap/overlap "
                             f"at {cur} vs {c.s})")
        if c.t is not None and not c.t > c.s:
            raise ValueError(f"REFUSED: degenerate cell [{c.s}, {c.t}]")
        cur = c.t
    if cur != stop:
        raise ValueError(f"REFUSED: cells for m = {m} end at {cur}, domain ends at {stop}")


def verify_certificate(cert: ConcavePooledCert) -> None:
    """Re-verify every obligation of ``cert`` exactly (raises ``ValueError`` on failure)."""
    ctx = _ctx_of(cert)
    for i in range(1, cert.K):
        if not cert.a[i] < cert.a[i - 1]:
            raise ValueError("REFUSED: slopes not strictly decreasing (witness not concave)")
    for mm in range(1, cert.M + 1):
        cs = [c for c in cert.cells if c.m == mm]
        _check_cover(cs, mm, mm * cert.lo, mm * cert.hi)
    if cert.tail:
        cs = [c for c in cert.cells if c.m is None]
        _check_cover(cs, "tail", (cert.M + 1) * cert.lo, None)
    for c in cert.cells:
        if (c.m is None) != (c.mode != "fixed"):
            raise ValueError(f"REFUSED: cell mode {c.mode} does not match m = {c.m} "
                             f"(fixed mode for m <= M, M1/Rhi for the tail)")
        if c.mode != "fixed" and cert.b[c.j] > 0:
            raise ValueError(f"REFUSED: tail mode {c.mode} on piece {c.j} needs b_j <= 0")
        fresh = _build_cell(ctx, c.m, c.s, c.t, c.j, c.mode, check=True)
        if fresh != c:
            raise ValueError(f"REFUSED: cell [{c.s}, {c.t}] (m = {c.m}) does not match its "
                             f"exact recomputation")
        for pc in list(c.dens) + ([c.dtot] if c.dtot else []) + [o.num for o in c.obligations]:
            if not pc.identity_holds():  # pragma: no cover - by construction
                raise ValueError("REFUSED: a Bernstein/Taylor identity does not expand back")
            if not pc.ok():
                raise ValueError(f"REFUSED: negative certificate coefficient on cell "
                                 f"[{c.s}, {c.t}] (m = {c.m})")


def _ctx_of(cert) -> dict:
    return dict(xs=cert.xs, a=cert.a, b=cert.b, lo=cert.lo, hi=cert.hi, M=cert.M,
                alpha=cert.alpha, h_num=cert.h_num, h_den=cert.h_den,
                g_num=cert.g_num, g_den=cert.g_den)


def concave_pooled_certificate(*, nodes, h, g, y_leaf, l_leaf, alpha=0, M, tail=True,
                               tail_breaks=None, check: bool = True) -> ConcavePooledCert:
    """Build (untrusted cell search) and EXACTLY verify a concave-pooled-induction certificate.

    ``nodes``: ``[(x_0, v_0), ..., (x_K, v_K)]`` rational, ``x`` strictly increasing, slopes
    strictly decreasing.  ``h``/``g``: rational functions of the symbols ``m``, ``R`` (sympy
    expressions or strings).  ``M``: the explicit child counts ``1..M``.  ``tail``: also cover
    every ``m >= M+1`` (needs m-free ``h``/``g``, ``lo >= 0``, ``hi > 0``, a piece with
    ``b_j <= 0``); otherwise the claim is for trees of maximum child count ``<= M``.

    ``check=False`` is for hand-forged negative controls ONLY: it computes the certificate
    algebra with every sign check skipped (the result carries ``checked=False``)."""
    if len(nodes) < 2:
        raise ValueError("REFUSED: need at least two nodes")
    xs = tuple(_rat(x, "node x") for x, _ in nodes)
    vs = tuple(_rat(v, "node value") for _, v in nodes)
    for i in range(1, len(xs)):
        if not xs[i] > xs[i - 1]:
            raise ValueError("REFUSED: nodes not strictly increasing")
    a = tuple((vs[i + 1] - vs[i]) / (xs[i + 1] - xs[i]) for i in range(len(xs) - 1))
    b = tuple(vs[i] - a[i] * xs[i] for i in range(len(a)))
    if check:
        for i in range(1, len(a)):
            if not a[i] < a[i - 1]:
                raise ValueError(f"REFUSED: slopes not strictly decreasing at node {i} "
                                 f"({a[i - 1]} then {a[i]}): the witness is not concave "
                                 f"(or has a redundant node)")
    if not isinstance(M, int) or M < 1:
        raise ValueError(f"REFUSED: M = {M!r} must be an integer >= 1")
    y0 = _rat(y_leaf, "y_leaf")
    l0 = _rat(l_leaf, "l_leaf")
    al = _rat(alpha, "alpha")
    hn, hd = _ratfun(h, "h")
    gn, gd = _ratfun(g, "g")
    lo, hi = xs[0], xs[-1]
    if check:
        if not (lo <= y0 <= hi):
            raise ValueError(f"REFUSED: y_leaf = {y0} outside I = [{lo}, {hi}]")
        if not l0 + al <= _U(a, b, y0):
            raise ValueError(f"REFUSED: base fails: l_leaf + alpha = {l0 + al} > "
                             f"U(y_leaf) = {_U(a, b, y0)}")
    ctx = dict(xs=xs, a=a, b=b, lo=lo, hi=hi, M=M, alpha=al,
               h_num=hn, h_den=hd, g_num=gn, g_den=gd)
    if tail:
        if any(M_SYM in p.as_expr().free_symbols for p in (hn, hd, gn, gd)):
            raise ValueError("REFUSED: tail needs h and g independent of m (use tail=False "
                             "for a bounded-degree claim)")
        if lo < 0:
            raise ValueError(f"REFUSED: tail needs lo >= 0 (lo = {lo})")
        if hi <= 0:
            raise ValueError(f"REFUSED: tail needs hi > 0 (hi = {hi})")
        if not any(bj <= 0 for bj in b):
            raise ValueError("REFUSED: tail requested but no piece has intercept b_j <= 0")
    cells: list = []
    if check:
        for mm in range(1, M + 1):
            cells += _fixed_m_cells(ctx, mm)
        if tail:
            cells += _tail_cells(ctx, tail_breaks)
    else:
        # forged: one cell per node segment per m, active piece, no sign checks
        for mm in range(1, M + 1):
            for j in range(len(xs) - 1):
                cells.append(_build_cell(ctx, mm, mm * xs[j], mm * xs[j + 1], j, "fixed",
                                         check=False))
        if tail:
            j0 = next((j for j in range(len(a)) if b[j] <= 0), 0)
            cells.append(_build_cell(ctx, None, (M + 1) * lo, None, j0, "M1", check=False))
    cert = ConcavePooledCert(xs=xs, vs=vs, a=a, b=b, h_num=hn, h_den=hd, g_num=gn, g_den=gd,
                             y_leaf=y0, l_leaf=l0, alpha=al, M=M, tail=bool(tail),
                             cells=tuple(cells), checked=check)
    if check:
        verify_certificate(cert)
    return cert


def certify_concave_pooled_induction_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``, a dict of the keyword arguments of
    :func:`concave_pooled_certificate`."""
    spec = dict(family.special[1](pt))
    cert = concave_pooled_certificate(**spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1 + len(cert.cells)


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

def _q(x) -> str:
    """An exact rational as a Lean real literal."""
    x = sp.Rational(x)
    if x.q == 1:
        return f"({x.p} : ℝ)"
    return f"({x.p} / {x.q} : ℝ)"


def _poly_lean(p: sp.Poly, mvar: str | None) -> str:
    """Render a polynomial in (R, m); ``mvar`` is the Lean text for m (None: must be m-free)."""
    terms = []
    for (dr, dm), c in sorted(p.terms(), key=lambda t: (t[0][1], t[0][0])):
        c = sp.Rational(c)
        if c == 0:
            continue
        parts = []
        if dm:
            if mvar is None:  # pragma: no cover - guarded by callers
                raise ValueError("internal: m in an m-free rendering")
            parts.append(mvar if dm == 1 else f"{mvar} ^ {dm}")
        if dr:
            parts.append("R" if dr == 1 else f"R ^ {dr}")
        if c != 1 or not parts:
            parts.insert(0, _q(c))
        terms.append(" * ".join(parts))
    return "(" + (" + ".join(terms) if terms else "(0 : ℝ)") + ")"


def _poly1(coeffs, var: str = "R") -> str:
    """Render an ascending coefficient tuple in one variable."""
    terms = []
    for i, c in enumerate(coeffs):
        c = sp.Rational(c)
        if c == 0:
            continue
        v = "" if i == 0 else (var if i == 1 else f"{var} ^ {i}")
        terms.append(_q(c) if not v else (v if c == 1 else f"{_q(c)} * {v}"))
    return "(" + (" + ".join(terms) if terms else "(0 : ℝ)") + ")"


def _facts(pc: PolyCert) -> str:
    """The product facts linarith needs for a PolyCert (hs : 0 <= R - s, ht : 0 <= t - R)."""
    d = pc.degree
    if pc.t is None:
        return ", ".join(f"pow_nonneg hs {i}" for i in range(d + 1))
    return ", ".join(f"mul_nonneg (pow_nonneg hs {i}) (pow_nonneg ht {d - i})"
                     for i in range(d + 1))


_GENERIC = r"""/-! ## Generic concave pooled induction (emitted once per file)

Method: concave-witness induction, from the draft "The maximum Laplacian ratio of a tree for
all n >= 303: concave witnesses and one-variable certificates" (28 September 2026),
communicated by Professor John L. Goldwasser (author: his London colleague; name to be added).
conjecture1_proved = False. -/

namespace ConcavePooled

/-- Finite rooted trees; an internal node has `m + 1 ≥ 1` children. -/
inductive PTree : Type
  | leaf : PTree
  | node (m : ℕ) (cs : Fin (m + 1) → PTree) : PTree

namespace PTree

/-- Number of vertices. -/
def size : PTree → ℕ
  | leaf => 1
  | node _ cs => (∑ i, size (cs i)) + 1

/-- The message: `y_leaf` at a leaf, `h (#children) (sum of the children's messages)`. -/
def msg (h : ℕ → ℝ → ℝ) (y0 : ℝ) : PTree → ℝ
  | leaf => y0
  | node m cs => h (m + 1) (∑ i, msg h y0 (cs i))

/-- The profit: `l_leaf` at a leaf, the children's profits plus `g (#children) (sum)`. -/
def ell (g h : ℕ → ℝ → ℝ) (l0 y0 : ℝ) : PTree → ℝ
  | leaf => l0
  | node m cs => (∑ i, ell g h l0 y0 (cs i)) + g (m + 1) (∑ i, msg h y0 (cs i))

/-- Every internal node's child count satisfies `ok`. -/
def AllDeg (ok : ℕ → Prop) : PTree → Prop
  | leaf => True
  | node m cs => ok (m + 1) ∧ ∀ i, AllDeg ok (cs i)

theorem allDeg_true (b : PTree) : b.AllDeg (fun _ => True) := by
  induction b with
  | leaf => trivial
  | node m cs ih => exact ⟨trivial, ih⟩

end PTree

/-- THE INDUCTION.  A carried function `U` and a pooling function `V ≥ U` on `I = [lo, hi]`
with Jensen for `V`; if every admissible node satisfies the pooled-mean step and keeps the
message in `I`, then every tree satisfies `ell + α·size ≤ U (msg)`. -/
theorem pooled_induction_core (ok : ℕ → Prop) (h g : ℕ → ℝ → ℝ) (U V : ℝ → ℝ)
    (y0 l0 lo hi α : ℝ)
    (hJ : ∀ (n : ℕ) (y : Fin n → ℝ), 0 < n →
      ∑ i, V (y i) ≤ (n : ℝ) * V ((∑ i, y i) / n))
    (hUV : ∀ y, lo ≤ y → y ≤ hi → U y ≤ V y)
    (hy0 : lo ≤ y0 ∧ y0 ≤ hi)
    (hbase : l0 + α ≤ U y0)
    (hclos : ∀ m : ℕ, 1 ≤ m → ok m → ∀ yb, lo ≤ yb → yb ≤ hi →
      lo ≤ h m (m * yb) ∧ h m (m * yb) ≤ hi)
    (hstep : ∀ m : ℕ, 1 ≤ m → ok m → ∀ yb, lo ≤ yb → yb ≤ hi →
      (m : ℝ) * V yb + g m (m * yb) + α ≤ U (h m (m * yb))) :
    ∀ b : PTree, b.AllDeg ok →
      lo ≤ b.msg h y0 ∧ b.msg h y0 ≤ hi ∧
        b.ell g h l0 y0 + α * b.size ≤ U (b.msg h y0) := by
  intro b
  induction b with
  | leaf =>
    intro _
    simp only [PTree.msg, PTree.ell, PTree.size, Nat.cast_one, mul_one]
    exact ⟨hy0.1, hy0.2, hbase⟩
  | node m cs ih =>
    intro hdeg
    obtain ⟨hok, hcs⟩ := hdeg
    have hc : ∀ i, lo ≤ (cs i).msg h y0 ∧ (cs i).msg h y0 ≤ hi ∧
        (cs i).ell g h l0 y0 + α * (cs i).size ≤ U ((cs i).msg h y0) :=
      fun i => ih i (hcs i)
    set R := ∑ i, (cs i).msg h y0 with hR
    have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hRlo : ((m + 1 : ℕ) : ℝ) * lo ≤ R := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
        (fun i _ => (hc i).1)
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    have hRhi : R ≤ ((m + 1 : ℕ) : ℝ) * hi := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
        (fun i _ => (hc i).2.1)
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    set yb := R / ((m + 1 : ℕ) : ℝ) with hyb
    have hmyb : ((m + 1 : ℕ) : ℝ) * yb = R := by
      rw [hyb]; field_simp
    have hyblo : lo ≤ yb := by
      rw [hyb, le_div_iff₀ hn]; linarith
    have hybhi : yb ≤ hi := by
      rw [hyb, div_le_iff₀ hn]; linarith
    have hm1 : 1 ≤ m + 1 := Nat.le_add_left 1 m
    have hcl := hclos (m + 1) hm1 hok yb hyblo hybhi
    have hst := hstep (m + 1) hm1 hok yb hyblo hybhi
    rw [hmyb] at hcl hst
    have hJ' := hJ (m + 1) (fun i => (cs i).msg h y0) (Nat.succ_pos m)
    have hsumU : ∑ i, ((cs i).ell g h l0 y0 + α * (cs i).size) ≤
        ∑ i, V ((cs i).msg h y0) :=
      Finset.sum_le_sum fun i _ =>
        le_trans (hc i).2.2 (hUV _ (hc i).1 (hc i).2.1)
    have hsize : (((PTree.node m cs).size : ℕ) : ℝ) = (∑ i, ((cs i).size : ℝ)) + 1 := by
      simp [PTree.size]
    refine ⟨hcl.1, hcl.2, ?_⟩
    simp only [PTree.msg, PTree.ell]
    rw [hsize, ← hR]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumU
    have : ∑ i, (cs i).ell g h l0 y0 + α * ∑ i, ((cs i).size : ℝ)
        ≤ ((m + 1 : ℕ) : ℝ) * V yb := le_trans hsumU hJ'
    linarith

/-- A concave piecewise-linear function as the MINIMUM of its `K + 1` affine pieces. -/
noncomputable def minPieces {K : ℕ} (a b : Fin (K + 1) → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k => a k * x + b k)

theorem minPieces_le {K : ℕ} (a b : Fin (K + 1) → ℝ) (x : ℝ) (k : Fin (K + 1)) :
    minPieces a b x ≤ a k * x + b k :=
  Finset.inf'_le _ (Finset.mem_univ k)

theorem le_minPieces {K : ℕ} (a b : Fin (K + 1) → ℝ) (x c : ℝ)
    (h : ∀ k, c ≤ a k * x + b k) : c ≤ minPieces a b x :=
  Finset.le_inf' _ _ (fun k _ => h k)

/-- Jensen for a minimum of affine pieces: the sum of minima is at most the minimum of the
sums, and each piece sums to `n` times its value at the mean. -/
theorem minPieces_jensen {K : ℕ} (a b : Fin (K + 1) → ℝ) (n : ℕ) (y : Fin n → ℝ)
    (hn : 0 < n) :
    ∑ i, minPieces a b (y i) ≤ (n : ℝ) * minPieces a b ((∑ i, y i) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_comm, ← div_le_iff₀ hn']
  apply le_minPieces
  intro k
  rw [div_le_iff₀ hn']
  calc ∑ i, minPieces a b (y i) ≤ ∑ i, (a k * y i + b k) :=
        Finset.sum_le_sum fun i _ => minPieces_le a b (y i) k
    _ = (a k * ((∑ i, y i) / n) + b k) * n := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp

end ConcavePooled

open ConcavePooled
"""


@dataclass
class ConcavePooledInductionEmitter(Emitter):
    """Emit the generic concave pooled induction once, then per instance the witness, the
    recursion, every certified cell obligation, the step and tail lemmas, the final theorem
    `∀ b, ell + α·size ≤ U (msg)` and the uniform corollary `ell + α·size ≤ max v_j`.

    HONEST SCOPE: a bound for one explicit rational recursion on every finite rooted tree
    (or every tree of child count at most `M` without a tail).  Nothing about BG or RH.
    Method credit: concave-witness induction, from a draft communicated by Professor John L.
    Goldwasser (author: his London colleague; name to be added).  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "concave_pooled_induction"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts = [_GENERIC]
        nthm = 6
        for inst in fam.instances:
            text, n = self._emit_instance(inst.payload, inst.lean_name)
            parts.append(text)
            nthm += n
        return "\n".join(parts), nthm

    def emit_units(self, fam, profile: LeanProfile):
        # the generic section is shared across instances: one unit
        return [self.emit_body(fam, profile)]

    # -- per instance -------------------------------------------------------------------
    def _emit_instance(self, c: ConcavePooledCert, nm: str) -> tuple[str, int]:
        L: list[str] = []
        n = 0
        K = c.K
        lo, hi = _q(c.lo), _q(c.hi)
        al = _q(c.alpha)
        mdep = c.m_dependent
        mv = "(m : ℝ)" if mdep else None

        def fun_text(num, den):
            nt = _poly_lean(num, mv)
            if den.total_degree() == 0:
                return nt
            return f"{nt} / {_poly_lean(den, mv)}"

        scope = ("every finite rooted tree" if c.tail
                 else f"every finite rooted tree of child count at most {c.M}")
        L.append(f"/-! ## Instance `{nm}`\n\n"
                 f"Claim: `ell + ({c.alpha}) * size ≤ U (msg)` on {scope}, for\n"
                 f"  h(m, R) = {sp.sstr(c.h_num.as_expr() / c.h_den.as_expr())},  "
                 f"g(m, R) = {sp.sstr(c.g_num.as_expr() / c.g_den.as_expr())},\n"
                 f"  leaf (y, l) = ({c.y_leaf}, {c.l_leaf}), U the concave interpolant of\n"
                 f"  {', '.join(f'({x}, {v})' for x, v in zip(c.xs, c.vs))}.\n"
                 f"Certificate: {len(c.cells)} cells (explicit m = 1..{c.M}"
                 f"{', plus the m-free tail m ≥ ' + str(c.M + 1) if c.tail else ''}). -/\n")
        L.append(f"noncomputable def {nm}_A : Fin {K} → ℝ := ![{', '.join(_q(x) for x in c.a)}]")
        L.append(f"noncomputable def {nm}_B : Fin {K} → ℝ := ![{', '.join(_q(x) for x in c.b)}]")
        L.append(f"/-- The witness: the minimum of its {K} affine pieces. -/")
        L.append(f"noncomputable def {nm}_U : ℝ → ℝ := minPieces {nm}_A {nm}_B")
        for fn, (pn, pd) in (("h", (c.h_num, c.h_den)), ("g", (c.g_num, c.g_den))):
            uses_m = any(M_SYM in p.as_expr().free_symbols for p in (pn, pd))
            L.append(f"noncomputable def {nm}_{fn} : ℕ → ℝ → ℝ := fun {'m' if uses_m else '_'} R => "
                     f"{fun_text(pn, pd)}")
        L.append("")
        U = f"{nm}_U"
        # pieces
        for j in range(K):
            L.append(f"theorem {nm}_piece{j} (x : ℝ) : {U} x ≤ {_q(c.a[j])} * x + {_q(c.b[j])} := by\n"
                     f"  have := minPieces_le {nm}_A {nm}_B x {j}\n"
                     f"  simpa [{U}, {nm}_A, {nm}_B] using this\n")
            n += 1
        # node table (kernel re-check of concavity/interpolation)
        for i, (x, v) in enumerate(zip(c.xs, c.vs)):
            j = 0 if i == 0 else i - 1
            L.append(f"theorem {nm}_node{i} : {U} {_q(x)} = {_q(v)} := by\n"
                     f"  apply le_antisymm\n"
                     f"  · linarith [{nm}_piece{j} {_q(x)}]\n"
                     f"  · apply le_minPieces; intro k; fin_cases k <;> norm_num [{nm}_A, {nm}_B]\n")
            n += 1
        # base
        L.append(f"theorem {nm}_base : {_q(c.l_leaf)} + {al} ≤ {U} {_q(c.y_leaf)} := by\n"
                 f"  apply le_minPieces; intro k; fin_cases k <;> norm_num [{nm}_A, {nm}_B]\n")
        n += 1
        # cells
        for ci, cell in enumerate(c.cells):
            text, k = self._emit_cell(c, nm, ci, cell)
            L.append(text)
            n += k
        # fixed-m steps
        for mm in range(1, c.M + 1):
            L.append(self._emit_step(c, nm, mm))
            n += 2
        if c.tail:
            L.append(self._emit_tail(c, nm))
            n += 2
        L.append(self._emit_assembly(c, nm))
        n += 5
        return "\n".join(L), n

    def _cell_args(self, cell, with_m: bool) -> str:
        margs = "(m : ℕ) " if with_m else ""
        up = "" if cell.t is None else f" (h2 : R ≤ {_q(cell.t)})"
        return f"{margs}(R : ℝ) (h1 : {_q(cell.s)} ≤ R){up}"

    def _cell_intro(self, cell) -> list[str]:
        out = [f"  have hs : 0 ≤ R - {_q(cell.s)} := by linarith"]
        if cell.t is not None:
            out.append(f"  have ht : 0 ≤ {_q(cell.t)} - R := by linarith")
        return out

    def _lhs_text(self, c, cell, R: str = "R") -> str:
        a, b = c.a[cell.j], c.b[cell.j]
        if cell.mode == "fixed":
            return f"{_q(a)} * {R} + {_q(cell.m)} * {_q(b)}"
        if cell.mode == "M1":
            return f"{_q(a)} * {R} + {_q(c.M + 1)} * {_q(b)}"
        return f"{_q(a + b / c.hi)} * {R}"

    def _emit_cell(self, c, nm, ci, cell) -> tuple[str, int]:
        L = []
        tailc = cell.m is None
        marg = "m" if tailc else str(cell.m)
        hcall, gcall = f"{nm}_h {marg} R", f"{nm}_g {marg} R"
        args = self._cell_args(cell, tailc)
        lhs = self._lhs_text(c, cell)
        mlit = cell.m
        hn, hd = _at_m(c.h_num, mlit), _at_m(c.h_den, mlit)
        gn, gd = _at_m(c.g_num, mlit), _at_m(c.g_den, mlit)

        def closed(num, den):
            nt = _poly1(_poly_tuple(num))
            return nt if den.degree() <= 0 else f"{nt} / {_poly1(_poly_tuple(den))}"

        h_closed, g_closed = f"({closed(hn, hd)})", f"({closed(gn, gd)})"
        # m-free: the closed form is printed exactly as the definition body, so unfolding
        # closes it; m-dependent: the cast `((m : ℕ) : ℝ)` and the expanded coefficients
        # differ syntactically, so `ring` finishes.
        def _mdep(*ps):
            return any(M_SYM in p.as_expr().free_symbols for p in ps)
        tail_h = "; ring" if _mdep(c.h_num, c.h_den) else ""
        tail_g = "; ring" if _mdep(c.g_num, c.g_den) else ""
        common = self._cell_intro(cell)
        dt_poly = cell.dtot.poly if cell.dtot is not None else None
        for di, pc in enumerate(cell.dens):
            if pc.poly == dt_poly:
                continue
            common.append(f"  have hD{di} : 0 < {_poly1(pc.poly)} := by linarith [{_facts(pc)}]")
        if cell.dtot is not None:
            common.append(f"  have hDt : 0 < {_poly1(cell.dtot.poly)} := by "
                          f"linarith [{_facts(cell.dtot)}]")
            common.append("  have hDt' := hDt.ne'")
        common.append(f"  have eh : {hcall} = {h_closed} := by simp only [{nm}_h]{tail_h}")
        common.append(f"  have eg : {gcall} = {g_closed} := by simp only [{nm}_g]{tail_g}")
        nthm = 0
        for ob in cell.obligations:
            if ob.side == "piece":
                lhs_t = f"{lhs} + {gcall} + {al_text(c)}"
                rhs_t = f"{_q(c.a[ob.k])} * {hcall} + {_q(c.b[ob.k])}"
                tag = f"k{ob.k}"
            elif ob.side == "lo":
                lhs_t, rhs_t = _q(c.lo), hcall
                tag = "lo"
            else:
                lhs_t, rhs_t = hcall, _q(c.hi)
                tag = "hi"
            stmt = f"{lhs_t} ≤ {rhs_t}"
            lhs_c = lhs_t.replace(hcall, h_closed).replace(gcall, g_closed)
            rhs_c = rhs_t.replace(hcall, h_closed).replace(gcall, g_closed)
            N = _poly1(ob.num.poly)
            body = [ln for ln in common
                    if not (ln.startswith("  have eg") and gcall not in stmt)]
            rws = ", ".join(x for x, cl in (("eh", hcall), ("eg", gcall)) if cl in stmt)
            body.append(f"  have key : 0 ≤ {N} := by linarith [{_facts(ob.num)}]")
            if cell.dtot is not None:
                D = _poly1(cell.dtot.poly)
                body.append(f"  have e : ({rhs_c}) - ({lhs_c}) = {N} / {D} := by")
                body.append(f"    field_simp")
                body.append(f"    ring")
                body.append(f"  have hq := div_nonneg key hDt.le")
                body.append(f"  rw [{rws}]")
                body.append(f"  linarith")
            else:
                body.append(f"  have e : ({rhs_c}) - ({lhs_c}) = {N} := by ring")
                body.append(f"  rw [{rws}]")
                body.append(f"  linarith")
            L.append(f"theorem {nm}_c{ci}_{tag} {args} :\n    {stmt} := by\n" + "\n".join(body)
                     + "\n")
            nthm += 1
        # aggregate: against U (min of pieces) and the closure pair
        call = "m R h1" if tailc else "R h1"
        if cell.t is not None:
            call += " h2"
        L.append(f"theorem {nm}_c{ci} {args} :\n"
                 f"    {lhs} + {gcall} + {al_text(c)} ≤ {nm}_U ({hcall}) := by\n"
                 f"  apply le_minPieces; intro k; fin_cases k\n"
                 + "".join(f"  · have := {nm}_c{ci}_k{k} {call}\n"
                           f"    simpa [{nm}_A, {nm}_B] using this\n" for k in range(c.K)))
        L.append(f"theorem {nm}_c{ci}_cl {args} :\n"
                 f"    {_q(c.lo)} ≤ {hcall} ∧ {hcall} ≤ {_q(c.hi)} :=\n"
                 f"  ⟨{nm}_c{ci}_lo {call}, {nm}_c{ci}_hi {call}⟩\n")
        return "\n".join(L), nthm + 2

    def _split(self, cells, Rt: str, lead: list[str], finish) -> list[str]:
        """Case-split `Rt` over consecutive cells; ``finish(idx, cell, lo_h, hi_h)`` -> line."""
        out = list(lead)
        ncell = len(cells)
        prev = None
        for i, (ci, cell) in enumerate(cells):
            lo_h = "(by linarith)" if prev is None else f"h_{i - 1}.le"
            if i < ncell - 1:
                out.append(f"  rcases le_or_gt ({Rt}) {_q(cell.t)} with h_{i} | h_{i}")
                out.append(f"  · {finish(ci, cell, lo_h, f'h_{i}')}")
            else:
                hi_h = None if cell.t is None else "(by linarith)"
                out.append(f"  · {finish(ci, cell, lo_h, hi_h)}")
            prev = i
        return out

    def _emit_step(self, c, nm, mm) -> str:
        cells = [(i, cl) for i, cl in enumerate(c.cells) if cl.m == mm]
        R = f"{mm} * yb"
        head = (f"theorem {nm}_step{mm} (yb : ℝ) (hl : {_q(c.lo)} ≤ yb) (hu : yb ≤ {_q(c.hi)}) :\n"
                f"    (({mm} : ℕ) : ℝ) * {nm}_U yb + {nm}_g {mm} ((({mm} : ℕ) : ℝ) * yb) + "
                f"{al_text(c)} ≤ {nm}_U ({nm}_h {mm} ((({mm} : ℕ) : ℝ) * yb)) := by\n")
        lead = [f"  rw [show (({mm} : ℕ) : ℝ) = {mm} by norm_num]"]

        def fin(ci, cell, lo_h, hi_h):
            args = f"({R}) {lo_h}" + ("" if hi_h is None else f" {hi_h}")
            return f"linarith [{nm}_c{ci} {args}, {nm}_piece{cell.j} yb]"
        body = self._split(cells, R, lead, fin)
        step = head + "\n".join(body) + "\n"

        head2 = (f"theorem {nm}_clos{mm} (yb : ℝ) (hl : {_q(c.lo)} ≤ yb) (hu : yb ≤ {_q(c.hi)}) :\n"
                 f"    {_q(c.lo)} ≤ {nm}_h {mm} ((({mm} : ℕ) : ℝ) * yb) ∧ "
                 f"{nm}_h {mm} ((({mm} : ℕ) : ℝ) * yb) ≤ {_q(c.hi)} := by\n")

        def fin2(ci, cell, lo_h, hi_h):
            args = f"({R}) {lo_h}" + ("" if hi_h is None else f" {hi_h}")
            return f"exact {nm}_c{ci}_cl {args}"
        body2 = self._split(cells, R, lead, fin2)
        return step + "\n" + head2 + "\n".join(body2) + "\n"

    def _emit_tail(self, c, nm) -> str:
        cells = [(i, cl) for i, cl in enumerate(c.cells) if cl.m is None]
        M1 = c.M + 1
        R = "(m : ℝ) * yb"
        pre = [f"  have hm4 : {M1} ≤ m := hm",
               f"  have hmr : ({M1} : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4",
               f"  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m",
               f"  have hR0 : ({M1} : ℝ) * {_q(c.lo)} ≤ {R} :=",
               f"    mul_le_mul hmr hl (by norm_num) hm0"]
        used = sorted({cl.j for _, cl in cells})
        for j in used:
            pre.append(f"  have hP{j} : (m : ℝ) * {nm}_U yb ≤ (m : ℝ) * "
                       f"({_q(c.a[j])} * yb + {_q(c.b[j])}) :=")
            pre.append(f"    mul_le_mul_of_nonneg_left ({nm}_piece{j} yb) hm0")
            pre.append(f"  have hM{j} : (m : ℝ) * {_q(c.b[j])} ≤ ({M1} : ℝ) * {_q(c.b[j])} :=")
            pre.append(f"    mul_le_mul_of_nonpos_right hmr (by norm_num)")
            pre.append(f"  have hH{j} : 0 ≤ (m : ℝ) * (-{_q(c.b[j])}) * ({_q(c.hi)} - yb) :=")
            pre.append(f"    mul_nonneg (mul_nonneg hm0 (by norm_num)) (by linarith)")
        head = (f"theorem {nm}_tail (m : ℕ) (hm : {c.M} < m) (yb : ℝ) (hl : {_q(c.lo)} ≤ yb)"
                f" (hu : yb ≤ {_q(c.hi)}) :\n"
                f"    (m : ℝ) * {nm}_U yb + {nm}_g m ((m : ℝ) * yb) + {al_text(c)} ≤ "
                f"{nm}_U ({nm}_h m ((m : ℝ) * yb)) := by\n")

        def fin(ci, cell, lo_h, hi_h):
            args = f"m ({R}) {lo_h}" + ("" if hi_h is None else f" {hi_h}")
            j = cell.j
            return f"linarith [{nm}_c{ci} {args}, hP{j}, hM{j}, hH{j}]"
        body = self._split(cells, R, pre, fin)
        tail = head + "\n".join(body) + "\n"

        head2 = ("set_option linter.unusedVariables false in\n"
                 f"theorem {nm}_tail_clos (m : ℕ) (hm : {c.M} < m) (yb : ℝ) "
                 f"(hl : {_q(c.lo)} ≤ yb) (hu : yb ≤ {_q(c.hi)}) :\n"
                 f"    {_q(c.lo)} ≤ {nm}_h m ((m : ℝ) * yb) ∧ "
                 f"{nm}_h m ((m : ℝ) * yb) ≤ {_q(c.hi)} := by\n")
        pre2 = pre[:5]

        def fin2(ci, cell, lo_h, hi_h):
            args = f"m ({R}) {lo_h}" + ("" if hi_h is None else f" {hi_h}")
            return f"exact {nm}_c{ci}_cl {args}"
        body2 = self._split(cells, R, pre2, fin2)
        return tail + "\n" + head2 + "\n".join(body2) + "\n"

    def _emit_assembly(self, c, nm) -> str:
        M = c.M
        lo, hi = _q(c.lo), _q(c.hi)
        U = f"{nm}_U"
        ind = "    " if c.tail else "  "
        steps = "\n".join(f"{ind}· exact {nm}_step{mm} yb hl hu" for mm in range(1, M + 1))
        closs = "\n".join(f"{ind}· exact {nm}_clos{mm} yb hl hu" for mm in range(1, M + 1))
        stmt_step = (f"(m : ℝ) * {U} yb + {nm}_g m (m * yb) + {al_text(c)} ≤ "
                     f"{U} ({nm}_h m (m * yb))")
        stmt_clos = f"{lo} ≤ {nm}_h m (m * yb) ∧ {nm}_h m (m * yb) ≤ {hi}"
        ok = "True" if c.tail else f"m ≤ {M}"
        okfun = "(fun _ => True)" if c.tail else f"(fun m => m ≤ {M})"
        if c.tail:
            split = (f"  rcases Nat.lt_or_ge {M} m with hM | hM\n"
                     f"  · exact {{TAIL}} m hM yb hl hu\n"
                     f"  · interval_cases m\n")
        else:
            split = "  interval_cases m\n"
        out = []
        out.append(f"theorem {nm}_hstep : ∀ m : ℕ, 1 ≤ m → {ok} → ∀ yb : ℝ, {lo} ≤ yb → "
                   f"yb ≤ {hi} →\n    {stmt_step} := by\n"
                   f"  intro m hm hok yb hl hu\n"
                   + split.replace("{TAIL}", f"{nm}_tail") + steps + "\n")
        out.append(f"theorem {nm}_hclos : ∀ m : ℕ, 1 ≤ m → {ok} → ∀ yb : ℝ, {lo} ≤ yb → "
                   f"yb ≤ {hi} →\n    {stmt_clos} := by\n"
                   f"  intro m hm hok yb hl hu\n"
                   + split.replace("{TAIL}", f"{nm}_tail_clos") + closs + "\n")
        # U <= max node value on I
        umax = _q(c.umax)
        segs = []
        for j in range(c.K):
            segs.append((j, c.xs[j + 1]))
        ul = ["set_option linter.unusedVariables false in",
              f"theorem {nm}_U_le_max (x : ℝ) (hl : {lo} ≤ x) (hu : x ≤ {hi}) : {U} x ≤ {umax} := by"]
        for i, (j, xr) in enumerate(segs):
            if i < len(segs) - 1:
                ul.append(f"  rcases le_or_gt x {_q(xr)} with h_{i} | h_{i}")
                ul.append(f"  · linarith [{nm}_piece{j} x]")
            else:
                ul.append(f"  · linarith [{nm}_piece{j} x]")
        out.append("\n".join(ul) + "\n")
        deg = "" if c.tail else f" (hb : b.AllDeg (fun m => m ≤ {M}))"
        hb = f"(PTree.allDeg_true b)" if c.tail else "hb"
        concl = (f"b.ell {nm}_g {nm}_h {_q(c.l_leaf)} {_q(c.y_leaf)} + {al_text(c)} * b.size ≤ "
                 f"{U} (b.msg {nm}_h {_q(c.y_leaf)})")
        out.append(f"/-- MAIN.  The certified bound on {'every finite rooted tree' if c.tail else f'every tree of child count at most {M}'}. -/\n"
                   f"theorem {nm} (b : PTree){deg} :\n"
                   f"    {lo} ≤ b.msg {nm}_h {_q(c.y_leaf)} ∧ b.msg {nm}_h {_q(c.y_leaf)} ≤ {hi} ∧\n"
                   f"      {concl} :=\n"
                   f"  pooled_induction_core {okfun} {nm}_h {nm}_g {U} {U} {_q(c.y_leaf)} "
                   f"{_q(c.l_leaf)} {lo} {hi} {al_text(c)}\n"
                   f"    (minPieces_jensen {nm}_A {nm}_B) (fun _ _ _ => le_rfl) "
                   f"⟨by norm_num, by norm_num⟩ {nm}_base {nm}_hclos {nm}_hstep b {hb}\n")
        out.append(f"/-- Uniform corollary: `ell + α·size ≤ max_j v_j = {c.umax}`. -/\n"
                   f"theorem {nm}_uniform (b : PTree){deg} :\n"
                   f"    b.ell {nm}_g {nm}_h {_q(c.l_leaf)} {_q(c.y_leaf)} + {al_text(c)} * b.size"
                   f" ≤ {umax} := by\n"
                   f"  obtain ⟨h1, h2, h3⟩ := {nm} b{'' if c.tail else ' hb'}\n"
                   f"  linarith [{nm}_U_le_max _ h1 h2]\n")
        return "\n".join(out)


def al_text(c) -> str:
    return _q(c.alpha)


def concave_pooled_induction_family(name, grid, lean_name, spec, constants=None):
    """Build a concave-pooled-induction family (kind='concave_pooled_induction').

    ``spec``: a callable ``pt -> dict`` of :func:`concave_pooled_certificate` keyword
    arguments (``nodes``, ``h``, ``g``, ``y_leaf``, ``l_leaf``, ``alpha``, ``M``, ``tail``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("concave_pooled_induction", spec),
        constants=dict(constants or {}),
    )


#: The dogfood: the classical matching message.  For a rooted tree `T_u`,
#: `y_u = Z(T_u - u) / Z(T_u)` (Z = number of matchings) is the probability that `u` is
#: unmatched in a uniform random matching of `T_u`; it obeys `y = 1 / (1 + sum_children y)`,
#: `y_leaf = 1`.  With `l = -sum_u y_u` the certificate proves `sum_u y_u >= (3/5) |T|`
#: for every rooted tree (the path shows the sharp constant is `1/phi = 0.618...`).
MATCHING_DENSITY_SPEC = dict(
    nodes=[(0, 0), (sp.Rational(1, 2), sp.Rational(-1, 8)), (1, sp.Rational(-3, 10))],
    h="1/(1+R)", g="-1/(1+R)", y_leaf=1, l_leaf=-1, alpha=sp.Rational(3, 5), M=2, tail=True,
)

#: The same recursion restricted to PATHS (child count at most 1): bounded-degree mode.
PATH_DENSITY_SPEC = dict(MATCHING_DENSITY_SPEC, M=1, tail=False)


if __name__ == "__main__":
    c = concave_pooled_certificate(**MATCHING_DENSITY_SPEC)
    print(f"matching density: {len(c.cells)} cells, pieces a={c.a} b={c.b}")
    for cl in c.cells:
        print(f"  m={cl.m} [{cl.s}, {cl.t}] j={cl.j} mode={cl.mode}")
    try:
        concave_pooled_certificate(**dict(MATCHING_DENSITY_SPEC, alpha=sp.Rational(13, 20)))
        raise SystemExit("FAIL: alpha = 13/20 (> 1/phi) was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:120]}")

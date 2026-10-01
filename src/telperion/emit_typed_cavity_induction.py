"""typed_cavity_induction emitter -- a finite TYPE TABLE with per-type bounds is an inductive
invariant of a branching (tree) recursion over every finite rooted tree.

conjecture1_proved = False.  Nothing in this module bears on the Brualdi-Goldwasser
conjecture, on RH, or on any other open problem.  It certifies, for one explicitly given
recursion and one explicitly given type table, a bound that holds on EVERY finite rooted tree
(or every tree of bounded child count); downstream consumers state their own scope.

THE SETTING
-----------
Finite rooted trees.  A node with `k >= 1` children `c_1..c_k` carries a MESSAGE `y` and a
VALUE `l`:

    R = y(c_1) + ... + y(c_k),      y = h(k, R),      l = l(c_1) + ... + l(c_k) + g(k, R),

and a leaf carries the fixed pair `(y_leaf, l_leaf)`.  `h` and `g` are rational functions of
`(k, R)` with rational coefficients (written in the symbols `m` and `R`).

THE TYPE TABLE
--------------
A finite list of types.  Each type has a predicate on (child count `k`, message sum `R`): a
DEGREE RANGE `klo <= k <= khi` (`khi` may be open) and a BIN `rlo <= R < rhi` (either end may
be open).  The degree ranges form consecutive GROUPS covering every `k >= 0`; inside a group
the bins partition the real line.  So the type of a tree is a function `tp(k, R)` (a leaf has
`tp(0, 0)`).  Each type carries a bound `B` and a message interval `[ylo, yhi]`; an EXACT ATOM
type carries `(E, Y)` and is the table entry `B = E`, `ylo = yhi = Y` (its message is pinned:
every step landing in it must produce exactly `Y`, which the closure obligations check).

The CLAIM, the inductive invariant:

    for every finite rooted tree b:   l(b) <= B[type b]   and   ylo[type b] <= y(b) <= yhi[type b].

THE CERTIFICATE (three devices for the infinitely many parent steps)
-------------------------------------------------------------------
Every step obligation says: if each child `i` satisfies the invariant for its type `t_i`, then
the parent satisfies it for its type `tp(k, R)`.  Writing `n_t` for the number of children of
type `t`, the children give `sum l <= S := sum_t n_t B_t` and `R` in `[sum n_t ylo_t,
sum n_t yhi_t]`.

(i)   ENUMERATION, `1 <= k <= M_enum`: for every MULTISET of child types (count vector `n`
      with `sum n = k`) and every parent bin meeting the reachable `R`-interval, three
      one-variable rational inequalities on the cell `[s, t]`:
          S + g(k, R) <= B_parent,    ylo_parent <= h(k, R),    h(k, R) <= yhi_parent.
      A point cell (`s = t`, e.g. when every message is exact) is checked by `norm_num`;
      an interval cell is cleared to `N(R) >= 0` with a certified-positive denominator and
      certified by exact Bernstein coefficients (the `PolyCert` machinery of
      `concave_pooled_induction`), bisected as needed.  In Lean one generic lemma
      (`step_of_counts`) turns a step stated for COUNT VECTORS into the step for every
      assignment of child types, and the count vectors are enumerated by nested
      `interval_cases`.
(ii)  TANGENT BAND, `M_enum < k <= M_tail`: a linear majorant `g(k, R) <= a_k + s_k R` on
      `R in [k ymin, k ymax]` (Bernstein cells; by default the tangent at the midpoint, exact
      when `g` is affine in `R`) makes the multiset sum SEPARABLE:
          sum l + g <= sum_i (B_{t_i} + s_k y_i) + a_k <= k mu_k + a_k,
          mu_k = max_t (B_t + s_k y*_t)    (y* = yhi if s_k >= 0 else ylo),
      so the value obligation is ONE linear inequality per degree and parent bin,
      `k mu_k + a_k <= B_parent`, plus the closure cells of `h(k, .)` per parent bin.
(iii) ANALYTIC TAIL, every `k > M_tail` at once: a uniform majorant
      `g(k, R) <= a_T + s_T R` for all real `k >= K0 = M_tail + 1` and `R >= K0 ymin`
      (needs `ymin >= 0`), certified as a TWO-variable polynomial inequality in
      `u = k - K0 >= 0` and `R`: every `u^j` coefficient carries its own Bernstein (bounded
      cell) or Taylor (unbounded cell) certificate.  With `mu_T <= 0`, `k mu_T <= K0 mu_T`,
      so ONE inequality uniform in `k` per tail bin, `K0 mu_T + a_T <= B_parent`, plus the
      two-variable closure cells of `h` per tail bin, cover all `k > M_tail`.
      Without a tail (`max_children = D`) the claim is for trees whose nodes all have at most
      `D` children (`PTree.AllDeg (fun k => k <= D)`); nothing is claimed beyond `D`.

Optional JOIN (closing a tree at a root): for a fixed root child count `K`, a rational
`gJ(R)` and a constant `C`, every multiset of `K` child types satisfies
`S + gJ(R) <= C` on its `R`-interval (cells as in (i)); the Lean corollary is
`sum_i l(b_i) + gJ(sum_i y(b_i)) <= C` for every `K`-tuple of trees.

THE LEAN (self-contained; only `import Mathlib`)
------------------------------------------------
Generic, emitted once per file (namespace `TypedCavity`): `PTree` (`leaf` | `node m (cs : Fin
(m+1) -> PTree)`), `size`, `msg`, `ell`, `typ` (the type of a tree), `AllDeg`, `Inv` (the
invariant of one tree), `typed_induction_core` (structural induction consuming one step
hypothesis), `sum_by_type` / `count_sum` / `step_of_counts` (assignments -> counts),
`separable_bound` (the tangent device), `msg_sum_range`, `join_of_counts`.  Per instance:
`h`, `g`, the table, `tp` and one lemma per (group, bin), the base, one lemma per cell
obligation, per (k, multiset), per k (count dispatch), the band and tail steps, `hstep`, the
main theorem `<nm>` and the uniform corollary `l(b) <= max_t B_t`, and the join.

v1 SCOPE (stated plainly)
-------------------------
* rational recursions only: no parameter boxes, no interval arithmetic, no logarithms (the
  design doc records parameter boxes with Taylor enclosures as v2);
* at most 8 types (the count dispatch uses `Fin.sum_univ_<n>`), `M_enum <= 6`;
* the tail domain is `R >= K0 ymin` (the coupling `R <= k ymax` is not used), so it needs
  `ymin >= 0`;
* an exact atom's VALUE is an upper bound (`l <= E`), its message is pinned.

ANTI-PHANTOM REFUSALS
---------------------
`typed_cavity_certificate` raises `TypedCavityRefusal` on: a float anywhere; a non-rational
`h`/`g`/`gJ`; degree groups that overlap, leave a gap or do not end open; bins in a group that
do not partition the line; `ylo > yhi`; more than 8 types; a failing base; any enumeration,
band, tail, closure or join obligation that is FALSE at a probed point (reported with the exact
point) or whose certificate stays negative to the subdivision limit; a denominator not
certified positive; a tail with `ymin < 0` or `mu_T > 0` or a tail group that does not cover
`k >= K0`; a polynomial of degree above 12.  ``check=False`` is for hand-forged negative
controls ONLY: it computes the same certificate algebra (one cell per obligation) with every
sign check skipped, so the kernel is the arbiter.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .emit_concave_pooled_induction import (
        M_SYM,
        R_SYM,
        PolyCert,
        _facts,
        _poly1,
        _poly_lean,
        _poly_tuple,
        _polycert,
        _q,
        _ratfun,
    )
    from .family import InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.emit_concave_pooled_induction import (
        M_SYM,
        R_SYM,
        PolyCert,
        _facts,
        _poly1,
        _poly_lean,
        _poly_tuple,
        _polycert,
        _q,
        _ratfun,
    )
    from telperion.family import InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter

conjecture1_proved = False

U_SYM = sp.Symbol("u")

_MAX_TYPES = 8
_MAX_ENUM = 6
_MAX_DEPTH = 10


class TypedCavityRefusal(ValueError):
    """A typed-cavity certificate request the exact layer refuses."""


def _refuse(msg: str):
    raise TypedCavityRefusal(f"REFUSED: {msg}")


def _rat(q, what: str) -> sp.Rational:
    if isinstance(q, float):
        _refuse(f"{what} = {q!r} is a float; pass an exact rational")
    if isinstance(q, Fraction):
        return sp.Rational(q.numerator, q.denominator)
    if isinstance(q, str):
        try:
            q = sp.Rational(q)
        except (TypeError, ValueError):
            _refuse(f"{what} = {q!r} is not an exact rational")
    q = sp.sympify(q)
    if isinstance(q, sp.Float) or not q.is_Rational:
        _refuse(f"{what} = {q} is not an exact rational")
    return sp.Rational(q)


def _ratfun_r(expr, what: str):
    try:
        return _ratfun(expr, what)
    except ValueError as e:
        raise TypedCavityRefusal(str(e)) from e


# ---------------------------------------------------------------------------
# the type table
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TypeSpec:
    name: str
    klo: int
    khi: int | None          # None = open
    rlo: object              # None = -oo
    rhi: object              # None = +oo
    B: object
    ylo: object
    yhi: object
    exact: bool


@dataclass(frozen=True)
class Group:
    """A degree group `klo <= k <= khi` and its bins: cut points `r_1 < ... < r_J` and the
    type index of each of the `J + 1` bins `(-oo, r_1), [r_1, r_2), ..., [r_J, oo)`."""

    klo: int
    khi: int | None
    cuts: tuple
    types: tuple

    def bin_bounds(self, j: int):
        lo = None if j == 0 else self.cuts[j - 1]
        hi = None if j == len(self.cuts) else self.cuts[j]
        return lo, hi


def _parse_types(types) -> tuple[tuple, tuple]:
    if not types:
        _refuse("no types")
    if len(types) > _MAX_TYPES:
        _refuse(f"{len(types)} types > {_MAX_TYPES} (the Lean count dispatch)")
    out = []
    names = set()
    for i, t in enumerate(types):
        nm = str(t.get("name", f"t{i}"))
        if nm in names:
            _refuse(f"duplicate type name {nm!r}")
        names.add(nm)
        deg = t.get("deg")
        if deg is None or len(deg) != 2:
            _refuse(f"type {nm}: give deg = (klo, khi or None)")
        klo, khi = deg
        if not isinstance(klo, int) or klo < 0 or (khi is not None and (not isinstance(khi, int)
                                                                        or khi < klo)):
            _refuse(f"type {nm}: bad degree range {deg}")
        rb = t.get("bin", (None, None))
        rlo = None if rb[0] is None else _rat(rb[0], f"type {nm} bin lo")
        rhi = None if rb[1] is None else _rat(rb[1], f"type {nm} bin hi")
        if rlo is not None and rhi is not None and not rlo < rhi:
            _refuse(f"type {nm}: empty bin [{rlo}, {rhi})")
        if "exact" in t:
            if "B" in t or "y" in t:
                _refuse(f"type {nm}: give either exact=(E, Y) or B and y, not both")
            E, Y = t["exact"]
            E, Y = _rat(E, f"type {nm} exact E"), _rat(Y, f"type {nm} exact Y")
            out.append(TypeSpec(nm, klo, khi, rlo, rhi, E, Y, Y, True))
        else:
            if "B" not in t or "y" not in t:
                _refuse(f"type {nm}: needs B and y = (ylo, yhi) (or exact)")
            B = _rat(t["B"], f"type {nm} B")
            ylo, yhi = _rat(t["y"][0], f"type {nm} ylo"), _rat(t["y"][1], f"type {nm} yhi")
            if ylo > yhi:
                _refuse(f"type {nm}: ylo = {ylo} > yhi = {yhi}")
            out.append(TypeSpec(nm, klo, khi, rlo, rhi, B, ylo, yhi, False))
    # groups
    ranges = sorted({(t.klo, t.khi) for t in out}, key=lambda r: r[0])
    expect = 0
    groups = []
    for gi, (klo, khi) in enumerate(ranges):
        if klo != expect:
            _refuse(f"degree groups do not cover k = {expect} exactly (next group starts at "
                    f"{klo}); groups must be consecutive from k = 0 and must not overlap")
        if khi is None and gi != len(ranges) - 1:
            _refuse("only the last degree group may be open")
        members = sorted((i for i, t in enumerate(out) if (t.klo, t.khi) == (klo, khi)),
                         key=lambda i: (out[i].rlo is not None,
                                        out[i].rlo if out[i].rlo is not None else 0))
        if out[members[0]].rlo is not None or out[members[-1]].rhi is not None:
            _refuse(f"bins of degree group [{klo}, {khi}] do not cover the whole line")
        cuts = []
        for a, b in zip(members, members[1:]):
            if out[a].rhi is None or out[a].rhi != out[b].rlo:
                _refuse(f"bins of degree group [{klo}, {khi}] are not contiguous at "
                        f"{out[a].name} / {out[b].name}")
            cuts.append(out[a].rhi)
        groups.append(Group(klo, khi, tuple(cuts), tuple(members)))
        expect = None if khi is None else khi + 1
    if expect is not None:
        _refuse("the last degree group must be open (khi = None) so the type map is total")
    return tuple(out), tuple(groups)


def _group_of(groups, k: int) -> int:
    for gi, g in enumerate(groups):
        if g.klo <= k and (g.khi is None or k <= g.khi):
            return gi
    raise AssertionError("groups cover every k")  # pragma: no cover


def _type_of(groups, k: int, R) -> int:
    g = groups[_group_of(groups, k)]
    j = sum(1 for c in g.cuts if R >= c)
    return g.types[j]


# ---------------------------------------------------------------------------
# two-variable certificate (the tail): N(K0 + u, R) = sum_j u^j N_j(R)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PolyCert2:
    """`0 <= P(k, R)` (or `0 < P` when ``strict``) for real `k >= K0` and `R` in `[s, t]`
    (`t is None`: `[s, oo)`).  With `u = k - K0`, `P = sum_j u^j P_j(R)` and every `P_j` carries
    a one-variable certificate (`PolyCert`); strict needs `P_0` strict, the rest nonneg."""

    poly: tuple            # ((deg_R, deg_m), coeff) terms of P in (R, m)
    K0: int
    s: object
    t: object
    parts: tuple           # PolyCert per power of u (index = power)
    strict: bool

    def ok(self) -> bool:
        if not self.parts:
            return not self.strict
        if self.strict and not self.parts[0].ok():
            return False
        return all(p.ok() for p in self.parts)

    def identity_holds(self) -> bool:
        P = sum(c * R_SYM ** dr * M_SYM ** dm for (dr, dm), c in self.poly)
        rhs = 0
        for j, pc in enumerate(self.parts):
            if pc.t is None:
                pj = sum(c * (R_SYM - pc.s) ** i for i, c in enumerate(pc.coeffs))
            else:
                pj = sum(c * (R_SYM - pc.s) ** i * (pc.t - R_SYM) ** (pc.degree - i)
                         for i, c in enumerate(pc.coeffs))
            rhs += (M_SYM - self.K0) ** j * pj
        return sp.expand(P - rhs) == 0 and all(pc.identity_holds() for pc in self.parts)


def _polycert2(P: sp.Poly, K0: int, s, t, strict: bool) -> PolyCert2:
    """``P`` a polynomial in (R, m)."""
    Q = sp.Poly(sp.expand(P.as_expr().subs(M_SYM, K0 + U_SYM)), U_SYM, R_SYM, domain="QQ")
    du = Q.degree(U_SYM) if not Q.is_zero else 0
    parts = []
    for j in range(max(du, 0) + 1):
        cj = sp.Poly(sum(c * R_SYM ** dr for (dj, dr), c in Q.terms() if dj == j),
                     R_SYM, domain="QQ")
        parts.append(_polycert(cj, s, t, strict and j == 0))
    terms = tuple(sorted(((dr, dm), sp.Rational(c)) for (dr, dm), c in
                         sp.Poly(P.as_expr(), R_SYM, M_SYM, domain="QQ").terms()))
    return PolyCert2(poly=terms, K0=K0, s=s, t=t, parts=tuple(parts), strict=strict)


def _facts2(pc: PolyCert2) -> str:
    out = []
    for j, p in enumerate(pc.parts):
        d = p.degree
        for i in range(d + 1):
            if p.t is None:
                inner = f"(pow_nonneg hs {i})"
            else:
                inner = f"(mul_nonneg (pow_nonneg hs {i}) (pow_nonneg ht {d - i}))"
            out.append(f"mul_nonneg (pow_nonneg hu {j}) {inner}")
    return ", ".join(out)


# ---------------------------------------------------------------------------
# obligations and cells
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Cell:
    """One cell `[s, t]` of an obligation `F >= 0`.  A point cell (``point``) stores the exact
    value `F(s)`; an interval cell stores the numerator certificate ``num`` of `F * dtot`, the
    strict certificates ``dens`` of each distinct denominator factor and ``dtot`` of their
    product (None when the obligation is polynomial)."""

    s: object
    t: object
    point: bool
    value: object
    num: object            # PolyCert | PolyCert2 | None
    dens: tuple            # (poly-of-(R,m) Poly, cert) pairs
    dtot: object           # (Poly, cert) | None

    def certs(self):
        out = [] if self.num is None else [self.num]
        out += [c for _, c in self.dens]
        if self.dtot is not None:
            out.append(self.dtot[1])
        return out

    def ok(self) -> bool:
        if self.point:
            return self.value >= 0
        return all(c.ok() for c in self.certs())


@dataclass(frozen=True)
class Ob:
    """One inequality on `[s, t]` (``k`` fixed, or ``k is None``: every `k >= K0`), covered by
    ``cells``.  ``kind``: "val" (`S + g <= B`), "lo" (`ylo <= h`), "hi" (`h <= yhi`), "tan"
    (`g <= a + s R`), "join" (`S + gJ <= C`); ``params`` holds the constants."""

    kind: str
    k: object
    s: object
    t: object
    params: tuple
    cells: tuple

    def ok(self) -> bool:
        return all(c.ok() for c in self.cells)


@dataclass(frozen=True)
class EnumStep:
    k: int
    counts: tuple
    lo: object
    hi: object
    S: object
    bins: tuple            # (j, type index, val Ob, lo Ob, hi Ob) for bins meeting [lo, hi]


@dataclass(frozen=True)
class BandStep:
    k: int
    a: object
    s: object
    mu: object
    tan: Ob
    bins: tuple            # (j, type index, lo Ob, hi Ob)


@dataclass(frozen=True)
class TailStep:
    K0: int
    a: object
    s: object
    mu: object
    tan: Ob
    bins: tuple            # (j, type index, lo Ob, hi Ob)


@dataclass(frozen=True)
class JoinStep:
    counts: tuple
    lo: object
    hi: object
    S: object
    ob: Ob


@dataclass(frozen=True)
class Join:
    K: int
    gJ_num: object
    gJ_den: object
    C: object
    steps: tuple


@dataclass(frozen=True)
class TypedCavityCert:
    """A verified typed-cavity-induction certificate (all fields exact)."""

    h_num: object
    h_den: object
    g_num: object
    g_den: object
    y_leaf: object
    l_leaf: object
    types: tuple
    groups: tuple
    M_enum: int
    M_tail: int
    bounded: bool          # True: trees of child count <= M_tail only, no tail
    base_type: int
    enum: tuple
    band: tuple
    tail: object           # TailStep | None
    join: object           # Join | None
    spec: tuple            # the normalised request, for re-verification
    checked: bool = True

    @property
    def n(self) -> int:
        return len(self.types)

    @property
    def ymin(self):
        return min(t.ylo for t in self.types)

    @property
    def ymax(self):
        return max(t.yhi for t in self.types)

    @property
    def Bmax(self):
        return max(t.B for t in self.types)

    def obligations(self):
        for e in self.enum:
            for _j, _t, *obs in e.bins:
                yield from obs
        for b in self.band:
            yield b.tan
            for _j, _t, *obs in b.bins:
                yield from obs
        if self.tail is not None:
            yield self.tail.tan
            for _j, _t, *obs in self.tail.bins:
                yield from obs
        if self.join is not None:
            for js in self.join.steps:
                yield js.ob


def _fn_parts(ctx, kind):
    if kind in ("val", "tan"):
        return ctx["g_num"], ctx["g_den"]
    if kind in ("lo", "hi"):
        return ctx["h_num"], ctx["h_den"]
    return ctx["gJ_num"], ctx["gJ_den"]


def _F_expr(ctx, kind, params):
    """`rhs - lhs` as a sympy expression in (m, R)."""
    num, den = _fn_parts(ctx, kind)
    f = num.as_expr() / den.as_expr()
    if kind == "val":
        S, B = params
        return B - S - f
    if kind == "lo":
        return f - params[0]
    if kind == "hi":
        return params[0] - f
    if kind == "tan":
        a, s = params
        return a + s * R_SYM - f
    S, C = params
    return C - S - f


def _spec_poly(P: sp.Poly, k) -> sp.Poly:
    e = P.as_expr()
    if k is not None:
        e = e.subs(M_SYM, k)
        return sp.Poly(sp.expand(e), R_SYM, domain="QQ")
    return sp.Poly(sp.expand(e), R_SYM, M_SYM, domain="QQ")


def _build_cell(ctx, kind, k, params, s, t, K0=None) -> Cell:
    """Exact certificate algebra of one cell (no sign decisions)."""
    num, den = _fn_parts(ctx, kind)
    if k is not None:
        dk = _spec_poly(den, k)
        if s == t:
            dval = dk.as_expr().subs(R_SYM, s)
            if dval == 0:
                return Cell(s, t, True, sp.Integer(-1), None, (), None)  # undefined: refuse
            F = _F_expr(ctx, kind, params).subs(M_SYM, k).subs(R_SYM, s)
            return Cell(s, t, True, sp.Rational(sp.nsimplify(F)), None, (), None)
        dens = []
        if dk.degree() > 0:
            dens.append((dk, _polycert(dk, s, t, True)))
        dtot = dens[0] if dens else None
        F = _F_expr(ctx, kind, params).subs(M_SYM, k)
        D = dk.as_expr() if dens else 1
        Nexpr = sp.cancel(sp.together(F * D))
        n_, d_ = sp.fraction(Nexpr)
        if d_.free_symbols:  # pragma: no cover - D clears every denominator
            raise AssertionError(f"internal: not polynomial after clearing: {Nexpr}")
        N = sp.Poly(sp.expand(n_ / d_), R_SYM, domain="QQ")
        return Cell(s, t, False, None, _polycert(N, s, t, False), tuple(dens), dtot)
    # two-variable (tail): k >= K0 real
    dk = _spec_poly(den, None)
    dens = []
    if dk.total_degree() > 0:
        dens.append((dk, _polycert2(dk, K0, s, t, True)))
    dtot = dens[0] if dens else None
    F = _F_expr(ctx, kind, params)
    D = dk.as_expr() if dens else 1
    Nexpr = sp.cancel(sp.together(F * D))
    n_, d_ = sp.fraction(Nexpr)
    if d_.free_symbols:  # pragma: no cover
        raise AssertionError(f"internal: not polynomial after clearing: {Nexpr}")
    N = sp.Poly(sp.expand(n_ / d_), R_SYM, M_SYM, domain="QQ")
    return Cell(s, t, False, None, _polycert2(N, K0, s, t, False), tuple(dens), dtot)


def _probe(ctx, kind, k, params, s, t, K0=None):
    """Search a few exact points for a GENUINE violation (to report, never to accept)."""
    F = _F_expr(ctx, kind, params)
    if t is None:
        pts = [s, s + 1, s + 10, s + 1000]
    elif s == t:
        pts = [s]
    else:
        pts = [s, t, (s + t) / 2, s + (t - s) / 4, s + 3 * (t - s) / 4]
    ks = [k] if k is not None else [K0, K0 + 1, K0 + 10, K0 + 1000]
    for kk in ks:
        for R in pts:
            try:
                v = F.subs(M_SYM, kk).subs(R_SYM, R)
            except ZeroDivisionError:  # pragma: no cover
                continue
            v = sp.nsimplify(v)
            if v.has(sp.zoo, sp.nan) or not v.is_Rational:
                return f"undefined at k = {kk}, R = {R}"
            if v < 0:
                return f"FALSE at k = {kk}, R = {R} (rhs - lhs = {v})"
    return None


def _describe(kind, k, params):
    kk = "every k >= K0" if k is None else f"k = {k}"
    if kind == "val":
        return f"value step {params[0]} + g({kk}, R) <= {params[1]}"
    if kind == "lo":
        return f"closure {params[0]} <= h({kk}, R)"
    if kind == "hi":
        return f"closure h({kk}, R) <= {params[0]}"
    if kind == "tan":
        return f"tangent g({kk}, R) <= {params[0]} + {params[1]} R"
    return f"join {params[0]} + gJ(R) <= {params[1]}"


def _cover(ctx, kind, k, params, s, t, depth, K0):
    cell = _build_cell(ctx, kind, k, params, s, t, K0)
    if cell.ok():
        return [cell]
    if cell.point or t is None or depth >= _MAX_DEPTH:
        return None
    mid = (s + t) / 2
    left = _cover(ctx, kind, k, params, s, mid, depth + 1, K0)
    if left is None:
        return None
    right = _cover(ctx, kind, k, params, mid, t, depth + 1, K0)
    if right is None:
        return None
    return left + right


def _make_ob(ctx, kind, k, params, s, t, *, check: bool, K0=None) -> Ob:
    params = tuple(sp.Rational(p) for p in params)
    if not check:
        cells = [_build_cell(ctx, kind, k, params, s, t, K0)]
        return Ob(kind, k, s, t, params, tuple(cells))
    if t is None:
        whole = _cover(ctx, kind, k, params, s, None, 0, K0)
        if whole is not None:
            return Ob(kind, k, s, t, params, tuple(whole))
        for e in range(-2, 12):
            Bk = s + sp.Rational(2) ** e
            last = _cover(ctx, kind, k, params, Bk, None, 0, K0)
            if last is None:
                continue
            first = _cover(ctx, kind, k, params, s, Bk, 0, K0)
            if first is not None:
                return Ob(kind, k, s, t, params, tuple(first + last))
        cells = None
    else:
        cells = _cover(ctx, kind, k, params, s, t, 0, K0)
    if cells is None:
        why = _probe(ctx, kind, k, params, s, t, K0)
        _refuse(f"no certificate for the {_describe(kind, k, params)} on R in "
                f"[{s}, {'oo' if t is None else t}]" + (f"; {why}" if why else
                                                       f" down to depth {_MAX_DEPTH}"))
    return Ob(kind, k, s, t, params, tuple(cells))


# ---------------------------------------------------------------------------
# the certificate
# ---------------------------------------------------------------------------

def _count_vectors(n: int, k: int):
    """Count vectors (n_0, ..., n_{n-1}) with sum k, in the order of the Lean dispatch
    (lexicographic, first coordinate slowest)."""
    out = []

    def rec(prefix, left, i):
        if i == n - 1:
            out.append(tuple(prefix + [left]))
            return
        for v in range(left + 1):
            rec(prefix + [v], left - v, i + 1)
    rec([], k, 0)
    return out


def _tangent(ctx, k, lo, hi):
    """Default linear majorant of g(k, .) on [lo, hi]: exact if affine in R, else the tangent at
    the midpoint (valid where g(k, .) is concave)."""
    gk = (ctx["g_num"].as_expr() / ctx["g_den"].as_expr()).subs(M_SYM, k)
    gk = sp.cancel(gk)
    num, den = sp.fraction(gk)
    if not den.free_symbols and sp.Poly(num, R_SYM).degree() <= 1:
        P = sp.Poly(sp.expand(gk), R_SYM)
        return sp.Rational(P.coeff_monomial(1)), sp.Rational(P.coeff_monomial(R_SYM))
    S0 = (lo + hi) / 2
    s = sp.Rational(sp.diff(gk, R_SYM).subs(R_SYM, S0))
    a = sp.Rational(gk.subs(R_SYM, S0)) - s * S0
    return a, s


def _mu(types, s):
    return max(t.B + s * (t.yhi if s >= 0 else t.ylo) for t in types)


def _bins_meeting(group: Group, lo, hi):
    """Bins of ``group`` meeting [lo, hi] (hi None = oo), with the closed cell of the
    intersection."""
    out = []
    for j, ti in enumerate(group.types):
        blo, bhi = group.bin_bounds(j)
        if bhi is not None and bhi <= lo:
            continue
        if blo is not None and hi is not None and blo > hi:
            continue
        s = lo if blo is None else max(lo, blo)
        if bhi is None:
            t = hi
        else:
            t = bhi if hi is None else min(hi, bhi)
        out.append((j, ti, s, t))
    return out


def typed_cavity_certificate(*, h, g, y_leaf, l_leaf, types, M_enum, M_tail=None,
                             max_children=None, band_tangents=None, tail_tangent=None,
                             join=None, check: bool = True) -> TypedCavityCert:
    """Build (untrusted cell search) and EXACTLY verify a typed-cavity-induction certificate.

    ``h``/``g``: rational functions of the symbols ``m`` (child count) and ``R`` (message sum).
    ``types``: list of dicts ``name``, ``deg = (klo, khi | None)``, ``bin = (rlo | None,
    rhi | None)`` and either ``B`` with ``y = (ylo, yhi)`` or ``exact = (E, Y)``.
    ``M_enum``: child counts ``1..M_enum`` are enumerated over all multisets of child types.
    ``M_tail``: child counts ``M_enum+1..M_tail`` use the tangent band; ``k > M_tail`` the
    analytic tail.  ``max_children = D`` instead claims only trees of child count ``<= D``
    (band up to ``D``, no tail).  ``band_tangents``: optional ``{k: (a, s)}``;
    ``tail_tangent``: optional ``(a, s)``.  ``join``: optional ``dict(K=..., g=..., C=...)``
    (``g`` in ``m`` and ``R``, evaluated at ``m = K``).

    ``check=False`` is for hand-forged negative controls ONLY (``checked=False``)."""
    hn, hd = _ratfun_r(h, "h")
    gn, gd = _ratfun_r(g, "g")
    y0 = _rat(y_leaf, "y_leaf")
    l0 = _rat(l_leaf, "l_leaf")
    tys, groups = _parse_types(types)
    if not isinstance(M_enum, int) or M_enum < 0 or M_enum > _MAX_ENUM:
        _refuse(f"M_enum = {M_enum!r} must be an integer in 0..{_MAX_ENUM}")
    bounded = max_children is not None
    if bounded:
        if not isinstance(max_children, int) or max_children < 1:
            _refuse(f"max_children = {max_children!r} must be an integer >= 1")
        if M_tail is not None and M_tail != max_children:
            _refuse("with max_children = D the band runs to D: leave M_tail unset (or = D)")
        M_tail = max_children
        if M_enum > max_children:
            _refuse(f"M_enum = {M_enum} > max_children = {max_children}")
    else:
        if M_tail is None or not isinstance(M_tail, int) or M_tail < max(M_enum, 1):
            _refuse(f"M_tail = {M_tail!r} must be an integer >= max(M_enum, 1)")
    ctx = dict(h_num=hn, h_den=hd, g_num=gn, g_den=gd)
    # base
    bt = _type_of(groups, 0, 0)
    if check:
        T = tys[bt]
        if not (l0 <= T.B and T.ylo <= y0 <= T.yhi):
            _refuse(f"base fails: leaf (l, y) = ({l0}, {y0}) not in type {T.name} "
                    f"(B = {T.B}, y in [{T.ylo}, {T.yhi}])")
    n = len(tys)
    if not bounded:  # tail preconditions, before any cell work
        if groups[-1].klo > M_tail + 1:
            _refuse(f"the tail k >= {M_tail + 1} must lie in ONE degree group (the last starts "
                    f"at {groups[-1].klo})")
        if min(t.ylo for t in tys) < 0:
            _refuse(f"the tail needs every ylo >= 0 (ymin = {min(t.ylo for t in tys)})")
    # (i) enumeration
    enum = []
    for k in range(1, M_enum + 1):
        grp = groups[_group_of(groups, k)]
        for cv in _count_vectors(n, k):
            lo = sum(c * t.ylo for c, t in zip(cv, tys))
            hi = sum(c * t.yhi for c, t in zip(cv, tys))
            S = sum(c * t.B for c, t in zip(cv, tys))
            bins = []
            for j, ti, s, t in _bins_meeting(grp, lo, hi):
                T = tys[ti]
                bins.append((j, ti,
                             _make_ob(ctx, "val", k, (S, T.B), s, t, check=check),
                             _make_ob(ctx, "lo", k, (T.ylo,), s, t, check=check),
                             _make_ob(ctx, "hi", k, (T.yhi,), s, t, check=check)))
            enum.append(EnumStep(k, cv, lo, hi, S, tuple(bins)))
    ymin, ymax = min(t.ylo for t in tys), max(t.yhi for t in tys)
    # (ii) band
    band = []
    bt_in = dict(band_tangents or {})
    for k in range(M_enum + 1, M_tail + 1):
        lo, hi = k * ymin, k * ymax
        if k in bt_in:
            a, s = _rat(bt_in[k][0], f"band a_{k}"), _rat(bt_in[k][1], f"band s_{k}")
        else:
            a, s = _tangent(ctx, k, lo, hi)
        mu = _mu(tys, s)
        if lo == hi:
            _refuse(f"band degree {k}: degenerate message range (enumerate it instead)")
        tan = _make_ob(ctx, "tan", k, (a, s), lo, hi, check=check)
        grp = groups[_group_of(groups, k)]
        bins = []
        for j, ti, s_, t_ in _bins_meeting(grp, lo, hi):
            T = tys[ti]
            if check and not k * mu + a <= T.B:
                _refuse(f"band degree {k}, parent type {T.name}: k mu + a = {k * mu + a} > "
                        f"B = {T.B} (mu = {mu}, tangent a = {a}, s = {s})")
            bins.append((j, ti, _make_ob(ctx, "lo", k, (T.ylo,), s_, t_, check=check),
                         _make_ob(ctx, "hi", k, (T.yhi,), s_, t_, check=check)))
        band.append(BandStep(k, a, s, mu, tan, tuple(bins)))
    for k in bt_in:
        if not (M_enum < k <= M_tail):
            _refuse(f"band tangent given for k = {k} outside the band {M_enum + 1}..{M_tail}")
    # (iii) tail
    tail = None
    if not bounded:
        K0 = M_tail + 1
        last = groups[-1]
        if last.klo > K0:
            _refuse(f"the tail k >= {K0} must lie in ONE degree group (the last starts at "
                    f"{last.klo})")
        if ymin < 0:
            _refuse(f"the tail needs every ylo >= 0 (ymin = {ymin})")
        if tail_tangent is not None:
            a, s = _rat(tail_tangent[0], "tail a"), _rat(tail_tangent[1], "tail s")
        else:
            a, s = _tangent(ctx, K0, K0 * ymin, K0 * ymax)
        mu = _mu(tys, s)
        if check and mu > 0:
            _refuse(f"the tail needs mu_T = max_t (B_t + s_T y*_t) <= 0 (mu_T = {mu}, "
                    f"s_T = {s})")
        R0 = K0 * ymin
        tan = _make_ob(ctx, "tan", None, (a, s), R0, None, check=check, K0=K0)
        bins = []
        for j, ti, s_, t_ in _bins_meeting(last, R0, None):
            T = tys[ti]
            if check and not K0 * mu + a <= T.B:
                _refuse(f"tail parent type {T.name}: K0 mu_T + a_T = {K0 * mu + a} > "
                        f"B = {T.B}")
            bins.append((j, ti, _make_ob(ctx, "lo", None, (T.ylo,), s_, t_, check=check, K0=K0),
                         _make_ob(ctx, "hi", None, (T.yhi,), s_, t_, check=check, K0=K0)))
        tail = TailStep(K0, a, s, mu, tan, tuple(bins))
    elif tail_tangent is not None:
        _refuse("tail_tangent given in bounded mode (max_children set)")
    # join
    jn = None
    if join is not None:
        K = join.get("K")
        if not isinstance(K, int) or K < 1 or K > _MAX_ENUM + 2:
            _refuse(f"join K = {K!r} must be an integer in 1..{_MAX_ENUM + 2}")
        if bounded and K > max_children + 1:
            _refuse(f"join K = {K} exceeds max_children + 1 = {max_children + 1}")
        jg = sp.sympify(join["g"], locals={"m": M_SYM, "R": R_SYM}) if isinstance(
            join["g"], str) else sp.sympify(join["g"])
        jn_, jd_ = _ratfun_r(jg.subs(M_SYM, K), "join g")
        C = _rat(join["C"], "join C")
        jctx = dict(ctx, gJ_num=jn_, gJ_den=jd_)
        steps = []
        for cv in _count_vectors(n, K):
            lo = sum(c * t.ylo for c, t in zip(cv, tys))
            hi = sum(c * t.yhi for c, t in zip(cv, tys))
            S = sum(c * t.B for c, t in zip(cv, tys))
            steps.append(JoinStep(cv, lo, hi, S,
                                  _make_ob(jctx, "join", K, (S, C), lo, hi, check=check)))
        jn = Join(K, jn_, jd_, C, tuple(steps))
    spec = (("h", h if isinstance(h, str) else sp.sstr(h)),
            ("g", g if isinstance(g, str) else sp.sstr(g)),
            ("y_leaf", y0), ("l_leaf", l0),
            ("types", tuple((t.name, t.klo, t.khi, t.rlo, t.rhi, t.B, t.ylo, t.yhi, t.exact)
                            for t in tys)),
            ("M_enum", M_enum), ("M_tail", None if bounded else M_tail),
            ("max_children", max_children),
            ("band_tangents", tuple(sorted((k, _rat(v[0], "a"), _rat(v[1], "s"))
                                           for k, v in bt_in.items()))),
            ("tail_tangent", None if tail_tangent is None else
             (_rat(tail_tangent[0], "a"), _rat(tail_tangent[1], "s"))),
            ("join", None if join is None else
             (join["K"], join["g"] if isinstance(join["g"], str) else sp.sstr(join["g"]),
              _rat(join["C"], "C"))))
    cert = TypedCavityCert(h_num=hn, h_den=hd, g_num=gn, g_den=gd, y_leaf=y0, l_leaf=l0,
                           types=tys, groups=groups, M_enum=M_enum, M_tail=M_tail,
                           bounded=bounded, base_type=bt, enum=tuple(enum), band=tuple(band),
                           tail=tail, join=jn, spec=spec, checked=check)
    if check:
        verify_certificate(cert)
    return cert


def _spec_kwargs(cert: TypedCavityCert) -> dict:
    sp_ = dict(cert.spec)
    types = []
    for (nm, klo, khi, rlo, rhi, B, ylo, yhi, exact) in sp_["types"]:
        d = dict(name=nm, deg=(klo, khi), bin=(rlo, rhi))
        if exact:
            d["exact"] = (B, ylo)
        else:
            d["B"], d["y"] = B, (ylo, yhi)
        types.append(d)
    kw = dict(h=sp_["h"], g=sp_["g"], y_leaf=sp_["y_leaf"], l_leaf=sp_["l_leaf"], types=types,
              M_enum=sp_["M_enum"], M_tail=sp_["M_tail"], max_children=sp_["max_children"],
              band_tangents={k: (a, s) for k, a, s in sp_["band_tangents"]} or None,
              tail_tangent=sp_["tail_tangent"])
    if sp_["join"] is not None:
        K, gj, C = sp_["join"]
        kw["join"] = dict(K=K, g=gj, C=C)
    return kw


def verify_certificate(cert: TypedCavityCert) -> None:
    """Re-verify every obligation of ``cert`` exactly (raises ``TypedCavityRefusal``)."""
    for ob in cert.obligations():
        if not ob.cells:
            _refuse(f"obligation {_describe(ob.kind, ob.k, ob.params)} has no cells")
        cur = ob.s
        for c in ob.cells:
            if c.s != cur:
                _refuse(f"cells of the {_describe(ob.kind, ob.k, ob.params)} do not cover "
                        f"[{ob.s}, {ob.t}] (gap/overlap at {cur})")
            if not c.point and c.t is not None and not c.t > c.s:
                _refuse(f"degenerate cell [{c.s}, {c.t}]")
            if not c.ok():
                _refuse(f"negative certificate on cell [{c.s}, {c.t}] of the "
                        f"{_describe(ob.kind, ob.k, ob.params)}")
            for pc in c.certs():
                if not pc.identity_holds():  # pragma: no cover - by construction
                    _refuse("a Bernstein/Taylor identity does not expand back")
            cur = c.t
        if cur != ob.t:
            _refuse(f"cells of the {_describe(ob.kind, ob.k, ob.params)} end at {cur}, the "
                    f"domain at {ob.t}")
    T = cert.types[cert.base_type]
    if not (cert.l_leaf <= T.B and T.ylo <= cert.y_leaf <= T.yhi):
        _refuse("base fails")
    for b in cert.band:
        for _j, ti, *_ in b.bins:
            if not b.k * b.mu + b.a <= cert.types[ti].B:
                _refuse(f"band degree {b.k} value check fails")
        if b.mu != _mu(cert.types, b.s):
            _refuse(f"band degree {b.k}: mu does not match the table")
    if cert.tail is not None:
        tl = cert.tail
        if tl.mu != _mu(cert.types, tl.s) or tl.mu > 0:
            _refuse("tail mu_T wrong or positive")
        for _j, ti, *_ in tl.bins:
            if not tl.K0 * tl.mu + tl.a <= cert.types[ti].B:
                _refuse("tail value check fails")
    # the whole certificate re-derives from its request
    fresh = typed_cavity_certificate(**_spec_kwargs(cert), check=False)
    for a, b in ((fresh.enum, cert.enum), (fresh.band, cert.band)):
        if len(a) != len(b):
            _refuse("certificate does not match its exact recomputation (step count)")
    for fe, ce in zip(fresh.enum, cert.enum):
        if (fe.k, fe.counts, fe.lo, fe.hi, fe.S) != (ce.k, ce.counts, ce.lo, ce.hi, ce.S) or \
                [x[:2] for x in fe.bins] != [x[:2] for x in ce.bins]:
            _refuse(f"enumeration step k = {ce.k}, counts {ce.counts} does not match its "
                    f"exact recomputation")
        for fb, cb in zip(fe.bins, ce.bins):
            for fo, co in zip(fb[2:], cb[2:]):
                if (fo.kind, fo.k, fo.s, fo.t, fo.params) != (co.kind, co.k, co.s, co.t,
                                                               co.params):
                    _refuse(f"obligation {_describe(co.kind, co.k, co.params)} does not match "
                            f"its exact recomputation")
    for fb, cb in zip(fresh.band, cert.band):
        if (fb.k, fb.a, fb.s, fb.mu) != (cb.k, cb.a, cb.s, cb.mu) or \
                [x[:2] for x in fb.bins] != [x[:2] for x in cb.bins]:
            _refuse(f"band degree {cb.k} does not match its exact recomputation")
    for ob in cert.obligations():
        for c in ob.cells:
            ctx = dict(h_num=cert.h_num, h_den=cert.h_den, g_num=cert.g_num, g_den=cert.g_den,
                       gJ_num=cert.join.gJ_num if cert.join else None,
                       gJ_den=cert.join.gJ_den if cert.join else None)
            K0 = cert.tail.K0 if (ob.k is None and cert.tail is not None) else None
            if _build_cell(ctx, ob.kind, ob.k, ob.params, c.s, c.t, K0) != c:
                _refuse(f"cell [{c.s}, {c.t}] of the {_describe(ob.kind, ob.k, ob.params)} "
                        f"does not match its exact recomputation")


def certify_typed_cavity_induction_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``, a dict of the keyword arguments of
    :func:`typed_cavity_certificate`."""
    spec = dict(family.special[1](pt))
    cert = typed_cavity_certificate(**spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1 + sum(len(ob.cells) for ob in cert.obligations())


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

_GENERIC = r"""/-! ## Generic typed cavity induction (emitted once per file)

A finite type table with per-type bounds is an inductive invariant of a branching recursion
over every finite rooted tree.  conjecture1_proved = False. -/

namespace TypedCavity

/-- Finite rooted trees; an internal node has `m + 1 ≥ 1` children. -/
inductive PTree : Type
  | leaf : PTree
  | node (m : ℕ) (cs : Fin (m + 1) → PTree) : PTree

namespace PTree

/-- Number of vertices. -/
def size : PTree → ℕ
  | leaf => 1
  | node _ cs => (∑ i, size (cs i)) + 1

/-- The message: `y0` at a leaf, `h (#children) (sum of the children's messages)`. -/
def msg (h : ℕ → ℝ → ℝ) (y0 : ℝ) : PTree → ℝ
  | leaf => y0
  | node m cs => h (m + 1) (∑ i, msg h y0 (cs i))

/-- The value: `l0` at a leaf, the children's values plus `g (#children) (sum)`. -/
def ell (g h : ℕ → ℝ → ℝ) (l0 y0 : ℝ) : PTree → ℝ
  | leaf => l0
  | node m cs => (∑ i, ell g h l0 y0 (cs i)) + g (m + 1) (∑ i, msg h y0 (cs i))

/-- The type of a tree: `tp 0 0` at a leaf, `tp (#children) (sum of the children's messages)`. -/
def typ {T : Type} (tp : ℕ → ℝ → T) (h : ℕ → ℝ → ℝ) (y0 : ℝ) : PTree → T
  | leaf => tp 0 0
  | node m cs => tp (m + 1) (∑ i, msg h y0 (cs i))

/-- Every internal node's child count satisfies `ok`. -/
def AllDeg (ok : ℕ → Prop) : PTree → Prop
  | leaf => True
  | node m cs => ok (m + 1) ∧ ∀ i, AllDeg ok (cs i)

theorem allDeg_true (b : PTree) : b.AllDeg (fun _ => True) := by
  induction b with
  | leaf => trivial
  | node m cs ih => exact ⟨trivial, ih⟩

end PTree

/-- The invariant of one tree of type `t` with value `l` and message `y`. -/
abbrev Inv {T : Type} (B ylo yhi : T → ℝ) (t : T) (l y : ℝ) : Prop :=
  l ≤ B t ∧ ylo t ≤ y ∧ y ≤ yhi t

/-- THE TYPED INDUCTION.  If the leaf satisfies the invariant of its type and every admissible
parent step preserves it (children of any types satisfying theirs), every tree satisfies the
invariant of its own type. -/
theorem typed_induction_core {T : Type} (ok : ℕ → Prop) (h g : ℕ → ℝ → ℝ) (y0 l0 : ℝ)
    (tp : ℕ → ℝ → T) (B ylo yhi : T → ℝ)
    (hbase : Inv B ylo yhi (tp 0 0) l0 y0)
    (hstep : ∀ k : ℕ, 1 ≤ k → ok k → ∀ (τ : Fin k → T) (y l : Fin k → ℝ),
      (∀ i, Inv B ylo yhi (τ i) (l i) (y i)) →
      Inv B ylo yhi (tp k (∑ i, y i)) ((∑ i, l i) + g k (∑ i, y i)) (h k (∑ i, y i))) :
    ∀ b : PTree, b.AllDeg ok →
      Inv B ylo yhi (b.typ tp h y0) (b.ell g h l0 y0) (b.msg h y0) := by
  intro b
  induction b with
  | leaf => intro _; simpa [PTree.typ, PTree.ell, PTree.msg] using hbase
  | node m cs ih =>
    intro hdeg
    obtain ⟨hok, hcs⟩ := hdeg
    simp only [PTree.typ, PTree.ell, PTree.msg]
    exact hstep (m + 1) (Nat.le_add_left 1 m) hok (fun i => (cs i).typ tp h y0)
      (fun i => (cs i).msg h y0) (fun i => (cs i).ell g h l0 y0) (fun i => ih i (hcs i))

/-- A sum over children is a sum over types weighted by the child counts. -/
theorem sum_by_type {n k : ℕ} (τ : Fin k → Fin n) (F : Fin n → ℝ) :
    ∑ i, F (τ i) = ∑ t, ((Finset.univ.filter (fun i => τ i = t)).card : ℝ) * F t := by
  rw [← Finset.sum_fiberwise Finset.univ τ (fun i => F (τ i))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem count_sum {n k : ℕ} (τ : Fin k → Fin n) :
    ∑ t, (Finset.univ.filter (fun i => τ i = t)).card = k := by
  rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (τ i))]
  simp

/-- ENUMERATION reduces to child-type COUNTS: a step stated for every count vector `c` with
`∑ c = k` gives the step for every assignment of child types. -/
theorem step_of_counts {n k : ℕ} (G H : ℝ → ℝ) (tpk : ℝ → Fin n) (B ylo yhi : Fin n → ℝ)
    (hc : ∀ c : Fin n → ℕ, ∑ t, c t = k → ∀ R : ℝ,
      ∑ t, (c t : ℝ) * ylo t ≤ R → R ≤ ∑ t, (c t : ℝ) * yhi t →
      Inv B ylo yhi (tpk R) ((∑ t, (c t : ℝ) * B t) + G R) (H R))
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    Inv B ylo yhi (tpk (∑ i, y i)) ((∑ i, l i) + G (∑ i, y i)) (H (∑ i, y i)) := by
  set c : Fin n → ℕ := fun t => (Finset.univ.filter (fun i => τ i = t)).card
  have h1 : ∑ t, (c t : ℝ) * ylo t ≤ ∑ i, y i := by
    rw [← sum_by_type τ ylo]; exact Finset.sum_le_sum fun i _ => (hch i).2.1
  have h2 : ∑ i, y i ≤ ∑ t, (c t : ℝ) * yhi t := by
    rw [← sum_by_type τ yhi]; exact Finset.sum_le_sum fun i _ => (hch i).2.2
  have hl : ∑ i, l i ≤ ∑ t, (c t : ℝ) * B t := by
    rw [← sum_by_type τ B]; exact Finset.sum_le_sum fun i _ => (hch i).1
  obtain ⟨a1, a2, a3⟩ := hc c (count_sum τ) _ h1 h2
  exact ⟨by linarith, a2, a3⟩

/-- The JOIN version of `step_of_counts` (a root closing `k` trees; value only). -/
theorem join_of_counts {n k : ℕ} (G : ℝ → ℝ) (C : ℝ) (B ylo yhi : Fin n → ℝ)
    (hc : ∀ c : Fin n → ℕ, ∑ t, c t = k → ∀ R : ℝ,
      ∑ t, (c t : ℝ) * ylo t ≤ R → R ≤ ∑ t, (c t : ℝ) * yhi t →
      (∑ t, (c t : ℝ) * B t) + G R ≤ C)
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    (∑ i, l i) + G (∑ i, y i) ≤ C := by
  set c : Fin n → ℕ := fun t => (Finset.univ.filter (fun i => τ i = t)).card
  have h1 : ∑ t, (c t : ℝ) * ylo t ≤ ∑ i, y i := by
    rw [← sum_by_type τ ylo]; exact Finset.sum_le_sum fun i _ => (hch i).2.1
  have h2 : ∑ i, y i ≤ ∑ t, (c t : ℝ) * yhi t := by
    rw [← sum_by_type τ yhi]; exact Finset.sum_le_sum fun i _ => (hch i).2.2
  have hl : ∑ i, l i ≤ ∑ t, (c t : ℝ) * B t := by
    rw [← sum_by_type τ B]; exact Finset.sum_le_sum fun i _ => (hch i).1
  have := hc c (count_sum τ) _ h1 h2
  linarith

/-- SEPARABLE (tangent) bound: with a per-type cap `B t + s y ≤ μ`, the children's values plus
`s` times their message sum are at most `k μ`. -/
theorem separable_bound {n k : ℕ} (B ylo yhi : Fin n → ℝ) (s μ : ℝ)
    (hμ : ∀ t y, ylo t ≤ y → y ≤ yhi t → B t + s * y ≤ μ)
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    (∑ i, l i) + s * ∑ i, y i ≤ (k : ℝ) * μ := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have : ∑ i, (l i + s * y i) ≤ ∑ _i : Fin k, μ :=
    Finset.sum_le_sum fun i _ => by
      have := hμ (τ i) (y i) (hch i).2.1 (hch i).2.2
      linarith [(hch i).1]
  simpa using this

/-- The children's message sum lies in `[k ymin, k ymax]`. -/
theorem msg_sum_range {n k : ℕ} (B ylo yhi : Fin n → ℝ) (ymin ymax : ℝ)
    (hmin : ∀ t, ymin ≤ ylo t) (hmax : ∀ t, yhi t ≤ ymax)
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    (k : ℝ) * ymin ≤ ∑ i, y i ∧ ∑ i, y i ≤ (k : ℝ) * ymax := by
  constructor
  · have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      le_trans (hmin (τ i)) (hch i).2.1
    simpa using this
  · have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      le_trans (hch i).2.2 (hmax (τ i))
    simpa using this

end TypedCavity

open TypedCavity
"""

_SUM_UNIV = {1: "Fin.sum_univ_one", 2: "Fin.sum_univ_two", 3: "Fin.sum_univ_three",
             4: "Fin.sum_univ_four", 5: "Fin.sum_univ_five", 6: "Fin.sum_univ_six",
             7: "Fin.sum_univ_seven", 8: "Fin.sum_univ_eight"}


def _counts_tag(cv) -> str:
    return "_".join(str(c) for c in cv)


def _strip(s: str) -> str:
    return s.replace("(", "").replace(")", "").replace(" ", "")


@dataclass
class TypedCavityInductionEmitter(Emitter):
    """Emit the generic typed cavity induction once, then per instance the recursion, the type
    table and type map, every certified cell obligation, the enumeration / band / tail steps,
    the main theorem `∀ b, Inv (type b) (ell b) (msg b)`, the uniform corollary
    `ell b ≤ max_t B_t` and the optional join.

    HONEST SCOPE: one explicit rational recursion and one explicit table, on every finite rooted
    tree (or every tree of bounded child count).  Nothing about BG or RH.
    conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "typed_cavity_induction"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts = [_GENERIC]
        for inst in fam.instances:
            parts.append(self._emit_instance(inst.payload, inst.lean_name))
        body = "\n".join(parts)
        nthm = sum(1 for ln in body.split("\n") if ln.startswith("theorem "))
        return body, nthm

    def emit_units(self, fam, profile: LeanProfile):
        return [self.emit_body(fam, profile)]

    # -- helpers ------------------------------------------------------------------------
    @staticmethod
    def _mdep(*ps) -> bool:
        return any(M_SYM in p.as_expr().free_symbols for p in ps)

    def _fn_names(self, c: TypedCavityCert, nm: str, kind: str):
        if kind in ("val", "tan"):
            return f"{nm}_g", c.g_num, c.g_den
        if kind in ("lo", "hi"):
            return f"{nm}_h", c.h_num, c.h_den
        return f"{nm}_gJ", c.join.gJ_num, c.join.gJ_den

    def _stmt(self, c, nm, ob: Ob, kv: str) -> str:
        """The statement of an obligation; ``kv`` is the Lean text of k."""
        if ob.kind == "val":
            S, B = ob.params
            return f"{_q(S)} + {nm}_g {kv} R ≤ {_q(B)}"
        if ob.kind == "lo":
            return f"{_q(ob.params[0])} ≤ {nm}_h {kv} R"
        if ob.kind == "hi":
            return f"{nm}_h {kv} R ≤ {_q(ob.params[0])}"
        if ob.kind == "tan":
            a, s = ob.params
            return f"{nm}_g {kv} R ≤ {_q(a)} + {_q(s)} * R"
        S, C = ob.params
        return f"{_q(S)} + {nm}_gJ R ≤ {_q(C)}"

    def _closed_stmt(self, ob: Ob, call: str, closed: str) -> tuple[str, str]:
        """(rhs, lhs) texts with the function call replaced by its closed form."""
        if ob.kind == "val":
            S, B = ob.params
            return _q(B), f"{_q(S)} + {closed}"
        if ob.kind == "lo":
            return closed, _q(ob.params[0])
        if ob.kind == "hi":
            return _q(ob.params[0]), closed
        if ob.kind == "tan":
            a, s = ob.params
            return f"{_q(a)} + {_q(s)} * R", closed
        S, C = ob.params
        return _q(C), f"{_q(S)} + {closed}"

    def _cell_lemma(self, c, nm, name, ob: Ob, cell: Cell) -> str:
        two = ob.k is None
        kv = "k" if two else str(ob.k)
        fname, fnum, fden = self._fn_names(c, nm, ob.kind)
        call = f"{fname} R" if ob.kind == "join" else f"{fname} {kv} R"
        stmt = self._stmt(c, nm, ob, kv)
        if two:
            args = f"(k : ℕ) (hk : {c.tail.K0} ≤ k) (R : ℝ) (h1 : {_q(cell.s)} ≤ R)"
        else:
            args = f"(R : ℝ) (h1 : {_q(cell.s)} ≤ R)"
        if cell.t is not None:
            args += f" (h2 : R ≤ {_q(cell.t)})"
        L = []
        if cell.point:
            unf = f"{fname}"
            L.append(f"theorem {name} {args} :\n    {stmt} := by")
            L.append(f"  obtain rfl : R = {_q(cell.s)} := le_antisymm h2 h1")
            L.append(f"  norm_num [{unf}]")
            return "\n".join(L) + "\n"
        L.append(f"theorem {name} {args} :\n    {stmt} := by")
        L.append(f"  have hs : 0 ≤ R - {_q(cell.s)} := by linarith")
        if cell.t is not None:
            L.append(f"  have ht : 0 ≤ {_q(cell.t)} - R := by linarith")
        if two:
            K0 = c.tail.K0
            L.append(f"  have hk' : ({K0} : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk")
            L.append(f"  have hu : 0 ≤ (k : ℝ) - {K0} := by linarith")
        # closed forms
        if ob.kind == "join":
            closed = self._closed1(fnum, fden, None)
            eq_tac = f"simp only [{fname}]"
        elif two:
            closed = self._closed2(fnum, fden)
            eq_tac = f"simp only [{fname}]"
        else:
            closed = self._closed1(fnum, fden, ob.k)
            eq_tac = f"simp only [{fname}]" + ("; ring" if self._mdep(fnum, fden) else "")
        closed = f"({closed})"
        facts = (lambda pc: _facts2(pc)) if two else (lambda pc: _facts(pc))
        for di, (dp, dc) in enumerate(cell.dens):
            dtxt = _poly_lean(dp, "(k : ℝ)") if two else _poly1(_poly_tuple(dp))
            L.append(f"  have hD{di} : 0 < {dtxt} := by linarith [{facts(dc)}]")
        L.append(f"  have ef : {call} = {closed} := by {eq_tac}")
        rhs, lhs = self._closed_stmt(ob, call, closed)
        if two:
            Ntxt = _poly_lean(sp.Poly(sum(cf * R_SYM ** dr * M_SYM ** dm
                                          for (dr, dm), cf in cell.num.poly), R_SYM, M_SYM,
                                      domain="QQ"), "(k : ℝ)")
        else:
            Ntxt = _poly1(cell.num.poly)
        L.append(f"  have key : 0 ≤ {Ntxt} := by linarith [{facts(cell.num)}]")
        zero_num = all(x == 0 for x in (cell.num.poly if not two
                                       else [cf for _, cf in cell.num.poly]))
        if cell.dtot is not None:
            dp = cell.dtot[0]
            Dtxt = _poly_lean(dp, "(k : ℝ)") if two else _poly1(_poly_tuple(dp))
            L.append(f"  have e : ({rhs}) - ({lhs}) = {Ntxt} / {Dtxt} := by")
            L.append("    field_simp")
            L.append("    ring")
            L.append("  have hq := div_nonneg key hD0.le")
        else:
            L.append(f"  have e : ({rhs}) - ({lhs}) = {Ntxt} := by ring")
        if zero_num and _strip(rhs) == _strip(lhs):
            L.append("  rw [ef]")
        else:
            L.append("  rw [ef]")
            L.append("  linarith")
        return "\n".join(L) + "\n"

    @staticmethod
    def _closed1(num, den, k) -> str:
        n_ = _spec_poly(num, k) if k is not None else sp.Poly(num.as_expr(), R_SYM, domain="QQ")
        d_ = _spec_poly(den, k) if k is not None else sp.Poly(den.as_expr(), R_SYM, domain="QQ")
        if d_.degree() <= 0:
            cc = sp.Rational(d_.as_expr())
            return _poly1(tuple(sp.Rational(x) / cc for x in _poly_tuple(n_)))
        return f"{_poly1(_poly_tuple(n_))} / {_poly1(_poly_tuple(d_))}"

    @staticmethod
    def _closed2(num, den) -> str:
        nt = _poly_lean(num, "(k : ℝ)")
        if den.total_degree() == 0:
            return nt
        return f"{nt} / {_poly_lean(den, '(k : ℝ)')}"

    def _cover_lemma(self, c, nm, name, ob: Ob) -> list:
        """Cell lemmas plus one lemma for the whole obligation (a le_or_gt chain)."""
        out = []
        two = ob.k is None
        kv = "k" if two else str(ob.k)
        cnames = []
        for i, cell in enumerate(ob.cells):
            cn = f"{name}_c{i}" if len(ob.cells) > 1 else name
            cnames.append(cn)
            out.append(self._cell_lemma(c, nm, cn, ob, cell))
        if len(ob.cells) == 1:
            return out
        stmt = self._stmt(c, nm, ob, kv)
        if two:
            args = f"(k : ℕ) (hk : {c.tail.K0} ≤ k) (R : ℝ) (h1 : {_q(ob.s)} ≤ R)"
            pre = "k hk "
        else:
            args = f"(R : ℝ) (h1 : {_q(ob.s)} ≤ R)"
            pre = ""
        if ob.t is not None:
            args += f" (h2 : R ≤ {_q(ob.t)})"
        L = [f"theorem {name} {args} :\n    {stmt} := by"]
        n = len(ob.cells)
        for i, (cell, cn) in enumerate(zip(ob.cells, cnames)):
            lo_h = "h1" if i == 0 else f"h_{i - 1}.le"
            if i < n - 1:
                L.append(f"  rcases le_or_gt R {_q(cell.t)} with h_{i} | h_{i}")
                L.append(f"  · exact {cn} {pre}R {lo_h} h_{i}")
            else:
                hi_h = "" if cell.t is None else " h2"
                L.append(f"  exact {cn} {pre}R {lo_h}{hi_h}")
        out.append("\n".join(L) + "\n")
        return out

    def _tp_lemma_name(self, nm, gi, j) -> str:
        return f"{nm}_tp_{gi}_{j}"

    # -- per instance -------------------------------------------------------------------
    def _emit_instance(self, c: TypedCavityCert, nm: str) -> str:
        L: list[str] = []
        n = c.n
        Tn = f"Fin {n}"
        scope = ("every finite rooted tree" if not c.bounded
                 else f"every finite rooted tree of child count at most {c.M_tail}")
        L.append(f"/-! ## Instance `{nm}`\n\n"
                 f"Claim: on {scope}, `ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ "
                 f"yhi[type b]`, for\n"
                 f"  h(m, R) = {dict(c.spec)['h']},  g(m, R) = {dict(c.spec)['g']}"
                 f"  (m = number of children),\n"
                 f"  leaf (y, l) = ({c.y_leaf}, {c.l_leaf}), and the type table\n"
                 + "".join(f"  {i} `{t.name}`: {t.klo} ≤ k"
                           + ("" if t.khi is None else f" ≤ {t.khi}")
                           + (", any R" if t.rlo is None and t.rhi is None else
                              ", " + ("" if t.rlo is None else f"{t.rlo} ≤ ") + "R"
                              + ("" if t.rhi is None else f" < {t.rhi}"))
                           + ", "
                           + (f"EXACT (l, y) = ({t.B}, {t.ylo})" if t.exact else
                              f"B = {t.B}, y in [{t.ylo}, {t.yhi}]") + "\n"
                           for i, t in enumerate(c.types))
                 + f"Devices: enumeration k = 1..{c.M_enum}"
                 + (f", tangent band k = {c.M_enum + 1}..{c.M_tail}" if c.M_tail > c.M_enum
                    else "")
                 + ("" if c.bounded else f", analytic tail k ≥ {c.M_tail + 1}")
                 + ".\nconjecture1_proved = False. -/\n")
        # recursion
        for fn, (pn, pd) in (("h", (c.h_num, c.h_den)), ("g", (c.g_num, c.g_den))):
            uses_m = self._mdep(pn, pd)
            uses_r = any(R_SYM in p.as_expr().free_symbols for p in (pn, pd))
            nt = _poly_lean(pn, "(m : ℝ)")
            body = nt if pd.total_degree() == 0 else f"{nt} / {_poly_lean(pd, '(m : ℝ)')}"
            L.append(f"noncomputable def {nm}_{fn} : ℕ → ℝ → ℝ := fun {'m' if uses_m else '_'} "
                     f"{'R' if uses_r else '_'} => {body}")
        # table
        for tag, vals in (("B", [t.B for t in c.types]), ("ylo", [t.ylo for t in c.types]),
                          ("yhi", [t.yhi for t in c.types])):
            L.append(f"noncomputable def {nm}_{tag} : {Tn} → ℝ := "
                     f"![{', '.join(_q(v) for v in vals)}]")
            for i, v in enumerate(vals):
                L.append(f"theorem {nm}_{tag}_{i} : {nm}_{tag} {i} = {_q(v)} := rfl")
        L.append("")
        # type map
        L.append(self._emit_tp(c, nm))
        # base
        gi0 = _group_of(c.groups, 0)
        j0 = sum(1 for cu in c.groups[gi0].cuts if 0 >= cu)
        T0 = c.types[c.base_type]
        L.append(f"theorem {nm}_base : Inv {nm}_B {nm}_ylo {nm}_yhi ({nm}_tp 0 0) "
                 f"{_q(c.l_leaf)} {_q(c.y_leaf)} := by\n"
                 f"  rw [{self._tp_call(c, nm, gi0, j0, '0', '0')}]\n"
                 f"  refine ⟨?_, ?_, ?_⟩ <;> norm_num [{nm}_B_{c.base_type}, "
                 f"{nm}_ylo_{c.base_type}, {nm}_yhi_{c.base_type}]\n")
        del T0
        # ymin / ymax / Bmax facts
        L.append(f"theorem {nm}_ymin : ∀ t, {_q(c.ymin)} ≤ {nm}_ylo t := by\n"
                 f"  intro t; fin_cases t <;> norm_num [{nm}_ylo]\n")
        L.append(f"theorem {nm}_ymax : ∀ t, {nm}_yhi t ≤ {_q(c.ymax)} := by\n"
                 f"  intro t; fin_cases t <;> norm_num [{nm}_yhi]\n")
        L.append(f"theorem {nm}_Bmax : ∀ t, {nm}_B t ≤ {_q(c.Bmax)} := by\n"
                 f"  intro t; fin_cases t <;> norm_num [{nm}_B]\n")
        # enumeration
        for k in range(1, c.M_enum + 1):
            steps = [e for e in c.enum if e.k == k]
            for e in steps:
                L.extend(self._emit_enum_step(c, nm, e))
            L.append(self._emit_count_dispatch(c, nm, k, steps))
        # band
        for b in c.band:
            L.extend(self._emit_band(c, nm, b))
        # tail
        if c.tail is not None:
            L.extend(self._emit_tail(c, nm, c.tail))
        L.append(self._emit_assembly(c, nm))
        if c.join is not None:
            L.extend(self._emit_join(c, nm, c.join))
        return "\n".join(L)

    # type map --------------------------------------------------------------------------
    def _emit_tp(self, c, nm) -> str:
        def bins_text(g: Group) -> str:
            if not g.cuts:
                return f"{g.types[0]}"
            txt = f"{g.types[-1]}"
            for j in range(len(g.cuts) - 1, -1, -1):
                txt = f"if R < {_q(g.cuts[j])} then {g.types[j]} else {txt}"
            return f"({txt})"
        body = bins_text(c.groups[-1])
        for g in reversed(c.groups[:-1]):
            body = f"if k ≤ {g.khi} then {bins_text(g)} else {body}"
        uses_r = any(g.cuts for g in c.groups)
        uses_k = len(c.groups) > 1
        L = [f"/-- The type map: degree groups, then bins of the message sum. -/",
             f"noncomputable def {nm}_tp ({'k' if uses_k else '_'} : ℕ) "
             f"({'R' if uses_r else '_'} : ℝ) : Fin {c.n} :=\n  {body}\n"]
        for gi, g in enumerate(c.groups):
            for j, ti in enumerate(g.types):
                blo, bhi = g.bin_bounds(j)
                hyps = []
                if g.klo > 0 and gi > 0:
                    hyps.append(f"(hk1 : {g.klo} ≤ k)")
                if g.khi is not None and gi < len(c.groups) - 1:
                    hyps.append(f"(hk2 : k ≤ {g.khi})")
                hyps.append("(R : ℝ)")
                if blo is not None:
                    hyps.append(f"(hr1 : {_q(blo)} ≤ R)")
                if bhi is not None:
                    hyps.append(f"(hr2 : R < {_q(bhi)})")
                rws = []
                for gp in c.groups[:gi]:
                    rws.append(f"if_neg (show ¬ (k ≤ {gp.khi}) by omega)")
                if gi < len(c.groups) - 1:
                    rws.append(f"if_pos (show k ≤ {g.khi} by omega)")
                for jj in range(j):
                    rws.append(f"if_neg (show ¬ (R < {_q(g.cuts[jj])}) from "
                               f"not_lt.mpr (by linarith))")
                if j < len(g.cuts):
                    rws.append("if_pos hr2")
                proof = f"  unfold {nm}_tp\n" + (f"  rw [{', '.join(rws)}]\n" if rws else "")
                if not rws:
                    proof = f"  rfl\n"
                L.append(f"theorem {self._tp_lemma_name(nm, gi, j)} (k : ℕ) {' '.join(hyps)} :\n"
                         f"    {nm}_tp k R = {ti} := by\n" + proof)
        return "\n".join(L)

    def _tp_call(self, c, nm, gi, j, kv, Rv) -> str:
        """`tp_lemma k [hk1] [hk2] R [hr1] [hr2]` with every hypothesis discharged in context."""
        g = c.groups[gi]
        blo, bhi = g.bin_bounds(j)
        parts = [self._tp_lemma_name(nm, gi, j), f"({kv})"]
        if g.klo > 0 and gi > 0:
            parts.append("(by omega)")
        if g.khi is not None and gi < len(c.groups) - 1:
            parts.append("(by omega)")
        parts.append(f"({Rv})")
        if blo is not None:
            parts.append("(by linarith)")
        if bhi is not None:
            parts.append("(by linarith)")
        return " ".join(parts)

    def _bin_split(self, c, nm, gi, Rv: str, lo, hi, finish) -> list:
        """Case split on the bins of group ``gi`` for the real ``Rv`` known to lie in
        ``[lo, hi]`` (``hi`` None: unbounded); bins not meeting it close by linarith.
        ``finish(j, type index)`` gives the tactic lines (indented by the caller's bullet)."""
        g = c.groups[gi]
        out = []
        nb = len(g.types)
        for j in range(nb):
            blo, bhi = g.bin_bounds(j)
            meets = not ((bhi is not None and bhi <= lo)
                         or (blo is not None and hi is not None and blo > hi))
            body = finish(j, g.types[j]) if meets else ["exfalso; linarith"]
            if j < nb - 1:
                out.append(f"rcases lt_or_ge ({Rv}) {_q(bhi)} with hb{j} | hb{j}")
                out.append("· " + body[0])
                out.extend("  " + ln for ln in body[1:])
            else:
                out.extend(body)
        return out

    # enumeration -----------------------------------------------------------------------
    def _emit_enum_step(self, c, nm, e: EnumStep) -> list:
        out = []
        tag = f"{nm}_e{e.k}_{_counts_tag(e.counts)}"
        for (j, ti, ov, olo, ohi) in e.bins:
            for ob, sfx in ((ov, "val"), (olo, "lo"), (ohi, "hi")):
                out.extend(self._cover_lemma(c, nm, f"{tag}_b{j}_{sfx}", ob))
        gi = _group_of(c.groups, e.k)
        bins = {j: (ti, ov) for (j, ti, ov, _olo, _ohi) in e.bins}

        def finish(j, ti):
            ov = bins[j][1]
            hi_arg = "h2" if (ov.t == e.hi) else "hb%d.le" % j
            lo_arg = "h1" if (ov.s == e.lo) else f"hb{j - 1}"
            if ov.s == ov.t:
                # a point cell inside a bin: both bounds pin R
                lo_arg = "(by linarith)"
                hi_arg = "(by linarith)"
            call = f"R {lo_arg} {hi_arg}"
            return [f"rw [{self._tp_call(c, nm, gi, j, str(e.k), 'R')}]",
                    "refine ⟨?_, ?_, ?_⟩",
                    f"· rw [{nm}_B_{ti}]; exact {tag}_b{j}_val {call}",
                    f"· rw [{nm}_ylo_{ti}]; exact {tag}_b{j}_lo {call}",
                    f"· rw [{nm}_yhi_{ti}]; exact {tag}_b{j}_hi {call}"]
        body = self._bin_split(c, nm, gi, "R", e.lo, e.hi, finish)
        out.append(f"theorem {tag} (R : ℝ) (h1 : {_q(e.lo)} ≤ R) (h2 : R ≤ {_q(e.hi)}) :\n"
                   f"    Inv {nm}_B {nm}_ylo {nm}_yhi ({nm}_tp {e.k} R) ({_q(e.S)} + "
                   f"{nm}_g {e.k} R) ({nm}_h {e.k} R) := by\n"
                   + "".join(f"  {ln}\n" for ln in body))
        return out

    def _emit_count_dispatch(self, c, nm, k, steps) -> str:
        n = c.n
        cs = [f"c{i}" for i in range(n)]
        rw_tab = ", ".join([_SUM_UNIV[n]] + [f"{nm}_{tg}_{i}" for tg in ("B", "ylo", "yhi")
                                             for i in range(n)])
        L = [f"theorem {nm}_cnt{k} (c : Fin {n} → ℕ) (hc : ∑ t, c t = {k}) (R : ℝ)\n"
             f"    (h1 : ∑ t, (c t : ℝ) * {nm}_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * {nm}_yhi t) :\n"
             f"    Inv {nm}_B {nm}_ylo {nm}_yhi ({nm}_tp {k} R)\n"
             f"      ((∑ t, (c t : ℝ) * {nm}_B t) + {nm}_g {k} R) ({nm}_h {k} R) := by",
             f"  simp only [{rw_tab}] at hc h1 h2 ⊢"]
        for i in range(n):
            L.append(f"  generalize c {i} = {cs[i]} at hc h1 h2 ⊢")
        by_counts = {e.counts: e for e in steps}

        def rec(i, prefix, left, ind):
            pad = "  " * ind
            if i == n - 1:
                cv = tuple(prefix + [left])
                e = by_counts[cv]
                tag = f"{nm}_e{k}_{_counts_tag(cv)}"
                lines = [f"{pad}obtain rfl : {cs[i]} = {left} := by omega",
                         f"{pad}push_cast at h1 h2 ⊢",
                         f"{pad}have hob := {tag} R (by linarith) (by linarith)",
                         f"{pad}exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩"]
                del e
                return lines
            lines = [f"{pad}have b{i} : {cs[i]} ≤ {left} := by omega",
                     f"{pad}interval_cases {cs[i]}"]
            for v in range(left + 1):
                sub = rec(i + 1, prefix + [v], left - v, ind + 1)
                lines.append(f"{pad}· " + sub[0].lstrip())
                lines.extend(sub[1:])
            return lines
        L.extend(rec(0, [], k, 1))
        return "\n".join(L) + "\n"

    # band ------------------------------------------------------------------------------
    def _emit_mu(self, c, nm, name, s, mu) -> str:
        return (f"theorem {name} : ∀ t y, {nm}_ylo t ≤ y → y ≤ {nm}_yhi t →\n"
                f"    {nm}_B t + {_q(s)} * y ≤ {_q(mu)} := by\n"
                f"  intro t y h1 h2\n"
                f"  fin_cases t <;> norm_num [{nm}_B, {nm}_ylo, {nm}_yhi] at h1 h2 ⊢ <;> "
                f"linarith\n")

    def _emit_band(self, c, nm, b: BandStep) -> list:
        out = []
        k = b.k
        tag = f"{nm}_band{k}"
        out.extend(self._cover_lemma(c, nm, f"{tag}_tan", b.tan))
        out.append(self._emit_mu(c, nm, f"{tag}_mu", b.s, b.mu))
        for (j, ti, olo, ohi) in b.bins:
            out.extend(self._cover_lemma(c, nm, f"{tag}_b{j}_lo", olo))
            out.extend(self._cover_lemma(c, nm, f"{tag}_b{j}_hi", ohi))
        gi = _group_of(c.groups, k)
        lo, hi = b.tan.s, b.tan.t
        bins = {j: (ti, olo) for (j, ti, olo, _ohi) in b.bins}

        def finish(j, ti):
            olo = bins[j][1]
            lo_arg = "(by linarith)"
            hi_arg = "(by linarith)" if olo.t == hi else f"hb{j}.le"
            call = f"R {lo_arg} {hi_arg}"
            return [f"rw [{self._tp_call(c, nm, gi, j, str(k), 'R')}]",
                    "refine ⟨?_, ?_, ?_⟩",
                    f"· rw [{nm}_B_{ti}]; linarith",
                    f"· rw [{nm}_ylo_{ti}]; exact {tag}_b{j}_lo {call}",
                    f"· rw [{nm}_yhi_{ti}]; exact {tag}_b{j}_hi {call}"]
        body = self._bin_split(c, nm, gi, "R", lo, hi, finish)
        out.append(
            f"theorem {tag} (τ : Fin {k} → Fin {c.n}) (y l : Fin {k} → ℝ)\n"
            f"    (hch : ∀ i, Inv {nm}_B {nm}_ylo {nm}_yhi (τ i) (l i) (y i)) :\n"
            f"    Inv {nm}_B {nm}_ylo {nm}_yhi ({nm}_tp {k} (∑ i, y i))\n"
            f"      ((∑ i, l i) + {nm}_g {k} (∑ i, y i)) ({nm}_h {k} (∑ i, y i)) := by\n"
            f"  have hsep := separable_bound {nm}_B {nm}_ylo {nm}_yhi {_q(b.s)} {_q(b.mu)} "
            f"{tag}_mu τ y l hch\n"
            f"  have hR := msg_sum_range {nm}_B {nm}_ylo {nm}_yhi {_q(c.ymin)} {_q(c.ymax)} "
            f"{nm}_ymin {nm}_ymax τ y l hch\n"
            f"  generalize ∑ i, y i = R at hsep hR ⊢\n"
            f"  generalize ∑ i, l i = L at hsep ⊢\n"
            f"  push_cast at hsep hR\n"
            f"  obtain ⟨hR1, hR2⟩ := hR\n"
            f"  have ht := {tag}_tan R (by linarith) (by linarith)\n"
            + "".join(f"  {ln}\n" for ln in body))
        return out

    # tail ------------------------------------------------------------------------------
    def _emit_tail(self, c, nm, tl: TailStep) -> list:
        out = []
        tag = f"{nm}_tail"
        K0 = tl.K0
        out.extend(self._cover_lemma(c, nm, f"{tag}_tan", tl.tan))
        out.append(self._emit_mu(c, nm, f"{tag}_mu", tl.s, tl.mu))
        for (j, ti, olo, ohi) in tl.bins:
            out.extend(self._cover_lemma(c, nm, f"{tag}_b{j}_lo", olo))
            out.extend(self._cover_lemma(c, nm, f"{tag}_b{j}_hi", ohi))
        gi = len(c.groups) - 1
        R0 = tl.tan.s
        bins = {j: (ti, olo) for (j, ti, olo, _ohi) in tl.bins}

        def finish(j, ti):
            olo = bins[j][1]
            hi_arg = "" if olo.t is None else f" hb{j}.le"
            call = f"k hk' R (by linarith){hi_arg}"
            return [f"rw [{self._tp_call(c, nm, gi, j, 'k', 'R')}]",
                    "refine ⟨?_, ?_, ?_⟩",
                    f"· rw [{nm}_B_{ti}]; linarith",
                    f"· rw [{nm}_ylo_{ti}]; exact {tag}_b{j}_lo {call}",
                    f"· rw [{nm}_yhi_{ti}]; exact {tag}_b{j}_hi {call}"]
        body = self._bin_split(c, nm, gi, "R", R0, None, finish)
        out.append(
            f"theorem {tag} (k : ℕ) (hk : {c.M_tail} < k) (τ : Fin k → Fin {c.n}) "
            f"(y l : Fin k → ℝ)\n"
            f"    (hch : ∀ i, Inv {nm}_B {nm}_ylo {nm}_yhi (τ i) (l i) (y i)) :\n"
            f"    Inv {nm}_B {nm}_ylo {nm}_yhi ({nm}_tp k (∑ i, y i))\n"
            f"      ((∑ i, l i) + {nm}_g k (∑ i, y i)) ({nm}_h k (∑ i, y i)) := by\n"
            f"  have hk' : {K0} ≤ k := hk\n"
            f"  have hsep := separable_bound {nm}_B {nm}_ylo {nm}_yhi {_q(tl.s)} {_q(tl.mu)} "
            f"{tag}_mu τ y l hch\n"
            f"  have hR := msg_sum_range {nm}_B {nm}_ylo {nm}_yhi {_q(c.ymin)} {_q(c.ymax)} "
            f"{nm}_ymin {nm}_ymax τ y l hch\n"
            f"  generalize ∑ i, y i = R at hsep hR ⊢\n"
            f"  generalize ∑ i, l i = L at hsep ⊢\n"
            f"  have hkr : ({K0} : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'\n"
            f"  have hmu : (k : ℝ) * {_q(tl.mu)} ≤ ({K0} : ℝ) * {_q(tl.mu)} :=\n"
            f"    mul_le_mul_of_nonpos_right hkr (by norm_num)\n"
            f"  have hR0 : ({K0} : ℝ) * {_q(c.ymin)} ≤ R :=\n"
            f"    le_trans (mul_le_mul_of_nonneg_right hkr (by norm_num)) hR.1\n"
            f"  have ht := {tag}_tan k hk' R (by linarith)\n"
            + "".join(f"  {ln}\n" for ln in body))
        return out

    # assembly --------------------------------------------------------------------------
    def _emit_assembly(self, c, nm) -> str:
        D = c.M_tail
        ok = f"k ≤ {D}" if c.bounded else "True"
        okfun = f"(fun k => k ≤ {D})" if c.bounded else "(fun _ => True)"
        lines = [f"theorem {nm}_hstep : ∀ k : ℕ, 1 ≤ k → {ok} → ∀ (τ : Fin k → Fin {c.n}) "
                 f"(y l : Fin k → ℝ),\n"
                 f"    (∀ i, Inv {nm}_B {nm}_ylo {nm}_yhi (τ i) (l i) (y i)) →\n"
                 f"    Inv {nm}_B {nm}_ylo {nm}_yhi ({nm}_tp k (∑ i, y i))\n"
                 f"      ((∑ i, l i) + {nm}_g k (∑ i, y i)) ({nm}_h k (∑ i, y i)) := by",
                 "  intro k hk hok τ y l hch"]
        ind = "  "
        if not c.bounded:
            lines.append(f"  rcases Nat.lt_or_ge {D} k with hK | hK")
            lines.append(f"  · exact {nm}_tail k hK τ y l hch")
        lines.append(f"{ind}interval_cases k")
        for k in range(1, D + 1):
            if k <= c.M_enum:
                lines.append(f"{ind}· exact step_of_counts ({nm}_g {k}) ({nm}_h {k}) ({nm}_tp {k}) "
                             f"{nm}_B {nm}_ylo {nm}_yhi {nm}_cnt{k} τ y l hch")
            else:
                lines.append(f"{ind}· exact {nm}_band{k} τ y l hch")
        if c.bounded:
            pass
        out = ["\n".join(lines) + "\n"]
        deg = f" (hb : b.AllDeg (fun k => k ≤ {D}))" if c.bounded else ""
        hb = "hb" if c.bounded else "(PTree.allDeg_true b)"
        out.append(
            f"/-- MAIN.  The type table is an inductive invariant on "
            f"{'every finite rooted tree' if not c.bounded else f'every tree of child count at most {D}'}:\n"
            f"`ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`. -/\n"
            f"theorem {nm} (b : PTree){deg} :\n"
            f"    Inv {nm}_B {nm}_ylo {nm}_yhi (b.typ {nm}_tp {nm}_h {_q(c.y_leaf)})\n"
            f"      (b.ell {nm}_g {nm}_h {_q(c.l_leaf)} {_q(c.y_leaf)}) (b.msg {nm}_h {_q(c.y_leaf)}) :=\n"
            f"  typed_induction_core {okfun} {nm}_h {nm}_g {_q(c.y_leaf)} {_q(c.l_leaf)} {nm}_tp "
            f"{nm}_B {nm}_ylo {nm}_yhi\n"
            f"    {nm}_base {nm}_hstep b {hb}\n")
        out.append(
            f"/-- Uniform corollary: `ell b ≤ max_t B_t = {c.Bmax}`. -/\n"
            f"theorem {nm}_uniform (b : PTree){deg} :\n"
            f"    b.ell {nm}_g {nm}_h {_q(c.l_leaf)} {_q(c.y_leaf)} ≤ {_q(c.Bmax)} :=\n"
            f"  le_trans ({nm} b{' hb' if c.bounded else ''}).1 ({nm}_Bmax _)\n")
        return "\n".join(out)

    # join ------------------------------------------------------------------------------
    def _emit_join(self, c, nm, jn: Join) -> list:
        out = []
        K = jn.K
        n = c.n
        out.append(f"/-- The join (root) function, `gJ(R)` at root child count {K}. -/\n"
                   f"noncomputable def {nm}_gJ : ℝ → ℝ := fun "
                   f"{'R' if R_SYM in (jn.gJ_num.as_expr() / jn.gJ_den.as_expr()).free_symbols else '_'}"
                   f" => {self._closed1(jn.gJ_num, jn.gJ_den, None)}\n")
        for js in jn.steps:
            out.extend(self._cover_lemma(c, nm, f"{nm}_j_{_counts_tag(js.counts)}", js.ob))
        cs = [f"c{i}" for i in range(n)]
        rw_tab = ", ".join([_SUM_UNIV[n]] + [f"{nm}_{tg}_{i}" for tg in ("B", "ylo", "yhi")
                                             for i in range(n)])
        L = [f"theorem {nm}_jcnt (c : Fin {n} → ℕ) (hc : ∑ t, c t = {K}) (R : ℝ)\n"
             f"    (h1 : ∑ t, (c t : ℝ) * {nm}_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * {nm}_yhi t) :\n"
             f"    (∑ t, (c t : ℝ) * {nm}_B t) + {nm}_gJ R ≤ {_q(jn.C)} := by",
             f"  simp only [{rw_tab}] at hc h1 h2 ⊢"]
        for i in range(n):
            L.append(f"  generalize c {i} = {cs[i]} at hc h1 h2 ⊢")

        def rec(i, prefix, left, ind):
            pad = "  " * ind
            if i == n - 1:
                cv = tuple(prefix + [left])
                tag = f"{nm}_j_{_counts_tag(cv)}"
                return [f"{pad}obtain rfl : {cs[i]} = {left} := by omega",
                        f"{pad}push_cast at h1 h2 ⊢",
                        f"{pad}linarith [{tag} R (by linarith) (by linarith)]"]
            lines = [f"{pad}have b{i} : {cs[i]} ≤ {left} := by omega",
                     f"{pad}interval_cases {cs[i]}"]
            for v in range(left + 1):
                sub = rec(i + 1, prefix + [v], left - v, ind + 1)
                lines.append(f"{pad}· " + sub[0].lstrip())
                lines.extend(sub[1:])
            return lines
        L.extend(rec(0, [], K, 1))
        out.append("\n".join(L) + "\n")
        deg = f" (hb : ∀ i, (b i).AllDeg (fun k => k ≤ {c.M_tail}))" if c.bounded else ""
        main = f"{nm} (b i) (hb i)" if c.bounded else f"{nm} (b i)"
        out.append(
            f"/-- JOIN.  A root with {K} children closing any {K} trees: "
            f"`∑ ell + gJ(∑ msg) ≤ {jn.C}`. -/\n"
            f"theorem {nm}_join (b : Fin {K} → PTree){deg} :\n"
            f"    (∑ i, (b i).ell {nm}_g {nm}_h {_q(c.l_leaf)} {_q(c.y_leaf)}) +\n"
            f"      {nm}_gJ (∑ i, (b i).msg {nm}_h {_q(c.y_leaf)}) ≤ {_q(jn.C)} :=\n"
            f"  join_of_counts {nm}_gJ {_q(jn.C)} {nm}_B {nm}_ylo {nm}_yhi {nm}_jcnt\n"
            f"    (fun i => (b i).typ {nm}_tp {nm}_h {_q(c.y_leaf)})\n"
            f"    (fun i => (b i).msg {nm}_h {_q(c.y_leaf)})\n"
            f"    (fun i => (b i).ell {nm}_g {nm}_h {_q(c.l_leaf)} {_q(c.y_leaf)})\n"
            f"    (fun i => {main})\n")
        return out


def typed_cavity_induction_family(name, grid, lean_name, spec, constants=None):
    """Build a typed-cavity-induction family (kind='typed_cavity_induction').

    ``spec``: a callable ``pt -> dict`` of :func:`typed_cavity_certificate` keyword
    arguments."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("typed_cavity_induction", spec),
        constants=dict(constants or {}),
    )


# ---------------------------------------------------------------------------
# instances
# ---------------------------------------------------------------------------

def bbg_c_table(Delta: int, beta) -> list:
    """The constants `c_1..c_Delta` of Balister-Bollobas-Gerke (J. Graph Theory 56 (2007)
    270-286), recursion (4)-(5) at alpha = gamma = 1:
    `c_1 = -beta`, `c_d = (d - 1) max_{1 <= k < d} (c_k + 1/(k d)) - beta`."""
    beta = _rat(beta, "beta")
    c = {1: -beta}
    for d in range(2, Delta + 1):
        c[d] = (d - 1) * max(c[k] + sp.Rational(1, k * d) for k in range(1, d)) - beta
    return [c[d] for d in range(1, Delta + 1)]


def bbg_randic_spec(Delta: int, beta) -> dict:
    """The BBG half-tree recursion (2) for `c_T = R_{-1}(T) - beta n(T)` with types by root
    degree, the table `c_d` of (4)-(5), trees of maximum degree `Delta`, and the join that
    closes a tree at a vertex of degree `Delta` (BBG Theorem 6 at alpha = gamma = 1).

    A half-tree node with `k` children has degree `d = k + 1` (the dangling edge counts), so
    the message is `y = 1/d = 1/(k + 1)` and recursion (2) reads
    `c_T = sum_i c_{T_i} + (1/d) sum_i y_i - beta`, i.e. `g(k, R) = R/(k + 1) - beta`.
    A leaf is the half-tree of one vertex: `(y, c) = (1, -beta)`."""
    beta = _rat(beta, "beta")
    c = bbg_c_table(Delta, beta)
    types = []
    for d in range(1, Delta + 1):
        k = d - 1
        types.append(dict(name=f"deg{d}", deg=(k, None if d == Delta else k), bin=(None, None),
                          exact=(c[d - 1], sp.Rational(1, d))) if d == 1 else
                     dict(name=f"deg{d}", deg=(k, None if d == Delta else k), bin=(None, None),
                          B=c[d - 1], y=(sp.Rational(1, d), sp.Rational(1, d))))
    C = (beta + Delta * c[Delta - 1]) / (Delta - 1)
    return dict(h="1/(m+1)", g=f"R/(m+1) - {beta}", y_leaf=1, l_leaf=-beta, types=types,
                M_enum=Delta - 1, max_children=Delta - 1,
                join=dict(K=Delta, g=f"R/m - {beta}", C=C))


#: Balister-Bollobas-Gerke, maximum degree 3, beta_3 = 7/27 (published).
BBG3_SPEC = bbg_randic_spec(3, sp.Rational(7, 27))
#: Balister-Bollobas-Gerke, maximum degree 4, beta_4 = 139/528 (published).
BBG4_SPEC = bbg_randic_spec(4, sp.Rational(139, 528))
#: The negative control: beta lowered below beta_3 (the table c_d recomputed at the lowered
#: beta).  FALSE: the degree-3 step `2 (c_3 + 1/9) - beta <= c_3` fails (by 3/500), and the
#: claim itself fails: joining two copies of a half-tree at a new root doubles the excess of
#: `c_T` over `beta - 2/9`, which is positive for `[3, 2, 1]` (`c_T = c_3`) when beta < 7/27.
BBG3_LOWERED_SPEC = bbg_randic_spec(3, sp.Rational(7, 27) - sp.Rational(1, 1000))

#: SYNTHETIC (no combinatorial meaning; of our own design, to exercise every device): the
#: matching-type message `y = 1/(1 + R)` with the value `g(m, R) = R/(1 + R) + 1/(4(m + 1))
#: - 3/5` (a concave reward for the children's message sum, a degree bonus that decays in m,
#: and a per-vertex price 3/5), leaf `(y, l) = (1, -3/5)`.  Eight types: the leaf (exact),
#: child count 1 and 2 each split into two message-sum bins, one band type for m = 3..4 and
#: two tail types for m >= 5 split at R = 1.  Enumeration m = 1..2 (Bernstein cells on
#: interval messages), tangent band m = 3..4 (midpoint tangents of the concave g), analytic
#: tail m >= 5 (two-variable certificates in u = m - 5 and R).
SYNTH_SPEC = dict(
    h="1/(1+R)", g="R/(1+R) + 1/(4*(m+1)) - 3/5", y_leaf=1, l_leaf="-3/5",
    types=[
        dict(name="leaf", deg=(0, 0), exact=("-3/5", 1)),
        dict(name="m1lo", deg=(1, 1), bin=(None, "3/4"), B="-17/25", y=("4/7", 1)),
        dict(name="m1hi", deg=(1, 1), bin=("3/4", None), B="-23/40", y=("1/2", "4/7")),
        dict(name="m2lo", deg=(2, 2), bin=(None, 1), B="-41/25", y=("1/2", 1)),
        dict(name="m2hi", deg=(2, 2), bin=(1, None), B="-21/20", y=("1/3", "1/2")),
        dict(name="band", deg=(3, 4), B="-29/20", y=("1/5", 1)),
        dict(name="tail_lo", deg=(5, None), bin=(None, 1), B="-13/5", y=("1/2", 1)),
        dict(name="tail_hi", deg=(5, None), bin=(1, None), B="-13/5", y=(0, "1/2")),
    ],
    M_enum=2, M_tail=4,
)


if __name__ == "__main__":
    for nm_, sp_ in (("bbg3", BBG3_SPEC), ("bbg4", BBG4_SPEC)):
        cc = typed_cavity_certificate(**sp_)
        print(nm_, "types", [(t.name, t.B) for t in cc.types], "join C", cc.join.C)
    try:
        typed_cavity_certificate(**BBG3_LOWERED_SPEC)
        raise SystemExit("FAIL: lowered beta_3 was NOT refused")
    except TypedCavityRefusal as e:
        print("correctly REFUSED:", str(e)[:160])

"""affine_hull_dominance emitter -- the EXACT MAXIMUM, over all finite trees on n vertices, of a
quantity computed by a POSITIVE MULTILINEAR tree recursion, certified by convex-hull pruning with
explicit convex-combination domination witnesses.

conjecture1_proved = False.  Nothing in this module bears on any open problem; it certifies, for
one explicitly given recursion and every n up to an explicit bound N, the value
M_n = max { pi(T) : T a tree on n vertices } and the shape of every maximizer.

THE SETTING
-----------
A rooted tree is built from PLANTED BRANCHES (a rooted tree whose root will be joined to one
parent) and BUNDLES (the multiset of branches hanging below one vertex).  Both carry a vector
state in Q^D:

    empty bundle      e
    bundle + child    (x (*) z)_i = sum_{j,l} T[i][j][l] x_j z_l        (bilinear)
    planting          (P_c x)_i   = sum_j P_c[i][j] x_j                   (c = number of children)
    root value        pi = F_k . x                                        (k = number of children)

A tree rooted at a vertex with children list L has pi(T) = F_{|L|} . bundle(L), bundle(t :: L) =
bundle(L) (*) branch(t), branch(node L) = P_{|L|} bundle(L).  Every tree on n vertices is such a
rooted tree (root it anywhere), so M_n is the maximum over rooted trees of size n.

The running example (D = 2) is the Randic-weighted matching sum
    pi(T) = sum over matchings M of prod_{uv in M} 1/(deg u deg v),
with branch state (Z, W): a root with c children has P = prod Z_i, Q = sum_i W_i prod_{j!=i} Z_j,
Z = P + Q/d, W = P/d, d = c + 1, and pi = P + Q/k at a root with k children.  In the vector form:
e = (1, 0), (P, Q) (*) (Z, W) = (PZ, QZ + PW), P_c = [[1, 1/(c+1)], [1/(c+1), 0]],
F_k = (1, 1/k).

THE KEY LEMMA (formalized generically in the emitted Lean)
---------------------------------------------------------
Every map is multilinear with NONNEGATIVE coefficients, so with the rest of a tree fixed, pi is
a nonnegative linear functional of the state of any one branch or bundle; more precisely any
nonnegative covector pulls back to a nonnegative covector through (*) and P_c (and a strictly
positive one to a strictly positive one, under the sign conditions below).  Hence a candidate
state that is dominated componentwise by a convex combination of other states of the SAME CLASS
(same number of vertices, and for bundles the same child count, which fixes the planting
degree) can be exchanged away: it never raises the maximum, and if the domination is strict
it can never occur in a maximizer.

In Lean, domination is stated in DUAL form, which is what makes the generic proof short:
    Dom K x  :=  for every covector a >= 0 there is p in K with a.x <= a.p,
    SDom K x :=  for every covector a > 0  there is p in K with a.x <  a.p.
A primal witness (weights w >= 0, sum w = 1, x <= sum w_k K_k, strict somewhere) implies both.
The generic theorems are `inv_branch`/`inv_bundle` (every branch/bundle state is nonnegative
and weakly dominated by its class's kept list), `kept_branch`/`kept_bundle` (every subtree is
kept all the way down, or its state is strictly dominated), `pi_le` (the upper bound),
`kept_of_pi_eq` (a maximizer has every branch and partial bundle state on the kept lists) and
`isGreatest_pi` (upper bound plus one attaining tree = the exact maximum).

THE CERTIFICATE
---------------
For every bundle class (s, c) with s < N and every branch class m < N: the KEPT points (the
points maximizing some strictly positive covector over the class's candidates: hull vertices
and points on hull edges; ties kept) and, for every candidate in the checker's own enumeration
order, a witness: `kept i` (the candidate equals kept point i) or `dom w` (rational convex
weights over the kept list, componentwise domination, strict in one coordinate).  Candidates of
(s, c) are all kept(s - j, c - 1) (*) kept-branch(j), j = 1..s; candidates of branch class m are
P_c applied to kept(m - 1, c), c = 0..m-1.  The Lean checker `Cert.Valid` enumerates the
candidates itself and is closed by one `decide +kernel` (exact rational arithmetic in the
kernel; standard axioms only).  Per n: `F_k . p <= M_n` for every kept root bundle (decide)
and one explicit tree with pi = M_n (decide).  Every listed maximizer is checked the same way.

SIGN CONDITIONS (checked here and again in Lean by decide, as `Rec.Signs`)
--------------------------------------------------------------------------
With a distinguished coordinate z0 (default 0): e >= 0 and e[z0] > 0; T >= 0, T[z0][z0][z0] > 0,
for every j some T[i][j][z0] > 0, for every l some T[i][z0][l] > 0; for every c < N: P_c >= 0,
P_c[z0][z0] > 0 and every column of P_c has a positive entry; F_k >= 0 for 1 <= k < N.  The
MAXIMIZER statement additionally needs F_k > 0 (strictly) for 1 <= k < N; without it the
emitter states the exact maximum only.

WHAT IS AND IS NOT PROVED (stated plainly)
------------------------------------------
* PROVED in Lean, for each n in 2..N: M_n = v_n exactly (IsGreatest), and every tree attaining
  v_n has EVERY branch state and EVERY partial bundle state equal to a kept hull point, its root
  bundle among the kept points of (n - 1, k).  Every tree in the emitted maximizer list attains
  v_n (checked by decide).
* NOT proved in Lean: that the emitted list is complete up to isomorphism.  The generator's
  payload propagation (all trees realizing each kept point) makes it complete by the exchange
  argument, and the Lean theorem pins every maximizer to the kept structure, but the final
  "these are all the isomorphism classes" enumeration is computed in Python, not in the kernel.
* The quantity is DEFINED by the recursion; that the recursion computes a given graph
  invariant (for instance the matching sum) is a classical identity that is not formalized.

ANTI-PHANTOM REFUSALS
---------------------
`hull_dominance_certificate` raises ``ValueError("REFUSED: ...")`` on: a float anywhere; a
dimension below 1 or shapes that do not match it; any sign condition failing (negative
coefficient, zero z0 entry, a column of P_c or of T with no positive entry reached from z0, a
negative root covector); `maximizers=True` with a root covector that is not strictly positive;
N < 2 or N > 16; a class whose candidate count exceeds the cap; and a non-rational entry.
`verify_certificate` re-checks every witness exactly, in the same enumeration order as the Lean
checker, before anything is emitted.  ``check=False`` (negative controls only) skips it.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

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

#: the symbols of the planting matrices (child count c) and root covectors (child count k)
C_SYM = sp.Symbol("c")
K_SYM = sp.Symbol("k")

_MAX_N = 16
_MAX_CAND = 4000


# ---------------------------------------------------------------------------
# exact inputs
# ---------------------------------------------------------------------------

def _frac(q, what: str) -> Fraction:
    """An exact rational; floats and non-rationals are refused."""
    if isinstance(q, bool):
        raise ValueError(f"REFUSED: {what} = {q!r} is not a rational")
    if isinstance(q, float):
        raise ValueError(f"REFUSED: {what} = {q!r} is a float; pass an exact rational")
    if isinstance(q, Fraction):
        return q
    if isinstance(q, int):
        return Fraction(q)
    if isinstance(q, str):
        q = sp.Rational(q)
    q = sp.sympify(q)
    if isinstance(q, sp.Float) or not q.is_Rational:
        raise ValueError(f"REFUSED: {what} = {q} is not an exact rational")
    return Fraction(int(q.p), int(q.q))


def _expr(e, sym: sp.Symbol, what: str) -> sp.Expr:
    """A rational function of one child-count symbol, with rational coefficients."""
    if isinstance(e, float):
        raise ValueError(f"REFUSED: {what} = {e!r} is a float")
    if isinstance(e, str):
        e = sp.sympify(e, locals={str(sym): sym})
    e = sp.sympify(e)
    if e.atoms(sp.Float):
        raise ValueError(f"REFUSED: {what} = {e} contains a float")
    extra = e.free_symbols - {sym}
    if extra:
        raise ValueError(f"REFUSED: {what} depends on {sorted(map(str, extra))}, not only {sym}")
    num, den = sp.fraction(sp.cancel(sp.together(e)))
    for part in (num, den):
        try:
            sp.Poly(part, sym, domain="QQ")
        except sp.PolynomialError as err:
            raise ValueError(f"REFUSED: {what} = {e} is not a rational function of {sym}") from err
    return e


def _at(e: sp.Expr, sym: sp.Symbol, n: int, what: str) -> Fraction:
    v = sp.sympify(e).subs(sym, n)
    if v.has(sp.zoo, sp.oo, sp.nan) or not v.is_Rational:
        raise ValueError(f"REFUSED: {what} is undefined or irrational at {sym} = {n}")
    return Fraction(int(v.p), int(v.q))


# ---------------------------------------------------------------------------
# the recursion
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class HullRecursion:
    """A positive multilinear tree recursion of dimension ``dim`` (see the module docstring).

    ``T`` holds the nonzero entries ``{(i, j, l): coefficient}``; ``P`` is a ``dim x dim``
    matrix of rational functions of ``c``; ``F`` a length-``dim`` vector of rational functions
    of ``k``."""
    dim: int
    e: tuple
    T: tuple            # sorted ((i, j, l), Fraction)
    P: tuple            # dim x dim sympy expressions in c
    F: tuple            # dim sympy expressions in k
    z0: int = 0

    def T_at(self, i, j, k) -> Fraction:
        return dict(self.T).get((i, j, k), Fraction(0))

    def P_at(self, c: int):
        return tuple(tuple(_at(self.P[i][j], C_SYM, c, f"P[{i}][{j}]") for j in range(self.dim))
                     for i in range(self.dim))

    def F_at(self, k: int):
        return tuple(_at(self.F[i], K_SYM, k, f"F[{i}]") for i in range(self.dim))

    def mul(self, x, z):
        out = [Fraction(0)] * self.dim
        for (i, j, k), t in self.T:
            out[i] += t * x[j] * z[k]
        return tuple(out)

    def plant(self, c: int, x, Pc=None):
        Pc = Pc if Pc is not None else self.P_at(c)
        return tuple(sum((Pc[i][j] * x[j] for j in range(self.dim)), Fraction(0))
                     for i in range(self.dim))

    def root(self, k: int, x, Fk=None) -> Fraction:
        Fk = Fk if Fk is not None else self.F_at(k)
        return sum((Fk[i] * x[i] for i in range(self.dim)), Fraction(0))


def hull_recursion(*, dim, e, T, P, F, z0=0) -> HullRecursion:
    """Validate the SHAPES and exactness of a recursion (signs are checked per N later)."""
    if not isinstance(dim, int) or dim < 1:
        raise ValueError(f"REFUSED: dim = {dim!r} must be an integer >= 1")
    if len(e) != dim:
        raise ValueError("REFUSED: e has the wrong length")
    ee = tuple(_frac(v, "e") for v in e)
    TT = {}
    for key, v in dict(T).items():
        if len(key) != 3 or not all(isinstance(t, int) and 0 <= t < dim for t in key):
            raise ValueError(f"REFUSED: T index {key!r} out of range")
        fv = _frac(v, f"T{key}")
        if fv != 0:
            TT[tuple(key)] = fv
    if len(P) != dim or any(len(row) != dim for row in P):
        raise ValueError("REFUSED: P must be a dim x dim matrix")
    PP = tuple(tuple(_expr(P[i][j], C_SYM, f"P[{i}][{j}]") for j in range(dim))
               for i in range(dim))
    if len(F) != dim:
        raise ValueError("REFUSED: F has the wrong length")
    FF = tuple(_expr(F[i], K_SYM, f"F[{i}]") for i in range(dim))
    if not isinstance(z0, int) or not 0 <= z0 < dim:
        raise ValueError(f"REFUSED: z0 = {z0!r} out of range")
    return HullRecursion(dim=dim, e=ee, T=tuple(sorted(TT.items())), P=PP, F=FF, z0=z0)


def sign_failures(rec: HullRecursion, N: int, *, strict: bool) -> list:
    """Every violated sign condition (empty = all hold), mirroring `Rec.Signs` + the F checks."""
    D, z = rec.dim, rec.z0
    bad = []
    if any(v < 0 for v in rec.e):
        bad.append("e has a negative entry")
    if not rec.e[z] > 0:
        bad.append(f"e[{z}] is not positive")
    if any(v < 0 for _, v in rec.T):
        bad.append("T has a negative coefficient")
    if not rec.T_at(z, z, z) > 0:
        bad.append(f"T[{z}][{z}][{z}] is not positive")
    for j in range(D):
        if not any(rec.T_at(i, j, z) > 0 for i in range(D)):
            bad.append(f"no T[i][{j}][{z}] > 0 (coordinate {j} of a bundle is invisible)")
        if not any(rec.T_at(i, z, j) > 0 for i in range(D)):
            bad.append(f"no T[i][{z}][{j}] > 0 (coordinate {j} of a child is invisible)")
    for c in range(N):
        Pc = rec.P_at(c)
        if any(Pc[i][j] < 0 for i in range(D) for j in range(D)):
            bad.append(f"P_{c} has a negative entry")
        if not Pc[z][z] > 0:
            bad.append(f"P_{c}[{z}][{z}] is not positive")
        for j in range(D):
            if not any(Pc[i][j] > 0 for i in range(D)):
                bad.append(f"column {j} of P_{c} has no positive entry")
    for k in range(1, N):
        Fk = rec.F_at(k)
        if any(v < 0 for v in Fk):
            bad.append(f"F_{k} has a negative entry")
        if strict and not all(v > 0 for v in Fk):
            bad.append(f"F_{k} is not strictly positive (needed for the maximizer statement)")
    return bad


# ---------------------------------------------------------------------------
# the hull dynamic program (exact)
# ---------------------------------------------------------------------------

def _dot(a, x) -> Fraction:
    return sum((ai * xi for ai, xi in zip(a, x)), Fraction(0))


def _simplex_max(c, A, b):
    """Exact two-phase simplex (Bland's rule) in Fractions: maximize c.z subject to A z = b, z >= 0.
    Returns (optimum, z), or raises ValueError if infeasible or unbounded. Self-contained so that the
    emitter works with every supported sympy version (sympy.solvers.simplex needs sympy >= 1.13)."""
    m, n = len(A), len(c)
    A = [[Fraction(v) for v in row] for row in A]
    b = [Fraction(v) for v in b]
    for i in range(m):                      # make b >= 0
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]
    # tableau with artificials a_0..a_{m-1} in columns n..n+m-1
    T = [A[i] + [Fraction(1 if j == i else 0) for j in range(m)] + [b[i]] for i in range(m)]
    basis = [n + i for i in range(m)]
    N = n + m

    def pivot(r, col):
        pv = T[r][col]
        T[r] = [v / pv for v in T[r]]
        for i in range(m):
            if i != r and T[i][col] != 0:
                f = T[i][col]
                T[i] = [vi - f * vr for vi, vr in zip(T[i], T[r])]
        basis[r] = col

    def run(cost, allowed):
        while True:
            # reduced costs for maximization: cost_j - sum cost_B T[.,j]
            enter = None
            for j in range(N):
                if j in basis or not allowed(j):
                    continue
                rc = cost[j] - sum(cost[basis[i]] * T[i][j] for i in range(m))
                if rc > 0:
                    enter = j
                    break                   # Bland: smallest index
            if enter is None:
                return
            best, r = None, None
            for i in range(m):
                if T[i][enter] > 0:
                    ratio = T[i][-1] / T[i][enter]
                    if best is None or ratio < best or (ratio == best and basis[i] < basis[r]):
                        best, r = ratio, i
            if r is None:
                raise ValueError("unbounded")
            pivot(r, enter)

    # phase I: maximize -sum(artificials)
    cost1 = [Fraction(0)] * n + [Fraction(-1)] * m
    run(cost1, lambda j: True)
    if sum(T[i][-1] for i in range(m) if basis[i] >= n) != 0:
        raise ValueError("infeasible")
    for i in range(m):                      # drive remaining (zero) artificials out of the basis
        if basis[i] >= n:
            for j in range(n):
                if T[i][j] != 0:
                    pivot(i, j)
                    break
    cost2 = [Fraction(v) for v in c] + [Fraction(0)] * m
    run(cost2, lambda j: j < n)
    z = [Fraction(0)] * n
    for i in range(m):
        if basis[i] < n:
            z[basis[i]] = T[i][-1]
    return sum((ci * zi for ci, zi in zip(c, z)), Fraction(0)), z


def _lp_dominance(pts, x):
    """Maximize sum(s) s.t. sum lam_i pts_i - s = x, lam >= 0, sum lam = 1, s >= 0 (exact).
    Returns (optimum, weights)."""
    D, k = len(x), len(pts)
    # variables: lam_0..lam_{k-1}, s_0..s_{D-1}
    A = [[Fraction(1)] * k + [Fraction(0)] * D]
    b = [Fraction(1)]
    for d in range(D):
        A.append([Fraction(p[d]) for p in pts] + [Fraction(-1 if e == d else 0) for e in range(D)])
        b.append(Fraction(x[d]))
    c = [Fraction(0)] * k + [Fraction(1)] * D
    opt, z = _simplex_max(c, A, b)
    return opt, z[:k]


def _dominates(y, x) -> bool:
    return all(a >= b for a, b in zip(y, x)) and y != x


def kept_points(cands) -> list:
    """K(C): the distinct candidates that maximize some strictly positive covector over C
    (hull vertices and points on hull edges; ties kept), sorted."""
    pts = sorted(set(cands))
    par = [x for x in pts if not any(_dominates(y, x) for y in pts)]
    if len(par) <= 1 or len(par[0]) == 1:
        return par
    if len(par[0]) == 2:
        # upper-right chain, collinear points kept (x ascending, y strictly descending)
        par.sort()
        out = []
        for p in par:
            while len(out) >= 2:
                a, b = out[-2], out[-1]
                cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
                if cross > 0:
                    out.pop()
                else:
                    break
            out.append(p)
        return out
    return [x for x in par if _lp_dominance(par, x)[0] == 0]


def witness_for(K, x):
    """('kept', i) or ('dom', weights) for candidate ``x`` against the kept list ``K``."""
    for i, p in enumerate(K):
        if p == x:
            return ("kept", i)
    for i, p in enumerate(K):
        if _dominates(p, x):
            return ("dom", tuple(Fraction(1) if t == i else Fraction(0) for t in range(len(K))))
    if len(x) == 2:
        # a chain edge [a, b] whose first-coordinate range covers x[0]
        for i in range(len(K) - 1):
            a, b = K[i], K[i + 1]
            if a[0] <= x[0] <= b[0] and a[0] < b[0]:
                lam = (b[0] - x[0]) / (b[0] - a[0])
                y1 = lam * a[1] + (1 - lam) * b[1]
                if y1 > x[1]:
                    w = [Fraction(0)] * len(K)
                    w[i], w[i + 1] = lam, 1 - lam
                    return ("dom", tuple(w))
    opt, w = _lp_dominance(K, x)
    if opt > 0:
        return ("dom", tuple(w))
    raise ValueError(f"REFUSED: candidate {x} is neither kept nor dominated (internal error)")


def _combo(w, K, D):
    return tuple(sum((w[i] * K[i][d] for i in range(len(K))), Fraction(0)) for d in range(D))


def witness_ok(K, x, wit) -> bool:
    """Exact mirror of the Lean `WitOK`."""
    kind, data = wit
    if kind == "kept":
        return 0 <= data < len(K) and K[data] == x
    w = data
    if len(w) != len(K) or any(c < 0 for c in w) or sum(w) != 1:
        return False
    y = _combo(w, K, len(x))
    return all(a <= b for a, b in zip(x, y)) and any(a < b for a, b in zip(x, y))


def cand_bundle(rec, KB, KH, s, c):
    """Candidates of bundle class (s, c) in the Lean `candB` order, with provenance."""
    if c == 0:
        return [(rec.e, None)] if s == 0 else []
    out = []
    for jp in range(s):
        j = jp + 1
        for bi, p in enumerate(KB.get((s - j, c - 1), [])):
            for hi, q in enumerate(KH.get(j, [])):
                out.append((rec.mul(p, q), (j, bi, hi)))
    return out


def cand_branch(rec, KB, m, Pcache):
    """Candidates of branch class m in the Lean `candH` order, with provenance."""
    out = []
    for c in range(m):
        for bi, p in enumerate(KB.get((m - 1, c), [])):
            out.append((rec.plant(c, p, Pcache[c]), (c, bi)))
    return out


# trees: a planted tree / rooted tree is the sorted tuple of its children (leaf = ())

def _tsort(children) -> tuple:
    return tuple(sorted(children))


@dataclass(frozen=True)
class HullDominanceCert:
    rec: HullRecursion
    N: int
    KB: tuple           # sorted ((s, c), tuple of points)
    KH: tuple           # sorted (m, tuple of points)
    WB: tuple           # sorted ((s, c), tuple of witnesses)
    WH: tuple           # sorted (m, tuple of witnesses)
    values: tuple       # ((n, M_n), ...) for n = 2..N
    maximizers: tuple   # ((n, (rooted tree, ...)), ...) one rooting per isomorphism class
    strict: bool        # emit the maximizer statement (F_k > 0)
    label: str = ""
    checked: bool = True

    def kb(self):
        return dict(self.KB)

    def kh(self):
        return dict(self.KH)

    def value(self, n):
        return dict(self.values)[n]

    @property
    def n_candidates(self) -> int:
        return sum(len(w) for _, w in self.WB) + sum(len(w) for _, w in self.WH)


def _canon_unrooted(tree) -> str:
    """Canonical string of the unrooted tree underlying a rooted tree (AHU at the centre)."""
    adj = [[]]

    def add(t, parent):
        v = len(adj)
        adj.append([parent])
        adj[parent].append(v)
        for ch in t:
            add(ch, v)

    for ch in tree:
        add(ch, 0)
    n = len(adj)
    if n == 1:
        return "()"
    deg = [len(a) for a in adj]
    layer = [v for v in range(n) if deg[v] == 1]
    rem = n
    while rem > 2:
        rem -= len(layer)
        nl = []
        for v in layer:
            for u in adj[v]:
                deg[u] -= 1
                if deg[u] == 1:
                    nl.append(u)
        layer = nl

    def enc(v, p):
        return "(" + "".join(sorted(enc(u, v) for u in adj[v] if u != p)) + ")"

    if len(layer) == 1:
        return enc(layer[0], -1)
    a, b = layer
    return "B" + "".join(sorted([enc(a, b), enc(b, a)]))


def tree_size(t) -> int:
    return 1 + sum(tree_size(c) for c in t)


def eval_pi(rec: HullRecursion, t) -> Fraction:
    """pi of a rooted tree (tuple of children) by the recursion, children folded like Lean."""
    def bundle(children):
        x = rec.e
        for ch in reversed(children):   # bundle (t :: l) = bundle l (*) branch t
            x = rec.mul(x, branch(ch))
        return x

    def branch(tt):
        return rec.plant(len(tt), bundle(tt))

    return rec.root(len(t), bundle(t))


def hull_dominance_certificate(*, recursion, N, maximizers=True, label="",
                               payload_cap=20000, check: bool = True) -> HullDominanceCert:
    """Run the exact hull DP for trees on at most ``N`` vertices and build the certificate.

    ``recursion``: a :class:`HullRecursion` or the keyword dict of :func:`hull_recursion`.
    ``maximizers``: also emit the maximizer statement (needs strictly positive F_k)."""
    rec = recursion if isinstance(recursion, HullRecursion) else hull_recursion(**recursion)
    if not isinstance(N, int) or N < 2 or N > _MAX_N:
        raise ValueError(f"REFUSED: N = {N!r} must be an integer in [2, {_MAX_N}]")
    bad = sign_failures(rec, N, strict=bool(maximizers))
    if bad:
        raise ValueError("REFUSED: sign conditions fail: " + "; ".join(bad))
    Pcache = {c: rec.P_at(c) for c in range(N)}
    KB: dict = {}
    KH: dict = {}
    WB: dict = {}
    WH: dict = {}
    payB: dict = {}     # (s, c) -> list (per kept point) of sets of child-multisets
    payH: dict = {}     # m -> list (per kept point) of sets of planted trees

    def build(cands, pay_of):
        if len(cands) > _MAX_CAND:
            raise ValueError(f"REFUSED: a class has {len(cands)} candidates (cap {_MAX_CAND})")
        K = kept_points([x for x, _ in cands])
        idx = {p: i for i, p in enumerate(K)}
        wits = tuple(witness_for(K, x) for x, _ in cands)
        pays = [set() for _ in K]
        for (x, prov), _w in zip(cands, wits):
            i = idx.get(x)
            if i is not None:
                pays[i] |= pay_of(prov)
                if len(pays[i]) > payload_cap:
                    raise ValueError("REFUSED: payload cap exceeded (too many tied trees)")
        return tuple(K), wits, pays

    for s in range(N):
        for c in range(s + 1):
            cands = cand_bundle(rec, KB, KH, s, c)

            def pay_b(prov, s=s, c=c):
                if prov is None:
                    return {()}
                j, bi, hi = prov
                return {_tsort(bun + (t,)) for bun in payB[(s - j, c - 1)][bi]
                        for t in payH[j][hi]}

            K, wits, pays = build(cands, pay_b)
            KB[(s, c)], WB[(s, c)], payB[(s, c)] = K, wits, pays
        m = s + 1
        if m < N:
            cands = cand_branch(rec, KB, m, Pcache)

            def pay_h(prov, m=m):
                c, bi = prov
                return set(payB[(m - 1, c)][bi])

            K, wits, pays = build(cands, pay_h)
            KH[m], WH[m], payH[m] = K, wits, pays
    values = []
    maxs = []
    for n in range(2, N + 1):
        best = None
        for k in range(1, n):
            Fk = rec.F_at(k)
            for p in KB.get((n - 1, k), ()):
                v = rec.root(k, p, Fk)
                best = v if best is None or v > best else best
        trees = {}
        for k in range(1, n):
            Fk = rec.F_at(k)
            for i, p in enumerate(KB.get((n - 1, k), ())):
                if rec.root(k, p, Fk) == best:
                    for bun in payB[(n - 1, k)][i]:
                        key = _canon_unrooted(bun)
                        if key not in trees or bun < trees[key]:
                            trees[key] = bun
        values.append((n, best))
        maxs.append((n, tuple(trees[k] for k in sorted(trees))))
    cert = HullDominanceCert(
        rec=rec, N=N, KB=tuple(sorted(KB.items())), KH=tuple(sorted(KH.items())),
        WB=tuple(sorted(WB.items())), WH=tuple(sorted(WH.items())),
        values=tuple(values), maximizers=tuple(maxs), strict=bool(maximizers), label=label,
        checked=check)
    if check:
        verify_certificate(cert)
    return cert


def verify_certificate(cert: HullDominanceCert) -> None:
    """Exact re-check of everything the Lean side decides, in the Lean enumeration order."""
    rec, N = cert.rec, cert.N
    bad = sign_failures(rec, N, strict=cert.strict)
    if bad:
        raise ValueError("REFUSED: sign conditions fail: " + "; ".join(bad))
    KB, KH, WB, WH = cert.kb(), cert.kh(), dict(cert.WB), dict(cert.WH)
    Pcache = {c: rec.P_at(c) for c in range(N)}
    z = rec.z0
    for s in range(N):
        for c in range(s + 1):
            K = KB.get((s, c), ())
            cands = [x for x, _ in cand_bundle(rec, KB, KH, s, c)]
            wits = WB.get((s, c), ())
            if len(cands) != len(wits):
                raise ValueError(f"REFUSED: bundle class {(s, c)}: {len(cands)} candidates, "
                                 f"{len(wits)} witnesses")
            for x, w in zip(cands, wits):
                if not witness_ok(K, x, w):
                    raise ValueError(f"REFUSED: bundle class {(s, c)}: witness {w} fails for {x}")
            for p in K:
                if any(v < 0 for v in p) or not p[z] > 0:
                    raise ValueError(f"REFUSED: kept point {p} not nonnegative / z0-positive")
    for m in range(1, N):
        K = KH.get(m, ())
        cands = [x for x, _ in cand_branch(rec, KB, m, Pcache)]
        wits = WH.get(m, ())
        if len(cands) != len(wits):
            raise ValueError(f"REFUSED: branch class {m}: candidate/witness count mismatch")
        for x, w in zip(cands, wits):
            if not witness_ok(K, x, w):
                raise ValueError(f"REFUSED: branch class {m}: witness {w} fails for {x}")
        for p in K:
            if any(v < 0 for v in p) or not p[z] > 0:
                raise ValueError(f"REFUSED: kept point {p} not nonnegative / z0-positive")
    for n, v in cert.values:
        for k in range(1, n):
            for p in KB.get((n - 1, k), ()):
                if rec.root(k, p) > v:
                    raise ValueError(f"REFUSED: n = {n}: a kept root bundle exceeds the claim {v}")
        trees = dict(cert.maximizers)[n]
        if not trees:
            raise ValueError(f"REFUSED: n = {n}: no attaining tree")
        for t in trees:
            if tree_size(t) != n or eval_pi(rec, t) != v:
                raise ValueError(f"REFUSED: n = {n}: listed tree does not attain {v}")


def certify_affine_hull_dominance_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``, a dict of the keyword arguments of
    :func:`hull_dominance_certificate`."""
    spec = dict(family.special[1](pt))
    cert = hull_dominance_certificate(**spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1 + cert.n_candidates


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

def _q(x) -> str:
    """An exact rational as a Lean rational literal."""
    x = Fraction(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)" if x.numerator < 0 else str(x.numerator)
    if x.numerator < 0:
        return f"(-{-x.numerator}/{x.denominator} : ℚ)"
    return f"({x.numerator}/{x.denominator} : ℚ)"


def _qv(x) -> str:
    """A rational in a statement position (always typed)."""
    x = Fraction(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    if x.numerator < 0:
        return f"(-{-x.numerator} / {x.denominator} : ℚ)"
    return f"({x.numerator} / {x.denominator} : ℚ)"


def _vec(p) -> str:
    return "![" + ", ".join(_q(v) for v in p) + "]"


def _expr_lean(e: sp.Expr, sym: sp.Symbol, var: str) -> str:
    """A rational function of the child count, as a Lean ℚ expression in ``((var : ℕ) : ℚ)``."""
    e = sp.sympify(e)

    def go(t) -> str:
        if t.is_Rational:
            return _q(Fraction(int(t.p), int(t.q)))
        if t == sym:
            return f"({var} : ℚ)"
        if t.is_Add:
            return "(" + " + ".join(go(a) for a in t.args) + ")"
        if t.is_Mul:
            return "(" + " * ".join(go(a) for a in t.args) + ")"
        if t.is_Pow and t.exp.is_Integer:
            n = int(t.exp)
            if n == -1:
                return f"({go(t.base)})⁻¹"
            if n < 0:
                return f"({go(t.base)} ^ {-n})⁻¹"
            return f"({go(t.base)} ^ {n})"
        raise ValueError(f"REFUSED: cannot render {t}")

    return go(sp.cancel(sp.together(e)) if not e.is_Rational else e)


def _tree_lean(t) -> str:
    if not t:
        return "RTree.node []"
    return "RTree.node [" + ", ".join(_tree_lean(c) for c in t) + "]"


def _wit_lean(w) -> str:
    kind, data = w
    if kind == "kept":
        return f".kept {data}"
    return ".dom [" + ", ".join(_q(c) for c in data) + "]"


def _fin_table(rec: HullRecursion) -> str:
    D = rec.dim
    return ("![" + ", ".join(
        "![" + ", ".join(
            "![" + ", ".join(_q(rec.T_at(i, j, k)) for k in range(D)) + "]"
            for j in range(D)) + "]"
        for i in range(D)) + "]")


_GENERIC = r"""/-! ## Generic affine hull dominance (emitted once per file)

A positive multilinear tree recursion, domination by convex combinations in dual form, the
exchange induction, the exact maximum and the maximizer structure theorem.
conjecture1_proved = False. -/

namespace HullDom

/-- States of a branch or a bundle: vectors of rationals. -/
abbrev Vec (D : ℕ) := Fin D → ℚ

/-- A positive multilinear tree recursion of dimension `D`. -/
structure Rec (D : ℕ) where
  /-- the value of the empty bundle -/
  e : Vec D
  /-- adding a child: `(x ⊗ z) i = ∑ j l, T i j l * x j * z l` -/
  T : Fin D → Fin D → Fin D → ℚ
  /-- planting a bundle of `c` children: `(P c x) i = ∑ j, P c i j * x j` -/
  P : ℕ → Fin D → Fin D → ℚ
  /-- the root functional for a root with `k` children -/
  F : ℕ → Fin D → ℚ

/-- Finite rooted trees; the children form a list. -/
inductive RTree : Type
  | node : List RTree → RTree

variable {D : ℕ}

def dot (a x : Vec D) : ℚ := ∑ i, a i * x i

namespace Rec

def mul (R : Rec D) (x z : Vec D) : Vec D := fun i => ∑ j, ∑ l, R.T i j l * x j * z l

def plant (R : Rec D) (c : ℕ) (x : Vec D) : Vec D := fun i => ∑ j, R.P c i j * x j

def root (R : Rec D) (k : ℕ) (x : Vec D) : ℚ := dot (R.F k) x

end Rec

mutual
/-- Number of vertices of a tree. -/
def RTree.size : RTree → ℕ
  | .node l => RTree.sizeL l + 1
/-- Total number of vertices of a list of trees. -/
def RTree.sizeL : List RTree → ℕ
  | [] => 0
  | t :: l => t.size + RTree.sizeL l
end

mutual
/-- The value of a planted branch. -/
def Rec.branch (R : Rec D) : RTree → Vec D
  | .node l => R.plant l.length (R.bundle l)
/-- The value of a bundle of branches. -/
def Rec.bundle (R : Rec D) : List RTree → Vec D
  | [] => R.e
  | t :: l => R.mul (R.bundle l) (R.branch t)
end

/-- The quantity: the root functional applied to the bundle of the root's children. -/
def Rec.pi (R : Rec D) : RTree → ℚ
  | .node l => R.root l.length (R.bundle l)

theorem RTree.length_le_sizeL : ∀ l : List RTree, l.length ≤ RTree.sizeL l
  | [] => le_rfl
  | t :: l => by
    have := RTree.length_le_sizeL l
    simp only [List.length_cons, RTree.sizeL]
    cases t with
    | node l' => simp only [RTree.size]; omega

/-! ### Domination by a convex combination, in dual form -/

/-- `x` is weakly dominated by the convex hull of `K`: every nonnegative covector is at least
as large at some point of `K`. -/
def Dom (K : List (Vec D)) (x : Vec D) : Prop :=
  ∀ a : Vec D, (∀ i, 0 ≤ a i) → ∃ p ∈ K, dot a x ≤ dot a p

/-- `x` is strictly dominated: every strictly positive covector is strictly larger at some
point of `K`. -/
def SDom (K : List (Vec D)) (x : Vec D) : Prop :=
  ∀ a : Vec D, (∀ i, 0 < a i) → ∃ p ∈ K, dot a x < dot a p

/-- A convex combination `∑ w_k K_k`. -/
def combo : List ℚ → List (Vec D) → Vec D
  | c :: w, p :: K => fun i => c * p i + combo w K i
  | _, _ => fun _ => 0

/-- A witness for one candidate: it is a kept point (by index), or it is dominated by a convex
combination of the kept points, strictly in at least one coordinate. -/
inductive Wit : Type
  | kept (i : ℕ)
  | dom (w : List ℚ)

def WitOK (K : List (Vec D)) (x : Vec D) : Wit → Prop
  | .kept i => i < K.length ∧ ∀ j, K.getD i 0 j = x j
  | .dom w => w.length = K.length ∧ (∀ c ∈ w, 0 ≤ c) ∧ w.sum = 1 ∧
      (∀ j, x j ≤ combo w K j) ∧ ∃ j, x j < combo w K j

instance (K : List (Vec D)) (x : Vec D) : (w : Wit) → Decidable (WitOK K x w)
  | .kept i => inferInstanceAs (Decidable (i < K.length ∧ ∀ j, K.getD i 0 j = x j))
  | .dom w => inferInstanceAs (Decidable (w.length = K.length ∧ (∀ c ∈ w, 0 ≤ c) ∧
      w.sum = 1 ∧ (∀ j, x j ≤ combo w K j) ∧ ∃ j, x j < combo w K j))

theorem dot_add (a u v : Vec D) : dot a (fun i => u i + v i) = dot a u + dot a v := by
  simp only [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul (a u : Vec D) (c : ℚ) : dot a (fun i => c * u i) = c * dot a u := by
  simp only [dot, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_zero (a : Vec D) : dot a (fun _ => 0) = 0 := by simp [dot]

theorem dot_combo (a : Vec D) :
    ∀ (w : List ℚ) (K : List (Vec D)), w.length = K.length →
      dot a (combo w K) = (List.zipWith (fun c p => c * dot a p) w K).sum
  | [], [], _ => by simp [combo, dot_zero]
  | c :: w, p :: K, h => by
    have ih := dot_combo a w K (by simpa using h)
    simp only [combo, List.zipWith_cons_cons, List.sum_cons]
    rw [dot_add, dot_smul, ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem zip_le (f : Vec D → ℚ) (M : ℚ) :
    ∀ (w : List ℚ) (K : List (Vec D)), w.length = K.length → (∀ c ∈ w, 0 ≤ c) →
      (∀ p ∈ K, f p ≤ M) → (List.zipWith (fun c p => c * f p) w K).sum ≤ w.sum * M
  | [], [], _, _, _ => by simp
  | c :: w, p :: K, h, hw, hK => by
    have ih := zip_le f M w K (by simpa using h) (fun c hc => hw c (by simp [hc]))
      (fun p hp => hK p (by simp [hp]))
    have h1 : c * f p ≤ c * M :=
      mul_le_mul_of_nonneg_left (hK p (by simp)) (hw c (by simp))
    simp only [List.zipWith_cons_cons, List.sum_cons]
    nlinarith
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

/-- A convex combination is below the best point of `K` for any covector. -/
theorem exists_ge_combo (a : Vec D) (w : List ℚ) (K : List (Vec D)) (hl : w.length = K.length)
    (hw : ∀ c ∈ w, 0 ≤ c) (hs : w.sum = 1) : ∃ p ∈ K, dot a (combo w K) ≤ dot a p := by
  classical
  have hne : K ≠ [] := by
    rintro rfl
    have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this; simp at hs
  obtain ⟨p, hp, hmax⟩ := K.toFinset.exists_max_image (fun p => dot a p)
    (by simpa [List.toFinset_nonempty_iff] using hne)
  refine ⟨p, by simpa using hp, ?_⟩
  rw [dot_combo a w K hl]
  have := zip_le (fun q => dot a q) (dot a p) w K hl hw (fun q hq => hmax q (by simpa using hq))
  simpa [hs] using this

theorem dom_of_mem {K : List (Vec D)} {x : Vec D} (h : x ∈ K) : Dom K x :=
  fun _ _ => ⟨x, h, le_rfl⟩

theorem dot_le_dot {a x y : Vec D} (ha : ∀ i, 0 ≤ a i) (h : ∀ i, x i ≤ y i) :
    dot a x ≤ dot a y :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (ha i)

theorem dot_lt_dot {a x y : Vec D} (ha : ∀ i, 0 < a i) (h : ∀ i, x i ≤ y i)
    (hj : ∃ j, x j < y j) : dot a x < dot a y := by
  obtain ⟨j, hj⟩ := hj
  exact Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (ha i).le)
    ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (ha j)⟩

/-- A checked witness makes the candidate kept, or strictly dominated; in both cases weakly
dominated. -/
theorem witOK_sound {K : List (Vec D)} {x : Vec D} {w : Wit} (h : WitOK K x w) :
    (x ∈ K ∨ SDom K x) ∧ Dom K x := by
  cases w with
  | kept i =>
    obtain ⟨hi, he⟩ := h
    have hx : x = K.getD i 0 := funext fun j => (he j).symm
    have hm : x ∈ K := by
      rw [hx, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact ⟨Or.inl hm, dom_of_mem hm⟩
  | dom w =>
    obtain ⟨hl, hw, hs, hle, hlt⟩ := h
    refine ⟨Or.inr fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨p, hp, hp'⟩ := exists_ge_combo a w K hl hw hs
      exact ⟨p, hp, lt_of_lt_of_le (dot_lt_dot ha hle hlt) hp'⟩
    · obtain ⟨p, hp, hp'⟩ := exists_ge_combo a w K hl hw hs
      exact ⟨p, hp, le_trans (dot_le_dot ha hle) hp'⟩

theorem forall2_exists {α β : Type} {Rl : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Rl l₁ l₂ → ∀ x ∈ l₁, ∃ y, Rl x y
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons (a := a) (b := b) h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, h⟩
    · exact forall2_exists t x hx

/-! ### Pulling covectors back through the recursion -/

namespace Rec

variable (R : Rec D)

theorem dot_mul_left (a x z : Vec D) :
    dot a (R.mul x z) = dot (fun j => ∑ i, ∑ l, a i * R.T i j l * z l) x := by
  simp only [dot, mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem dot_mul_right (a x z : Vec D) :
    dot a (R.mul x z) = dot (fun l => ∑ i, ∑ j, a i * R.T i j l * x j) z := by
  simp only [dot, mul, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ i, ∑ l, ∑ j, a i * (R.T i j l * x j * z l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, a i * (R.T i j l * x j * z l) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring

theorem dot_plant (a : Vec D) (c : ℕ) (x : Vec D) :
    dot a (R.plant c x) = dot (fun j => ∑ i, a i * R.P c i j) x := by
  simp only [dot, plant, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- Sign conditions on the recursion (checked per instance by `decide`), for child counts
below `N`: nonnegative coefficients, a positive `0`-th coordinate that propagates, and every
column reached from coordinate `0`, so strictly positive covectors pull back to strictly
positive covectors. -/
structure Signs (R : Rec D) (N : ℕ) (z0 : Fin D) : Prop where
  e_nn : ∀ i, 0 ≤ R.e i
  e_pos : 0 < R.e z0
  T_nn : ∀ i j l, 0 ≤ R.T i j l
  T_pos : 0 < R.T z0 z0 z0
  T_left : ∀ j, ∃ i, 0 < R.T i j z0
  T_right : ∀ l, ∃ i, 0 < R.T i z0 l
  P_nn : ∀ c < N, ∀ i j, 0 ≤ R.P c i j
  P_pos : ∀ c < N, 0 < R.P c z0 z0
  P_col : ∀ c < N, ∀ j, ∃ i, 0 < R.P c i j

end Rec

/-! ### Pulled-back covectors keep their sign -/

section Pull

variable {R : Rec D} {N : ℕ} {z0 : Fin D}

theorem pullL_nn (hT : ∀ i j l, 0 ≤ R.T i j l) {a z : Vec D} (ha : ∀ i, 0 ≤ a i)
    (hz : ∀ i, 0 ≤ z i) (j : Fin D) : 0 ≤ ∑ i, ∑ l, a i * R.T i j l * z l :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (ha i) (hT i j l)) (hz l)

theorem pullR_nn (hT : ∀ i j l, 0 ≤ R.T i j l) {a x : Vec D} (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ i, 0 ≤ x i) (l : Fin D) : 0 ≤ ∑ i, ∑ j, a i * R.T i j l * x j :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (ha i) (hT i j l)) (hx j)

theorem pullP_nn {c : ℕ} (hP : ∀ i j, 0 ≤ R.P c i j) {a : Vec D} (ha : ∀ i, 0 ≤ a i)
    (j : Fin D) : 0 ≤ ∑ i, a i * R.P c i j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hP i j)

theorem pullL_pos (hS : R.Signs N z0) {a z : Vec D} (ha : ∀ i, 0 < a i)
    (hz : ∀ i, 0 ≤ z i) (hz0 : 0 < z z0) (j : Fin D) :
    0 < ∑ i, ∑ l, a i * R.T i j l * z l := by
  obtain ⟨i, hi⟩ := hS.T_left j
  have hnn : ∀ i l, 0 ≤ a i * R.T i j l * z l := fun i l =>
    mul_nonneg (mul_nonneg (ha i).le (hS.T_nn i j l)) (hz l)
  have h1 : 0 < a i * R.T i j z0 * z z0 := mul_pos (mul_pos (ha i) hi) hz0
  have h2 : a i * R.T i j z0 * z z0 ≤ ∑ l, a i * R.T i j l * z l :=
    Finset.single_le_sum (fun l _ => hnn i l) (Finset.mem_univ z0)
  have h3 : ∑ l, a i * R.T i j l * z l ≤ ∑ i, ∑ l, a i * R.T i j l * z l :=
    Finset.single_le_sum (f := fun i => ∑ l, a i * R.T i j l * z l)
      (fun i _ => Finset.sum_nonneg fun l _ => hnn i l) (Finset.mem_univ i)
  linarith

theorem pullR_pos (hS : R.Signs N z0) {a x : Vec D} (ha : ∀ i, 0 < a i)
    (hx : ∀ i, 0 ≤ x i) (hx0 : 0 < x z0) (l : Fin D) :
    0 < ∑ i, ∑ j, a i * R.T i j l * x j := by
  obtain ⟨i, hi⟩ := hS.T_right l
  have hnn : ∀ i j, 0 ≤ a i * R.T i j l * x j := fun i j =>
    mul_nonneg (mul_nonneg (ha i).le (hS.T_nn i j l)) (hx j)
  have h1 : 0 < a i * R.T i z0 l * x z0 := mul_pos (mul_pos (ha i) hi) hx0
  have h2 : a i * R.T i z0 l * x z0 ≤ ∑ j, a i * R.T i j l * x j :=
    Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ z0)
  have h3 : ∑ j, a i * R.T i j l * x j ≤ ∑ i, ∑ j, a i * R.T i j l * x j :=
    Finset.single_le_sum (f := fun i => ∑ j, a i * R.T i j l * x j)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ i)
  linarith

theorem pullP_pos (hS : R.Signs N z0) {c : ℕ} (hc : c < N) {a : Vec D}
    (ha : ∀ i, 0 < a i) (j : Fin D) : 0 < ∑ i, a i * R.P c i j := by
  obtain ⟨i, hi⟩ := hS.P_col c hc j
  have h1 : 0 < a i * R.P c i j := mul_pos (ha i) hi
  have h2 : a i * R.P c i j ≤ ∑ i, a i * R.P c i j :=
    Finset.single_le_sum (f := fun i => a i * R.P c i j)
      (fun i _ => mul_nonneg (ha i).le (hS.P_nn c hc i j)) (Finset.mem_univ i)
  linarith

/-! ### One step of the recursion transports domination -/

/-- Adding a child: weak domination (the exchange argument). -/
theorem mul_dom (hS : R.Signs N z0) {K1 K2 K : List (Vec D)} {x z : Vec D}
    (hx : Dom K1 x) (hz : Dom K2 z) (hz0 : ∀ i, 0 ≤ z i) (hK1 : ∀ p ∈ K1, ∀ i, 0 ≤ p i)
    (hc : ∀ p ∈ K1, ∀ q ∈ K2, Dom K (R.mul p q)) : Dom K (R.mul x z) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullL_nn hS.T_nn ha hz0)
  obtain ⟨q, hq, h2⟩ := hz _ (pullR_nn hS.T_nn ha (hK1 p hp))
  obtain ⟨r, hr, h3⟩ := hc p hp q hq a ha
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_mul_left a x z
  have e2 := R.dot_mul_left a p z
  have e3 := R.dot_mul_right a p z
  have e4 := R.dot_mul_right a p q
  linarith

/-- Adding a child to a strictly dominated bundle. -/
theorem mul_sdom_left (hS : R.Signs N z0) {K1 K2 K : List (Vec D)} {x z : Vec D}
    (hx : SDom K1 x) (hz : Dom K2 z) (hz0 : ∀ i, 0 ≤ z i) (hzp : 0 < z z0)
    (hK1 : ∀ p ∈ K1, ∀ i, 0 ≤ p i)
    (hc : ∀ p ∈ K1, ∀ q ∈ K2, Dom K (R.mul p q)) : SDom K (R.mul x z) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullL_pos hS ha hz0 hzp)
  obtain ⟨q, hq, h2⟩ := hz _ (pullR_nn hS.T_nn (fun i => (ha i).le) (hK1 p hp))
  obtain ⟨r, hr, h3⟩ := hc p hp q hq a (fun i => (ha i).le)
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_mul_left a x z
  have e2 := R.dot_mul_left a p z
  have e3 := R.dot_mul_right a p z
  have e4 := R.dot_mul_right a p q
  linarith

/-- Adding a strictly dominated child to a kept bundle. -/
theorem mul_sdom_right (hS : R.Signs N z0) {K1 K2 K : List (Vec D)} {x z : Vec D}
    (hx : x ∈ K1) (hx0 : ∀ i, 0 ≤ x i) (hxp : 0 < x z0) (hz : SDom K2 z)
    (hc : ∀ p ∈ K1, ∀ q ∈ K2, Dom K (R.mul p q)) : SDom K (R.mul x z) := by
  intro a ha
  obtain ⟨q, hq, h2⟩ := hz _ (pullR_pos hS ha hx0 hxp)
  obtain ⟨r, hr, h3⟩ := hc x hx q hq a (fun i => (ha i).le)
  refine ⟨r, hr, ?_⟩
  have e3 := R.dot_mul_right a x z
  have e4 := R.dot_mul_right a x q
  linarith

/-- Planting: weak domination. -/
theorem plant_dom (hS : R.Signs N z0) {c : ℕ} (hcN : c < N) {K1 K : List (Vec D)}
    {x : Vec D} (hx : Dom K1 x) (hc : ∀ p ∈ K1, Dom K (R.plant c p)) :
    Dom K (R.plant c x) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullP_nn (hS.P_nn c hcN) ha)
  obtain ⟨r, hr, h3⟩ := hc p hp a ha
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_plant a c x
  have e2 := R.dot_plant a c p
  linarith

/-- Planting a strictly dominated bundle. -/
theorem plant_sdom (hS : R.Signs N z0) {c : ℕ} (hcN : c < N) {K1 K : List (Vec D)}
    {x : Vec D} (hx : SDom K1 x) (hc : ∀ p ∈ K1, Dom K (R.plant c p)) :
    SDom K (R.plant c x) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullP_pos hS hcN ha)
  obtain ⟨r, hr, h3⟩ := hc p hp a (fun i => (ha i).le)
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_plant a c x
  have e2 := R.dot_plant a c p
  linarith

theorem mul_nn (hT : ∀ i j l, 0 ≤ R.T i j l) {x z : Vec D} (hx : ∀ i, 0 ≤ x i)
    (hz : ∀ i, 0 ≤ z i) (i : Fin D) : 0 ≤ R.mul x z i :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (hT i j l) (hx j)) (hz l)

theorem mul_pos0 (hS : R.Signs N z0) {x z : Vec D} (hx : ∀ i, 0 ≤ x i)
    (hz : ∀ i, 0 ≤ z i) (hxp : 0 < x z0) (hzp : 0 < z z0) : 0 < R.mul x z z0 := by
  have hnn : ∀ j l, 0 ≤ R.T z0 j l * x j * z l := fun j l =>
    mul_nonneg (mul_nonneg (hS.T_nn z0 j l) (hx j)) (hz l)
  have h1 : 0 < R.T z0 z0 z0 * x z0 * z z0 := mul_pos (mul_pos hS.T_pos hxp) hzp
  have h2 : R.T z0 z0 z0 * x z0 * z z0 ≤ ∑ l, R.T z0 z0 l * x z0 * z l :=
    Finset.single_le_sum (f := fun l => R.T z0 z0 l * x z0 * z l)
      (fun l _ => hnn z0 l) (Finset.mem_univ z0)
  have h3 : ∑ l, R.T z0 z0 l * x z0 * z l ≤ ∑ j, ∑ l, R.T z0 j l * x j * z l :=
    Finset.single_le_sum (f := fun j => ∑ l, R.T z0 j l * x j * z l)
      (fun j _ => Finset.sum_nonneg fun l _ => hnn j l) (Finset.mem_univ z0)
  show 0 < ∑ j, ∑ l, R.T z0 j l * x j * z l
  linarith

theorem plant_nn {c : ℕ} (hP : ∀ i j, 0 ≤ R.P c i j) {x : Vec D} (hx : ∀ i, 0 ≤ x i)
    (i : Fin D) : 0 ≤ R.plant c x i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hx j)

theorem plant_pos0 (hS : R.Signs N z0) {c : ℕ} (hc : c < N) {x : Vec D}
    (hx : ∀ i, 0 ≤ x i) (hxp : 0 < x z0) : 0 < R.plant c x z0 := by
  have h1 : 0 < R.P c z0 z0 * x z0 := mul_pos (hS.P_pos c hc) hxp
  have h2 : R.P c z0 z0 * x z0 ≤ ∑ j, R.P c z0 j * x j :=
    Finset.single_le_sum (f := fun j => R.P c z0 j * x j)
      (fun j _ => mul_nonneg (hS.P_nn c hc z0 j) (hx j)) (Finset.mem_univ z0)
  show 0 < ∑ j, R.P c z0 j * x j
  linarith

end Pull

/-! ### The certificate -/

/-- Kept hull points per class, and one witness per candidate.  `KB s c`: bundles of `c`
branches with `s` vertices in total; `KH m`: planted branches on `m` vertices. -/
structure Cert (D : ℕ) where
  KB : ℕ → ℕ → List (Vec D)
  KH : ℕ → List (Vec D)
  WB : ℕ → ℕ → List Wit
  WH : ℕ → List Wit

/-- Every candidate of the bundle class `(s, c)`: a kept bundle of `(s - j, c - 1)` joined with
a kept branch on `j` vertices, for every `j = 1..s`. -/
def candB (R : Rec D) (C : Cert D) (s c : ℕ) : List (Vec D) :=
  if c = 0 then (if s = 0 then [R.e] else [])
  else (List.range s).flatMap fun j' =>
    (C.KB (s - (j' + 1)) (c - 1)).flatMap fun p => (C.KH (j' + 1)).map fun q => R.mul p q

/-- Every candidate of the branch class `m`: a kept bundle of `(m - 1, c)`, planted. -/
def candH (R : Rec D) (C : Cert D) (m : ℕ) : List (Vec D) :=
  (List.range m).flatMap fun c => (C.KB (m - 1) c).map fun p => R.plant c p

/-- The decidable certificate: every candidate of every class below `N` carries a checked
witness, and every kept point is nonnegative with a positive `z0` coordinate. -/
abbrev Cert.Valid (R : Rec D) (C : Cert D) (N : ℕ) (z0 : Fin D) : Prop :=
  (∀ s < N, ∀ c ≤ s, List.Forall₂ (WitOK (C.KB s c)) (candB R C s c) (C.WB s c)) ∧
  (∀ m < N, 1 ≤ m → List.Forall₂ (WitOK (C.KH m)) (candH R C m) (C.WH m)) ∧
  (∀ s < N, ∀ c ≤ s, ∀ p ∈ C.KB s c, (∀ i, 0 ≤ p i) ∧ 0 < p z0) ∧
  (∀ m < N, 1 ≤ m → ∀ p ∈ C.KH m, (∀ i, 0 ≤ p i) ∧ 0 < p z0)

section Main

variable {R : Rec D} {C : Cert D} {N : ℕ} {z0 : Fin D}

theorem candB_sound (hC : C.Valid R N z0) {s c : ℕ} (hs : s < N) (hc : c ≤ s) :
    ∀ x ∈ candB R C s c, (x ∈ C.KB s c ∨ SDom (C.KB s c) x) ∧ Dom (C.KB s c) x := by
  intro x hx
  obtain ⟨w, hw⟩ := forall2_exists (hC.1 s hs c hc) x hx
  exact witOK_sound hw

theorem candH_sound (hC : C.Valid R N z0) {m : ℕ} (hm : m < N) (hm1 : 1 ≤ m) :
    ∀ x ∈ candH R C m, (x ∈ C.KH m ∨ SDom (C.KH m) x) ∧ Dom (C.KH m) x := by
  intro x hx
  obtain ⟨w, hw⟩ := forall2_exists (hC.2.1 m hm hm1) x hx
  exact witOK_sound hw

theorem mem_candB {s c j : ℕ} (hc : 1 ≤ c) (hj : 1 ≤ j) (hjs : j ≤ s) {p q : Vec D}
    (hp : p ∈ C.KB (s - j) (c - 1)) (hq : q ∈ C.KH j) : R.mul p q ∈ candB R C s c := by
  unfold candB
  rw [if_neg (by omega)]
  refine List.mem_flatMap.2 ⟨j - 1, List.mem_range.2 (by omega), ?_⟩
  have e : j - 1 + 1 = j := by omega
  rw [e]
  exact List.mem_flatMap.2 ⟨p, hp, List.mem_map.2 ⟨q, hq, rfl⟩⟩

theorem mem_candH {m c : ℕ} (hc : c < m) {p : Vec D} (hp : p ∈ C.KB (m - 1) c) :
    R.plant c p ∈ candH R C m :=
  List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, List.mem_map.2 ⟨p, hp, rfl⟩⟩

theorem RTree.size_pos (t : RTree) : 1 ≤ t.size := by
  cases t; simp [RTree.size]

/-- The value invariant of a class: nonnegative, positive `z0` coordinate, weakly dominated. -/
def Inv (z0 : Fin D) (K : List (Vec D)) (x : Vec D) : Prop :=
  (∀ i, 0 ≤ x i) ∧ 0 < x z0 ∧ Dom K x

mutual
/-- THE INDUCTION (weak part), branches. -/
theorem inv_branch (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ t : RTree, t.size < N → Inv z0 (C.KH t.size) (R.branch t)
  | .node l, h => by
    have hl : RTree.sizeL l < N := by simp only [RTree.size] at h; omega
    obtain ⟨h1, h2, h3⟩ := inv_bundle hS hC l hl
    have hlen := RTree.length_le_sizeL l
    have hcN : l.length < N := by omega
    simp only [Rec.branch, RTree.size]
    refine ⟨plant_nn (hS.P_nn _ hcN) h1, plant_pos0 hS hcN h1 h2, ?_⟩
    refine plant_dom hS hcN h3 fun p hp => ?_
    have hm := mem_candH (R := R) (m := RTree.sizeL l + 1) (c := l.length) (by omega)
      (by simpa using hp)
    exact (candH_sound hC (by simp only [RTree.size] at h; omega) (by omega) _ hm).2

/-- THE INDUCTION (weak part), bundles. -/
theorem inv_bundle (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ l : List RTree, RTree.sizeL l < N →
      Inv z0 (C.KB (RTree.sizeL l) l.length) (R.bundle l)
  | [], h => by
    simp only [Rec.bundle, RTree.sizeL, List.length_nil]
    refine ⟨hS.e_nn, hS.e_pos, ?_⟩
    exact (candB_sound (s := 0) (c := 0) hC (by simpa [RTree.sizeL] using h) le_rfl R.e
      (by simp [candB])).2
  | t :: l, h => by
    have ht0 := RTree.size_pos t
    have ht : t.size < N := by simp only [RTree.sizeL] at h; omega
    have hl : RTree.sizeL l < N := by simp only [RTree.sizeL] at h; omega
    obtain ⟨x1, x2, x3⟩ := inv_bundle hS hC l hl
    obtain ⟨z1, z2, z3⟩ := inv_branch hS hC t ht
    have hlen := RTree.length_le_sizeL l
    simp only [Rec.bundle, RTree.sizeL, List.length_cons]
    refine ⟨mul_nn hS.T_nn x1 z1, mul_pos0 hS x1 z1 x2 z2, ?_⟩
    refine mul_dom hS x3 z3 z1 (fun p hp => (hC.2.2.1 _ hl _ hlen p hp).1) fun p hp q hq => ?_
    have hm := mem_candB (R := R) (C := C) (s := t.size + RTree.sizeL l)
      (c := l.length + 1) (j := t.size) (by omega) ht0 (by omega)
      (by simpa using hp) hq
    exact (candB_sound hC (by simpa [RTree.sizeL] using h) (by omega) _ hm).2
end

mutual
/-- A tree whose every branch value and every partial bundle value is a KEPT hull point. -/
def KeptT (R : Rec D) (C : Cert D) : RTree → Prop
  | .node l => KeptL R C l ∧ R.branch (.node l) ∈ C.KH (RTree.sizeL l + 1)
/-- The same for a list of children (all partial bundles kept). -/
def KeptL (R : Rec D) (C : Cert D) : List RTree → Prop
  | [] => R.e ∈ C.KB 0 0
  | t :: l => KeptT R C t ∧ KeptL R C l ∧
      R.bundle (t :: l) ∈ C.KB (t.size + RTree.sizeL l) (l.length + 1)
end

theorem keptL_mem {l : List RTree} (h : KeptL R C l) :
    R.bundle l ∈ C.KB (RTree.sizeL l) l.length := by
  cases l with
  | nil => simpa [Rec.bundle, RTree.sizeL, KeptL] using h
  | cons t l => simpa [RTree.sizeL, KeptL] using h.2.2

theorem keptT_mem {t : RTree} (h : KeptT R C t) : R.branch t ∈ C.KH t.size := by
  cases t with
  | node l => simpa [RTree.size, KeptT] using h.2

mutual
/-- THE INDUCTION (strict part), branches: a branch is kept all the way down, or its value
is strictly dominated in its class. -/
theorem kept_branch (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ t : RTree, t.size < N → KeptT R C t ∨ SDom (C.KH t.size) (R.branch t)
  | .node l, h => by
    have hl : RTree.sizeL l < N := by simp only [RTree.size] at h; omega
    have hlen := RTree.length_le_sizeL l
    have hcN : l.length < N := by omega
    have hmN : RTree.sizeL l + 1 < N := by simp only [RTree.size] at h; omega
    have hcand : ∀ p ∈ C.KB (RTree.sizeL l) l.length,
        (R.plant l.length p ∈ C.KH (RTree.sizeL l + 1) ∨
          SDom (C.KH (RTree.sizeL l + 1)) (R.plant l.length p)) ∧
        Dom (C.KH (RTree.sizeL l + 1)) (R.plant l.length p) := fun p hp =>
      candH_sound hC hmN (by omega) _
        (mem_candH (R := R) (m := RTree.sizeL l + 1) (c := l.length) (by omega)
          (by simpa using hp))
    simp only [RTree.size]
    rcases kept_bundle hS hC l hl with hk | hsd
    · rcases (hcand _ (keptL_mem hk)).1 with hm | hsd'
      · exact Or.inl ⟨hk, hm⟩
      · exact Or.inr hsd'
    · exact Or.inr (plant_sdom hS hcN hsd fun p hp => (hcand p hp).2)

/-- THE INDUCTION (strict part), bundles. -/
theorem kept_bundle (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ l : List RTree, RTree.sizeL l < N →
      KeptL R C l ∨ SDom (C.KB (RTree.sizeL l) l.length) (R.bundle l)
  | [], h => by
    simp only [Rec.bundle, RTree.sizeL, List.length_nil, KeptL]
    exact (candB_sound (s := 0) (c := 0) hC (by simpa [RTree.sizeL] using h) le_rfl R.e
      (by simp [candB])).1
  | t :: l, h => by
    have ht0 := RTree.size_pos t
    have ht : t.size < N := by simp only [RTree.sizeL] at h; omega
    have hl : RTree.sizeL l < N := by simp only [RTree.sizeL] at h; omega
    have hlen := RTree.length_le_sizeL l
    obtain ⟨x1, x2, x3⟩ := inv_bundle hS hC l hl
    obtain ⟨z1, z2, z3⟩ := inv_branch hS hC t ht
    have hsN : t.size + RTree.sizeL l < N := by simpa [RTree.sizeL] using h
    have hcand : ∀ p ∈ C.KB (RTree.sizeL l) l.length, ∀ q ∈ C.KH t.size,
        (R.mul p q ∈ C.KB (t.size + RTree.sizeL l) (l.length + 1) ∨
          SDom (C.KB (t.size + RTree.sizeL l) (l.length + 1)) (R.mul p q)) ∧
        Dom (C.KB (t.size + RTree.sizeL l) (l.length + 1)) (R.mul p q) := fun p hp q hq =>
      candB_sound hC hsN (by omega) _
        (mem_candB (R := R) (C := C) (s := t.size + RTree.sizeL l) (c := l.length + 1)
          (j := t.size) (by omega) ht0 (by omega) (by simpa using hp) hq)
    have hK1 : ∀ p ∈ C.KB (RTree.sizeL l) l.length, ∀ i, 0 ≤ p i :=
      fun p hp => (hC.2.2.1 _ hl _ hlen p hp).1
    simp only [Rec.bundle, RTree.sizeL, List.length_cons, KeptL]
    rcases kept_bundle hS hC l hl with hk | hsd
    · have hxm := keptL_mem hk
      rcases kept_branch hS hC t ht with hkt | hsdt
      · rcases (hcand _ hxm _ (keptT_mem hkt)).1 with hm | hsd'
        · exact Or.inl ⟨hkt, hk, hm⟩
        · exact Or.inr hsd'
      · exact Or.inr (mul_sdom_right hS hxm x1 x2 hsdt fun p hp q hq => (hcand p hp q hq).2)
    · exact Or.inr (mul_sdom_left hS hsd z3 z1 z2 hK1 fun p hp q hq => (hcand p hp q hq).2)
end

/-- UPPER BOUND.  Every tree on `n ≤ N` vertices has `pi ≤ v`, as soon as every kept root
bundle has root value at most `v`. -/
theorem pi_le (hS : R.Signs N z0) (hC : C.Valid R N z0) {n : ℕ} (hn : n ≤ N) (hn2 : 2 ≤ n)
    {v : ℚ} (hF : ∀ k, 1 ≤ k → k < n → ∀ i, 0 ≤ R.F k i)
    (hV : ∀ k, 1 ≤ k → k < n → ∀ p ∈ C.KB (n - 1) k, R.root k p ≤ v) :
    ∀ T : RTree, T.size = n → R.pi T ≤ v
  | .node l, h => by
    simp only [RTree.size] at h
    have hl : RTree.sizeL l < N := by omega
    have hlen := RTree.length_le_sizeL l
    have hk1 : 1 ≤ l.length := by
      cases l with
      | nil => simp [RTree.sizeL] at h; omega
      | cons _ _ => simp
    obtain ⟨_, _, h3⟩ := inv_bundle hS hC l hl
    obtain ⟨p, hp, hle⟩ := h3 (R.F l.length) (hF _ hk1 (by omega))
    have hs : RTree.sizeL l = n - 1 := by omega
    rw [hs] at hp
    have := hV _ hk1 (by omega) p hp
    simp only [Rec.pi, Rec.root] at this ⊢
    linarith

/-- MAXIMIZERS.  If the root functionals are strictly positive, a tree attaining `v` has every
branch value and every partial bundle value on the kept hull points. -/
theorem kept_of_pi_eq (hS : R.Signs N z0) (hC : C.Valid R N z0) {n : ℕ} (hn : n ≤ N)
    (hn2 : 2 ≤ n) {v : ℚ} (hF : ∀ k, 1 ≤ k → k < n → ∀ i, 0 < R.F k i)
    (hV : ∀ k, 1 ≤ k → k < n → ∀ p ∈ C.KB (n - 1) k, R.root k p ≤ v) :
    ∀ l : List RTree, (RTree.node l).size = n → R.pi (.node l) = v →
      KeptL R C l ∧ R.bundle l ∈ C.KB (n - 1) l.length := by
  intro l h hpi
  simp only [RTree.size] at h
  have hl : RTree.sizeL l < N := by omega
  have hlen := RTree.length_le_sizeL l
  have hk1 : 1 ≤ l.length := by
    cases l with
    | nil => simp [RTree.sizeL] at h; omega
    | cons _ _ => simp
  have hs : RTree.sizeL l = n - 1 := by omega
  rcases kept_bundle hS hC l hl with hk | hsd
  · exact ⟨hk, hs ▸ keptL_mem hk⟩
  · exfalso
    obtain ⟨p, hp, hlt⟩ := hsd (R.F l.length) (hF _ hk1 (by omega))
    rw [hs] at hp
    have := hV _ hk1 (by omega) p hp
    simp only [Rec.pi, Rec.root] at hpi this
    linarith

/-- EXACT MAXIMUM: the upper bound together with one tree attaining it. -/
theorem isGreatest_pi (hS : R.Signs N z0) (hC : C.Valid R N z0) {n : ℕ} (hn : n ≤ N)
    (hn2 : 2 ≤ n) {v : ℚ} (hF : ∀ k, 1 ≤ k → k < n → ∀ i, 0 ≤ R.F k i)
    (hV : ∀ k, 1 ≤ k → k < n → ∀ p ∈ C.KB (n - 1) k, R.root k p ≤ v)
    (Tw : RTree) (hTw : Tw.size = n ∧ R.pi Tw = v) :
    IsGreatest {x | ∃ T : RTree, T.size = n ∧ R.pi T = x} v :=
  ⟨⟨Tw, hTw⟩, by
    rintro x ⟨T, hT, rfl⟩
    exact pi_le hS hC hn hn2 hF hV T hT⟩

end Main

end HullDom

open HullDom
"""


@dataclass
class AffineHullDominanceEmitter(Emitter):
    """Emit the generic hull-dominance theory once, then per instance: the recursion, the kept
    tables and witnesses, `Rec.Signs` and `Cert.Valid` by `decide +kernel`, and per n the exact
    maximum (`IsGreatest`), the maximizer structure theorem and the checked maximizer list.

    HONEST SCOPE: the exact maximum of one explicit positive multilinear recursion over all
    trees on n vertices, n = 2..N.  Nothing about any open problem.  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "affine_hull_dominance"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts = [_GENERIC]
        nthm = 24
        for inst in fam.instances:
            text, n = self._emit_instance(inst.payload, inst.lean_name)
            parts.append(text)
            nthm += n
        return "\n".join(parts), nthm

    def emit_units(self, fam, profile: LeanProfile):
        # the generic section is shared across instances: one unit
        return [self.emit_body(fam, profile)]

    def _emit_instance(self, c: HullDominanceCert, nm: str) -> tuple[str, int]:
        rec, N, D, z = c.rec, c.N, c.rec.dim, c.rec.z0
        KB, KH, WB, WH = c.kb(), c.kh(), dict(c.WB), dict(c.WH)
        L: list[str] = []
        n = 0
        vals = ", ".join(f"M_{k} = {v}" for k, v in c.values)
        L.append(f"/-! ## Instance `{nm}`{': ' + c.label if c.label else ''}\n\n"
                 f"Dimension {D}, trees on n = 2..{N} vertices, "
                 f"{sum(len(K) for K in KB.values()) + sum(len(K) for K in KH.values())} kept "
                 f"points, {c.n_candidates} candidate witnesses.\n"
                 f"Certified values: {vals}. -/\n")
        P_rows = ", ".join(
            "![" + ", ".join(_expr_lean(rec.P[i][j], C_SYM, "c") for j in range(D)) + "]"
            for i in range(D))
        F_row = ", ".join(_expr_lean(rec.F[i], K_SYM, "k") for i in range(D))
        L.append(f"/-- The recursion. -/\n"
                 f"def {nm}_R : Rec {D} where\n"
                 f"  e := {_vec(rec.e)}\n"
                 f"  T := fun i j l => ({_fin_table(rec)} : Fin {D} → Fin {D} → Fin {D} → ℚ) i j l\n"
                 f"  P := fun c => ![{P_rows}]\n"
                 f"  F := fun k => ![{F_row}]\n")
        # tables
        kb_rows = []
        wb_rows = []
        for s in range(N):
            kb_rows.append("[" + ", ".join(
                "[" + ", ".join(_vec(p) for p in KB.get((s, cc), ())) + "]"
                for cc in range(s + 1)) + "]")
            wb_rows.append("[" + ", ".join(
                "[" + ", ".join(_wit_lean(w) for w in WB.get((s, cc), ())) + "]"
                for cc in range(s + 1)) + "]")
        kh_rows = ["[" + ", ".join(_vec(p) for p in KH.get(m, ())) + "]" for m in range(N)]
        wh_rows = ["[" + ", ".join(_wit_lean(w) for w in WH.get(m, ())) + "]" for m in range(N)]
        nl = ",\n  "
        L.append(f"/-- Kept bundle points, indexed [s][c]. -/\n"
                 f"def {nm}_KBt : List (List (List (Vec {D}))) := [\n  {nl.join(kb_rows)}]\n")
        L.append(f"/-- Kept branch points, indexed [m]. -/\n"
                 f"def {nm}_KHt : List (List (Vec {D})) := [\n  {nl.join(kh_rows)}]\n")
        L.append(f"/-- Bundle candidate witnesses, in `candB` order. -/\n"
                 f"def {nm}_WBt : List (List (List Wit)) := [\n  {nl.join(wb_rows)}]\n")
        L.append(f"/-- Branch candidate witnesses, in `candH` order. -/\n"
                 f"def {nm}_WHt : List (List Wit) := [\n  {nl.join(wh_rows)}]\n")
        L.append(f"/-- The certificate. -/\n"
                 f"def {nm}_C : Cert {D} where\n"
                 f"  KB s c := ({nm}_KBt.getD s []).getD c []\n"
                 f"  KH m := {nm}_KHt.getD m []\n"
                 f"  WB s c := ({nm}_WBt.getD s []).getD c []\n"
                 f"  WH m := {nm}_WHt.getD m []\n")
        zz = f"({z} : Fin {D})"
        L.append(f"/-- The sign conditions (positive multilinear recursion). -/\n"
                 f"theorem {nm}_signs : {nm}_R.Signs {N} {zz} where\n"
                 f"  e_nn := by decide +kernel\n"
                 f"  e_pos := by decide +kernel\n"
                 f"  T_nn := by decide +kernel\n"
                 f"  T_pos := by decide +kernel\n"
                 f"  T_left := by decide +kernel\n"
                 f"  T_right := by decide +kernel\n"
                 f"  P_nn := by decide +kernel\n"
                 f"  P_pos := by decide +kernel\n"
                 f"  P_col := by decide +kernel\n")
        L.append(f"/-- The dominance certificate: every candidate of every class has a checked\n"
                 f"witness (exact rational arithmetic, evaluated by the kernel). -/\n"
                 f"theorem {nm}_valid : {nm}_C.Valid {nm}_R {N} {zz} := by decide +kernel\n")
        L.append(f"theorem {nm}_F_nn : ∀ k, 1 ≤ k → k < {N} → ∀ i, 0 ≤ {nm}_R.F k i := by\n"
                 f"  decide +kernel\n")
        n += 4
        if c.strict:
            L.append(f"theorem {nm}_F_pos : ∀ k, 1 ≤ k → k < {N} → ∀ i, 0 < {nm}_R.F k i := by\n"
                     f"  decide +kernel\n")
            n += 1
        maxs = dict(c.maximizers)
        mains = []
        for nn, v in c.values:
            V = _qv(v)
            trees = maxs[nn]
            L.append(f"/-- n = {nn}: every kept root bundle has value at most M_{nn} = {v}. -/\n"
                     f"theorem {nm}_hV_{nn} : ∀ k, 1 ≤ k → k < {nn} → ∀ p ∈ {nm}_C.KB {nn - 1} k,\n"
                     f"    {nm}_R.root k p ≤ {V} := by\n"
                     f"  decide +kernel\n")
            L.append(f"/-- n = {nn}: the listed maximizers (one rooting per isomorphism class)\n"
                     f"attain {v}. -/\n"
                     f"theorem {nm}_listed_{nn} : ∀ T ∈ ([{', '.join(_tree_lean(t) for t in trees)}] : List RTree),\n"
                     f"    T.size = {nn} ∧ {nm}_R.pi T = {V} := by\n"
                     f"  decide +kernel\n")
            L.append(f"/-- EXACT MAXIMUM over all trees on {nn} vertices. -/\n"
                     f"theorem {nm}_max_{nn} :\n"
                     f"    IsGreatest {{x | ∃ T : RTree, T.size = {nn} ∧ {nm}_R.pi T = x}} {V} :=\n"
                     f"  isGreatest_pi {nm}_signs {nm}_valid (n := {nn}) (by norm_num) (by norm_num)\n"
                     f"    (fun k h1 h2 => {nm}_F_nn k h1 (by omega)) {nm}_hV_{nn} _\n"
                     f"    ({nm}_listed_{nn} _ List.mem_cons_self)\n")
            n += 3
            if c.strict:
                L.append(f"/-- MAXIMIZER STRUCTURE on {nn} vertices: a tree attaining {v} has every\n"
                         f"branch state and every partial bundle state on the kept hull points. -/\n"
                         f"theorem {nm}_kept_{nn} : ∀ l : List RTree, (RTree.node l).size = {nn} →\n"
                         f"    {nm}_R.pi (.node l) = {V} →\n"
                         f"      KeptL {nm}_R {nm}_C l ∧ {nm}_R.bundle l ∈ {nm}_C.KB {nn - 1} l.length :=\n"
                         f"  kept_of_pi_eq {nm}_signs {nm}_valid (by norm_num) (by norm_num)\n"
                         f"    (fun k h1 h2 => {nm}_F_pos k h1 (by omega)) {nm}_hV_{nn}\n")
                n += 1
            mains.append((nn, V))
        stmt = " ∧\n    ".join(
            f"IsGreatest {{x | ∃ T : RTree, T.size = {nn} ∧ {nm}_R.pi T = x}} {V}"
            for nn, V in mains)
        proof = ", ".join(f"{nm}_max_{nn}" for nn, _ in mains)
        L.append(f"/-- MAIN.  The exact maximum for every n = 2..{N}. -/\n"
                 f"theorem {nm} :\n    {stmt} :=\n  ⟨{proof}⟩\n")
        n += 1
        return "\n".join(L), n


def affine_hull_dominance_family(name, grid, lean_name, spec, constants=None):
    """Build an affine-hull-dominance family (kind='affine_hull_dominance').

    ``spec``: a callable ``pt -> dict`` of :func:`hull_dominance_certificate` keyword
    arguments (``recursion``, ``N``, ``maximizers``, ``label``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("affine_hull_dominance", spec),
        constants=dict(constants or {}),
    )


#: The running example: the Randic-weighted matching sum
#:   pi(T) = sum over matchings M of prod_{uv in M} 1/(deg u deg v).
MATCHING_SUM_RECURSION = dict(
    dim=2, e=(1, 0),
    T={(0, 0, 0): 1, (1, 1, 0): 1, (1, 0, 1): 1},
    P=(("1", "1/(c+1)"), ("1/(c+1)", "0")),
    F=("1", "1/k"),
)

#: The Randic-type edge sum, plus one:  1 + sum_{uv in E} 1/(deg u deg v).  State (Z, W, V):
#: Z = 1 (homogenizing coordinate), W = the edge sum inside the branch, V = 1/deg(root).
RANDIC_SUM_RECURSION = dict(
    dim=3, e=(1, 0, 0),
    T={(0, 0, 0): 1, (1, 1, 0): 1, (1, 0, 1): 1, (2, 2, 0): 1, (2, 0, 2): 1},
    P=(("1", "0", "0"), ("0", "1", "1/(c+1)"), ("1/(c+1)", "0", "0")),
    F=("1", "1", "1/k"),
)

#: A SYNTHETIC recursion (no claimed combinatorial significance), for coverage: the matching
#: bilinear map with a different planting and root,
#:   P_c = [[1, 2/(c+1)^2], [1/(c+2), 0]],   F_k = (1, 2/k^2).
SYNTHETIC_RECURSION = dict(
    dim=2, e=(1, 0),
    T={(0, 0, 0): 1, (1, 1, 0): 1, (1, 0, 1): 1},
    P=(("1", "2/(c+1)**2"), ("1/(c+2)", "0")),
    F=("1", "2/k**2"),
)


if __name__ == "__main__":
    import time

    for nm, spec, N in (("matching", MATCHING_SUM_RECURSION, 12),
                        ("randic", RANDIC_SUM_RECURSION, 10),
                        ("synthetic", SYNTHETIC_RECURSION, 12)):
        t0 = time.time()
        cert = hull_dominance_certificate(recursion=spec, N=N)
        print(f"{nm}: N={N} candidates={cert.n_candidates} "
              f"maxK={max(len(K) for _, K in cert.KB)} t={time.time() - t0:.2f}s")
        for n, v in cert.values:
            print(f"  n={n} M={v} ({float(v):.6f}) maximizers={len(dict(cert.maximizers)[n])}")

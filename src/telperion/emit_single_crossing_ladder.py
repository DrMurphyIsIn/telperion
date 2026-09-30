"""single_crossing_ladder emitter -- single crossing of consecutive members of a parametric
family, increasing breakpoints, and the resulting best-member ladder.

conjecture1_proved = False.  This module certifies elementary one-variable facts about an
explicit family of log-sums; it says nothing about any open conjecture.

THE SHAPE
---------
A family of functions of a real parameter ``x`` on ``S = [0, X]`` or ``S = [0, oo)``,

    F_j(x) = sum_i kappa_i(j) * log(1 + beta_i(j) * x),        j = a, a+1, ..., J+1,

with ``kappa_i``, ``beta_i`` rational functions of ``j`` (all members tie at the anchor
``x = 0``, where every log vanishes).  Certify, kernel-checked:

(a) SINGLE CROSSING.  For each consecutive pair, ``D_j = F_j - F_{j+1}`` has derivative
    ``D_j' = N_j / P_j`` with ``P_j = prod (1 + beta x) > 0`` on ``S`` and ``N_j`` a
    polynomial with ONE sign change ``+ -> -`` on ``S ∩ (0, oo)``, certified exactly: a
    Bernstein (or, on an unbounded cell, Taylor) cover of ``[0, a_c]`` where ``N_j > 0``, a
    crossing cell ``[a_c, b_c]`` where ``N_j' < 0`` (so ``N_j`` falls through zero once), and
    a cover of ``[b_c, X]`` (or ``[b_c, oo)``) where ``N_j < 0``.  Since ``D_j(0) = 0``,
    ``D_j`` rises then falls: with a rational bracket ``D_j(lo) > 0 > D_j(hi)`` (both values
    certified by ``enclosure_tree`` log atoms) there is EXACTLY ONE zero ``lambda_j`` of
    ``D_j`` on ``S ∩ (0, oo)``, it lies in ``(lo, hi)``, ``F_j`` is ahead before it and
    ``F_{j+1}`` after it.  A pair may instead be DOMINATED (``N_j < 0`` on all of
    ``S ∩ (0, oo)``): then ``F_{j+1} > F_j`` everywhere and the breakpoint is ``0``.
(b) INCREASING BREAKPOINTS.  Dominated pairs come first; the brackets of the crossing pairs
    are disjoint and increasing, ``hi_j < lo_{j+1}`` (exact rationals).
(c) THE LADDER.  On ``(lambda_{j-1}, lambda_j)`` (open at the ends of the window) ``F_j``
    is the UNIQUE maximum of ``F_a, ..., F_{J+1}``: one generic lemma (``ladder_core``)
    chains the crossings up and down the window.

LEAN (generic section emitted once per file; every theorem sorry-free)
---------------------------------------------------------------------
``logSum`` / ``logSumDeriv`` / ``hasDerivAt_logSum`` (list induction), ``polyEval`` /
``polyDeriv`` / ``hasDerivAt_polyEval`` (Horner form), ``up_of_deriv`` / ``down_of_deriv``
(mean value theorem ``exists_hasDerivAt_eq_slope``), ``sign_change_of_cell`` (intermediate
value ``intermediate_value_Ioo'`` on the crossing cell), ``single_crossing_core`` and
``dominated_core`` (monotone pieces + intermediate value on ``[max s lo, hi]``), and
``ladder_core`` (``Nat.le_induction`` up and down the window).  Per instance: the family
definition, one lemma per sign cell (``linarith`` over the Bernstein / Taylor product
facts), the factorisation ``D' * P = N`` (``field_simp; ring``), the bracket values (log
atoms from ``enclosure_tree``, then ``norm_num`` + ``linarith``), one crossing (or
domination) theorem per pair, the bracket order, and the capstone ``<nm>`` (the instance name).

ANTI-PHANTOM REFUSALS
---------------------
``single_crossing_ladder_certificate`` refuses: floats; ``a > J``; a member whose
``kappa``/``beta`` is undefined at an integer ``j``; a log argument ``1 + beta x`` not
positive on ``S`` (``beta < 0`` on an unbounded domain, ``1 + beta X <= 0``); identical
consecutive members; ``N_j(0) = 0``; a crossing pair whose ``N_j`` has no single ``+ -> -``
sign change certifiable to the subdivision limit (a DOUBLE crossing is refused here); a
dominated pair whose ``N_j`` is not certified negative; a bracket with ``lo <= 0``,
``lo >= hi`` or ``hi`` outside ``S``; a bracket whose values ``D(lo) > 0 > D(hi)`` the exact
enclosure fold does not imply (a WRONG breakpoint enclosure is refused here); a log argument
``<= 1/2`` at a bracket end (outside the fold range); a dominated pair after a crossing
pair; overlapping or decreasing brackets.  ``check=False`` is for hand-forged negative
controls ONLY: it computes the same certificate algebra with every sign check skipped, so
the kernel is the arbiter.

HONEST SCOPE: the ladder is proved over the FINITE window ``a..J+1`` of members.  Beyond the
window (e.g. that no member past ``J+1`` ever wins on the window's intervals) needs a
separate argument (for the running example, the unimodality of ``j -> F_j``), which this
shape does not certify.  The breakpoints are pinned only to their rational brackets.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import floor, log as _flog

import sympy as sp

from .certify import CertifiedInstance
from .emit_concave_pooled_induction import R_SYM, PolyCert, _facts, _poly1, _polycert, _q
from .emit_enclosure_tree import (
    EnclosureTreeCert,
    EnclosureTreeRefusal,
    enclosure_tree_certificate,
    node_add,
    node_log,
    node_mul,
    node_rat,
    node_sub,
)
from .emit_enclosure_tree import _header as _enc_header
from .emit_enclosure_tree import _proof_body as _enc_proof_body
from .emit_enclosure_tree import _statement as _enc_statement
from .family import InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

J_SYM = sp.Symbol("j")
X_SYM = sp.Symbol("x")

#: bisection depth for the sign covers and the crossing-cell search
_MAX_DEPTH = 14
#: polynomial degree cap (Lean cost of the Bernstein product facts)
_MAX_DEGREE = 10
#: window cap (one crossing theorem per pair)
_MAX_PAIRS = 24
#: Taylor order of the log atoms when a forged certificate skips the claim search
_FORGED_ORDER = 40


class SingleCrossingRefusal(ValueError):
    """Raised when the certificate cannot be built or verified."""


def _refuse(msg: str) -> SingleCrossingRefusal:
    return SingleCrossingRefusal(f"single_crossing_ladder REFUSED: {msg}")


def _rat(v, what: str) -> sp.Rational:
    if isinstance(v, bool) or isinstance(v, float):
        raise _refuse(f"{what} = {v!r}: floats/bools are not exact; pass a Rational or a string")
    try:
        r = sp.Rational(v) if not isinstance(v, str) else sp.Rational(sp.sympify(v))
    except (TypeError, ValueError, sp.SympifyError):
        raise _refuse(f"{what} = {v!r} is not an exact rational") from None
    return r


def _jexpr(e, what: str) -> sp.Expr:
    """A rational function of ``j`` with rational coefficients (no floats)."""
    if isinstance(e, float):
        raise _refuse(f"{what} = {e!r}: floats are not exact")
    ex = sp.sympify(e, locals={"j": J_SYM}) if isinstance(e, str) else sp.sympify(e)
    if ex.has(sp.Float):
        raise _refuse(f"{what} = {ex}: contains a float")
    if not ex.free_symbols <= {J_SYM}:
        raise _refuse(f"{what} = {ex}: only the symbol j is allowed")
    num, den = sp.fraction(sp.together(ex))
    for p in (num, den):
        try:
            sp.Poly(p, J_SYM, domain="QQ")
        except sp.PolynomialError:
            raise _refuse(f"{what} = {ex} is not a rational function of j") from None
    return ex


def _at(ex: sp.Expr, j: int, what: str) -> sp.Rational:
    num, den = sp.fraction(sp.together(ex))
    d = sp.Rational(den.subs(J_SYM, j))
    if d == 0:
        raise _refuse(f"{what} is undefined at j = {j}")
    return sp.Rational(num.subs(J_SYM, j)) / d


# ---------------------------------------------------------------------------
# polynomial sign covers (Bernstein / Taylor, shared with concave_pooled_induction)
# ---------------------------------------------------------------------------

def _poly(expr) -> sp.Poly:
    return sp.Poly(sp.expand(expr), R_SYM, domain="QQ")


def _sign_cover(P: sp.Poly, s, t, *, check: bool, depth: int = 0) -> list:
    """Cells covering [s, t] (t None = oo) with P > 0 on each (exact PolyCerts, strict)."""
    pc = _polycert(P, s, t, True)
    if pc.ok() or not check:
        return [pc]
    if depth >= _MAX_DEPTH:
        raise _refuse(f"no positive Bernstein/Taylor certificate for {P.as_expr()} on "
                      f"[{s}, {'oo' if t is None else t}] down to the subdivision limit")
    if t is None:
        # push the Taylor anchor out: cover [s, m] by Bernstein, recurse on [m, oo)
        m = 2 * s + 1
        return (_sign_cover(P, s, m, check=check, depth=depth + 1)
                + _sign_cover(P, m, None, check=check, depth=depth + 1))
    m = (s + t) / 2
    return (_sign_cover(P, s, m, check=check, depth=depth + 1)
            + _sign_cover(P, m, t, check=check, depth=depth + 1))


def _dyadic_below(r: float, k: int) -> sp.Rational:
    return sp.Rational(floor(r * 2 ** k), 2 ** k)


# ---------------------------------------------------------------------------
# certificate dataclasses
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SignCell:
    """``sign * N > 0`` on ``[s, t]`` (``t is None``: ``[s, oo)``); ``pc`` certifies
    ``sign * N`` (or ``-N'`` on the crossing cell)."""

    s: object
    t: object
    sign: int
    pc: PolyCert


@dataclass(frozen=True)
class PairCert:
    """One consecutive pair ``(F_j, F_{j+1})``.

    ``mode`` is ``"cross"`` (bracket ``lo < lambda_j < hi``) or ``"dominated"``
    (``F_{j+1} > F_j`` on all of ``S ∩ (0, oo)``).  ``dterms`` are the merged
    ``(kappa, beta)`` of ``D_j = F_j - F_{j+1}``, ``betas`` the factors of ``P``, ``N`` the
    ascending coefficients of the derivative numerator, ``dN`` those of ``N'``."""

    j: int
    mode: str
    dterms: tuple
    betas: tuple
    N: tuple
    dN: tuple
    left: tuple = ()             # SignCells, N > 0 on [0, a_c]
    cross_cell: tuple = ()       # (a_c, b_c, PolyCert of -N')
    right: tuple = ()            # SignCells, N < 0 on [b_c, X] (or [b_c, oo)) / whole S
    lo: object = None
    hi: object = None
    enc_lo: object = None        # EnclosureTreeCert of D(lo) (claim > 0)
    enc_hi: object = None        # EnclosureTreeCert of D(hi) (claim < 0)


@dataclass(frozen=True)
class SingleCrossingCert:
    terms: tuple                 # ((kappa(j), beta(j)), ...) sympy expressions in j
    a: int
    J: int
    X: object                    # None = [0, oo)
    member_terms: tuple          # per member j = a..J+1: ((kappa, beta), ...) rationals
    pairs: tuple                 # PairCert per j = a..J
    checked: bool = True

    @property
    def crossings(self):
        return tuple(p for p in self.pairs if p.mode == "cross")

    @property
    def dominated(self):
        return tuple(p for p in self.pairs if p.mode == "dominated")


# ---------------------------------------------------------------------------
# the certificate
# ---------------------------------------------------------------------------

def _log_node(q: sp.Rational):
    """``log q`` as an enclosure_tree node from Taylor atoms only (no log 2 atom, whose
    Mathlib bracket is only 1e-9 wide): directly when ``|1 - q| <= 1/3``, otherwise by the
    fold ``q = (3/2)^e * r`` with ``|1 - r| <= 1/3``."""
    if q <= sp.Rational(1, 2):
        raise _refuse(f"log({q}): arguments <= 1/2 are outside the supported fold range")
    if abs(1 - q) <= sp.Rational(1, 3):
        return node_log(q)
    three_halves = sp.Rational(3, 2)
    e = max(1, round(_flog(float(q)) / _flog(1.5)))
    r = q / three_halves ** e
    while abs(1 - r) > sp.Rational(1, 3) and r > 1:
        e += 1
        r = q / three_halves ** e
    if e > 8 or abs(1 - r) > sp.Rational(1, 3):
        raise _refuse(f"log({q}): no fold (3/2)^e * r with e <= 8 and |1 - r| <= 1/3")
    base = node_log(three_halves)
    if r == 1:
        return node_log(q, factors=((e, base),))
    return node_log(q, factors=((e, base), (1, node_log(r))))


def _value_tree(dterms, x: sp.Rational):
    acc = None
    for kap, beta in dterms:
        q = 1 + beta * x
        if q == 1 or kap == 0:
            continue
        n = _log_node(q)
        mag = abs(kap)
        term = n if mag == 1 else node_mul(node_rat(mag), n)
        if acc is None:
            acc = term if kap > 0 else node_mul(node_rat(kap), n)
        else:
            acc = node_add(acc, term) if kap > 0 else node_sub(acc, term)
    if acc is None:
        raise _refuse(f"D({x}) has no transcendental content (every log argument is 1)")
    return acc


def _enclose(dterms, x, *, positive: bool, check: bool, what: str) -> EnclosureTreeCert:
    tree = _value_tree(dterms, x)
    try:
        if not check:
            return _enc_forged(tree)
        if positive:
            return enclosure_tree_certificate(tree, lo=0)
        return enclosure_tree_certificate(tree, hi=0)
    except EnclosureTreeRefusal as exc:
        raise _refuse(f"{what}: the enclosure fold does not imply the sign "
                      f"({'D > 0' if positive else 'D < 0'}); is the bracket wrong? "
                      f"[{str(exc)[:200]}]") from None


def _enc_forged(tree) -> EnclosureTreeCert:
    """A claim-free enclosure (forged controls): the atoms at a fixed high Taylor order."""
    from dataclasses import replace

    def pin(node):
        kw = {"children": tuple(pin(ch) for ch in node.children)}
        if node.op == "log":
            kw["order"] = _FORGED_ORDER
            if node.factors:
                kw["factors"] = tuple((m, pin(f)) for m, f in node.factors)
        return replace(node, **kw)

    return enclosure_tree_certificate(pin(tree))


def _dterms(mt_j, mt_k) -> tuple:
    """Merge the (kappa, beta) of F_j - F_k by beta (beta = 0 contributes nothing)."""
    acc: dict = {}
    for kap, beta in mt_j:
        acc[beta] = acc.get(beta, 0) + kap
    for kap, beta in mt_k:
        acc[beta] = acc.get(beta, 0) - kap
    return tuple((sp.Rational(k), sp.Rational(b)) for b, k in sorted(acc.items())
                 if b != 0 and k != 0)


def _numerator(dterms) -> tuple[tuple, sp.Poly]:
    betas = tuple(b for _, b in dterms)
    x = R_SYM
    P = sp.prod([1 + b * x for b in betas])
    Dp = sum(k * b / (1 + b * x) for k, b in dterms)
    N = sp.cancel(sp.together(Dp * P))
    num, den = sp.fraction(N)
    if sp.Poly(den, x).degree() != 0:
        raise _refuse("internal: D' * P is not a polynomial")   # pragma: no cover
    return betas, _poly(N)


def _coeffs(P: sp.Poly) -> tuple:
    d = max(P.degree(), 0)
    return tuple(sp.Rational(P.coeff_monomial(R_SYM ** k)) for k in range(d + 1))


def _crossing_cells(N: sp.Poly, X, *, check: bool, j: int):
    """Left cover (N > 0), crossing cell (N' < 0) and right cover (N < 0)."""
    dN = _poly(sp.diff(N.as_expr(), R_SYM))
    roots = sorted(float(r) for r in sp.Poly(N.as_expr(), R_SYM).real_roots()
                   if r > 0 and (X is None or r < X))
    if not roots:
        if check:
            raise _refuse(f"pair j = {j}: N_j has no sign change on S ∩ (0, oo); it is "
                          f"not a crossing pair (N_j(0) = {N.eval(0)})")
        roots = [float(X) / 2 if X is not None else 1.0]
    if check and len(roots) != 1:
        raise _refuse(f"pair j = {j}: N_j has {len(roots)} sign changes on S ∩ (0, oo) "
                      f"(roots ~ {[round(r, 6) for r in roots]}): not a single crossing")
    r = roots[0]
    last = None
    for k in range(3, 3 + _MAX_DEPTH + 10):
        a_c = _dyadic_below(r, k)
        b_c = a_c + sp.Rational(1, 2 ** k)
        if a_c <= 0:
            continue
        if X is not None and b_c >= X:
            continue
        cpc = _polycert(_poly(-dN.as_expr()), a_c, b_c, True)
        if not cpc.ok() and check:
            last = f"N' not negative on [{a_c}, {b_c}]"
            continue
        try:
            left = _sign_cover(N, sp.Integer(0), a_c, check=check)
            right = _sign_cover(_poly(-N.as_expr()), b_c, X, check=check)
        except SingleCrossingRefusal as exc:
            last = str(exc)
            continue
        return (tuple(SignCell(p.s, p.t, 1, p) for p in left),
                (a_c, b_c, cpc),
                tuple(SignCell(p.s, p.t, -1, p) for p in right), dN)
    raise _refuse(f"pair j = {j}: no crossing cell certifies the single sign change of "
                  f"N_j = {N.as_expr()} ({last})")


def single_crossing_ladder_certificate(*, terms, a: int, J: int, brackets: dict, X=None,
                                       check: bool = True) -> SingleCrossingCert:
    """Build and EXACTLY verify a single-crossing ladder certificate.

    ``terms``: ``[(kappa(j), beta(j)), ...]``, sympy expressions or strings in ``j``;
    member ``F_j(x) = sum kappa(j) log(1 + beta(j) x)``.  ``a <= J``: the pairs
    ``(F_j, F_{j+1})`` for ``j = a..J``.  ``brackets``: ``{j: (lo, hi)}`` for the CROSSING
    pairs (exact rationals); every other pair must be DOMINATED and precede them.  ``X``:
    the right end of ``S = [0, X]`` (``None``: ``[0, oo)``).

    ``check=False`` is for hand-forged negative controls ONLY."""
    if not isinstance(a, int) or not isinstance(J, int) or isinstance(a, bool):
        raise _refuse(f"a = {a!r}, J = {J!r} must be integers")
    if a < 0 or a > J:
        raise _refuse(f"need 0 <= a <= J (a = {a}, J = {J})")
    if J - a + 1 > _MAX_PAIRS:
        raise _refuse(f"window of {J - a + 1} pairs exceeds {_MAX_PAIRS}")
    if not terms:
        raise _refuse("empty family")
    tt = tuple((_jexpr(k, "kappa"), _jexpr(b, "beta")) for k, b in terms)
    Xr = None if X is None else _rat(X, "X")
    if Xr is not None and Xr <= 0:
        raise _refuse(f"X = {Xr} must be positive")
    br = {}
    for j, pair in dict(brackets).items():
        if not isinstance(j, int) or not (a <= j <= J):
            raise _refuse(f"bracket index {j!r} outside the window {a}..{J}")
        lo, hi = _rat(pair[0], f"lo_{j}"), _rat(pair[1], f"hi_{j}")
        if check and not (0 < lo < hi):
            raise _refuse(f"bracket of j = {j}: need 0 < lo < hi, got ({lo}, {hi})")
        if check and Xr is not None and hi > Xr:
            raise _refuse(f"bracket of j = {j}: hi = {hi} lies outside S = [0, {Xr}]")
        br[j] = (lo, hi)
    member_terms = []
    for j in range(a, J + 2):
        mt = []
        for i, (k, b) in enumerate(tt):
            kv, bv = _at(k, j, f"kappa_{i}"), _at(b, j, f"beta_{i}")
            if check:
                if Xr is None and bv < 0:
                    raise _refuse(f"member j = {j}: beta_{i} = {bv} < 0 on an unbounded "
                                  "domain (1 + beta x would vanish)")
                if Xr is not None and not 1 + bv * Xr > 0:
                    raise _refuse(f"member j = {j}: 1 + beta_{i} X = {1 + bv * Xr} <= 0")
            mt.append((kv, bv))
        member_terms.append(tuple(mt))
    pairs = []
    seen_cross = False
    prev_hi = None
    for j in range(a, J + 1):
        dt = _dterms(member_terms[j - a], member_terms[j + 1 - a])
        if not dt:
            raise _refuse(f"members {j} and {j + 1} are identical")
        betas, N = _numerator(dt)
        if N.degree() > _MAX_DEGREE:
            raise _refuse(f"pair j = {j}: N_j has degree {N.degree()} > {_MAX_DEGREE}")
        N0 = N.eval(0)
        if check and N0 == 0:
            raise _refuse(f"pair j = {j}: N_j(0) = 0 (degenerate start; not supported)")
        if j in br:
            lo, hi = br[j]
            if check and N0 < 0:
                raise _refuse(f"pair j = {j}: N_j(0) < 0, so D_j falls from 0 at once; "
                              "the pair is dominated, not crossing")
            left, cross, right, dN = _crossing_cells(N, Xr, check=check, j=j)
            enc_lo = _enclose(dt, lo, positive=True, check=check, what=f"D_{j}(lo = {lo})")
            enc_hi = _enclose(dt, hi, positive=False, check=check, what=f"D_{j}(hi = {hi})")
            if check and prev_hi is not None and not prev_hi < lo:
                raise _refuse(f"brackets not increasing: hi_{j - 1} = {prev_hi} >= "
                              f"lo_{j} = {lo}")
            prev_hi = hi
            seen_cross = True
            pairs.append(PairCert(j=j, mode="cross", dterms=dt, betas=betas,
                                  N=_coeffs(N), dN=_coeffs(dN), left=left,
                                  cross_cell=cross, right=right, lo=lo, hi=hi,
                                  enc_lo=enc_lo, enc_hi=enc_hi))
        else:
            if check and seen_cross:
                raise _refuse(f"pair j = {j} is dominated (no bracket) but follows a "
                              "crossing pair: the breakpoints would not increase")
            if check and N0 > 0:
                raise _refuse(f"pair j = {j}: N_j(0) > 0 (F_j pulls ahead first); give a "
                              "bracket for its crossing")
            cells = _sign_cover(_poly(-N.as_expr()), sp.Integer(0), Xr, check=check)
            dN = _poly(sp.diff(N.as_expr(), R_SYM))
            pairs.append(PairCert(j=j, mode="dominated", dterms=dt, betas=betas,
                                  N=_coeffs(N), dN=_coeffs(dN),
                                  right=tuple(SignCell(p.s, p.t, -1, p) for p in cells)))
    cert = SingleCrossingCert(terms=tt, a=a, J=J, X=Xr, member_terms=tuple(member_terms),
                              pairs=tuple(pairs), checked=check)
    if check:
        verify_certificate(cert)
    return cert


def verify_certificate(cert: SingleCrossingCert) -> None:
    """Independent exact re-check of the stored algebra (identities and signs)."""
    for p in cert.pairs:
        betas, N = _numerator(p.dterms)
        if _coeffs(N) != p.N or betas != p.betas:
            raise _refuse(f"pair j = {p.j}: stored N_j does not match its recomputation")
        cells = list(p.left) + list(p.right)
        for c in cells:
            if not (c.pc.identity_holds() and c.pc.ok()):
                raise _refuse(f"pair j = {p.j}: a sign cell fails its exact re-check")
            want = _coeffs(_poly(c.sign * N.as_expr()))
            if c.pc.poly != want:
                raise _refuse(f"pair j = {p.j}: a sign cell certifies the wrong polynomial")
        if p.mode == "cross":
            a_c, b_c, cpc = p.cross_cell
            dN = _poly(-sp.diff(N.as_expr(), R_SYM))
            if not (cpc.identity_holds() and cpc.ok() and cpc.poly == _coeffs(dN)):
                raise _refuse(f"pair j = {p.j}: the crossing cell fails its exact re-check")
            if [(c.s, c.t) for c in p.left][0][0] != 0 or p.left[-1].t != a_c:
                raise _refuse(f"pair j = {p.j}: the left cover does not tile [0, a_c]")
            if p.right[0].s != b_c or p.right[-1].t != cert.X:
                raise _refuse(f"pair j = {p.j}: the right cover does not tile [b_c, X]")
        else:
            if p.right[0].s != 0 or p.right[-1].t != cert.X:
                raise _refuse(f"pair j = {p.j}: the dominated cover does not tile S")
        for side in (p.left, p.right):
            for c1, c2 in zip(side, side[1:]):
                if c1.t != c2.s:
                    raise _refuse(f"pair j = {p.j}: a gap or overlap in a sign cover")


def certify_single_crossing_ladder_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``, a dict of the keyword arguments
    of :func:`single_crossing_ladder_certificate`."""
    spec = dict(family.special[1](pt))
    cert = single_crossing_ladder_certificate(**spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.pairs)


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

_GENERIC = r"""set_option linter.unusedVariables false

/-! ## Generic single-crossing ladder (emitted once per file)

`logSum L x = sum kappa * log (1 + beta * x)` over `L = [(kappa, beta), ...]`; `polyEval` is
Horner evaluation of an ascending coefficient list.  The cores below are proved once. -/

noncomputable def logSum : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | p :: L, x => p.1 * Real.log (1 + p.2 * x) + logSum L x

noncomputable def logSumDeriv : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | p :: L, x => p.1 * p.2 / (1 + p.2 * x) + logSumDeriv L x

theorem logSum_zero (L : List (ℝ × ℝ)) : logSum L 0 = 0 := by
  induction L with
  | nil => simp [logSum]
  | cons p L ih => simp [logSum, ih]

theorem hasDerivAt_logSum (L : List (ℝ × ℝ)) (x : ℝ) (h : ∀ p ∈ L, 0 < 1 + p.2 * x) :
    HasDerivAt (logSum L) (logSumDeriv L x) x := by
  induction L with
  | nil => simpa [logSum, logSumDeriv] using hasDerivAt_const x (0 : ℝ)
  | cons p L ih =>
    have hp : 0 < 1 + p.2 * x := h p (by simp)
    have hL : ∀ q ∈ L, 0 < 1 + q.2 * x := fun q hq => h q (by simp [hq])
    have h1 : HasDerivAt (fun y => 1 + p.2 * y) p.2 x := by
      simpa using ((hasDerivAt_id x).const_mul p.2).const_add 1
    have h3 := ((h1.log hp.ne').const_mul p.1).add (ih hL)
    have hfun : logSum (p :: L) = fun y => p.1 * Real.log (1 + p.2 * y) + logSum L y := by
      funext y; rfl
    have hv : logSumDeriv (p :: L) x = p.1 * (p.2 / (1 + p.2 * x)) + logSumDeriv L x := by
      simp only [logSumDeriv]; ring
    rw [hfun, hv]
    exact h3

noncomputable def polyEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: L, x => a + x * polyEval L x

noncomputable def polyDeriv : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: L, x => polyEval L x + x * polyDeriv L x

theorem hasDerivAt_polyEval (L : List ℝ) (x : ℝ) :
    HasDerivAt (polyEval L) (polyDeriv L x) x := by
  induction L with
  | nil => simpa [polyEval, polyDeriv] using hasDerivAt_const x (0 : ℝ)
  | cons a L ih =>
    have hfun : polyEval (a :: L) = fun y => a + y * polyEval L y := by funext y; rfl
    have h := ((hasDerivAt_id x).mul ih).const_add a
    have hv : polyDeriv (a :: L) x = 1 * polyEval L x + id x * polyDeriv L x := by
      simp [polyDeriv]
    rw [hfun, hv]
    exact h

theorem up_of_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f' x) :
    f a < f b := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have := hpos c hc
  rw [hcs, lt_div_iff₀ (by linarith)] at this
  linarith

theorem down_of_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Set.Ioo a b, f' x < 0) :
    f b < f a := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have := hneg c hc
  rw [hcs, div_lt_iff₀ (by linarith)] at this
  linarith

/-- `N` changes sign once, `+ -> -`, on `S ∩ (0, oo)`: positive up to `a`, negative from
`b` on, strictly decreasing on the crossing cell `[a, b]`. -/
theorem sign_change_of_cell {S : Set ℝ} [S.OrdConnected] {N N' : ℝ → ℝ} {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb : b ∈ S)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt N (N' x) x) (hN' : ∀ x ∈ Set.Icc a b, N' x < 0)
    (hleft : ∀ x ∈ S, 0 < x → x ≤ a → 0 < N x) (hright : ∀ x ∈ S, b ≤ x → N x < 0)
    (h0 : (0 : ℝ) ∈ S) :
    ∃ s, 0 < s ∧ (∀ x ∈ S, 0 < x → x < s → 0 < N x) ∧ (∀ x ∈ S, s < x → N x < 0) := by
  have hS : Set.Icc 0 b ⊆ S := Set.OrdConnected.out ‹_› h0 hb
  have haS : a ∈ S := hS ⟨ha0.le, hab.le⟩
  have hNa : 0 < N a := hleft a haS ha0 le_rfl
  have hNb : N b < 0 := hright b hb le_rfl
  have hcont : ContinuousOn N (Set.Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨s, hs, _⟩ := intermediate_value_Ioo' hab.le hcont ⟨hNb, hNa⟩
  have hNs : N s = 0 := by assumption
  refine ⟨s, by linarith [hs.1], ?_, ?_⟩
  · intro x hx hx0 hxs
    rcases le_or_gt x a with h | h
    · exact hleft x hx hx0 h
    · have := down_of_deriv (f := N) hxs
        (fun y hy => hd y ⟨by linarith [hy.1], by linarith [hy.2, hs.2]⟩)
        (fun y hy => hN' y ⟨by linarith [hy.1], by linarith [hy.2, hs.2]⟩)
      linarith
  · intro x hx hsx
    rcases le_or_gt b x with h | h
    · exact hright x hx h
    · have := down_of_deriv (f := N) hsx
        (fun y hy => hd y ⟨by linarith [hy.1, hs.1], by linarith [hy.2]⟩)
        (fun y hy => hN' y ⟨by linarith [hy.1, hs.1], by linarith [hy.2]⟩)
      linarith

/-- Single crossing: `D 0 = 0`, `D' * P = N` with `P > 0`, `N` changes sign once `+ -> -`
at `s`, and `D lo > 0 > D hi`.  Then `D` has exactly one zero `c` on `S ∩ (0, oo)`, it lies
in `(lo, hi)`, and `D > 0` before it, `D < 0` after it. -/
theorem single_crossing_core {S : Set ℝ} [S.OrdConnected] (h0 : (0 : ℝ) ∈ S)
    {D D' P N : ℝ → ℝ} (hD0 : D 0 = 0)
    (hd : ∀ x ∈ S, HasDerivAt D (D' x) x)
    (hfac : ∀ x ∈ S, 0 < x → D' x * P x = N x) (hP : ∀ x ∈ S, 0 < x → 0 < P x)
    {s : ℝ} (hs : 0 < s) (hNpos : ∀ x ∈ S, 0 < x → x < s → 0 < N x)
    (hNneg : ∀ x ∈ S, s < x → N x < 0)
    {lo hi : ℝ} (hlo0 : 0 < lo) (hlohi : lo < hi) (hhi : hi ∈ S)
    (hDlo : 0 < D lo) (hDhi : D hi < 0) :
    ∃ c ∈ Set.Ioo lo hi, D c = 0 ∧
      ∀ x ∈ S, 0 < x → (x < c → 0 < D x) ∧ (c < x → D x < 0) := by
  have hsub : ∀ a ∈ S, ∀ b ∈ S, Set.Icc a b ⊆ S :=
    fun a ha b hb => Set.OrdConnected.out ‹_› ha hb
  have hpos' : ∀ x ∈ S, 0 < x → 0 < N x → 0 < D' x := by
    intro x hx hx0 hN
    have h1 := hfac x hx hx0; have h2 := hP x hx hx0
    by_contra hc; have hc := not_lt.mp hc
    nlinarith
  have hneg' : ∀ x ∈ S, 0 < x → N x < 0 → D' x < 0 := by
    intro x hx hx0 hN
    have h1 := hfac x hx hx0; have h2 := hP x hx hx0
    by_contra hc; have hc := not_lt.mp hc
    nlinarith
  have up : ∀ a ∈ S, ∀ b ∈ S, 0 ≤ a → a < b → b ≤ s → D a < D b := by
    intro a ha b hb ha0 hab hbs
    refine up_of_deriv hab (fun x hx => hd x (hsub a ha b hb hx)) ?_
    intro x hx
    have hxS := hsub a ha b hb (Set.Ioo_subset_Icc_self hx)
    exact hpos' x hxS (by linarith [hx.1]) (hNpos x hxS (by linarith [hx.1]) (by linarith [hx.2]))
  have down : ∀ a ∈ S, ∀ b ∈ S, s ≤ a → a < b → D b < D a := by
    intro a ha b hb hsa hab
    refine down_of_deriv hab (fun x hx => hd x (hsub a ha b hb hx)) ?_
    intro x hx
    have hxS := hsub a ha b hb (Set.Ioo_subset_Icc_self hx)
    exact hneg' x hxS (by linarith [hx.1]) (hNneg x hxS (by linarith [hx.1]))
  have hshi : s < hi := by
    by_contra hc; have hc := not_lt.mp hc
    have := up 0 h0 hi hhi le_rfl (by linarith) hc
    linarith
  set m := max s lo with hm
  have hmS : m ∈ S := hsub 0 h0 hi hhi ⟨by positivity, by
    rcases le_total s lo with h | h
    · simp [hm, h]; linarith
    · simp [hm, h]; linarith⟩
  have hDm : 0 < D m := by
    rcases le_total s lo with h | h
    · simpa [hm, h] using hDlo
    · have hms : m = s := by simp [hm, h]
      rw [hms]
      rw [hms] at hmS
      have := up 0 h0 s hmS le_rfl hs le_rfl
      linarith
  have hmhi : m < hi := max_lt hshi hlohi
  have hcont : ContinuousOn D (Set.Icc m hi) :=
    fun x hx => (hd x (hsub m hmS hi hhi hx)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hDc⟩ := intermediate_value_Ioo' hmhi.le hcont ⟨hDhi, hDm⟩
  have hcS : c ∈ S := hsub m hmS hi hhi (Set.Ioo_subset_Icc_self hc)
  have hsm : s ≤ m := le_max_left _ _
  have hlom : lo ≤ m := le_max_right _ _
  refine ⟨c, ⟨by linarith [hc.1], hc.2⟩, hDc, ?_⟩
  intro x hx hx0
  constructor
  · intro hxc
    rcases le_or_gt x s with h | h
    · have := up 0 h0 x hx le_rfl hx0 h
      linarith
    · have := down x hx c hcS h.le hxc
      linarith
  · intro hcx
    have := down c hcS x hx (by linarith [hc.1]) hcx
    linarith

/-- Domination: `D 0 = 0` and `N < 0` on `S ∩ (0, oo)` give `D < 0` there. -/
theorem dominated_core {S : Set ℝ} [S.OrdConnected] (h0 : (0 : ℝ) ∈ S)
    {D D' P N : ℝ → ℝ} (hD0 : D 0 = 0)
    (hd : ∀ x ∈ S, HasDerivAt D (D' x) x)
    (hfac : ∀ x ∈ S, 0 < x → D' x * P x = N x) (hP : ∀ x ∈ S, 0 < x → 0 < P x)
    (hNneg : ∀ x ∈ S, 0 < x → N x < 0) :
    ∀ x ∈ S, 0 < x → D x < 0 := by
  intro x hx hx0
  have hsub : Set.Icc 0 x ⊆ S := Set.OrdConnected.out ‹_› h0 hx
  have := down_of_deriv hx0 (fun y hy => hd y (hsub hy)) (by
    intro y hy
    have hyS := hsub (Set.Ioo_subset_Icc_self hy)
    have h1 := hfac y hyS hy.1; have h2 := hP y hyS hy.1; have h3 := hNneg y hyS hy.1
    by_contra hc; have hc := not_lt.mp hc
    nlinarith)
  linarith

/-- The best-member ladder.  Consecutive members `F j`, `F (j+1)` (`a ≤ j ≤ J`) cross at
`Λ j` (`F j` ahead before, `F (j+1)` ahead after) and the breakpoints are nondecreasing.
Then on `(Λ (j-1), Λ j)` (open at the ends of the window) `F j` is the unique maximum of
`F a, ..., F (J+1)`. -/
theorem ladder_core {S : Set ℝ} {F : ℕ → ℝ → ℝ} {Λ : ℕ → ℝ} {a J : ℕ}
    (hcross : ∀ j, a ≤ j → j ≤ J → ∀ x ∈ S, 0 < x →
      (x < Λ j → F (j + 1) x < F j x) ∧ (Λ j < x → F j x < F (j + 1) x))
    (hmono : ∀ j, a ≤ j → j < J → Λ j ≤ Λ (j + 1)) :
    ∀ j, a ≤ j → j ≤ J + 1 → ∀ x ∈ S, 0 < x →
      (j = a ∨ Λ (j - 1) < x) → (j = J + 1 ∨ x < Λ j) →
      ∀ k, a ≤ k → k ≤ J + 1 → k ≠ j → F k x < F j x := by
  have hmon : ∀ i i', a ≤ i → i ≤ i' → i' ≤ J → Λ i ≤ Λ i' := by
    intro i i' hi hii' hi'
    induction i', hii' using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact le_trans (ih (by omega)) (hmono k (by omega) (by omega))
  intro j hja hjJ x hx hx0 hleft hright k hka hkJ hkj
  rcases lt_or_gt_of_ne hkj with hkj | hkj
  · have hbelow : ∀ i, a ≤ i → i < j → Λ i < x := by
      intro i hia hij
      rcases hleft with h | h
      · omega
      · exact lt_of_le_of_lt (hmon i (j - 1) hia (by omega) (by omega)) h
    have climb : ∀ i, k ≤ i → i ≤ j → F k x ≤ F i x ∧ (k < i → F k x < F i x) := by
      intro i hki hij
      induction i, hki using Nat.le_induction with
      | base => exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
      | succ m hm ih =>
        have hstep := (hcross m (by omega) (by omega) x hx hx0).2 (hbelow m (by omega) (by omega))
        have ih' := ih (by omega)
        exact ⟨le_trans ih'.1 hstep.le, fun _ => lt_of_le_of_lt ih'.1 hstep⟩
    exact (climb j hkj.le le_rfl).2 hkj
  · have habove : ∀ i, j ≤ i → i ≤ J → x < Λ i := by
      intro i hji hiJ
      rcases hright with h | h
      · omega
      · exact lt_of_lt_of_le h (hmon j i hja hji hiJ)
    have desc : ∀ i, j ≤ i → i ≤ k → F i x ≤ F j x ∧ (j < i → F i x < F j x) := by
      intro i hji hik
      induction i, hji using Nat.le_induction with
      | base => exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
      | succ m hm ih =>
        have hstep := (hcross m (by omega) (by omega) x hx hx0).1 (habove m hm (by omega))
        have ih' := ih (by omega)
        exact ⟨le_trans hstep.le ih'.1, fun _ => lt_of_lt_of_le hstep ih'.1⟩
    exact (desc k hkj.le le_rfl).2 hkj
"""

def _lean_jpoly(p: sp.Expr) -> str:
    """A polynomial in j with rational coefficients, over `(j : ℝ)`."""
    P = sp.Poly(sp.expand(p), J_SYM, domain="QQ")
    d = max(P.degree(), 0)
    return _poly1([P.coeff_monomial(J_SYM ** k) for k in range(d + 1)], var="(j : ℝ)")


def _lean_jexpr(e: sp.Expr) -> str:
    num, den = sp.fraction(sp.together(e))
    n = _lean_jpoly(num)
    if sp.Poly(den, J_SYM).degree() == 0 and sp.Rational(den) == 1:
        return n
    return f"{n} / {_lean_jpoly(den)}"


def _lean_list(cs) -> str:
    return "[" + ", ".join(_q(c) for c in cs) + "]"


@dataclass
class SingleCrossingLadderEmitter(Emitter):
    """Emit the generic single-crossing ladder theory once, then per instance the family,
    the sign cells, the factorisations, the bracket values, one crossing or domination
    theorem per pair, the bracket order and the capstone ``<nm>`` (the instance name).

    HONEST SCOPE: the ladder over the finite window of members ``a..J+1``; breakpoints
    pinned to rational brackets.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "single_crossing_ladder"

    def emit_units(self, fam, profile: LeanProfile):
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts = [_GENERIC]
        names: dict = {}
        used: set = set()
        for inst in fam.instances:
            text, _n = self._emit_instance(inst.payload, inst.lean_name, names, used)
            parts.append(text)
        body = "\n".join(parts)
        nthm = sum(1 for ln in body.split("\n") if ln.startswith("theorem "))
        return body, nthm

    # -- per instance -------------------------------------------------------------------
    def _emit_instance(self, c: SingleCrossingCert, nm: str, names: dict,
                       used: set) -> tuple[str, int]:
        L: list[str] = []
        n = 0
        bounded = c.X is not None
        S = f"Set.Icc (0 : ℝ) {_q(c.X)}" if bounded else "Set.Ici (0 : ℝ)"
        x0 = "hx.1" if bounded else "(Set.mem_Ici.mp hx)"
        mem0 = ("Set.left_mem_Icc.mpr (by norm_num)" if bounded
                else "Set.self_mem_Ici")

        def mem(_q_unused) -> str:
            return ("⟨by norm_num, by norm_num⟩" if bounded
                    else "Set.mem_Ici.mpr (by norm_num)")

        fam_txt = " + ".join(f"({sp.sstr(k)}) log(1 + ({sp.sstr(b)}) x)" for k, b in c.terms)
        dom_txt = f"Icc 0 ({c.X})" if bounded else "Ici 0"
        L.append(f"/-! ## Instance `{nm}`\n\n"
                 f"Family `F_j(x) = {fam_txt}` on `S = {dom_txt}`, members j = {c.a}..{c.J + 1}.\n"
                 f"Pairs: {len(c.dominated)} dominated, {len(c.crossings)} crossing "
                 f"(brackets {', '.join(f'{p.j}: ({p.lo}, {p.hi})' for p in c.crossings)}).\n"
                 f"conjecture1_proved = False. -/\n")
        items = ", ".join(f"({_lean_jexpr(k)}, {_lean_jexpr(b)})" for k, b in c.terms)
        L.append(f"noncomputable def {nm}_terms (j : ℕ) : List (ℝ × ℝ) :=\n  [{items}]\n")
        L.append(f"noncomputable def {nm}_F (j : ℕ) (x : ℝ) : ℝ := logSum ({nm}_terms j) x\n")
        L.append(f"/-- The domain `S`. -/\nabbrev {nm}_S : Set ℝ := {S}\n")

        # positivity of every log argument of every member on S
        nt = len(c.terms)
        rc = " | ".join(["rfl"] * nt)
        L.append(f"theorem {nm}_argpos (j : ℕ) (hj : {c.a} ≤ j ∧ j ≤ {c.J + 1}) :\n"
                 f"    ∀ x ∈ {nm}_S, ∀ p ∈ {nm}_terms j, 0 < 1 + p.2 * x := by\n"
                 f"  obtain ⟨hj1, hj2⟩ := hj\n"
                 f"  intro x hx p hp\n"
                 f"  have hx0 : (0 : ℝ) ≤ x := {x0}\n"
                 + ("" if not bounded else f"  have hxX : x ≤ {_q(c.X)} := hx.2\n")
                 + f"  interval_cases j <;>\n"
                 f"  · simp only [{nm}_terms, List.mem_cons, List.not_mem_nil, or_false] at hp\n"
                 f"    rcases hp with {rc} <;> norm_num <;> nlinarith\n")
        n += 1

        for p in c.pairs:
            t, n_add = self._emit_pair(c, p, nm, S, x0, mem0, mem, names, used)
            L.append(t)
            n += n_add

        # bracket order
        cr = c.crossings
        if len(cr) >= 2:
            facts = " ∧ ".join(f"{_q(p.hi)} < {_q(q.lo)}" for p, q in zip(cr, cr[1:]))
            L.append(f"/-- (b) the brackets increase, so the breakpoints do. -/\n"
                     f"theorem {nm}_brackets_increasing : {facts} := by norm_num\n")
            n += 1

        # the capstone and the rational-interval corollaries
        L.append(self._ladder(c, nm, mem0))
        n += 1
        best = self._best(c, nm)
        L.extend(best)
        n += len(best)
        return "\n".join(L), n

    def _best(self, c: SingleCrossingCert, nm: str) -> list:
        """Per winning member j: on the rational interval between the brackets, F j is the
        unique maximum of the window (a corollary of the ladder)."""
        a, J = c.a, c.J
        mode = {p.j: p for p in c.pairs}
        pat = ["Λ"] + [f"hL{p.j}" for p in c.pairs] + ["hmono", "hlad"]
        facts = []
        for p in c.pairs:
            facts += [f"hL{p.j}"] if p.mode == "dominated" else [f"hL{p.j}.1", f"hL{p.j}.2.1"]
        out = []
        for j in range(a, J + 2):
            if j <= J and mode[j].mode == "dominated":
                continue
            left_open = j == a or mode[j - 1].mode == "dominated"
            hyps, conds = [], []
            if not left_open:
                hyps.append(f"{_q(mode[j - 1].hi)} ≤ x")
            if j <= J:
                hyps.append(f"x ≤ {_q(mode[j].lo)}")
            lc = "Or.inl rfl" if j == a else f"Or.inr (by norm_num; linarith [{', '.join(facts)}])"
            rc = "Or.inl rfl" if j == J + 1 else f"Or.inr (by linarith [{', '.join(facts)}])"
            where = " ∧ ".join(hyps) if hyps else "True"
            hb = "hb" if hyps else "_hb"
            unpack = ""
            if len(hyps) == 2:
                unpack = "  obtain ⟨hb1, hb2⟩ := hb\n"
            out.append(f"/-- On `{where}`, member {j} is the UNIQUE maximum of members {a}..{J + 1}. -/\n"
                       f"theorem {nm}_best_{j} : ∀ x ∈ {nm}_S, 0 < x → {where} →\n"
                       f"    ∀ k, {a} ≤ k → k ≤ {J + 1} → k ≠ {j} → {nm}_F k x < {nm}_F {j} x := by\n"
                       f"  obtain ⟨{', '.join(pat)}⟩ := {nm}\n"
                       f"  intro x hx hx0 {hb}\n" + unpack +
                       f"  exact hlad {j} (by norm_num) (by norm_num) x hx hx0\n"
                       f"    ({lc})\n"
                       f"    ({rc})\n")
        return out

    def _cell_lemma(self, nm: str, cell_nm: str, pc: PolyCert, coeffs: tuple, sign: int,
                    deriv: bool = False) -> str:
        fn = "polyDeriv" if deriv else "polyEval"
        rel = (f"0 < {fn} {_lean_list(coeffs)} x" if sign > 0
               else f"{fn} {_lean_list(coeffs)} x < 0")
        hyps = f"(hs : 0 ≤ x - {_q(pc.s)})"
        if pc.t is not None:
            hyps += f" (ht : 0 ≤ {_q(pc.t)} - x)"
        unf = "polyDeriv, polyEval" if deriv else "polyEval"
        return (f"theorem {cell_nm} (x : ℝ) {hyps} :\n    {rel} := by\n"
                f"  simp only [{unf}]\n"
                f"  linarith [{_facts(pc)}]\n")

    def _cover_proof(self, cells: list, cell_names: list) -> str:
        """Tactic text: x in [cells[0].s, cells[-1].t] -> the cells' conclusion, by a
        le_or_gt chain (the bounds `s0 ≤ x`, `x ≤ t_last` are in context for linarith)."""
        out = []
        for i, (cell, cn) in enumerate(zip(cells, cell_names)):
            last = i == len(cells) - 1
            args = "(by linarith)" + ("" if cell.t is None else " (by linarith)")
            if last:
                out.append(f"  exact {cn} x {args}")
            else:
                out.append(f"  rcases le_or_gt x {_q(cell.t)} with h{i} | h{i}")
                out.append(f"  · exact {cn} x {args}")
        return "\n".join(out) + "\n"

    def _enc_atoms(self, enc: EnclosureTreeCert, base: str, names: dict, used: set) -> tuple:
        """Emit the non-root theorems of an enclosure (shared atoms once); return the text
        and the names of the frontier theorems the root would consume."""
        chunks = []
        k = 0
        for node in enc.order:
            if node.key == enc.root.key:
                continue
            if node.key in names:
                continue
            nmx = f"{base}_a{k}"
            k += 1
            while nmx in used:
                nmx += "'"
            used.add(nmx)
            names[node.key] = nmx
            chunks.append(_enc_header(node, nmx) + f"theorem {nmx} :\n    "
                          f"{_enc_statement(node)} := by\n" + _enc_proof_body(node, names))
        # the atom facts the root's linarith needs: every emitted non-root node
        facts = []
        for node in enc.order:
            if node.key != enc.root.key and node.key in names:
                facts.append(names[node.key])
        return "\n".join(chunks), facts

    def _emit_pair(self, c, p: PairCert, nm, S, x0, mem0, mem, names, used):
        L = []
        n = 0
        j, k = p.j, p.j + 1
        pre = f"{nm}_p{j}"
        Nl = _lean_list(p.N)
        # D' * P = N
        facs = [f"(1 + {_q(b)} * x)" for b in p.betas]
        Ptxt = " * ".join(facs)
        nes = "\n".join(f"  have hne{i} : 1 + {_q(b)} * x ≠ 0 := by nlinarith [hpos{i}]"
                        for i, b in enumerate(p.betas))
        poss = "\n".join(f"  have hpos{i} : 0 < 1 + {_q(b)} * x := by nlinarith"
                         for i, b in enumerate(p.betas))
        bnd = "" if c.X is None else f"  have hxX : x ≤ {_q(c.X)} := hx.2\n"
        L.append(f"/-! ### Pair j = {j}: `D = F {j} - F {k}`, `D' * P = N`,\n"
                 f"`N = {sp.sstr(sum(cc * X_SYM ** i for i, cc in enumerate(p.N)))}` -/\n")
        L.append(f"theorem {pre}_P_pos (x : ℝ) (hx : x ∈ {nm}_S) (hx0 : 0 < x) :\n"
                 f"    0 < {Ptxt} := by\n{bnd}{poss}\n  positivity\n"
                 if all(b > 0 for b in p.betas) else
                 f"theorem {pre}_P_pos (x : ℝ) (hx : x ∈ {nm}_S) (hx0 : 0 < x) :\n"
                 f"    0 < {Ptxt} := by\n{bnd}{poss}\n"
                 f"  exact {self._mul_pos(len(p.betas))}\n")
        L.append(f"theorem {pre}_fac (x : ℝ) (hx : x ∈ {nm}_S) (hx0 : 0 < x) :\n"
                 f"    (logSumDeriv ({nm}_terms {j}) x - logSumDeriv ({nm}_terms {k}) x) *\n"
                 f"      ({Ptxt}) = polyEval {Nl} x := by\n{bnd}{poss}\n{nes}\n"
                 f"  simp only [logSumDeriv, {nm}_terms, polyEval]\n"
                 f"  norm_num at hne{' hne'.join(str(i) for i in range(len(p.betas)))} ⊢\n"
                 f"  field_simp\n"
                 f"  ring\n")
        n += 2
        common = (f"  have hD0 : {nm}_F {j} 0 - {nm}_F {k} 0 = 0 := by simp [{nm}_F, logSum_zero]\n"
                  f"  have hd : ∀ x ∈ {nm}_S, HasDerivAt (fun y => {nm}_F {j} y - {nm}_F {k} y)\n"
                  f"      (logSumDeriv ({nm}_terms {j}) x - logSumDeriv ({nm}_terms {k}) x) x :=\n"
                  f"    fun x hx => (hasDerivAt_logSum _ x ({nm}_argpos {j} (by norm_num) x hx)).sub\n"
                  f"      (hasDerivAt_logSum _ x ({nm}_argpos {k} (by norm_num) x hx))\n")
        cell_txt = []
        if p.mode == "cross":
            a_c, b_c, cpc = p.cross_cell
            lnames, rnames = [], []
            for i, cell in enumerate(p.left):
                cn = f"{pre}_L{i}"
                lnames.append(cn)
                cell_txt.append(self._cell_lemma(nm, cn, cell.pc, p.N, 1))
            for i, cell in enumerate(p.right):
                cn = f"{pre}_R{i}"
                rnames.append(cn)
                cell_txt.append(self._cell_lemma(nm, cn, cell.pc, p.N, -1))
            cell_txt.append(self._cell_lemma(nm, f"{pre}_C", cpc, p.N, -1, deriv=True))
            n += len(p.left) + len(p.right) + 1
            L.extend(cell_txt)
            # N sign change
            left_proof = self._cover_proof(list(p.left), lnames)
            right_proof = self._cover_proof(list(p.right), rnames)
            L.append(f"theorem {pre}_sign : ∃ s, 0 < s ∧\n"
                     f"    (∀ x ∈ {nm}_S, 0 < x → x < s → 0 < polyEval {Nl} x) ∧\n"
                     f"    (∀ x ∈ {nm}_S, s < x → polyEval {Nl} x < 0) := by\n"
                     f"  have hleft : ∀ x ∈ {nm}_S, 0 < x → x ≤ {_q(a_c)} → 0 < polyEval {Nl} x := by\n"
                     f"    intro x hx hx0 hxa\n"
                     + _indent(left_proof, 2) +
                     f"  have hright : ∀ x ∈ {nm}_S, {_q(b_c)} ≤ x → polyEval {Nl} x < 0 := by\n"
                     f"    intro x hx hxb\n"
                     + ("" if c.X is None else f"    have hxX : x ≤ {_q(c.X)} := hx.2\n")
                     + _indent(right_proof, 2) +
                     f"  exact sign_change_of_cell (S := {nm}_S) (N' := polyDeriv {Nl})\n"
                     f"    (by norm_num) (by norm_num) ({mem(b_c)})\n"
                     f"    (fun x _ => hasDerivAt_polyEval {Nl} x)\n"
                     f"    (fun x hx => {pre}_C x (by linarith [hx.1]) (by linarith [hx.2]))\n"
                     f"    hleft hright ({mem0})\n")
            n += 1
            # bracket values
            t_lo, f_lo = self._enc_atoms(p.enc_lo, f"{pre}_vlo", names, used)
            t_hi, f_hi = self._enc_atoms(p.enc_hi, f"{pre}_vhi", names, used)
            L.append(t_lo)
            L.append(t_hi)
            n += t_lo.count("\ntheorem ") + t_lo.startswith("theorem ")
            n += t_hi.count("\ntheorem ") + t_hi.startswith("theorem ")
            L.append(self._value_thm(nm, pre, j, k, p.lo, f_lo, positive=True))
            L.append(self._value_thm(nm, pre, j, k, p.hi, f_hi, positive=False))
            n += 2
            L.append(f"/-- (a) `F {j}` and `F {k}` cross EXACTLY ONCE on `S ∩ (0, oo)`, at a point of\n"
                     f"`({p.lo}, {p.hi})`: `F {j}` is ahead before it, `F {k}` after it. -/\n"
                     f"theorem {pre}_cross : ∃ c ∈ Set.Ioo ({_q(p.lo)}) ({_q(p.hi)}),\n"
                     f"    {nm}_F {j} c = {nm}_F {k} c ∧ ∀ x ∈ {nm}_S, 0 < x →\n"
                     f"      (x < c → {nm}_F {k} x < {nm}_F {j} x) ∧ (c < x → {nm}_F {j} x < {nm}_F {k} x) := by\n"
                     + common +
                     f"  obtain ⟨s, hs, hNp, hNn⟩ := {pre}_sign\n"
                     f"  obtain ⟨c, hc, hDc, hsg⟩ := single_crossing_core (S := {nm}_S)\n"
                     f"    (P := fun x => {Ptxt}) ({mem0}) hD0 hd {pre}_fac {pre}_P_pos\n"
                     f"    hs hNp hNn (by norm_num) (by norm_num) ({mem(p.hi)}) {pre}_vlo {pre}_vhi\n"
                     f"  refine ⟨c, hc, by linarith, fun x hx hx0 => ⟨fun h => ?_, fun h => ?_⟩⟩\n"
                     f"  · have := (hsg x hx hx0).1 h; linarith\n"
                     f"  · have := (hsg x hx hx0).2 h; linarith\n")
            n += 1
        else:
            rnames = []
            for i, cell in enumerate(p.right):
                cn = f"{pre}_R{i}"
                rnames.append(cn)
                L.append(self._cell_lemma(nm, cn, cell.pc, p.N, -1))
            n += len(p.right)
            proof = self._cover_proof(list(p.right), rnames)
            L.append(f"/-- `F {k}` beats `F {j}` on all of `S ∩ (0, oo)` (no crossing). -/\n"
                     f"theorem {pre}_dom : ∀ x ∈ {nm}_S, 0 < x → {nm}_F {j} x < {nm}_F {k} x := by\n"
                     + common +
                     f"  have hN : ∀ x ∈ {nm}_S, 0 < x → polyEval {Nl} x < 0 := by\n"
                     f"    intro x hx hx0\n"
                     + ("" if c.X is None else f"    have hxX : x ≤ {_q(c.X)} := hx.2\n")
                     + _indent(proof, 2) +
                     f"  intro x hx hx0\n"
                     f"  have := dominated_core (S := {nm}_S) (P := fun x => {Ptxt})\n"
                     f"    ({mem0}) hD0 hd {pre}_fac {pre}_P_pos hN x hx hx0\n"
                     f"  linarith\n")
            n += 1
        return "\n".join(L), n

    @staticmethod
    def _mul_pos(m: int) -> str:
        e = "hpos0"
        for i in range(1, m):
            e = f"mul_pos ({e}) hpos{i}"
        return e

    def _value_thm(self, nm, pre, j, k, x, facts, *, positive: bool) -> str:
        nmv = f"{pre}_vlo" if positive else f"{pre}_vhi"
        stmt = (f"0 < {nm}_F {j} {_q(x)} - {nm}_F {k} {_q(x)}" if positive
                else f"{nm}_F {j} {_q(x)} - {nm}_F {k} {_q(x)} < 0")
        haves = "\n".join(f"  have h{i} := {f}" for i, f in enumerate(facts))
        hs = " ".join(f"h{i}" for i in range(len(facts)))
        return (f"theorem {nmv} : {stmt} := by\n{haves}\n"
                f"  simp only [{nm}_F, {nm}_terms, logSum]\n"
                f"  norm_num at {hs} ⊢\n"
                f"  linarith [{', '.join(f'h{i}.1, h{i}.2' for i in range(len(facts)))}]\n")

    def _ladder(self, c: SingleCrossingCert, nm: str, mem0: str) -> str:
        a, J = c.a, c.J
        cr = c.crossings
        # Λ as nested ifs over the crossing indices; dominated ones are 0
        lam = "0"
        for p in reversed(cr):
            lam = f"if j = {p.j} then c{p.j} else {lam}"
        facts = []
        for p in c.dominated:
            facts.append(f"Λ {p.j} = 0")
        for p in cr:
            facts.append(f"({_q(p.lo)} < Λ {p.j} ∧ Λ {p.j} < {_q(p.hi)} ∧ "
                         f"{nm}_F {p.j} (Λ {p.j}) = {nm}_F {p.j + 1} (Λ {p.j}))")
        head = " ∧\n    ".join(facts)
        obt = "\n".join(f"  obtain ⟨c{p.j}, hc{p.j}, hz{p.j}, hs{p.j}⟩ := {nm}_p{p.j}_cross"
                        for p in cr)
        n_facts = len(facts)
        refine_holes = ", ".join(["?_"] * (n_facts + 2))
        lines = [f"/-- (c) THE LADDER over members {a}..{J + 1}: the breakpoints `Λ j` (0 for a\n"
                 f"dominated pair, the unique crossing in its bracket otherwise) and, on\n"
                 f"`(Λ (j-1), Λ j)`, `F j` is the UNIQUE maximum of `F {a}, ..., F {J + 1}`. -/\n"
                 f"theorem {nm} : ∃ Λ : ℕ → ℝ,\n    {head} ∧\n"
                 f"    (∀ j, {a} ≤ j → j < {J} → Λ j ≤ Λ (j + 1)) ∧\n"
                 f"    (∀ j, {a} ≤ j → j ≤ {J + 1} → ∀ x ∈ {nm}_S, 0 < x →\n"
                 f"      (j = {a} ∨ Λ (j - 1) < x) → (j = {J + 1} ∨ x < Λ j) →\n"
                 f"      ∀ k, {a} ≤ k → k ≤ {J + 1} → k ≠ j → {nm}_F k x < {nm}_F j x) := by",
                 obt,
                 f"  have hcross : ∀ j, {a} ≤ j → j ≤ {J} → ∀ x ∈ {nm}_S, 0 < x →\n"
                 f"      (x < (fun j : ℕ => {lam}) j → {nm}_F (j + 1) x < {nm}_F j x) ∧\n"
                 f"      ((fun j : ℕ => {lam}) j < x → {nm}_F j x < {nm}_F (j + 1) x) := by\n"
                 f"    intro j hja hjJ x hx hx0\n"
                 f"    interval_cases j"]
        for p in c.pairs:
            if p.mode == "dominated":
                lines.append(f"    · refine ⟨fun h => ?_, fun _ => by simpa using "
                             f"{nm}_p{p.j}_dom x hx hx0⟩\n"
                             f"      simp at h; linarith")
            else:
                lines.append(f"    · simpa using hs{p.j} x hx hx0")
        lines.append(f"  have hmono : ∀ j, {a} ≤ j → j < {J} → (fun j : ℕ => {lam}) j ≤\n"
                     f"      (fun j : ℕ => {lam}) (j + 1) := by\n"
                     f"    intro j hja hjJ\n"
                     + (f"    omega" if J == a else
                        f"    interval_cases j <;> simp <;> linarith "
                        f"[{', '.join(f'hc{p.j}.1, hc{p.j}.2' for p in cr) or 'le_rfl'}]"))
        lines.append(f"  refine ⟨fun j : ℕ => {lam}, {refine_holes}⟩")
        for p in c.dominated:
            lines.append("  · simp")
        for p in cr:
            lines.append(f"  · simp\n"
                         f"    exact ⟨hc{p.j}.1, hc{p.j}.2, hz{p.j}⟩")
        lines.append("  · exact hmono")
        lines.append(f"  · exact ladder_core (a := {a}) (J := {J}) hcross hmono")
        return "\n".join(lines) + "\n"


def _indent(text: str, k: int) -> str:
    pad = "  " * (k - 1)
    return "".join(pad + ln + "\n" if ln else "\n" for ln in text.rstrip("\n").split("\n"))


def single_crossing_ladder_family(name, grid, lean_name, spec, constants=None):
    """Build a single-crossing ladder family (kind='single_crossing_ladder').

    ``spec``: a callable ``pt -> dict`` of :func:`single_crossing_ladder_certificate`
    keyword arguments (``terms``, ``a``, ``J``, ``brackets``, ``X``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("single_crossing_ladder", spec),
        constants=dict(constants or {}),
    )


#: The running example: the per-vertex log-weight of an arm with j cherries under the
#: matching sum with activity x,
#:   F_j(x) = [j log((2+x)/2) + log((j+1 + x j/(2+x))/(j+1))] / (2j+1)
#:          = ((j-1)/(2j+1)) log(1 + x/2) + (1/(2j+1)) log(1 + (2j+1)/(2j+2) x).
#: Arms 1 and 2 are dominated (never best); arms 3..7 form the ladder with breakpoints
#: lambda_3..lambda_6 bracketed to 1e-5.
ARM_LADDER_SPEC = dict(
    terms=[("(j-1)/(2*j+1)", "1/2"), ("1/(2*j+1)", "(2*j+1)/(2*j+2)")],
    a=1, J=6,
    brackets={3: ("43050/100000", "43051/100000"),
              4: ("87247/100000", "87248/100000"),
              5: ("119239/100000", "119240/100000"),
              6: ("143559/100000", "143560/100000")},
    X=None,
)

#: One pair of the arm ladder (A_3 against A_4) with the TRUE 1e-5 bracket of lambda_3; the
#: negative control shifts it two grid steps right, (0.43052, 0.43053), which misses
#: lambda_3 = 0.4305018...: D(0.43052) < 0, so the claim D(lo) > 0 is FALSE.
ARM_PAIR3_SPEC = dict(ARM_LADDER_SPEC, a=3, J=3, brackets={3: ("43050/100000", "43051/100000")})
ARM_PAIR3_WRONG_BRACKET_SPEC = dict(ARM_PAIR3_SPEC,
                                    brackets={3: ("43052/100000", "43053/100000")})

#: SYNTHETIC (no combinatorial meaning): F_0 = 0 and
#: F_1 = log(1+x) - (3/2) log(1+x/10) - (1/2) log(1+2x), so D = F_0 - F_1 rises, crosses
#: zero near 0.9713, and crosses AGAIN near 4.3153 (N has roots ~0.307 and ~2.443).  On
#: S = [0, 2] the crossing is single (and certified); on [0, oo) the single-crossing claim is FALSE (refused by Layer 1; the
#: forged certificate is the double-crossing negative control).
DOUBLE_DIP_BOUNDED_SPEC = dict(
    terms=[("j", "1"), ("-3*j/2", "1/10"), ("-j/2", "2")],
    a=0, J=0,
    brackets={0: ("97/100", "98/100")},
    X="2",
)

#: The same family on [0, oo): a double crossing, claimed single (FALSE).
DOUBLE_DIP_UNBOUNDED_SPEC = dict(DOUBLE_DIP_BOUNDED_SPEC, X=None)


if __name__ == "__main__":
    c = single_crossing_ladder_certificate(**ARM_LADDER_SPEC)
    for p in c.pairs:
        extra = f" cross cell {p.cross_cell[:2]}" if p.mode == "cross" else ""
        print(f"j={p.j} {p.mode} N={p.N} left={len(p.left)} right={len(p.right)}{extra}")

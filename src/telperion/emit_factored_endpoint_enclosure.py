"""factored_endpoint_enclosure emitter -- an inequality ``F >= 0`` on closed boxes that TOUCH a
singular endpoint, by factoring out the vanishing power and checking the cofactor's sign.

conjecture1_proved = False.  This module certifies elementary real inequalities in one or two
variables; it says nothing about any open conjecture.

THE SHAPE
---------
Variables ``l`` (the parameter with the endpoint) and, optionally, ``x``.  The claim is

    0 <= F(l, x)    for every  l in [A, B],  x in [C, D]          (closed box)

where ``F`` vanishes at an endpoint ``l = s`` (``s <= A``, side ``right``; or ``s >= B``,
side ``left``) to order ``k``.  The quantity of interest is usually the quotient
``F / (l - s)^k``, which naive interval evaluation cannot enclose near ``l = s`` (``0/0``).
Example: ``F = l - log(1 + l)``; the quotient ``F / l = 1 - (1/l) log(1 + l)`` is undefined
at ``l = 0`` and ``F`` itself has zero margin there.

``F`` is a rational function of ``(l, x)`` plus ``log(1 + u_i)`` atoms with polynomial
``u_i >= 0``, written over a positive denominator as

    D * F = N0 + sum_i kappa_i * log(1 + u_i)        (D, N0, kappa_i, u_i polynomials).

THE CERTIFICATE
---------------
* Each ``log`` atom is replaced by its Taylor polynomial ``T_n(u)`` whose remainder has the
  needed SIGN on all of ``[0, oo)`` (``transcendental_enclosure``, face ``log_taylor``):
  odd ``n`` when ``kappa_i <= 0`` (``log <= T_n``), even ``n`` when ``kappa_i >= 0``.  So
  ``Q := N0 + sum kappa_i T_{n_i}(u_i) <= D * F`` on the domain.
* The FACTORIZATION ``Q = (sigma (l - s))^k * H`` holds as an exact polynomial identity
  (``sigma = +1`` right, ``-1`` left); ``H`` is computed by exact division (or supplied and
  checked).  No Taylor at all when ``F`` has no atoms: then ``Q = D F`` exactly (the
  closed-form route).
* A BOX COVER of the domain by bisection.  On each box, with exact rational arithmetic:
  ``H >= 0`` (tensor Bernstein coefficients), ``u_i >= 0``, ``sigma_i kappa_i >= 0``, and
  every irreducible factor of ``D`` ``> 0``.  The boxes touching ``l = s`` are ordinary
  boxes: ``H`` is a polynomial, so the endpoint is not special any more.

LEAN (generic section once per file; every theorem sorry-free)
--------------------------------------------------------------
``factored_endpoint_core`` -- the ONE generic lemma: on any box predicate, ``0 <= t``,
``0 < D``, ``Q <= D * F``, ``Q = t^k * H`` and ``0 <= H`` give ``0 <= F``, endpoint
included.  Plus the ``log_taylor`` section (generic ``log_le_T`` / ``T_le_log`` and the
explicit orders used).  Per instance: definitions ``F, D, Q, H``; the factorization
``_fac`` (``ring``); per box ``_bi_H`` (``linarith`` over Bernstein products), ``_bi_D``,
``_bi_low`` (``field_simp; ring`` for ``D * F``, the Taylor atoms, ``linarith``) and
``_bi`` (the core lemma); the union ``<nm>`` over the closed domain (``le_total`` along the
bisection tree), and ``<nm>_quot``: ``0 <= F / (sigma (l - s))^k`` off the endpoint.

ANTI-PHANTOM REFUSALS
---------------------
``factored_endpoint_certificate`` refuses: floats; functions other than ``log`` (no ``sin``,
``exp``, ...); a ``log`` argument that is not a polynomial, a ``log`` that is not linear in
the cleared numerator (products / nested logs); a denominator with a log; an endpoint ``s``
inside the open domain; ``k`` outside ``1..12``; an empty or reversed range; a ``u_i`` not
certified ``>= 0``, a ``kappa_i`` that changes sign, a denominator factor not certified
``> 0``; a ``Q`` that the claimed power ``(l - s)^k`` does not divide (wrong ``k``); a
supplied ``H`` that does not match; an ``H`` not certified ``>= 0`` to the bisection limit
-- reported FALSE with an exact rational point of a 9 x 9 sample grid where ``F < 0`` (60
digits) when one is found, otherwise OBSTRUCTED.  ``check=False`` is for
hand-forged negative controls ONLY: the same algebra with the sign checks skipped, so the
kernel is the arbiter.

HONEST SCOPE: the Taylor-with-signed-remainder route covers ``log(1 + u)`` atoms only; the
mean-value route (derivative bounds on the hull) is not implemented.  Boxes are closed and
rational; the quotient corollary is stated off the endpoint only (at ``l = s`` Lean's
``F / 0 = 0`` would make it vacuous).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb

import sympy as sp

from .certify import CertifiedInstance
from .emit_transcendental_enclosure import (
    LOG_TAYLOR_MAX_ORDER,
    log_taylor_lean,
    log_taylor_poly,
)
from .family import InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

L_SYM = sp.Symbol("l")
X_SYM = sp.Symbol("x")

#: bisection depth of the box cover
_MAX_DEPTH = 10
#: per-variable degree cap of every certified polynomial (Lean cost of the product facts)
_MAX_DEGREE = 12
#: vanishing-order cap
_MAX_K = 12
#: box cap (one group of theorems per box)
_MAX_BOXES = 64
#: Lean namespace of the shared log Taylor section
_LT_NS = "FEELogTaylor"


class FactoredEndpointRefusal(ValueError):
    """Raised when the certificate cannot be built or verified."""


def _refuse(msg: str) -> FactoredEndpointRefusal:
    return FactoredEndpointRefusal(f"factored_endpoint_enclosure REFUSED: {msg}")


def _rat(v, what: str) -> sp.Rational:
    if isinstance(v, (bool, float)):
        raise _refuse(f"{what} = {v!r}: floats/bools are not exact; pass a Rational or a string")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    try:
        r = sp.sympify(v) if isinstance(v, str) else sp.sympify(v)
    except (TypeError, ValueError, sp.SympifyError):
        raise _refuse(f"{what} = {v!r} is not an exact rational") from None
    if not getattr(r, "is_Rational", False):
        raise _refuse(f"{what} = {v!r} is not an exact rational")
    return sp.Rational(r)


def _poly(e, gens) -> sp.Poly:
    return sp.Poly(sp.expand(e), *gens, domain="QQ")


# ---------------------------------------------------------------------------
# parsing F
# ---------------------------------------------------------------------------

def _parse(F, two_var: bool):
    """Return (F_expr, N0, atoms, D_const, D_factors) with
    ``D * F = N0 + sum kappa_i log(1 + u_i)``, ``D = D_const * prod f^e``."""
    if isinstance(F, float):
        raise _refuse(f"F = {F!r} is a float")
    loc = {"l": L_SYM, "x": X_SYM, "log": sp.log}
    try:
        ex = sp.sympify(F, locals=loc) if isinstance(F, str) else sp.sympify(F)
    except (TypeError, ValueError, sp.SympifyError) as e:
        raise _refuse(f"F = {F!r} does not parse: {e}") from None
    if ex.atoms(sp.Float):
        raise _refuse(f"F = {ex}: contains a float")
    allowed = {L_SYM, X_SYM} if two_var else {L_SYM}
    if not ex.free_symbols <= allowed:
        raise _refuse(f"F = {ex}: free symbols {sorted(map(str, ex.free_symbols - allowed))} "
                      f"(allowed: {', '.join(sorted(map(str, allowed)))}; give x_range for x)")
    for fn in ex.atoms(sp.Function):
        if not isinstance(fn, sp.log):
            raise _refuse(f"F contains {fn.func}: only log(1 + u) atoms have a signed-remainder "
                          f"enclosure (no sin/exp/... enclosure here)")
    if ex.atoms(sp.Pow) and any(not p.exp.is_Integer for p in ex.atoms(sp.Pow)):
        raise _refuse(f"F = {ex}: non-integer powers are not supported")
    gens = (L_SYM, X_SYM)
    logs = sorted(ex.atoms(sp.log), key=sp.default_sort_key)
    dums = sp.symbols(f"_lg0:{len(logs)}") if logs else ()
    atoms_u = []
    for lg in logs:
        arg = lg.args[0]
        if arg.atoms(sp.log):
            raise _refuse(f"nested log {lg}")
        try:
            _poly(arg, gens)
        except sp.PolynomialError:
            raise _refuse(f"log argument {arg} is not a polynomial in (l, x)") from None
        atoms_u.append(sp.expand(arg - 1))
    sub = dict(zip(logs, dums))
    num, den = sp.fraction(sp.together(ex.xreplace(sub)))
    if den.free_symbols & set(dums):
        raise _refuse("a log appears in the denominator of F")
    try:
        pn = _poly(num, gens + tuple(dums))
        pd = _poly(den, gens)
    except sp.PolynomialError:
        raise _refuse(f"F = {ex} is not a rational function of (l, x) plus log atoms") from None
    for mon in pn.monoms():
        if sum(mon[2:]) > 1:
            raise _refuse("F is not linear in its log atoms (a product or power of logs)")
    c0, facs = sp.factor_list(pd.as_expr())
    c0 = sp.Rational(c0)
    factors = []
    for f, e in facs:
        f = sp.expand(f)
        if f.free_symbols == set():
            c0 *= sp.Rational(f) ** e
            continue
        factors.append([f, int(e)])
    # fold the constant into the numerator: D = prod f^e (monic up to sign normalisation)
    D_const = sp.Integer(1)
    pe = sp.expand(num / c0)
    N0 = sp.expand(pe.subs({d: 0 for d in dums}))
    atoms = []
    for d, u in zip(dums, atoms_u):
        kap = sp.expand(sp.diff(pe, d))
        if kap != 0:
            atoms.append((kap, u))
    return ex, N0, tuple(atoms), D_const, factors


# ---------------------------------------------------------------------------
# tensor Bernstein form on a box
# ---------------------------------------------------------------------------

def _degs(P: sp.Poly) -> tuple[int, int]:
    if P.is_zero:
        return 0, 0
    return max(m[0] for m in P.monoms()), max(m[1] for m in P.monoms())


def bernstein2(P: sp.Poly, a, b, c, d) -> tuple[int, int, tuple]:
    """``P = sum w_ij (l-a)^i (b-l)^(p-i) (x-c)^j (d-x)^(q-j)`` with exact ``w_ij``.

    ``c, d = None`` for a polynomial in ``l`` alone (``q = 0``).  Returns ``(p, q, w)`` with
    ``w[i][j]``."""
    p, q = _degs(P)
    S, T = sp.Symbol("_S"), sp.Symbol("_T")
    if c is None:
        sub = {L_SYM: a + (b - a) * S, X_SYM: 0}
        q = 0
    else:
        sub = {L_SYM: a + (b - a) * S, X_SYM: c + (d - c) * T}
    G = sp.Poly(sp.expand(P.as_expr().subs(sub, simultaneous=True)), S, T, domain="QQ")
    A = {m: sp.Rational(v) for m, v in zip(G.monoms(), G.coeffs())}
    w = []
    sc_l = (b - a) ** p
    sc_x = 1 if c is None else (d - c) ** q
    for i in range(p + 1):
        row = []
        for j in range(q + 1):
            beta = sum(sp.Rational(comb(i, k), comb(p, k)) * sp.Rational(comb(j, m), comb(q, m))
                       * A.get((k, m), 0) for k in range(i + 1) for m in range(j + 1))
            row.append(sp.Rational(beta * comb(p, i) * comb(q, j)) / (sc_l * sc_x))
        w.append(tuple(row))
    return p, q, tuple(w)


def _bern_rhs(p, q, w, a, b, c, d):
    if c is None:
        return sum(w[i][0] * (L_SYM - a) ** i * (b - L_SYM) ** (p - i) for i in range(p + 1))
    return sum(w[i][j] * (L_SYM - a) ** i * (b - L_SYM) ** (p - i)
               * (X_SYM - c) ** j * (d - X_SYM) ** (q - j)
               for i in range(p + 1) for j in range(q + 1))


@dataclass(frozen=True)
class SignCert:
    """``0 <= P`` (or ``0 < P`` when ``strict``) on a box, as a tensor Bernstein form."""

    expr: object   # the polynomial (sympy expression in l, x)
    p: int
    q: int
    w: tuple
    strict: bool

    def ok(self) -> bool:
        flat = [v for row in self.w for v in row]
        return all(v > 0 for v in flat) if self.strict else all(v >= 0 for v in flat)


def _signcert(expr, box, strict: bool) -> SignCert:
    a, b, c, d = box
    P = _poly(expr, (L_SYM, X_SYM))
    p, q = _degs(P)
    if p > _MAX_DEGREE or q > _MAX_DEGREE:
        raise _refuse(f"a certified polynomial has degree ({p}, {q}) > {_MAX_DEGREE} "
                      f"(Lean cost)")
    p, q, w = bernstein2(P, a, b, c, d)
    return SignCert(expr=sp.expand(expr), p=p, q=q, w=w, strict=strict)


def _signcert_identity(sc: SignCert, box) -> bool:
    a, b, c, d = box
    return sp.expand(sc.expr - _bern_rhs(sc.p, sc.q, sc.w, a, b, c, d)) == 0


# ---------------------------------------------------------------------------
# certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BoxCert:
    """One box ``[a, b] x [c, d]`` (``c = d = None`` for one variable) and its sign facts."""

    box: tuple
    H: SignCert
    us: tuple        # SignCert per atom: 0 <= u_i
    kappas: tuple    # SignCert per atom: 0 <= sigma_i kappa_i
    dens: tuple      # SignCert per denominator factor: 0 < f

    def ok(self) -> bool:
        return all(sc.ok() for sc in (self.H, *self.us, *self.kappas, *self.dens))


@dataclass(frozen=True)
class FactoredEndpointCert:
    F: object            # the user's F (sympy expression)
    two_var: bool
    s: object
    k: int
    side: str            # "right" (s <= A) or "left" (s >= B)
    l_range: tuple
    x_range: tuple       # (None, None) for one variable
    N0: object
    atoms: tuple         # ((kappa, u, order, sign), ...); sign = +1 (kappa >= 0) or -1
    D_const: object
    D_factors: tuple     # ((f, e), ...)
    Q: object
    H: object
    boxes: tuple         # BoxCert, in tree order
    tree: tuple          # ("leaf", i) | ("split", var, mid, left, right)
    checked: bool

    @property
    def sigma(self) -> int:
        return 1 if self.side == "right" else -1

    @property
    def orders(self) -> tuple:
        return tuple(a[2] for a in self.atoms)


def _box_cert(box, H, atoms, factors) -> BoxCert:
    return BoxCert(
        box=box,
        H=_signcert(H, box, False),
        us=tuple(_signcert(u, box, False) for (_k, u, _n, _sg) in atoms),
        kappas=tuple(_signcert(sg * kap, box, False) for (kap, _u, _n, sg) in atoms),
        dens=tuple(_signcert(f, box, True) for f, _e in factors),
    )


def _split(box, two_var: bool):
    a, b, c, d = box
    if two_var and (d - c) > (b - a):
        m = (c + d) / 2
        return "x", m, (a, b, c, m), (a, b, m, d)
    m = (a + b) / 2
    return "l", m, (a, m, c, d), (m, b, c, d)


def _cover(box, H, atoms, factors, two_var, depth, max_depth, check, out):
    bc = _box_cert(box, H, atoms, factors)
    if bc.ok() or (not check and depth >= max_depth):
        out.append(bc)
        return ("leaf", len(out) - 1)
    if depth >= max_depth or len(out) >= _MAX_BOXES:
        return None
    var, m, lo, hi = _split(box, two_var)
    left = _cover(lo, H, atoms, factors, two_var, depth + 1, max_depth, check, out)
    if left is None:
        return None
    right = _cover(hi, H, atoms, factors, two_var, depth + 1, max_depth, check, out)
    if right is None:
        return None
    return ("split", var, m, left, right)


def _sample_points(box, two_var):
    a, b, c, d = box
    ls = [a + (b - a) * sp.Rational(i, 8) for i in range(9)]
    xs = [c + (d - c) * sp.Rational(j, 8) for j in range(9)] if two_var else [0]
    return [(lv, xv) for lv in ls for xv in xs]


def _find_violation(F_expr, domain, two_var):
    """An exact rational point of the domain where ``F < 0`` (evaluated to 60 digits; a
    value below ``-1e-40`` is a located violation of the claim), or None."""
    best = None
    for (lv, xv) in _sample_points(domain, two_var):
        try:
            v = sp.N(F_expr.subs({L_SYM: lv, X_SYM: xv}), 60)
        except (TypeError, ZeroDivisionError):  # pragma: no cover - a pole on the grid
            continue
        if v.is_real and v < sp.Rational(-1, 10 ** 40) and (best is None or v < best[0]):
            best = (v, lv, xv)
    return best


def _check_orders(orders, atoms):
    if orders is None:
        return None
    orders = tuple(orders)
    if len(orders) != len(atoms):
        raise _refuse(f"orders has {len(orders)} entries but F has {len(atoms)} log atoms")
    for n, (_k, _u, sg) in zip(orders, atoms):
        if isinstance(n, bool) or not isinstance(n, int) or not 1 <= n <= LOG_TAYLOR_MAX_ORDER:
            raise _refuse(f"Taylor order {n!r} must be an int in 1..{LOG_TAYLOR_MAX_ORDER}")
        if (n % 2 == 0) != (sg > 0):
            raise _refuse(f"Taylor order {n} has the wrong parity: a log atom with "
                          f"{'positive' if sg > 0 else 'negative'} coefficient needs an "
                          f"{'even (lower bound)' if sg > 0 else 'odd (upper bound)'} order")
    return orders


def factored_endpoint_certificate(*, F, s, k, l_range, x_range=None, side="right",
                                  orders=None, H=None, max_depth=_MAX_DEPTH,
                                  check: bool = True) -> FactoredEndpointCert:
    """Build and self-check a factored endpoint enclosure certificate for ``0 <= F`` on the
    closed domain ``l_range x x_range`` (see the module docstring)."""
    two_var = x_range is not None
    A, B = (_rat(v, "l_range") for v in l_range)
    if not A < B:
        raise _refuse(f"empty or reversed l_range [{A}, {B}]")
    if two_var:
        C, Dd = (_rat(v, "x_range") for v in x_range)
        if not C < Dd:
            raise _refuse(f"empty or reversed x_range [{C}, {Dd}]")
    else:
        C = Dd = None
    s = _rat(s, "s")
    if side not in ("right", "left"):
        raise _refuse(f"side = {side!r} (expected 'right' or 'left')")
    sigma = 1 if side == "right" else -1
    if (side == "right" and s > A) or (side == "left" and s < B):
        raise _refuse(f"endpoint s = {s} lies inside the domain [{A}, {B}] "
                      f"(side {side}: need s {'<= A' if side == 'right' else '>= B'})")
    if isinstance(k, bool) or not isinstance(k, int) or not 1 <= k <= _MAX_K:
        raise _refuse(f"k = {k!r} must be an int in 1..{_MAX_K}")
    if not isinstance(max_depth, int) or not 0 <= max_depth <= 14:
        raise _refuse(f"max_depth = {max_depth!r} must be an int in 0..14")

    F_expr, N0, atoms0, D_const, factors = _parse(F, two_var)
    domain = (A, B, C, Dd)
    # orient each denominator factor positive at the domain centre
    ctr = {L_SYM: (A + B) / 2, X_SYM: ((C + Dd) / 2) if two_var else 0}
    fixed = []
    flip = 1
    for f, e in factors:
        if f.subs(ctr) < 0:
            f = sp.expand(-f)
            flip *= (-1) ** e
        fixed.append((f, e))
    factors = tuple(fixed)
    if flip < 0:
        N0 = sp.expand(-N0)
        atoms0 = tuple((sp.expand(-kp), u) for kp, u in atoms0)
    # sign of each kappa (at the centre; the cover certifies it on every box)
    atoms_s = []
    for kap, u in atoms0:
        v = kap.subs(ctr)
        if v == 0:
            vals = [kap.subs({L_SYM: p[0], X_SYM: p[1]}) for p in _sample_points(domain, two_var)]
            v = next((t for t in vals if t != 0), 0)
        if v == 0:  # pragma: no cover - kappa != 0 as a polynomial
            raise _refuse(f"log coefficient {kap} vanishes on the sample grid")
        atoms_s.append((kap, u, 1 if v > 0 else -1))
    orders = _check_orders(orders, atoms_s)

    fac = (sigma * (L_SYM - s)) ** k
    gens = (L_SYM, X_SYM)
    H_user = None
    if H is not None:
        loc = {"l": L_SYM, "x": X_SYM}
        H_user = sp.expand(sp.sympify(H, locals=loc) if isinstance(H, str) else sp.sympify(H))
        if H_user.atoms(sp.Float):
            raise _refuse("H contains a float")

    if orders is not None:
        ladder = [orders]
    else:
        ladder = []
        for lvl in range(LOG_TAYLOR_MAX_ORDER // 2 + 1):
            o = tuple(2 * lvl + (2 if sg > 0 else 1) for (_k, _u, sg) in atoms_s)
            if all(n <= LOG_TAYLOR_MAX_ORDER for n in o):
                ladder.append(o)
        if not atoms_s:
            ladder = [()]
    last_err = None
    for ords in ladder:
        Q = sp.expand(N0 + sum(kap * log_taylor_poly(n, u)
                               for (kap, u, _sg), n in zip(atoms_s, ords)))
        qq, rr = sp.div(_poly(Q, gens), _poly(fac, gens))
        if not rr.is_zero:
            last_err = (f"the factorization fails: ({sp.sstr(sp.expand(sigma * (L_SYM - s)))})"
                        f"^{k} does not divide Q = {Q} (wrong k, or Taylor order {ords} too "
                        f"low)")
            if not check:
                raise _refuse(last_err)
            continue
        Hq = sp.expand(qq.as_expr())
        if H_user is not None and sp.expand(H_user - Hq) != 0:
            raise _refuse(f"the supplied H = {H_user} does not satisfy Q = (factor)^k H "
                          f"(exact H = {Hq})")
        atoms = tuple((kap, u, n, sg) for (kap, u, sg), n in zip(atoms_s, ords))
        out: list = []
        try:
            tree = _cover(domain, Hq, atoms, factors, two_var, 0, max_depth, check, out)
        except FactoredEndpointRefusal as e:
            if "degree" not in str(e) or last_err is None:
                raise
            break   # higher Taylor orders only grow the degree: report the last failure
        if tree is not None:
            cert = FactoredEndpointCert(
                F=F_expr, two_var=two_var, s=s, k=k, side=side, l_range=(A, B),
                x_range=(C, Dd), N0=N0, atoms=atoms, D_const=D_const, D_factors=factors,
                Q=Q, H=Hq, boxes=tuple(out), tree=tree, checked=check)
            if check:
                verify_certificate(cert)
            return cert
        viol = _find_violation(F_expr, domain, two_var)
        if viol is not None:
            v, lv, xv = viol
            last_err = (f"FALSE: the claim fails at l = {lv}" + (f", x = {xv}" if two_var else "")
                        + f" (F = {sp.N(v, 8)} < 0)")
            break
        last_err = (f"OBSTRUCTED: H = {Hq} (Taylor orders {ords}) is not certified >= 0 on "
                    f"every box to depth {max_depth}")
    raise _refuse(last_err or "no Taylor order certifies the claim")


def verify_certificate(cert: FactoredEndpointCert) -> None:
    """Independent exact re-check of the stored algebra and every box."""
    gens = (L_SYM, X_SYM)
    F_expr, N0, atoms0, D_const, factors = _parse(cert.F, cert.two_var)
    Dfull = cert.D_const * sp.prod([f ** e for f, e in cert.D_factors])
    lhs = sp.together(Dfull * cert.F)
    rhs = cert.N0 + sum(kap * sp.log(1 + u) for (kap, u, _n, _sg) in cert.atoms)
    if sp.simplify(sp.expand(lhs - rhs)) != 0:
        raise _refuse("stored D * F does not equal N0 + sum kappa log(1 + u)")
    Q = sp.expand(cert.N0 + sum(kap * log_taylor_poly(n, u) for (kap, u, n, _sg) in cert.atoms))
    if Q != sp.expand(cert.Q):
        raise _refuse("stored Q does not match its recomputation")
    for (_kap, _u, n, sg) in cert.atoms:
        if (n % 2 == 0) != (sg > 0):
            raise _refuse("a Taylor order has the wrong remainder sign")
    fac = (cert.sigma * (L_SYM - cert.s)) ** cert.k
    if sp.expand(Q - fac * cert.H) != 0:
        raise _refuse("Q != (factor)^k * H")
    for bc in cert.boxes:
        for sc in (bc.H, *bc.us, *bc.kappas, *bc.dens):
            if not (_signcert_identity(sc, bc.box) and sc.ok()):
                raise _refuse(f"box {bc.box}: a sign certificate fails its exact re-check")
        if sp.expand(bc.H.expr - cert.H) != 0:
            raise _refuse(f"box {bc.box}: certifies the wrong H")
    # the tree tiles the domain
    A, B = cert.l_range
    C, Dd = cert.x_range

    def walk(node, box):
        if node[0] == "leaf":
            if tuple(cert.boxes[node[1]].box) != tuple(box):
                raise _refuse(f"the box tree does not tile the domain at {box}")
            return
        _tag, var, m, lt, rt = node
        a, b, c, d = box
        if var == "l":
            if not a < m < b:
                raise _refuse("a bisection point lies outside its box")
            walk(lt, (a, m, c, d))
            walk(rt, (m, b, c, d))
        else:
            if not c < m < d:
                raise _refuse("a bisection point lies outside its box")
            walk(lt, (a, b, c, m))
            walk(rt, (a, b, m, d))
    walk(cert.tree, (A, B, C, Dd))


def certify_factored_endpoint_enclosure_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``, a dict of the keyword arguments
    of :func:`factored_endpoint_certificate`."""
    spec = dict(family.special[1](pt))
    cert = factored_endpoint_certificate(**spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.boxes)


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

def _q(x) -> str:
    x = sp.Rational(x)
    if x.q == 1:
        return f"({x.p} : ℝ)"
    return f"({x.p} / {x.q} : ℝ)"


def _lit(x) -> str:
    """A rational literal inside an already-real context."""
    x = sp.Rational(x)
    return str(x.p) if x.q == 1 else f"({x.p} / {x.q})"


def _ptext(e) -> str:
    """A polynomial in (l, x) as Lean text."""
    P = _poly(e, (L_SYM, X_SYM))
    terms = []
    for (i, j), c in sorted(zip(P.monoms(), P.coeffs()), key=lambda t: (t[0][0] + t[0][1], t[0])):
        c = sp.Rational(c)
        parts = []
        if i:
            parts.append("l" if i == 1 else f"l ^ {i}")
        if j:
            parts.append("x" if j == 1 else f"x ^ {j}")
        if c != 1 or not parts:
            parts.insert(0, _q(c))
        terms.append(" * ".join(parts))
    return "(" + (" + ".join(terms) if terms else "(0 : ℝ)") + ")"


def _logtext(u) -> str:
    return f"Real.log (1 + {_ptext(u)})"


def _etext(e) -> str:
    """A rational function of (l, x) with log atoms, as Lean text (logs as log(1 + u))."""
    if e.is_Rational:
        return _q(e)
    if e.is_Symbol:
        return str(e)
    if isinstance(e, sp.log):
        return _logtext(sp.expand(e.args[0] - 1))
    if e.is_Add:
        return "(" + " + ".join(_etext(a) for a in e.args) + ")"
    if e.is_Mul:
        num, den = sp.fraction(e)
        if den == 1:
            return "(" + " * ".join(_etext(a) for a in e.args) + ")"
        return f"({_etext(num)} / {_etext(den)})"
    if e.is_Pow:
        base, ex = e.args
        ex = int(ex)
        if ex > 0:
            return f"({_etext(base)} ^ {ex})"
        return f"(1 / {_etext(base)} ^ {-ex})"
    raise _refuse(f"cannot render {e} in Lean")  # pragma: no cover - guarded by _parse


_GENERIC = r"""set_option linter.unusedVariables false

/-! ## Generic factored endpoint enclosure (emitted once per file)

`factored_endpoint_core`: on a box (any predicate), if `0 <= t`, `0 < D`, the lower bound
`Q <= D * F`, the factorization `Q = t^k * H`, and `0 <= H`, then `0 <= F`.  The box may
contain the endpoint `t = 0`, where `F / t^k` is undefined: only `H` (a polynomial) is
evaluated there.  conjecture1_proved = False. -/

theorem factored_endpoint_core {α : Type*} {Box : α → Prop} {F D Q H t : α → ℝ} (k : ℕ)
    (ht : ∀ p, Box p → 0 ≤ t p) (hD : ∀ p, Box p → 0 < D p)
    (hlow : ∀ p, Box p → Q p ≤ D p * F p)
    (hfac : ∀ p, Q p = t p ^ k * H p)
    (hH : ∀ p, Box p → 0 ≤ H p) :
    ∀ p, Box p → 0 ≤ F p := by
  intro p hp
  have h1 := hlow p hp
  rw [hfac] at h1
  have h2 := mul_nonneg (pow_nonneg (ht p hp) k) (hH p hp)
  have h3 : 0 ≤ D p * F p := le_trans h2 h1
  exact (mul_nonneg_iff_of_pos_left (hD p hp)).mp h3

/-- The quotient corollary: off the endpoint, `0 <= F / t^k`. -/
theorem factored_endpoint_quot {F t : ℝ} (k : ℕ) (hF : 0 ≤ F) (ht : 0 ≤ t) :
    0 ≤ F / t ^ k :=
  div_nonneg hF (pow_nonneg ht k)
"""


def _facts(sc: SignCert, two_var: bool) -> str:
    out = []
    for i in range(sc.p + 1):
        lpart = f"mul_nonneg (pow_nonneg hl {i}) (pow_nonneg hr {sc.p - i})"
        if not two_var:
            out.append(lpart)
            continue
        for j in range(sc.q + 1):
            out.append(f"mul_nonneg ({lpart}) "
                       f"(mul_nonneg (pow_nonneg hc {j}) (pow_nonneg hd {sc.q - j}))")
    return ", ".join(out)


def _ttext(c, v: str = "l") -> str:
    """Lean text of ``t = sigma (l - s)`` (``l`` itself when ``s = 0`` on the right)."""
    if c.sigma > 0:
        return v if c.s == 0 else f"({v} - {_lit(c.s)})"
    return f"(-{v})" if c.s == 0 else f"({_lit(c.s)} - {v})"


def _sign_proof(sc: SignCert, two_var: bool) -> str:
    """Tactic text proving `0 <= P` / `0 < P` from the box facts hl hr (hc hd)."""
    if _poly(sc.expr, (L_SYM, X_SYM)).total_degree() <= 0:
        return "by norm_num"
    return f"by linarith [{_facts(sc, two_var)}]"


@dataclass
class FactoredEndpointEnclosureEmitter(Emitter):
    """Emit the generic factored-endpoint core and the ``log_taylor`` section once, then per
    instance the definitions, the factorization, the per-box sign lemmas, the per-box
    core applications, the union over the closed domain and the quotient corollary.

    HONEST SCOPE: ``log(1 + u)`` atoms via Taylor with signed remainder only.
    conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "factored_endpoint_enclosure"

    def emit_units(self, fam, profile: LeanProfile):
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts = [_GENERIC]
        orders = sorted({n for inst in fam.instances for n in inst.payload.orders})
        if orders:
            text, _n = log_taylor_lean(_LT_NS, orders)
            parts.append(text)
        for inst in fam.instances:
            parts.append(self._emit_instance(inst.payload, inst.lean_name))
        body = "\n".join(parts)
        nthm = sum(1 for ln in body.split("\n") if ln.startswith("theorem "))
        return body, nthm

    # -- per instance -------------------------------------------------------------------
    def _emit_instance(self, c: FactoredEndpointCert, nm: str) -> str:
        tv = c.two_var
        V = "l x" if tv else "l"
        app = f"{nm}_F {V}"
        A, B = c.l_range
        C, Dd = c.x_range
        tl = _ttext(c)
        L: list[str] = []
        dom = f"l ∈ [{A}, {B}]" + (f", x ∈ [{C}, {Dd}]" if tv else "")
        atoms_txt = "; ".join(f"log(1 + {u}) with coefficient {kap}, Taylor order {n} "
                              f"({'lower' if n % 2 == 0 else 'upper'} bound)"
                              for kap, u, n, _sg in c.atoms) or "none (closed form)"
        L.append(f"/-! ## Instance `{nm}`\n\n"
                 f"`0 <= F` with `F = {sp.sstr(c.F)}` on the closed box {dom}, endpoint "
                 f"`l = {c.s}` ({c.side} side) included.\n"
                 f"Factorization `Q = {tl}^{c.k} * H` with `H = {sp.sstr(c.H)}`.\n"
                 f"Log atoms: {atoms_txt}.  Boxes: {len(c.boxes)}.\n"
                 f"conjecture1_proved = False. -/\n")
        L.append(f"noncomputable def {nm}_F ({V} : ℝ) : ℝ :=\n  {_etext(c.F)}\n")
        Dtxt = _q(c.D_const)
        for f, e in c.D_factors:
            Dtxt += f" * {_ptext(f)} ^ {e}"
        L.append(f"noncomputable def {nm}_D ({V} : ℝ) : ℝ :=\n  {Dtxt}\n")
        L.append(f"noncomputable def {nm}_Q ({V} : ℝ) : ℝ :=\n  {_ptext(c.Q)}\n")
        L.append(f"noncomputable def {nm}_H ({V} : ℝ) : ℝ :=\n  {_ptext(c.H)}\n")
        L.append(f"/-- The factorization `Q = {tl}^{c.k} * H` (exact polynomial identity). -/\n"
                 f"theorem {nm}_fac ({V} : ℝ) :\n"
                 f"    {nm}_Q {V} = {tl} ^ {c.k} * {nm}_H {V} := by\n"
                 f"  simp only [{nm}_Q, {nm}_H]\n  ring\n")
        for bi, bc in enumerate(c.boxes):
            L.append(self._emit_box(c, nm, bi, bc, tl))
        L.append(self._emit_union(c, nm))
        # quotient corollary
        if tv:
            hyp = (f"∀ l ∈ Set.Icc {_q(A)} {_q(B)}, l ≠ {_q(c.s)} → "
                   f"∀ x ∈ Set.Icc {_q(C)} {_q(Dd)},\n      0 ≤ {nm}_F l x / {tl} ^ {c.k}")
            intro = "  intro l hl hne x hx\n"
            call = f"{nm} l hl x hx"
        else:
            hyp = f"∀ l ∈ Set.Icc {_q(A)} {_q(B)}, l ≠ {_q(c.s)} → 0 ≤ {nm}_F l / {tl} ^ {c.k}"
            intro = "  intro l hl hne\n"
            call = f"{nm} l hl"
        L.append(f"/-- The quotient `F / {tl}^{c.k}` (the quantity of interest) is `>= 0` "
                 f"off the endpoint. -/\n"
                 f"theorem {nm}_quot :\n    {hyp} := by\n{intro}"
                 f"  exact factored_endpoint_quot {c.k} ({call}) (by linarith [hl.1, hl.2])\n")
        return "\n".join(L)

    def _box_binders(self, c, bc) -> str:
        a, b, cc, d = bc.box
        s = f"(h1 : {_q(a)} ≤ l) (h2 : l ≤ {_q(b)})"
        if c.two_var:
            s += f" (h3 : {_q(cc)} ≤ x) (h4 : x ≤ {_q(d)})"
        return s

    def _box_intro(self, c, bc) -> list[str]:
        a, b, cc, d = bc.box
        out = [f"  have hl : 0 ≤ l - {_lit(a)} := by linarith",
               f"  have hr : 0 ≤ {_lit(b)} - l := by linarith"]
        if c.two_var:
            out += [f"  have hc : 0 ≤ x - {_lit(cc)} := by linarith",
                    f"  have hd : 0 ≤ {_lit(d)} - x := by linarith"]
        return out

    def _emit_box(self, c, nm, bi, bc: BoxCert, tl) -> str:
        tv = c.two_var
        V = "l x" if tv else "l"
        bnd = self._box_binders(c, bc)
        intro = self._box_intro(c, bc)
        pre = f"{nm}_b{bi}"
        out = []
        # H >= 0
        out.append(f"theorem {pre}_H ({V} : ℝ) {bnd} :\n    0 ≤ {nm}_H {V} := by\n"
                   + "\n".join(intro) + f"\n  simp only [{nm}_H]\n"
                   f"  linarith [{_facts(bc.H, tv)}]\n"
                   if _poly(bc.H.expr, (L_SYM, X_SYM)).total_degree() > 0 else
                   f"theorem {pre}_H ({V} : ℝ) {bnd} :\n    0 ≤ {nm}_H {V} := by\n"
                   f"  simp only [{nm}_H]\n  norm_num\n")
        # denominator factors > 0, then D > 0
        dl = []
        for fi, (sc, (f, e)) in enumerate(zip(bc.dens, c.D_factors)):
            dl.append(f"  have hf{fi} : 0 < {_ptext(f)} := {_sign_proof(sc, tv)}")
        dterm = "(by norm_num)"
        for fi, (_f, e) in enumerate(c.D_factors):
            dterm = f"(mul_pos {dterm} (pow_pos hf{fi} {e}))"
        out.append(f"theorem {pre}_D ({V} : ℝ) {bnd} :\n    0 < {nm}_D {V} := by\n"
                   + "\n".join(intro + dl) + f"\n  simp only [{nm}_D]\n  exact {dterm}\n")
        # the Taylor lower bound Q <= D * F
        rhs = _ptext(c.N0) + "".join(f" + {_ptext(kap)} * {_logtext(u)}"
                                     for kap, u, _n, _sg in c.atoms)
        body = list(intro) + dl + [f"  have hf{fi}' := hf{fi}.ne'" for fi in range(len(c.D_factors))]
        body.append(f"  have e : {nm}_D {V} * {nm}_F {V} = {rhs} := by")
        body.append(f"    simp only [{nm}_D, {nm}_F]")
        if c.D_factors:
            body.append("    field_simp")
        body.append("    ring")
        hp = []
        for ai, ((kap, u, n, sg), usc, ksc) in enumerate(zip(c.atoms, bc.us, bc.kappas)):
            lem = f"{_LT_NS}.{'lower' if n % 2 == 0 else 'upper'}_{n}"
            body.append(f"  have hu{ai} : 0 ≤ {_ptext(u)} := {_sign_proof(usc, tv)}")
            body.append(f"  have hT{ai} := {lem} {_ptext(u)} hu{ai}")
            body.append(f"  have hk{ai} : 0 ≤ {_ptext(sg * kap)} := {_sign_proof(ksc, tv)}")
            if n % 2 == 0:   # T <= log, kappa >= 0
                body.append(f"  have hp{ai} := mul_nonneg hk{ai} (sub_nonneg.2 hT{ai})")
            else:            # log <= T, -kappa >= 0
                body.append(f"  have hp{ai} := mul_nonneg hk{ai} (sub_nonneg.2 hT{ai})")
            hp.append(f"hp{ai}")
        body.append(f"  simp only [{nm}_Q]")
        body.append(f"  linarith [{', '.join(['e'] + hp)}]")
        out.append(f"theorem {pre}_low ({V} : ℝ) {bnd} :\n"
                   f"    {nm}_Q {V} ≤ {nm}_D {V} * {nm}_F {V} := by\n" + "\n".join(body) + "\n")
        # the core application
        a, b, cc, d = bc.box
        if tv:
            boxp = (f"fun p : ℝ × ℝ => {_q(a)} ≤ p.1 ∧ p.1 ≤ {_q(b)} ∧ {_q(cc)} ≤ p.2 ∧ "
                    f"p.2 ≤ {_q(d)}")
            fn = lambda f: f"fun p => {f} p.1 p.2"  # noqa: E731
            args = "p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2"
            tfun = "fun p => " + _ttext(c, "p.1")
            pt, mem = "(l, x)", "⟨h1, h2, h3, h4⟩"
            tproof = "fun p hp => by linarith [hp.1, hp.2.1]"
        else:
            boxp = f"fun p : ℝ => {_q(a)} ≤ p ∧ p ≤ {_q(b)}"
            fn = lambda f: f  # noqa: E731
            args = "p hp.1 hp.2"
            tfun = "fun p => " + _ttext(c, "p")
            pt, mem = "l", "⟨h1, h2⟩"
            tproof = "fun p hp => by linarith [hp.1, hp.2]"
        out.append(
            f"theorem {pre} ({V} : ℝ) {bnd} :\n    0 ≤ {nm}_F {V} :=\n"
            f"  factored_endpoint_core (Box := {boxp})\n"
            f"    (F := {fn(nm + '_F')}) (D := {fn(nm + '_D')}) (Q := {fn(nm + '_Q')})\n"
            f"    (H := {fn(nm + '_H')}) (t := {tfun}) {c.k}\n"
            f"    ({tproof})\n"
            f"    (fun p hp => {pre}_D {args})\n"
            f"    (fun p hp => {pre}_low {args})\n"
            f"    (fun p => {nm}_fac {'p.1 p.2' if tv else 'p'})\n"
            f"    (fun p hp => {pre}_H {args})\n"
            f"    {pt} {mem}\n")
        return "\n".join(out)

    def _emit_union(self, c, nm) -> str:
        tv = c.two_var
        A, B = c.l_range
        C, Dd = c.x_range
        hs = "(by linarith) (by linarith)" + (" (by linarith) (by linarith)" if tv else "")
        V = "l x" if tv else "l"

        def rec(node, ind) -> list[str]:
            pad = " " * ind
            if node[0] == "leaf":
                return [f"{pad}exact {nm}_b{node[1]} {V} {hs}"]
            _t, var, m, lt, rt = node
            v = "l" if var == "l" else "x"
            lines = [f"{pad}rcases le_total {v} {_q(m)} with h | h"]
            lines.append(f"{pad}· " + rec(lt, ind + 2)[0].lstrip())
            lines += rec(lt, ind + 2)[1:]
            lines.append(f"{pad}· " + rec(rt, ind + 2)[0].lstrip())
            lines += rec(rt, ind + 2)[1:]
            return lines

        if tv:
            stmt = (f"∀ l ∈ Set.Icc {_q(A)} {_q(B)}, ∀ x ∈ Set.Icc {_q(C)} {_q(Dd)}, "
                    f"0 ≤ {nm}_F l x")
            intro = "  intro l hl x hx\n  obtain ⟨hl1, hl2⟩ := hl\n  obtain ⟨hx1, hx2⟩ := hx\n"
        else:
            stmt = f"∀ l ∈ Set.Icc {_q(A)} {_q(B)}, 0 ≤ {nm}_F l"
            intro = "  intro l hl\n  obtain ⟨hl1, hl2⟩ := hl\n"
        return (f"/-- `0 <= F` on the CLOSED box, endpoint `l = {c.s}` included. -/\n"
                f"theorem {nm} :\n    {stmt} := by\n{intro}" + "\n".join(rec(c.tree, 2)) + "\n")


def factored_endpoint_enclosure_family(name, grid, lean_name, spec, constants=None):
    """Build a factored endpoint enclosure family (kind='factored_endpoint_enclosure').

    ``spec``: a callable ``pt -> dict`` of :func:`factored_endpoint_certificate` keyword
    arguments (``F``, ``s``, ``k``, ``l_range``, optional ``x_range``, ``side``, ``orders``,
    ``H``, ``max_depth``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("factored_endpoint_enclosure", spec),
        constants=dict(constants or {}),
    )


# ---------------------------------------------------------------------------
# dogfood instances (classical or synthetic)
# ---------------------------------------------------------------------------

#: (a) ``(1 + l)^(1/l) <= e`` near ``l = 0``, i.e. ``(1/l) log(1 + l) <= 1``: ``F = l - log(1+l)``
#: vanishes at ``l = 0``; ``F >= l^2/2 - l^3/3 = l (l/2 - l^2/3)`` by the order-3 upper bound.
LOG_EXP_SPEC = dict(F="l - log(1 + l)", s=0, k=1, l_range=("0", "1/10"), orders=(3,))

#: (a') the sharp companion: ``l - log(1+l) >= (117/250) l^2`` on ``[0, 1/10]``; the true
#: minimum of ``(l - log(1+l))/l^2`` there is ``0.46898...`` at ``l = 1/10``, so the claim
#: holds with margin ``~1/1000`` (order-5 upper bound, ``k = 2``).
LOG_SHARP_SPEC = dict(F="l - log(1 + l) - 117/250*l**2", s=0, k=2, l_range=("0", "1/10"),
                      orders=(5,))

#: The negative control: the constant ``47/100`` exceeds the minimum ``0.46898...`` by
#: ``~1/1000``, so the claim is FALSE near ``l = 1/10``.
LOG_SHARP_FALSE_SPEC = dict(LOG_SHARP_SPEC, F="l - log(1 + l) - 47/100*l**2")

#: (c') two-variable negative-control pair: ``H = (x - l)^2 + l x`` has minimum ``3/64`` on
#: ``[0, 1/2] x [1/4, 1]`` (at ``l = 1/8, x = 1/4``), so ``F - m l >= 0`` is TRUE for
#: ``m = 3/64 - 1/1000`` and FALSE for ``m = 3/64 + 1/1000``.
SYNTH2_MARGIN_SPEC = dict(F="l*(x - l)**2 + l**2*x - (3/64 - 1/1000)*l", s=0, k=1,
                          l_range=("0", "1/2"), x_range=("1/4", "1"))
SYNTH2_MARGIN_FALSE_SPEC = dict(SYNTH2_MARGIN_SPEC,
                                F="l*(x - l)**2 + l**2*x - (3/64 + 1/1000)*l")

#: (b) polynomial-rational (no sin enclosure exists in Telperion): the alternating bound
#: ``(1 + l)^-2 >= 1 - 2l + 3l^2 - 4l^3`` on ``[0, 1]``; ``D F = l^4 (5 + 4l)`` with
#: ``D = (1 + l)^2``, ``k = 4``, ``H = 5 + 4l`` (closed form, no Taylor).
RATIONAL_SPEC = dict(F="1/(1 + l)**2 - (1 - 2*l + 3*l**2 - 4*l**3)", s=0, k=4,
                     l_range=("0", "1"))

#: (c) synthetic, two variables: ``F = l (x - l)^2 + l^2 x`` with ``H = (x - l)^2 + l x`` on
#: ``[0, 1/2] x [1/8, 1]`` (endpoint boxes at ``l = 0``; the cover splits in both variables).
SYNTH2_SPEC = dict(F="l*(x - l)**2 + l**2*x", s=0, k=1, l_range=("0", "1/2"),
                   x_range=("1/8", "1"))

#: (d) the [2/1] Pade bound ``log(1 + l) <= l (6 + l)/(6 + 4 l)`` on ``[0, 1/3]``, tight to
#: order 4 at ``l = 0``: with ``D = 3 + 2 l``, ``D F >= l^4 (1/12 - l/10 - 2 l^2/5)``, ``k = 4``.
PADE_SPEC = dict(F="l*(6 + l)/(6 + 4*l) - log(1 + l)", s=0, k=4, l_range=("0", "1/3"))


if __name__ == "__main__":
    for nm, sp_ in (("log_exp", LOG_EXP_SPEC), ("log_sharp", LOG_SHARP_SPEC),
                    ("rational", RATIONAL_SPEC), ("synth2", SYNTH2_SPEC), ("pade", PADE_SPEC)):
        c = factored_endpoint_certificate(**sp_)
        print(f"{nm}: k={c.k} orders={c.orders} H={c.H} boxes={len(c.boxes)}")

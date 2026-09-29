"""gap_budget_multiplicity emitter -- pruning a multiset optimisation by a tangent-price GAP
BUDGET, with every step checked by the Lean kernel.

conjecture1_proved = False.  Nothing in this module bears on the Riemann Hypothesis or on the
Brualdi-Goldwasser Laplacian-ratio problem: it certifies finite pruning consequences of one
elementary inequality per instance.  Downstream consumers state their own scope.

Acknowledgement.  The tangent-gap pricing pattern is from a draft communicated by Professor
John L. Goldwasser ("The maximum Laplacian ratio of a tree for all n >= 303: concave witnesses
and one-variable certificates", 28 Sep 2026; author: his London colleague, name to be added).
Nothing from the draft (text or data) is reproduced here; the dogfood is a classical
instance.

THE SETTING
-----------
A configuration is a multiset ``m`` of integer-labelled atoms ``k`` from an alphabet
``[kmin, kmax]`` (or ``[kmin, oo)`` with a certified tail).  Its value is

    Phi(m) = sum_{k in m} w(k)  [ + c * log( sum_{k in m} y(k) / M ) ]

under a fixed linear normalisation ``sum_{k in m} ell(k) = M``.  The bracketed term is the
optional CONCAVE part; the only certified concave family is ``f(x) = c * log x`` with ``c >= 0``
(anything else is refused).  Its tangent at a rational ``x0 > 0`` with slope ``mu = c / x0``
gives ``f(x) <= f(x0) + mu (x - x0)``, and with the price ``tau``

    Phi(m) <= C - sum_{k in m} gamma(k),
    gamma(k) = tau * ell(k) - w(k) - (c / x0 / M) * y(k),
    C        = tau * M + c * log x0 - c.

(the separable case has ``c = 0``: ``gamma(k) = tau * ell(k) - w(k)``, ``C = tau * M``).  The
``gamma(k)`` are the per-atom GAPS.  A benchmark configuration ``bench`` with value ``B`` and
the same normalisation is given; any ``m`` with ``Phi(m) >= B`` then satisfies the BUDGET

    sum_{k in m} gamma(k) <= theta := C - B.

With every gap ``>= 0`` on the alphabet and rational lower bounds ``g_k <= gamma(k)``:

  (1) caps       ``count k <= floor(theta_hi / g_k)`` for every atom with ``g_k > 0``;
  (2) exclusion  ``count k = 0`` when ``g_k > theta_hi`` (the cap is 0), and, with a tail,
                 ``k < K0`` for every element when the tail bound exceeds ``theta_hi``;
  (3) knapsack   the vector of counts of the surviving positive-gap atoms lies in the
                 finite list of all vectors ``x <= caps`` with ``sum x_k g_k <= theta_hi``
                 (enumerated here, re-decided in the kernel by ``decide`` over naturals).

WHERE EACH NUMBER COMES FROM
----------------------------
* ``theta_hi`` -- an upper bound on ``theta``: exact when ``theta`` is rational, otherwise the
  stated upper end of an ``enclosure_tree`` certificate of ``theta`` (the log atoms are
  bracketed by Mathlib's ``Real.log_two_gt_d9`` / the Taylor estimate / the ``Real.log_mul``
  fold -- REUSED, not re-implemented), rounded UP to the grid ``1/D``.
* ``g_k`` -- a lower bound on ``gamma(k)``: exact when rational, else the stated lower end of
  an ``enclosure_tree`` certificate rounded DOWN to the grid.  A caller may CLAIM ``g_k`` /
  ``theta_hi``; the enclosure fold refuses any claim it does not imply.
* the tail -- for ``k >= K0`` the gap must have the shape
  ``gamma(k) = P k - c_t log(k + s) + d`` with ``c_t >= 0``; convexity (the same log tangent
  lemma, at ``K0 + s``) gives ``gamma(k) >= gamma(K0) + (P - c_t/(K0+s)) (k - K0)``, so the
  tail inherits ``g_{K0}`` once a rational ``P_lo <= P`` satisfies ``P_lo >= c_t/(K0+s)``.

THE LEAN (generic core, emitted once per file; instance files only instantiate it)
---------------------------------------------------------------------------------
``gapBudget_log_tangent`` (``Real.log_le_sub_one_of_pos`` at ``x / x0``),
``gapBudget_of_sep`` / ``gapBudget_of_concave`` (the budget from the model: multiset sums
``Multiset.sum_map_sub`` / ``sum_map_mul_left`` and the tangent step),
``gapBudget_count_mul_le`` (``count k * g_k <= theta``: split ``m`` by ``filter (. = k)``,
``Multiset.filter_eq'`` is a replicate, the rest is a sum of nonnegative gaps),
``gapBudget_nat_cap`` (the integer cap from ``theta < (cap + 1) g``), and
``gapBudget_knapsack`` (``sum_{k in A} count k * g_k <= theta`` through
``Finset.sum_multiset_map_count``).  Per instance: the model ``def``s, the enclosure theorems,
one gap lemma per listed atom, the tail lemma, the benchmark lemma
``Phi(bench) = B /\\ sum ell(bench) = M`` (so ``B`` is attained), and the main theorem.

HONEST SCOPE.  The main theorem is CONDITIONAL on ``Phi(m) >= B`` and the normalisation; it
prunes, it does not solve.  It says nothing about which surviving configuration is optimal,
nor about any problem the instance is not.  ``conjecture1_proved = False``.

ANTI-PHANTOM REFUSALS
---------------------
``gap_budget_multiplicity_certificate`` REFUSES (``GapBudgetRefusal``, a ``ValueError``):

* floats, bools, non-rational constants, functions other than the ``gb_log`` / ``gb_logk``
  atoms (``sp.log``/``exp`` are refused -- the log atoms carry their own domain checks)
* a concave part that is not ``("log", c >= 0)`` -- ``c < 0`` is CONVEX, the tangent inequality
  runs the wrong way; ``c = 0`` belongs to the separable model; ``x0 <= 0``; a non-rational or
  non-positive ``M``; ``y`` / ``ell`` that are not rational polynomials in ``k``
* a log argument ``<= 0`` at some atom (``Real.log`` is junk there), a ``gb_log`` argument
  ``<= 0``, ``= 1``, ``< 1/2`` or beyond the fold range
* a benchmark atom outside the alphabet, a negative or non-integral multiplicity, a benchmark
  whose normalisation is not ``M`` exactly, a benchmark mean ``<= 0``
* ``theta`` that depends on a parameter or on ``k`` (the budget must be uniform), a
  certified ``theta < 0`` (the benchmark would beat the tangent bound: inconsistent input)
* a gap that is negative, or not provably ``>= 0``, at some listed atom (the price does not
  dominate there: the budget argument needs every gap ``>= 0``)
* a claimed ``g_k`` / ``theta_hi`` the enclosure fold does not imply (the forge case)
* a tail whose gap is not ``P k - c_t log(k + s) + d`` with ``c_t >= 0``, ``K0 + s <= 0``, a
  slope ``P_lo < c_t / (K0 + s)`` (monotonicity not certified), a missing / stray tail start
* more than ``MAX_ATOMS`` listed atoms, a knapsack box above ``MAX_KNAPSACK_BOX`` points,
  a budget that prunes nothing, non-identifier names
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from itertools import product as _iproduct
from math import floor, log2
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .emit_enclosure_tree import (
    EnclosureTreeCert,
    EnclosureTreeRefusal,
    _header as _enc_header,
    _proof_body as _enc_proof_body,
    _statement as _enc_statement,
    enclosure_tree_certificate,
    node_add,
    node_log,
    node_mul,
    node_rat,
    node_sub,
)
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# --- caps (each one a refusal boundary, never a silent clamp) ----------------------

#: listed atoms above this count are refused (`interval_cases` cost grows linearly).
MAX_ATOMS = 48
#: knapsack boxes (prod of (cap + 1)) above this are refused (`decide` cost).
MAX_KNAPSACK_BOX = 4096
#: default rounding grid: gap lower bounds are rounded DOWN, theta_hi UP, to multiples of 1/D.
DEFAULT_GRID = 10 ** 6
#: a `gb_log` argument must stay inside the enclosure fold's reach (2^8 * 4/3).
MAX_LOG_ARG = sp.Integer(340)

K = sp.Symbol("k", integer=True, nonnegative=True)
_RESERVED = {"k", "m", "hA", "hl", "hB", "hdom", "Real", "Multiset"}
_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


class GapBudgetRefusal(ValueError):
    """A gap-budget certificate was refused (never widened, never weakened)."""


def _refuse(msg: str) -> GapBudgetRefusal:
    return GapBudgetRefusal(f"REFUSED: {msg}")


def _rat(v, what: str) -> sp.Rational:
    if isinstance(v, bool):
        raise _refuse(f"{what} was given as a bool ({v!r})")
    if isinstance(v, (float, sp.Float)):
        raise _refuse(f"{what} was given as a float ({v!r}); pass an exact rational")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    try:
        q = sp.Rational(v)
    except (TypeError, ValueError) as exc:
        raise _refuse(f"{what} = {v!r} is not rational ({exc})") from None
    return q


def _int(v, what: str) -> int:
    if isinstance(v, bool) or not isinstance(v, int):
        raise _refuse(f"{what} = {v!r} is not an int")
    return v


# --- the log atoms (the DSL the caller writes) --------------------------------------

def gb_log(q) -> sp.Symbol:
    """`Real.log q` for a POSITIVE RATIONAL constant `q` (an atom symbol; never `sp.log`, whose
    automatic simplifications would drift from the Lean text)."""
    q = _rat(q, "gb_log argument")
    if q <= 0:
        raise _refuse(f"gb_log({q}): the argument is <= 0 (outside log's domain)")
    if q == 1:
        raise _refuse("gb_log(1) = 0 exactly; write 0")
    return sp.Symbol(f"GBL_{q.p}_{q.q}", positive=True)


def gb_logk(shift=0) -> sp.Symbol:
    """`Real.log ((k : R) + shift)` for the atom label `k` and an INTEGER shift."""
    s = _int(shift, "gb_logk shift")
    return sp.Symbol(f"GBLK_{'m' if s < 0 else ''}{abs(s)}")


def _log_arg(sym: sp.Symbol):
    m = re.fullmatch(r"GBL_(\d+)_(\d+)", sym.name)
    return sp.Rational(int(m.group(1)), int(m.group(2))) if m else None


def _logk_shift(sym: sp.Symbol):
    m = re.fullmatch(r"GBLK_(m?)(\d+)", sym.name)
    if not m:
        return None
    return -int(m.group(2)) if m.group(1) else int(m.group(2))


def _check_expr(e, what: str, allowed: str, params=()) -> sp.Expr:
    """Sympify and check: a polynomial with RATIONAL coefficients in the allowed symbols."""
    if isinstance(e, bool):
        raise _refuse(f"{what} was given as a bool")
    if isinstance(e, (float, sp.Float)):
        raise _refuse(f"{what} was given as a float ({e!r}); pass an exact rational")
    if isinstance(e, Fraction):
        e = sp.Rational(e.numerator, e.denominator)
    try:
        e = sp.sympify(e)
    except (sp.SympifyError, TypeError) as exc:
        raise _refuse(f"{what} = {e!r} is not an expression ({exc})") from None
    if e.atoms(sp.Float):
        raise _refuse(f"{what} contains a float; pass exact rationals")
    if e.atoms(sp.Function) or e.has(sp.E, sp.pi, sp.I, sp.oo):
        raise _refuse(f"{what} = {e} contains a function or special constant; use gb_log / "
                      "gb_logk for logarithms (the only transcendental atoms supported)")
    ok = set()
    for s in e.free_symbols:
        if s == K and "k" in allowed:
            ok.add(s)
        elif _log_arg(s) is not None and "L" in allowed:
            ok.add(s)
        elif _logk_shift(s) is not None and "K" in allowed:
            ok.add(s)
        elif s in params and "p" in allowed:
            ok.add(s)
        else:
            raise _refuse(f"{what} = {e} mentions {s}, which is not allowed here")
    e = sp.expand(e)
    gens = sorted(e.free_symbols, key=lambda s: s.name)
    if gens:
        if not e.is_polynomial(*gens):
            raise _refuse(f"{what} = {e} is not a polynomial in its atoms")
        poly = sp.Poly(e, *gens)
        if not all(isinstance(c, sp.Rational) for c in poly.coeffs()):
            raise _refuse(f"{what} = {e} has a non-rational coefficient")
    elif not isinstance(e, sp.Rational):
        raise _refuse(f"{what} = {e} is not rational")
    return e


def _at_atom(e: sp.Expr, k0: int, what: str) -> sp.Expr:
    """Substitute the atom label `k = k0` (and `log(k + s)` -> `gb_log(k0 + s)`)."""
    subs = {K: k0}
    for s in e.free_symbols:
        sh = _logk_shift(s)
        if sh is None:
            continue
        arg = k0 + sh
        if arg <= 0:
            raise _refuse(f"{what}: log((k) + {sh}) at the atom k = {k0} has argument {arg} "
                          "<= 0 (Real.log is junk there)")
        subs[s] = 0 if arg == 1 else gb_log(arg)
    return sp.expand(e.subs(subs))


# --- Lean rendering of the polynomial DSL -------------------------------------------

def _q_lean(q: sp.Rational, prec: int = 0) -> str:
    """A rational as a Lean real term at precedence `prec` (1024 = application argument)."""
    q = sp.Rational(q)
    if q.q == 1:
        s = str(q.p)
        return f"({s})" if q.p < 0 and prec > 0 else s
    s = f"{abs(q.p)} / {q.q}"
    if q.p < 0:
        return f"(-({s}))" if prec > 0 else f"-({s})"
    return f"({s})" if prec > 70 else s


def _logk_lean(sh: int) -> str:
    if sh == 0:
        return "Real.log (k : ℝ)"
    return f"Real.log ((k : ℝ) {'+' if sh > 0 else '-'} {abs(sh)})"


def _factor_lean(s: sp.Symbol, e: int, params) -> str:
    if s == K:
        base = "(k : ℝ)"
    elif s in params:
        base = f"({s.name} : ℝ)"
    elif _log_arg(s) is not None:
        base = f"Real.log {_q_lean(_log_arg(s), 1024)}"
    else:
        base = _logk_lean(_logk_shift(s))
    if e == 1:
        return base
    if base.startswith("Real.log"):
        base = f"({base})"
    return f"{base} ^ {e}"


def lean_poly(e: sp.Expr, params=()) -> str:
    """Deterministic Lean text of a DSL polynomial over R (terms ordered by degree, then name;
    the constant last)."""
    e = sp.expand(sp.sympify(e))
    if e == 0:
        return "0"
    gens = sorted(e.free_symbols, key=lambda s: s.name)
    if not gens:
        return _q_lean(e)
    terms = sp.Poly(e, *gens).terms()

    def key(t):
        mon, _c = t
        return (sum(mon) == 0, -sum(mon), [(-x) for x in mon])

    out = []
    for mon, c in sorted(terms, key=key):
        c = sp.Rational(c)
        facs = [_factor_lean(g, x, params) for g, x in zip(gens, mon) if x]
        if facs:
            body = " * ".join(facs)
            mag = abs(c)
            txt = body if mag == 1 else f"{_q_lean(mag, 70)} * {body}"
        else:
            txt = _q_lean(abs(c), 70)
        if not out:
            out.append(txt if c > 0 else f"-({txt})" if " " in txt else f"-{txt}")
        else:
            out.append(f"{'+' if c > 0 else '-'} {txt}")
    return " ".join(out)


def _lean_nat_poly(e: sp.Expr) -> str:
    """A benchmark multiplicity (a polynomial in the parameters with natural coefficients) as
    a Lean natural-number term."""
    e = sp.expand(e)
    if e.is_Integer:
        return str(int(e))
    gens = sorted(e.free_symbols, key=lambda s: s.name)
    out = []
    for mon, c in sorted(sp.Poly(e, *gens).terms(), key=lambda t: (sum(t[0]) == 0, -sum(t[0]))):
        facs = [g.name if x == 1 else f"{g.name} ^ {x}" for g, x in zip(gens, mon) if x]
        c = int(c)
        if facs:
            out.append(" * ".join(facs) if c == 1 else f"{c} * " + " * ".join(facs))
        else:
            out.append(str(c))
    return " + ".join(out)


# --- sympy constant -> enclosure tree ------------------------------------------------

def _log_node(q: sp.Rational):
    """`Real.log q` as an enclosure_tree node: the Mathlib atom (q = 2), the Taylor estimate
    (|1 - q| < 1/2), or the fold `q = 2^e * r` with `r` in (2/3, 4/3]."""
    if q < sp.Rational(1, 2):
        raise _refuse(f"log({q}): arguments below 1/2 are outside the supported fold range "
                      "(write -gb_log(1/q))")
    if q > MAX_LOG_ARG:
        raise _refuse(f"log({q}): the argument exceeds {MAX_LOG_ARG} (fold multiplicity cap)")
    if q == 2:
        return node_log(2)
    if abs(1 - q) < sp.Rational(1, 2):
        return node_log(q)
    e = int(floor(log2(float(q))))
    while sp.Integer(2) ** e > q:
        e -= 1
    while sp.Integer(2) ** (e + 1) <= q:
        e += 1
    r = q / sp.Integer(2) ** e                # r in [1, 2)
    if r > sp.Rational(4, 3):
        e += 1
        r = q / sp.Integer(2) ** e            # r in (2/3, 1)
    if r == 1:
        return node_log(q, factors=((e, node_log(2)),))
    if e == 0:                                # q in [1/2, 3/2) handled above; unreachable
        return node_log(q)                    # pragma: no cover
    return node_log(q, factors=((e, node_log(2)), (1, node_log(r))))


def tree_of_constant(e: sp.Expr):
    """A constant DSL polynomial (rationals and `gb_log` atoms only) as an enclosure tree."""
    e = sp.expand(e)
    gens = sorted(e.free_symbols, key=lambda s: s.name)
    if not gens:
        raise _refuse(f"{e} is rational; it takes the exact route, not an enclosure")
    for g in gens:
        if _log_arg(g) is None:
            raise _refuse(f"{e}: {g} is not a constant log atom")
    acc = None
    const = sp.Integer(0)
    for mon, c in sorted(sp.Poly(e, *gens).terms(), key=lambda t: (-sum(t[0]), t[0])):
        c = sp.Rational(c)
        if sum(mon) == 0:
            const = c
            continue
        node = None
        for g, x in zip(gens, mon):
            for _ in range(x):
                ln = _log_node(_log_arg(g))
                node = ln if node is None else node_mul(node, ln)
        mag = abs(c)
        term = node if mag == 1 else node_mul(node_rat(mag), node)
        if acc is None:
            acc = term if c > 0 else node_mul(node_rat(c), node)
        else:
            acc = node_add(acc, term) if c > 0 else node_sub(acc, term)
    if const > 0:
        acc = node_add(acc, node_rat(const))
    elif const < 0:
        acc = node_sub(acc, node_rat(-const))
    return acc


def _round_down(q: sp.Rational, grid: int) -> sp.Rational:
    return sp.Rational(floor(q * grid), grid)


def _round_up(q: sp.Rational, grid: int) -> sp.Rational:
    return -_round_down(-q, grid)


def _enclose(e: sp.Expr, what: str, *, lo=None, hi=None) -> EnclosureTreeCert:
    try:
        return enclosure_tree_certificate(tree_of_constant(e), lo=lo, hi=hi)
    except EnclosureTreeRefusal as exc:
        raise _refuse(f"{what}: the enclosure fold refuses: {exc}") from None


# --- the certificate ----------------------------------------------------------------

@dataclass(frozen=True)
class AtomGap:
    """One listed atom: the exact gap value (a constant DSL polynomial), its certified
    rational lower bound ``g`` and -- unless the gap is rational -- the enclosure certificate
    whose stated lower end is ``g``."""

    k: int
    value: sp.Expr
    g: sp.Rational
    enc: EnclosureTreeCert | None = None


@dataclass(frozen=True)
class TailGap:
    """The certified tail ``k >= K0``: ``gamma(k) = P k - c log(k + s) + d`` with ``c >= 0``
    and ``P >= P_lo >= c / (K0 + s)``; the tail inherits the anchor's bound ``anchor.g``."""

    K0: int
    shift: int
    c: sp.Rational
    P: sp.Expr
    P_lo: sp.Rational
    P_enc: EnclosureTreeCert | None
    anchor: AtomGap


@dataclass(frozen=True)
class KnapsackCert:
    """The joint knapsack over the surviving positive-gap listed atoms: every count vector
    ``x <= caps`` with ``sum x_i * ints_i <= bound`` (the rational budget cleared by the
    common denominator ``denom``) is listed in ``vectors``."""

    atoms: tuple
    gs: tuple
    caps: tuple
    denom: int
    ints: tuple
    bound: int
    vectors: tuple


@dataclass(frozen=True)
class GapBudgetCert:
    """One gap-budget certificate (all fields exact; see the module docstring)."""

    kmin: int
    kmax: int | None
    params: tuple
    w: sp.Expr
    ell: sp.Expr
    tau: sp.Expr
    M: sp.Expr
    concave: tuple | None          # (c, x0, y) or None
    bench: tuple                   # ((atom, multiplicity), ...)
    B: sp.Expr
    theta: sp.Expr
    theta_hi: sp.Rational
    theta_enc: EnclosureTreeCert | None
    atoms: tuple                   # AtomGap per listed atom
    tail: TailGap | None
    caps: tuple                    # ((k, cap), ...) for listed atoms with g > 0
    tail_cap: int | None           # 0 = tail excluded
    knapsack: KnapsackCert | None

    @property
    def gap(self) -> sp.Expr:
        return _gap_expr(self.tau, self.ell, self.w, self.M, self.concave)

    @property
    def n_theorems(self) -> int:
        n = len(self.atoms) + 2                    # gap lemmas, bench, main
        if self.tail is not None:
            n += 2                                 # anchor + tail
        return n


def _gap_expr(tau, ell, w, M, concave):
    g = tau * ell - w
    if concave is not None:
        c, x0, y = concave
        g = g - c / x0 / M * y
    return sp.expand(g)


def _atom_gap(value: sp.Expr, k0: int, grid: int, claim) -> AtomGap:
    what = f"gap at atom k = {k0}"
    if value.is_Rational:
        if value < 0:
            raise _refuse(f"{what} is {value} < 0: the price does not dominate this atom (every "
                          "gap on the alphabet must be >= 0 for the budget argument)")
        if claim is not None and claim != value:
            raise _refuse(f"{what} is exactly {value}; the claimed lower bound {claim} is not it "
                          "(an exact gap takes no other bound)")
        return AtomGap(k=k0, value=value, g=value)
    probe = _enclose(value, what)
    if probe.root.box_lo <= 0 or probe.root.lo <= 0:
        if probe.root.hi < 0:
            raise _refuse(f"{what} is certified NEGATIVE (<= {probe.root.hi}): the price does "
                          "not dominate this atom")
        raise _refuse(f"{what} is not provably >= 0 (fold [{probe.root.box_lo}, "
                      f"{probe.root.box_hi}]); a zero-gap atom must be exactly zero")
    if claim is None:
        g = _round_down(probe.root.lo, grid)
        if g <= 0:
            g = probe.root.lo
    else:
        g = claim
        if g <= 0:
            raise _refuse(f"{what}: a claimed lower bound {g} <= 0 prunes nothing; omit it")
    enc = _enclose(value, what, lo=g, hi=_round_up(probe.root.hi, grid))
    return AtomGap(k=k0, value=value, g=g, enc=enc)


def _consequences(atoms, theta_hi, tail, tail_anchor_g, knapsack: bool):
    """The pure arithmetic of the budget: caps, the tail cap, the knapsack list."""
    caps = tuple((a.k, int(floor(theta_hi / a.g))) for a in atoms if a.g > 0)
    tail_cap = None
    if tail is not None:
        tail_cap = int(floor(theta_hi / tail_anchor_g))
    ks = None
    surv = [(a, c) for a, (k, c) in zip([a for a in atoms if a.g > 0], caps) if c >= 1]
    if knapsack and len(surv) >= 2:
        box = 1
        for _a, c in surv:
            box *= c + 1
        if box > MAX_KNAPSACK_BOX:
            raise _refuse(f"the knapsack box has {box} points > {MAX_KNAPSACK_BOX} (decide "
                          "cost); pass knapsack=False or a tighter budget")
        gs = tuple(a.g for a, _c in surv)
        denom = int(sp.ilcm(*[g.q for g in gs], theta_hi.q))
        ints = tuple(int(g * denom) for g in gs)
        bound = int(floor(theta_hi * denom))
        vecs = tuple(v for v in _iproduct(*[range(c + 1) for _a, c in surv])
                     if sum(x * p for x, p in zip(v, ints)) <= bound)
        ks = KnapsackCert(atoms=tuple(a.k for a, _c in surv), gs=gs,
                          caps=tuple(c for _a, c in surv), denom=denom, ints=ints,
                          bound=bound, vectors=vecs)
    if not caps and tail is None:
        raise _refuse("the budget prunes nothing: every listed atom has gap 0 and there is no "
                      "tail (the certificate would restate its hypotheses)")
    return caps, tail_cap, ks


def gap_budget_multiplicity_certificate(
    *, atoms, w, ell, tau, M, bench, params=(), concave=None, tail_start=None,
    knapsack=True, grid=DEFAULT_GRID, gap_lo=None, theta_hi=None,
) -> GapBudgetCert:
    """Build (and exactly re-check) a gap-budget certificate.  Every refusal of the module
    docstring raises :class:`GapBudgetRefusal`; nothing is widened.

    ``atoms = (kmin, kmax)`` (``kmax=None``: an infinite alphabet with a certified tail from
    ``tail_start``); ``w``, ``ell``, ``tau``, ``M`` are DSL expressions (``K`` the atom label,
    ``gb_log(q)`` / ``gb_logk(s)`` the log atoms, ``params`` natural-number parameters that may
    appear in ``M`` and the benchmark multiplicities only); ``bench`` is ``((atom, mult), ...)``;
    ``concave = ("log", c, x0, y)`` adds ``c * log(sum y / M)`` (``c > 0``, ``x0 > 0``
    rational, ``M`` rational); ``gap_lo = {k: g}`` / ``theta_hi`` CLAIM bounds (refused unless
    the fold implies them); ``grid`` is the rounding denominator."""
    if not isinstance(atoms, (tuple, list)) or len(atoms) != 2:
        raise _refuse(f"atoms must be (kmin, kmax), got {atoms!r}")
    kmin = _int(atoms[0], "kmin")
    kmax = None if atoms[1] is None else _int(atoms[1], "kmax")
    if kmin < 0:
        raise _refuse(f"kmin = {kmin} < 0 (atoms are natural-number labels)")
    grid = _int(grid, "grid")
    if grid < 1:
        raise _refuse(f"grid = {grid} < 1")
    if not isinstance(knapsack, bool):
        raise _refuse("knapsack must be a bool")
    params = tuple(params)
    for p in params:
        if not isinstance(p, sp.Symbol) or not _IDENT.match(p.name) or p.name in _RESERVED \
                or p.name.startswith("GBL") or p == K:
            raise _refuse(f"parameter {p!r} is not a fresh Lean identifier symbol")
    if kmax is None:
        if tail_start is None:
            raise _refuse("an infinite alphabet (kmax=None) needs a certified tail: pass "
                          "tail_start")
        K0 = _int(tail_start, "tail_start")
        if K0 <= kmin:
            raise _refuse(f"tail_start = {K0} must exceed kmin = {kmin}")
        listed = list(range(kmin, K0))
    else:
        if tail_start is not None:
            raise _refuse("tail_start given for a finite alphabet")
        if kmax < kmin:
            raise _refuse(f"kmax = {kmax} < kmin = {kmin}")
        K0 = None
        listed = list(range(kmin, kmax + 1))
    if len(listed) > MAX_ATOMS:
        raise _refuse(f"{len(listed)} listed atoms exceed {MAX_ATOMS}")

    w = _check_expr(w, "w", "kLK")
    ell = _check_expr(ell, "ell", "k")
    tau = _check_expr(tau, "tau", "L")
    conc = None
    if concave is not None:
        if not isinstance(concave, (tuple, list)) or len(concave) != 4:
            raise _refuse("concave must be ('log', c, x0, y)")
        fam, c, x0, y = concave
        if fam != "log":
            raise _refuse(f"concave family {fam!r} is not certified concave (only c * log x "
                          "with c >= 0 has an emitted tangent lemma)")
        c = _rat(c, "concave c")
        x0 = _rat(x0, "tangent point x0")
        if c < 0:
            raise _refuse(f"c = {c} < 0: c * log x is CONVEX, the tangent bound runs the wrong "
                          "way")
        if c == 0:
            raise _refuse("c = 0: there is no concave part; use the separable model")
        if x0 <= 0:
            raise _refuse(f"tangent point x0 = {x0} <= 0 is outside log's domain")
        y = _check_expr(y, "y", "k")
        M = _check_expr(M, "M", "")
        if M <= 0:
            raise _refuse(f"M = {M} <= 0 (the normalisation divides)")
        conc = (c, x0, y)
    else:
        M = _check_expr(M, "M", "p", params)

    # benchmark
    if not isinstance(bench, (tuple, list)) or not bench:
        raise _refuse("the benchmark must be a non-empty ((atom, multiplicity), ...)")
    bnorm = []
    seen = set()
    for entry in bench:
        if not isinstance(entry, (tuple, list)) or len(entry) != 2:
            raise _refuse(f"benchmark entry {entry!r} is not (atom, multiplicity)")
        a = _int(entry[0], "benchmark atom")
        if a in seen:
            raise _refuse(f"benchmark atom {a} repeated; merge the multiplicities")
        seen.add(a)
        if a < kmin or (kmax is not None and a > kmax):
            raise _refuse(f"benchmark atom {a} is outside the alphabet")
        mult = _check_expr(entry[1], f"multiplicity of {a}", "p", params)
        if conc is not None and not mult.is_Integer:
            raise _refuse("a concave instance needs natural benchmark multiplicities")
        coeffs = sp.Poly(mult, *params).coeffs() if params and not mult.is_Rational else [mult]
        if any((not sp.Rational(cf).is_integer) or cf < 0 for cf in coeffs):
            raise _refuse(f"multiplicity {mult} of {a} is not a natural-number polynomial")
        bnorm.append((a, mult))
    bench = tuple(bnorm)
    ell_b = sp.expand(sum(mult * _at_atom(ell, a, "ell") for a, mult in bench))
    if sp.expand(ell_b - M) != 0:
        raise _refuse(f"the benchmark normalisation sum ell = {ell_b} is not M = {M}")
    B = sp.expand(sum(mult * _at_atom(w, a, "w") for a, mult in bench))
    if conc is not None:
        c, x0, y = conc
        ybar = sp.expand(sum(mult * _at_atom(y, a, "y") for a, mult in bench)) / M
        if ybar <= 0:
            raise _refuse(f"the benchmark mean {ybar} <= 0 is outside log's domain")
        if ybar != 1:
            B = sp.expand(B + c * gb_log(ybar))
        C = tau * M + (c * gb_log(x0) if x0 != 1 else 0) - c
    else:
        C = tau * M
    theta = sp.expand(C - B)
    stray = [s for s in theta.free_symbols if _log_arg(s) is None]
    if stray:
        raise _refuse(f"theta = {theta} depends on {stray}: the budget is not uniform")

    # theta_hi
    claim_hi = None if theta_hi is None else _rat(theta_hi, "theta_hi")
    if theta.is_Rational:
        if theta < 0:
            raise _refuse(f"theta = {theta} < 0: the benchmark beats the tangent bound "
                          "(inconsistent input)")
        if claim_hi is not None and claim_hi < theta:
            raise _refuse(f"claimed theta_hi = {claim_hi} is below the exact theta = {theta}")
        th_hi = theta if claim_hi is None else claim_hi
        th_enc = None
    else:
        probe = _enclose(theta, "theta")
        if probe.root.hi < 0:
            raise _refuse(f"theta is certified NEGATIVE (<= {probe.root.hi}): inconsistent "
                          "input")
        th_hi = _round_up(probe.root.hi, grid) if claim_hi is None else claim_hi
        th_enc = _enclose(theta, "theta", lo=_round_down(probe.root.lo, grid), hi=th_hi)

    # gaps
    gap = _gap_expr(tau, ell, w, M, conc)
    claims = {}
    for k0, g in (gap_lo or {}).items():
        claims[_int(k0, "gap_lo atom")] = _rat(g, f"gap_lo[{k0}]")
    stray_claims = set(claims) - set(listed) - ({K0} if K0 is not None else set())
    if stray_claims:
        raise _refuse(f"gap_lo claims for atoms {sorted(stray_claims)} outside the listed atoms "
                      "and the tail anchor")
    atom_gaps = tuple(_atom_gap(_at_atom(gap, k0, f"gap at {k0}"), k0, grid, claims.get(k0))
                      for k0 in listed)

    tail = None
    if K0 is not None:
        tail = _tail(gap, K0, grid, claims.get(K0))
    caps, tail_cap, ks = _consequences(atom_gaps, th_hi, tail,
                                       tail.anchor.g if tail else None, knapsack)
    _bench_self_check(bench, params, caps, tail, tail_cap, ks)
    return GapBudgetCert(kmin=kmin, kmax=kmax, params=params, w=w, ell=ell, tau=tau, M=M,
                         concave=conc, bench=bench, B=B, theta=theta, theta_hi=th_hi,
                         theta_enc=th_enc, atoms=atom_gaps, tail=tail, caps=caps,
                         tail_cap=tail_cap, knapsack=ks)


def _bench_self_check(bench, params, caps, tail, tail_cap, ks) -> None:
    """The benchmark attains `B`, so it MUST satisfy every consequence; a violation means the
    input is inconsistent (or this module has a bug) -- refuse rather than emit.  Checked at
    the parameter values 0..3."""
    for vals in _iproduct(range(4), repeat=len(params)):
        at = dict(zip(params, vals))
        cnt = {a: int(sp.sympify(mult).subs(at)) for a, mult in bench}
        for k0, cap in caps:
            if cnt.get(k0, 0) > cap:
                raise _refuse(f"self-check: the benchmark has {cnt[k0]} copies of atom {k0} "
                              f"but the certified cap is {cap} (inconsistent input)")
        if tail is not None and tail_cap is not None:
            for a, c in cnt.items():
                if a >= tail.K0 and c > tail_cap:
                    raise _refuse(f"self-check: the benchmark violates the tail cap at {a}")
        if ks is not None:
            v = tuple(cnt.get(a, 0) for a in ks.atoms)
            if v not in ks.vectors:
                raise _refuse(f"self-check: the benchmark count vector {v} is not in the "
                              "knapsack list (inconsistent input)")


def _tail(gap: sp.Expr, K0: int, grid: int, claim) -> TailGap:
    lks = [s for s in gap.free_symbols if _logk_shift(s) is not None]
    for lk in lks:
        if sp.Poly(gap, lk).degree() > 1:
            raise _refuse(f"tail gap {gap} has a power of log(k + {_logk_shift(lk)}) above 1; "
                          "the certified tail shape is P k - c log(k + s) + d")
    if len(lks) > 1:
        raise _refuse(f"tail gap {gap} has several log(k + s) terms; the certified tail shape "
                      "is P k - c log(k + s) + d")
    if lks:
        lk = lks[0]
        shift = _logk_shift(lk)
        coeff = sp.expand(gap).coeff(lk)
        if not coeff.is_Rational or coeff > 0:
            raise _refuse(f"tail gap: the coefficient of log(k + {shift}) is {coeff}; the "
                          "certified shape needs -c log(k + s) with rational c >= 0 (convex)")
        c = -sp.Rational(coeff)
        rest = sp.expand(gap - coeff * lk)
    else:
        shift, c, rest = 0, sp.Integer(0), sp.expand(gap)
    if rest.has(K) and sp.Poly(rest, K).degree() > 1:
        raise _refuse(f"tail gap: {rest} is not affine in k; the certified tail shape is "
                      "P k - c log(k + s) + d")
    P = sp.expand(rest.coeff(K, 1))
    if P.has(K) or any(_logk_shift(s) is not None for s in P.free_symbols):
        raise _refuse(f"tail gap: the slope {P} is not a constant")
    if K0 + shift <= 0:
        raise _refuse(f"tail: K0 + s = {K0 + shift} <= 0 is outside log's domain")
    need = c / (K0 + shift)
    if P.is_Rational:
        P_lo, P_enc = sp.Rational(P), None
    else:
        probe = _enclose(P, "tail slope")
        P_lo = probe.root.lo
        if probe.root.lo < need:
            raise _refuse(f"tail slope: the certified lower bound {probe.root.lo} of P = {P} is "
                          f"below c/(K0+s) = {need}; monotonicity from K0 = {K0} is not "
                          "certified")
        P_lo = _round_down(P_lo, grid)
        if P_lo < need:
            P_lo = need
        P_enc = _enclose(P, "tail slope", lo=P_lo, hi=_round_up(probe.root.hi, grid))
    if P_lo < need:
        raise _refuse(f"tail slope P = {P} < c/(K0+s) = {need}: the gap is not certified "
                      f"nondecreasing from K0 = {K0}")
    anchor = _atom_gap(_at_atom(gap, K0, "tail anchor"), K0, grid, claim)
    if anchor.g <= 0:
        raise _refuse(f"tail anchor gap at K0 = {K0} is 0; a zero-gap tail prunes nothing")
    return TailGap(K0=K0, shift=shift, c=c, P=P, P_lo=P_lo, P_enc=P_enc, anchor=anchor)


def certify_gap_budget_multiplicity_point(family, pt, name):
    """Certify one point: ``(CertifiedInstance, n_checks)``; the spec dict is
    ``family.special[1](pt)`` with the keyword arguments of
    :func:`gap_budget_multiplicity_certificate`.  Unknown keys are refused."""
    spec = family.special[1](pt)
    if not isinstance(spec, dict):
        raise _refuse(f"the family spec must be a dict, got {type(spec).__name__}")
    unknown = set(spec) - _SPEC_KEYS
    if unknown:
        raise _refuse(f"unknown gap_budget_multiplicity spec key(s) {sorted(unknown)}")
    if not _IDENT.match(name):
        raise _refuse(f"instance name {name!r} is not a Lean identifier")
    cert = gap_budget_multiplicity_certificate(**spec)
    return (CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert),
            cert.n_theorems)


_SPEC_KEYS = frozenset({"atoms", "w", "ell", "tau", "M", "bench", "params", "concave",
                        "tail_start", "knapsack", "grid", "gap_lo", "theta_hi"})


# --- the Lean -----------------------------------------------------------------------

_CORE = """\
/-- The tangent step for the certified concave family `c * log`: for `c >= 0`,
    `c log x <= c log x0 + (c / x0) (x - x0)` (`Real.log_le_sub_one_of_pos` at `x / x0`).
    conjecture1_proved = False. -/
theorem gapBudget_log_tangent {c x x0 : ℝ} (hc : 0 ≤ c) (hx0 : 0 < x0) (hx : 0 < x) :
    c * Real.log x ≤ c * Real.log x0 + c / x0 * (x - x0) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hx0)
  rw [Real.log_div hx.ne' hx0.ne'] at h
  have h2 : c * (Real.log x - Real.log x0) ≤ c * (x / x0 - 1) :=
    mul_le_mul_of_nonneg_left h hc
  have e : c * (x / x0 - 1) = c / x0 * (x - x0) := by field_simp
  linarith

/-- The budget of the SEPARABLE model: `sum ell = M` and `B <= sum w` give
    `sum gamma <= tau M - B` for `gamma = tau ell - w`. -/
theorem gapBudget_of_sep {α : Type*} (m : Multiset α) (w ℓ γ : α → ℝ) (τ M B : ℝ)
    (hγ : ∀ a, γ a = τ * ℓ a - w a)
    (hℓ : (m.map ℓ).sum = M) (hB : B ≤ (m.map w).sum) :
    (m.map γ).sum ≤ τ * M - B := by
  have e : (m.map γ).sum = τ * (m.map ℓ).sum - (m.map w).sum := by
    rw [show γ = fun a => τ * ℓ a - w a from funext hγ, Multiset.sum_map_sub,
      Multiset.sum_map_mul_left]
  rw [e, hℓ]
  linarith

/-- The budget of the CONCAVE model `Phi = sum w + c log (sum y / M)`: the tangent at `x0`
    with slope `c / x0` gives `sum gamma <= tau M + c log x0 - c - B` for
    `gamma = tau ell - w - (c / x0 / M) y`. -/
theorem gapBudget_of_concave {α : Type*} (m : Multiset α) (w ℓ y γ : α → ℝ)
    (τ M B c x0 : ℝ) (hγ : ∀ a, γ a = τ * ℓ a - w a - c / x0 / M * y a)
    (hc : 0 ≤ c) (hx0 : 0 < x0) (hdom : 0 < (m.map y).sum / M)
    (hℓ : (m.map ℓ).sum = M)
    (hB : B ≤ (m.map w).sum + c * Real.log ((m.map y).sum / M)) :
    (m.map γ).sum ≤ τ * M + c * Real.log x0 - c / x0 * x0 - B := by
  have ht := gapBudget_log_tangent hc hx0 hdom
  have e : (m.map γ).sum
      = τ * (m.map ℓ).sum - (m.map w).sum - c / x0 / M * (m.map y).sum := by
    rw [show γ = fun a => τ * ℓ a - w a - c / x0 / M * y a from funext hγ,
      Multiset.sum_map_sub, Multiset.sum_map_sub, Multiset.sum_map_mul_left,
      Multiset.sum_map_mul_left]
  have e2 : c / x0 / M * (m.map y).sum = c / x0 * ((m.map y).sum / M) := by ring
  rw [e, hℓ, e2]
  linarith

/-- One atom's share of the budget: with every gap in `m` nonnegative,
    `count a * g <= theta` for any `g <= gamma a`. -/
theorem gapBudget_count_mul_le {α : Type*} [DecidableEq α] (m : Multiset α) (γ : α → ℝ)
    (θ : ℝ) (hγ : ∀ a ∈ m, 0 ≤ γ a) (hbud : (m.map γ).sum ≤ θ) (a : α) (g : ℝ)
    (hg : g ≤ γ a) : (m.count a : ℝ) * g ≤ θ := by
  rw [← Multiset.filter_add_not (· = a) m, Multiset.map_add, Multiset.sum_add,
    Multiset.filter_eq' m a, Multiset.map_replicate, Multiset.sum_replicate,
    nsmul_eq_mul] at hbud
  have hrest : 0 ≤ ((m.filter (fun b => ¬ b = a)).map γ).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
      exact hγ b (Multiset.mem_of_mem_filter hb)
  have := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α := ℝ) (m.count a))
  linarith

/-- The integer cap: `x g <= theta < (cap + 1) g` with `g > 0` forces `x <= cap`. -/
theorem gapBudget_nat_cap {x : ℕ} {g θ : ℝ} (cap : ℕ) (hg : 0 < g)
    (h : (x : ℝ) * g ≤ θ) (hcap : θ < ((cap : ℝ) + 1) * g) : x ≤ cap := by
  by_contra hc
  have h1 : (cap : ℝ) + 1 ≤ x := by exact_mod_cast Nat.succ_le_of_lt (not_le.mp hc)
  nlinarith

/-- The joint knapsack: `sum_{a in A} count a * g a <= theta` for gap lower bounds on `A`. -/
theorem gapBudget_knapsack {α : Type*} [DecidableEq α] (m : Multiset α) (γ g : α → ℝ)
    (θ : ℝ) (hγ : ∀ a ∈ m, 0 ≤ γ a) (hbud : (m.map γ).sum ≤ θ) (A : Finset α)
    (hg : ∀ a ∈ A, g a ≤ γ a) : ∑ a ∈ A, (m.count a : ℝ) * g a ≤ θ := by
  have h1 : ∑ a ∈ A, (m.count a : ℝ) * g a ≤ ∑ a ∈ A, (m.count a : ℝ) * γ a :=
    Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hg a ha) (Nat.cast_nonneg _)
  have h2 : ∑ a ∈ A, (m.count a : ℝ) * γ a
      = ∑ a ∈ A with a ∈ m.toFinset, (m.count a : ℝ) * γ a := by
    refine (Finset.sum_filter_of_ne fun a _ hne => ?_).symm
    by_contra hn
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hn
    simp [hn] at hne
  have h3 : ∑ a ∈ A with a ∈ m.toFinset, (m.count a : ℝ) * γ a
      ≤ ∑ a ∈ m.toFinset, (m.count a : ℝ) * γ a :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_filter.mp ha).2)
      fun a ha _ => mul_nonneg (Nat.cast_nonneg _) (hγ a (Multiset.mem_toFinset.mp ha))
  have h4 : (m.map γ).sum = ∑ a ∈ m.toFinset, (m.count a : ℝ) * γ a := by
    rw [Finset.sum_multiset_map_count]
    simp [nsmul_eq_mul]
  linarith
"""

#: the number of theorems in `_CORE`.
CORE_THEOREMS = 6


def _lit(q: sp.Rational) -> str:
    q = sp.Rational(q)
    if q.q == 1:
        return f"({q.p} : ℝ)"
    if q.p >= 0:
        return f"({q.p} / {q.q} : ℝ)"
    return f"(-({-q.p} / {q.q}) : ℝ)"


class _EncBook:
    """Family-wide book of emitted enclosure theorems (shared subtrees proved ONCE)."""

    def __init__(self, prefix: str, used: set):
        self.prefix = prefix
        self.names: dict = {}
        self.used = used
        self.k: dict = {}

    def emit(self, cert: EnclosureTreeCert, root_name: str, chunks: list) -> tuple:
        n = 0
        for node in cert.order:
            if node.key in self.names:
                continue
            if node.key == cert.root.key:
                nm = root_name
            else:
                self.k[self.prefix] = self.k.get(self.prefix, -1) + 1
                nm = f"{self.prefix}_enc{self.k[self.prefix]}"
            _claim(self.used, nm)
            self.names[node.key] = nm
            chunks.append(_enc_header(node, nm) + f"theorem {nm} :\n    "
                          f"{_enc_statement(node)} := by\n" + _enc_proof_body(node, self.names))
            n += 1
        return self.names[cert.root.key], n


def _claim(used: set, nm: str) -> None:
    if nm in used:
        raise _refuse(f"duplicate emitted theorem name {nm!r}")
    used.add(nm)


def _pretty(e) -> str:
    """A DSL expression for a comment: the log atoms as `log(q)` / `log(k + s)`."""
    e = sp.sympify(e)
    subs = {}
    for s in e.free_symbols:
        if _log_arg(s) is not None:
            subs[s] = sp.Symbol(f"log({_log_arg(s)})")
        elif _logk_shift(s) is not None:
            sh = _logk_shift(s)
            subs[s] = sp.Symbol("log(k)" if sh == 0 else f"log(k {'+' if sh > 0 else '-'} {abs(sh)})")
    return str(e.subs(subs))


def _kb(e: sp.Expr) -> str:
    """The atom binder of a model `def`: `k`, or `_k` when the body does not mention it."""
    return "k" if any(s == K or _logk_shift(s) is not None for s in e.free_symbols) else "_k"


def _binders(params) -> str:
    return "".join(f"({p.name} : ℕ) " for p in params)


def _bench_lean(cert: GapBudgetCert) -> str:
    parts = [f"Multiset.replicate {_paren_nat(_lean_nat_poly(mult))} {a}"
             for a, mult in cert.bench]
    return f"({' + '.join(parts)} : Multiset ℕ)"


def _paren_nat(s: str) -> str:
    return s if re.fullmatch(r"[A-Za-z0-9_']+", s) else f"({s})"


def _phi_lean(cert: GapBudgetCert, nm: str, ms: str) -> str:
    base = f"({ms}.map {nm}_w).sum"
    if cert.concave is None:
        return base
    c, _x0, _y = cert.concave
    return (f"{base} + {_q_lean(c, 70)} * Real.log (({ms}.map {nm}_y).sum / "
            f"{_q_lean(cert.M, 71)})")


def _emit_instance(cert: GapBudgetCert, nm: str, book: _EncBook, used: set) -> tuple:
    chunks: list = []
    n = 0
    P = cert.params
    defs = [f"{nm}_w", f"{nm}_ell", f"{nm}_gap"] + ([f"{nm}_y"] if cert.concave else [])
    for d in defs:
        _claim(used, d)
    unfold = ", ".join(defs)

    # the model
    tau_l = lean_poly(cert.tau)
    model = [f"/-- `{nm}` -- the gap-budget model (kind gap_budget_multiplicity).",
             f"    Atoms k in [{cert.kmin}, {'oo' if cert.kmax is None else cert.kmax}], "
             f"normalisation sum ell = {cert.M}, price tau = {_pretty(cert.tau)}"
             + (f", concave part {cert.concave[0]} * log(sum y / M) tangent at x0 = "
                f"{cert.concave[1]}" if cert.concave else "") + ".",
             "    conjecture1_proved = False. -/",
             f"noncomputable def {nm}_w ({_kb(cert.w)} : ℕ) : ℝ := {lean_poly(cert.w)}",
             f"noncomputable def {nm}_ell ({_kb(cert.ell)} : ℕ) : ℝ := {lean_poly(cert.ell)}"]
    if cert.concave:
        c, x0, y = cert.concave
        model.append(f"noncomputable def {nm}_y ({_kb(y)} : ℕ) : ℝ := {lean_poly(y)}")
        model.append(f"noncomputable def {nm}_gap (k : ℕ) : ℝ :=\n  ({tau_l}) * {nm}_ell k - "
                     f"{nm}_w k - ({_q_lean(c)}) / ({_q_lean(x0)}) / ({_q_lean(cert.M)}) * "
                     f"{nm}_y k")
    else:
        model.append(f"noncomputable def {nm}_gap (k : ℕ) : ℝ :=\n  ({tau_l}) * {nm}_ell k - "
                     f"{nm}_w k")
    chunks.append("\n".join(model) + "\n")

    # enclosures and gap lemmas
    def gap_lemma(a: AtomGap, lname: str, role: str) -> str:
        nonlocal n
        head = (f"/-- `{lname}` -- {role}: the gap at k = {a.k} is at least {a.g}"
                + (" (exact: the gap is rational)" if a.enc is None else
                   " (the stated lower end of a rational enclosure; the generator refuses a "
                   "bound the fold does not imply)")
                + ".\n    conjecture1_proved = False. -/\n")
        if a.enc is None:
            body = (f"  have e : {nm}_gap {a.k} = {_lit(a.g)} := by\n"
                    f"    simp only [{unfold}]\n"
                    "    ring_nf\n"
                    "  exact e.symm.le\n")
        else:
            rn, k = book.emit(a.enc, f"{lname}_enc", chunks)
            n += k
            body = (f"  obtain ⟨h0, h1⟩ := {rn}\n"
                    f"  norm_num [{unfold}]\n"
                    "  linarith\n")
        _claim(used, lname)
        n += 1
        return head + f"theorem {lname} : {_lit(a.g)} ≤ {nm}_gap {a.k} := by\n" + body

    for a in cert.atoms:
        chunks.append(gap_lemma(a, f"{nm}_gap_{a.k}", "listed atom"))

    tail = cert.tail
    if tail is not None:
        an = f"{nm}_gap_{tail.K0}"
        chunks.append(gap_lemma(tail.anchor, an, "the tail anchor"))
        _claim(used, f"{nm}_tail")
        txt, k = _tail_lemma(cert, nm, an, unfold, book, chunks)
        chunks.append(txt)
        n += 1 + k

    # theta enclosure
    th_name = None
    if cert.theta_enc is not None:
        th_name, k = book.emit(cert.theta_enc, f"{nm}_theta_enc", chunks)
        n += k

    # benchmark lemma
    bench = _bench_lean(cert)
    _claim(used, f"{nm}_bench")
    tac = (f"norm_num [{unfold}, Multiset.map_replicate, Multiset.sum_replicate, "
           "nsmul_eq_mul]")
    rng = (f"{cert.kmin} ≤ k" if cert.kmax is None
           else f"{cert.kmin} ≤ k ∧ k ≤ {cert.kmax}")
    bs = ["set_option linter.unusedTactic false in",
          "set_option linter.unreachableTactic false in",
          f"/-- `{nm}_bench` -- the benchmark meets EVERY hypothesis of `{nm}` and ATTAINS `B`:",
          "    `Phi(bench) = B`, `sum ell(bench) = M`, its atoms lie in the alphabet"
          + (" and its mean is positive" if cert.concave else "") + ",",
          "    so the main theorem is not vacuous and applies to every optimum.",
          "    conjecture1_proved = False. -/",
          f"theorem {nm}_bench {_binders(P)}:",
          f"    {_phi_lean(cert, nm, bench)} = {lean_poly(cert.B, P)} ∧",
          f"    ({bench}.map {nm}_ell).sum = {lean_poly(cert.M, P)} ∧",
          f"    (∀ k ∈ {bench}, {rng})"
          + (f" ∧\n    0 < ({bench}.map {nm}_y).sum / {_q_lean(cert.M, 71)}" if cert.concave
             else "") + " := by",
          "  refine ⟨?_, ?_, ?_" + (", ?_" if cert.concave else "") + "⟩",
          f"  · {tac}",
          "    all_goals ring_nf",
          f"  · {tac}",
          "    all_goals ring_nf",
          "  · intro k hk",
          "    simp only ["
          + ("Multiset.mem_add, " if len(cert.bench) > 1 else "")
          + "Multiset.mem_replicate] at hk",
          "    omega"]
    if cert.concave:
        bs.append(f"  · {tac}")
    chunks.append("\n".join(bs) + "\n")
    n += 1

    chunks.append(_main_theorem(cert, nm, th_name))
    _claim(used, nm)
    n += 1
    return chunks, n


def _tail_lemma(cert, nm, anchor_name, unfold, book, chunks_ref) -> tuple:
    t = cert.tail
    x = "(k : ℝ)" if t.shift == 0 else f"(k : ℝ) {'+' if t.shift > 0 else '-'} {abs(t.shift)}"
    x0 = t.K0 + t.shift
    lines = [f"/-- `{nm}_tail` -- the certified TAIL: every atom k >= {t.K0} has gap at least "
             f"{t.anchor.g}.",
             f"    The gap is P k - {t.c} log(k + {t.shift}) + d with P >= {t.P_lo} >= "
             f"{t.c}/{x0}; the",
             "    log tangent at K0 + s (convexity) makes it nondecreasing from the anchor.",
             "    conjecture1_proved = False. -/",
             f"theorem {nm}_tail (k : ℕ) (hk : {t.K0} ≤ k) : {_lit(t.anchor.g)} ≤ {nm}_gap k := by",
             f"  have hk' : ({t.K0} : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk",
             f"  have h0 := {anchor_name}"]
    if t.c > 0:
        lines.append(f"  have ht := gapBudget_log_tangent (c := {_q_lean(t.c, 1024)}) "
                     f"(x := {x}) (x0 := {x0}) (by norm_num)\n    (by norm_num) (by linarith)")
    nenc = 0
    if t.P_enc is not None:
        rn, nenc = book.emit(t.P_enc, f"{nm}_slope_enc", chunks_ref)
        lines.append(f"  obtain ⟨hp0, hp1⟩ := {rn}")
    P_l = lean_poly(t.P)
    lines.append(f"  have hprod : 0 ≤ ({P_l} - {_q_lean(t.c, 70)} / {x0}) * ((k : ℝ) - {t.K0}) "
                 ":=\n    mul_nonneg (by linarith) (by linarith)")
    lines.append(f"  simp only [{unfold}] at h0 ⊢")
    lines.append("  norm_num at h0" + (" ht" if t.c > 0 else ""))
    lines.append("  linarith")
    return "\n".join(lines) + "\n", nenc


def _main_theorem(cert: GapBudgetCert, nm: str, th_name) -> str:
    P = cert.params
    t = cert.tail
    rng = (f"{cert.kmin} ≤ k" if cert.kmax is None
           else f"{cert.kmin} ≤ k ∧ k ≤ {cert.kmax}")
    hyps = [f"(hA : ∀ k ∈ m, {rng})",
            f"(hl : (m.map {nm}_ell).sum = {lean_poly(cert.M, P)})"]
    if cert.concave:
        hyps.append(f"(hdom : 0 < (m.map {nm}_y).sum / {_q_lean(cert.M, 71)})")
    hyps.append(f"(hB : {lean_poly(cert.B, P)} ≤ {_phi_lean(cert, nm, 'm')})")

    # conclusions
    concl: list = []            # (statement, proof lines)
    gmap = {a.k: a for a in cert.atoms}
    for k0, cap in cert.caps:
        lem = f"{nm}_gap_{k0}"
        core = (f"gapBudget_nat_cap {cap} (by norm_num) (hc {k0} _ {lem}) "
                "(by norm_num)")
        if cap == 0:
            concl.append((f"m.count {k0} = 0", [f"Nat.le_zero.mp ({core})"]))
        else:
            concl.append((f"m.count {k0} ≤ {cap}", [core]))
    if t is not None:
        if cert.tail_cap == 0:
            concl.append((f"∀ k ∈ m, k < {t.K0}", [
                "by",
                "    intro k hk",
                "    by_contra hlt",
                f"    have hK : {t.K0} ≤ k := by omega",
                "    have h1 : 1 ≤ m.count k := Multiset.one_le_count_iff_mem.mpr hk",
                f"    have := gapBudget_nat_cap 0 (by norm_num) (hc k _ ({nm}_tail k hK)) "
                "(by norm_num)",
                "    omega"]))
        else:
            concl.append((f"∀ k, {t.K0} ≤ k → m.count k ≤ {cert.tail_cap}", [
                f"fun k hK => gapBudget_nat_cap {cert.tail_cap} (by norm_num) "
                f"(hc k _ ({nm}_tail k hK)) (by norm_num)"]))
    ks = cert.knapsack
    kn_lines: list = []
    if ks is not None:
        xs = [f"x{a}" for a in ks.atoms]
        vec = ", ".join(f"m.count {a}" for a in ks.atoms)
        lst = ", ".join("[" + ", ".join(str(v) for v in vec_) + "]" for vec_ in ks.vectors)
        concl.append((f"[{vec}] ∈ [{lst}]", None))
        ite = " else ".join(f"if k = {a} then {_q_lean(g, 1024)}"
                            for a, g in zip(ks.atoms[:-1], ks.gs[:-1]))
        gfun = (f"fun k => {ite} else {_q_lean(ks.gs[-1], 1024)}" if ite
                else f"fun _ => {_q_lean(ks.gs[-1], 1024)}")
        fin = "{" + ", ".join(str(a) for a in ks.atoms) + "}"
        rc = " | ".join("rfl" for _ in ks.atoms)
        kn_lines += [
            f"  have hkn := gapBudget_knapsack m {nm}_gap ({gfun}) _ hγ hbud {fin} (by",
            "    intro a ha",
            "    simp only [Finset.mem_insert, Finset.mem_singleton] at ha",
            f"    rcases ha with {rc}",
        ]
        for a in ks.atoms:
            kn_lines.append(f"    · simpa using {nm}_gap_{a}")
        kn_lines[-1] += ")"
        rw = ", ".join(["Finset.sum_insert (by decide)"] * (len(ks.atoms) - 1)
                       + ["Finset.sum_singleton"])
        kn_lines.append(f"  rw [{rw}] at hkn")
        kn_lines.append("  norm_num at hkn")
        binders = " ".join(f"∀ {x} ∈ List.range {c + 1}," for x, c in zip(xs, ks.caps))
        lin = " + ".join(f"{x} * {p}" for x, p in zip(xs, ks.ints))
        kn_lines.append(f"  have hdec : {binders} {lin} ≤ {ks.bound} →\n"
                        f"      [{', '.join(xs)}] ∈ [{lst}] := by decide")
        clin = " + ".join(f"m.count {a} * {p}" for a, p in zip(ks.atoms, ks.ints))
        kn_lines.append(f"  have hint : (({clin} : ℕ) : ℝ) ≤ {ks.bound} := by push_cast; linarith")
        args = " ".join(f"_ (List.mem_range.mpr (Nat.lt_succ_of_le c{a}))" for a in ks.atoms)
        kn_lines.append(f"  have ckn := hdec {args} (by exact_mod_cast hint)")
    if not concl:
        raise _refuse("the budget prunes nothing")  # pragma: no cover (checked at certify)

    stmts = [f"({s})" if s.startswith("∀") and len(concl) > 1 else s for s, _ in concl]
    statement = " ∧\n      ".join(stmts)
    head = [f"/-- `{nm}` -- the GAP-BUDGET PRUNING.  Any multiset of atoms in the alphabet with",
            "    the benchmark's normalisation and at least its value `B` (attained, see",
            f"    `{nm}_bench`) obeys the budget sum gamma <= theta <= {cert.theta_hi}, hence",
            "    the caps / exclusions / knapsack below.  Conditional pruning only; it does not",
            "    identify the optimum.  conjecture1_proved = False. -/",
            f"theorem {nm} {_binders(P)}(m : Multiset ℕ)"]
    head += [f"    {h}" for h in hyps]
    head[-1] += " :"
    head.append(f"    {statement} := by")
    body = []
    if cert.concave:
        c, x0, _y = cert.concave
        body.append(f"  have hbud0 := gapBudget_of_concave m {nm}_w {nm}_ell {nm}_y {nm}_gap "
                    f"({lean_poly(cert.tau)})\n    ({_q_lean(cert.M)}) _ ({_q_lean(c)}) "
                    f"({_q_lean(x0)}) (fun _ => rfl) (by norm_num) (by norm_num) hdom hl hB")
    else:
        body.append(f"  have hbud0 := gapBudget_of_sep m {nm}_w {nm}_ell {nm}_gap "
                    f"({lean_poly(cert.tau)})\n    ({lean_poly(cert.M, P)}) _ (fun _ => rfl) "
                    "hl hB")
    body.append(f"  have hbud : (m.map {nm}_gap).sum ≤ {_lit(cert.theta_hi)} := by")
    if th_name is not None:
        body.append(f"    obtain ⟨ht0, ht1⟩ := {th_name}")
    if cert.concave and cert.concave[1] == 1:
        body.append("    have hl1 : Real.log (1 : ℝ) = 0 := Real.log_one")
    body.append("    linarith")
    lemmas = ", ".join(f"{nm}_gap_{a.k}" for a in cert.atoms)
    body.append(f"  have hγ : ∀ k ∈ m, 0 ≤ {nm}_gap k := by")
    body.append("    intro k hk")
    if t is None:
        body.append("    obtain ⟨h1, h2⟩ := hA k hk")
        body.append("    interval_cases k")
        body.append(f"    all_goals linarith [{lemmas}]")
    else:
        body.append("    have h1 := hA k hk")
        body.append(f"    by_cases hK : {t.K0} ≤ k")
        body.append(f"    · linarith [{nm}_tail k hK]")
        body.append("    · interval_cases k")
        body.append(f"      all_goals linarith [{lemmas}]")
    body.append(f"  have hc := gapBudget_count_mul_le m {nm}_gap _ hγ hbud")
    names = []
    for i, (s, pf) in enumerate(concl):
        if pf is None:
            continue
        cn = _concl_name(s, i)
        names.append(cn)
        if len(pf) == 1:
            body.append(f"  have {cn} : {s} :=\n    {pf[0]}")
        else:
            body.append(f"  have {cn} : {s} := {pf[0]}")
            body.extend(pf[1:])
    if ks is not None:
        body.extend(kn_lines)
        names.append("ckn")
    body.append("  exact " + (names[0] if len(names) == 1 else "⟨" + ", ".join(names) + "⟩"))
    return "\n".join(head + body) + "\n"


def _concl_name(stmt: str, i: int) -> str:
    m = re.match(r"m\.count (\d+)", stmt)
    return f"c{m.group(1)}" if m else f"ctail{i}"


@dataclass
class GapBudgetMultiplicityEmitter(Emitter):
    """Emit the gap-budget pruning of a multiset optimisation: the generic Lean core once per
    file, then per instance the model ``def``s, the enclosure theorems (shared subtrees ONCE
    across the family), one gap lemma per listed atom, the tail lemma, the benchmark lemma
    and the main pruning theorem.  No proof hole; `decide` only on the natural-number
    knapsack box.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "gap_budget_multiplicity"

    def emit_units(self, fam, profile: LeanProfile) -> list:
        """ONE unit: the core lemmas and the shared enclosures are consumed by name."""
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple:
        used: set = set()
        for nm in ("gapBudget_log_tangent", "gapBudget_of_sep", "gapBudget_of_concave",
                   "gapBudget_count_mul_le", "gapBudget_nat_cap", "gapBudget_knapsack"):
            _claim(used, nm)
        chunks = [_CORE]
        n_thm = CORE_THEOREMS
        insts = list(fam.instances)
        book = _EncBook(insts[0].lean_name if insts else "gb", used)
        for inst in insts:
            book.prefix = inst.lean_name
            ch, n = _emit_instance(inst.payload, inst.lean_name, book, used)
            chunks.extend(ch)
            n_thm += n
        return "\n".join(chunks), n_thm


def gap_budget_multiplicity_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a gap-budget family (kind ``gap_budget_multiplicity``); ``spec: pt -> dict`` of
    :func:`gap_budget_multiplicity_certificate` keyword arguments."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("gap_budget_multiplicity", spec),
        constants=dict(constants or {}),
    )

"""enclosure_tree emitter -- kernel-checked RATIONAL TWO-SIDED ENCLOSURES of an expression
TREE over transcendental and algebraic atoms.

conjecture1_proved = False.  Nothing in this module bears on the Riemann Hypothesis: it
certifies finite rational arithmetic facts about named real constants (and, in the
`log_sqrt` face, one elementary real inequality).  Downstream consumers state their own
scope.

WHY THIS EMITTER EXISTS (SHAPES_AUDIT_48H_2026-09-22.md section 2, rank 1)
-------------------------------------------------------------------------
The 48-hour shapes audit merged three independent new-shape candidates and three fold-ins
into ONE kind:

    A N2  `RadicalExpressionEnclosure`  -- nested and quotient square roots
    A N3  `LogTaylorBracket`            -- `log r` from Mathlib's Taylor estimate + fold
    A N4  `AtomPolynomialEnclosure`     -- the polynomial CONSUMER those two feed
    B C2  `sqrt_of_bracketed`           -- `sqrt` of a bracketed (non-rational) radicand
    C 4.7 `log y <= c y^alpha`          -- the `log_sqrt` face (alpha = 1/2)
    D 4   `pi` and `arctan` faces        -- `Real.pi_gt_dN` rate corollaries, `|arctan t| <= |t|`

All but C 4.7 are the SAME object: a rational two-sided enclosure `lo <= E <= hi` (or `<`)
of an expression tree `E` over `{+, -, *, /, ^, sqrt, log, exp, pi, arctan, rational
constants}`, computed by an EXACT interval fold and emitted as Lean theorems that consume
each other by name.  About thirty hand-written sites across the four cluster audits have
this shape.

THE MATHEMATICS (no analysis of our own; one Mathlib fact per atom)
------------------------------------------------------------------
* `pi`     -- `Real.pi_gt_three`/`pi_lt_four` and `Real.pi_gt_dN`/`pi_lt_dN`, N in 2, 4, 6,
              20 (both inequalities STRICT, so a strict claim at the rung is free).
* `log`    -- three routes: the Mathlib atom `Real.log_two_{gt,lt}_d9` (strict); the Taylor
              estimate `Real.abs_log_sub_add_sum_range_le` at `x = 1 - r`, `|1 - r| < 1`; and
              the multiplicative FOLD `log (prod f_i^c_i) = sum c_i log f_i` (`Real.log_mul`,
              rewritten BACKWARDS) that reaches any positive rational from those atoms.
* `exp`    -- `Real.exp_bound`'s exact order-`n` Taylor box (the `emit_exp_enclosure` route).
* `sqrt`   -- `Real.sq_sqrt` + `Real.sqrt_nonneg`, then `nlinarith` against the two rational
              squares `lo^2 <= radicand`, `radicand <= hi^2` (verbatim `LeakageDictionary`).
* `arctan` -- `|arctan t| <= |t|` (the `abs` route, from `Real.le_tan`), and on `[0, 1]` the
              `half` route `t/2 <= arctan t <= t` (`monotoneOn_of_deriv_nonneg`); both lemmas
              are proved inline, copied from `LiFacePrelude` / `E6Bridge28`.
* `+ - * /` and `^` -- the exact interval fold.  A LINEAR node (`+`, `-`, negation, product
              with a constant factor, quotient by a constant) emits no theorem of its own: its
              parent's `linarith` sees through it to the nearest theorem-emitting descendants.
              A product of two non-constant factors emits the four McCORMICK corner facts
              `0 <= (A - alo)(B - blo)`, ... so the closing step is `linarith` (a linear
              program); a quotient by a non-constant rewrites with `le_div_iff0`/`div_le_iff0`
              against a denominator certified positive, after which the goal is linear; a
              power uses `pow_le_pow_left0` on a nonnegative base.

The emitted proof term is determined by the certificate: every step is a named rewrite,
`norm_num`, or `linarith` on named hypotheses, except the `sqrt` atom, which mirrors the hand
proof's `nlinarith [h2, hn, <child bounds>]`.  No `decide`, no proof hole.

STRICTNESS, EXACTLY
-------------------
Each side of every stated bracket is strict or not.  A side may be stated STRICT iff the
exact fold gives slack there, or the endpoint is OPEN (inherited from a strict Mathlib fact:
the `pi` rungs and `log 2`; propagated through `+`, `-`, negation and constant scaling; any
other operation is treated as closed, which can only cause a refusal, never an unsound
acceptance).  `strict=None` (the default) states each side as strongly as it can be proved;
`strict=True` demands both sides strict and REFUSES when the slack is not there;
`strict=False` states both sides with `<=`.

WHAT A CERTIFICATE CERTIFIES (read this before citing it)
---------------------------------------------------------
Only the stated rational enclosure of the stated expression, and -- in `rate` mode -- the
finite arithmetic consequence `n <= cap  ==>  (n + 1 : R) <= E`.  These are finite,
kernel-checkable arithmetic facts about real constants.  They say nothing about RH, about
the zeros of zeta, or about any conjecture; they DISCHARGE numeric side conditions that hand
proofs currently close with `nlinarith` plus a Mathlib constant.

ANTI-PHANTOM REFUSALS (the forge face; the audit's list, item by item)
---------------------------------------------------------------------
`enclosure_tree_certificate` REFUSES -- it never widens, never weakens:

* a radicand interval not `>= 0`                    (`sqrt` out of domain)
* a denominator interval containing 0, or strictly negative
* a claimed bracket the exact fold does NOT imply, at ANY node (the forge case)
* an inverted bracket `lo > hi`
* a strict claim without strict slack or an open endpoint
* `log` with argument `r <= 0`, or `r = 1` (log 1 = 0 is not transcendental content)
* `log` with `|1 - r| >= 1` and no factorisation into in-radius atoms (or the atom 2)
* `log` Taylor order `n > 64` (the `Finset.sum_range_succ` cost cliff), or `< 1`
* a fold whose factors do not multiply to the argument, a non-positive or above-8
  multiplicity, a non-positive factor, a single-log "fold", more than 8 factors
* `exp` at `|x| > 1` (outside `Real.exp_bound`) or at `x = 0`
* a base interval not `>= 0` under a power (the sign split is the caller's), an exponent
  outside `2..8`
* a `pi` precision that does not reach the claim, or one outside Mathlib's ladder
* a `rate` cap the certified lower bound does not reach (`cap + 1 > lo`)
* a tree with no transcendental content, a claim or name on a rational-constant subtree,
  a product with the constant factor 0
* non-rational input (a float would smuggle in its binary expansion), bools, malformed
  nodes, non-identifier theorem names, trees above 64 nodes
* (`log_sqrt`) `alpha != 1/2`, a shift `< 0`, a floor `<= 0`, `k < 1`, a floor at which
  `y + a <= k^2 y` fails, a constant `c < 2k`

conjecture1_proved = False.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, replace
from fractions import Fraction
from math import factorial, isqrt
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# --- caps (every one is a refusal boundary, never a silent clamp) -------------

#: `Real.abs_log_sub_add_sum_range_le` orders above this are refused: the emitted
#: `norm_num [Finset.sum_range_succ]` unfolding stops being a cheap check.
MAX_LOG_ORDER = 64
#: `Real.exp_bound` orders above this are refused (same cliff as `emit_exp_enclosure`).
MAX_EXP_ORDER = 64
#: Default Taylor order of a `log` atom whose order the caller does not pin (the
#: `LeakageDictionary.log_three_halves_bounds` order).
DEFAULT_LOG_ORDER = 24
#: Default `Real.exp_bound` order of an `exp` atom whose order is not pinned.
DEFAULT_EXP_ORDER = 14
#: The global Taylor-order levels searched (after the defaults) when the root claim or the
#: rate cap needs tighter unpinned, unclaimed Taylor atoms.
ORDER_LEVELS = (None, 32, 48, 64)
#: Default decimal precision of a derived `sqrt` bracket (the leakage dictionary's 1e-12).
DEFAULT_SQRT_DIGITS = 12
MAX_SQRT_DIGITS = 40
#: Repeated-`Real.log_mul` folds: at most this multiplicity per factor, this many factors.
MAX_FOLD_COEFF = 8
MAX_FOLD_FACTORS = 8
#: Powers above this exponent are refused (the literal cost cliff).
MAX_POW = 8
#: Trees above this many nodes are refused (the emitted file grows with the tree).
MAX_NODES = 64
#: Rate caps above this are refused (the corollary is about ladder rungs, not bignums).
MAX_RATE_CAP = 10 ** 12

ATOMS = ("pi", "log", "exp")
OPS = ("rat", "pi", "sqrt", "log", "exp", "arctan",
       "add", "sub", "mul", "div", "neg", "pow")
_ARITY = {"rat": 0, "pi": 0, "log": 0, "exp": 0, "sqrt": 1, "arctan": 1, "neg": 1,
          "pow": 1, "add": 2, "sub": 2, "mul": 2, "div": 2}

#: Mathlib's `pi` ladder, exactly (`Mathlib/Analysis/Real/Pi/Bounds.lean`, identical at the
#: v4.32.0 and v4.34 pins).  Every inequality is STRICT.
#:   d0  : 3 < pi < 4                               (`pi_gt_three`, `pi_lt_four`)
#:   d2  : 3.14 < pi < 3.15
#:   d4  : 3.1415 < pi < 3.1416
#:   d6  : 3.141592 < pi < 3.141593
#:   d20 : 3.14159265358979323846 < pi < 3.14159265358979323847
PI_LADDER: dict[int, tuple[sp.Rational, sp.Rational, str, str]] = {
    0: (sp.Integer(3), sp.Integer(4), "Real.pi_gt_three", "Real.pi_lt_four"),
    2: (sp.Rational(314, 100), sp.Rational(315, 100), "Real.pi_gt_d2", "Real.pi_lt_d2"),
    4: (sp.Rational(31415, 10 ** 4), sp.Rational(31416, 10 ** 4),
        "Real.pi_gt_d4", "Real.pi_lt_d4"),
    6: (sp.Rational(3141592, 10 ** 6), sp.Rational(3141593, 10 ** 6),
        "Real.pi_gt_d6", "Real.pi_lt_d6"),
    20: (sp.Rational(314159265358979323846, 10 ** 20),
         sp.Rational(314159265358979323847, 10 ** 20),
         "Real.pi_gt_d20", "Real.pi_lt_d20"),
}
PI_DIGITS = (0, 2, 4, 6, 20)

#: Mathlib's `Real.log_two_{gt,lt}_d9`, exactly (both STRICT).
LOG_TWO_LO = sp.Rational(6931471803, 10 ** 10)
LOG_TWO_HI = sp.Rational(6931471808, 10 ** 10)

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
#: names the emitted proofs bind (a `log_sqrt` variable must not shadow them)
_RESERVED = frozenset({
    "by", "fun", "have", "show", "from", "at", "in", "let", "do", "then", "else", "if",
    "match", "with", "theorem", "lemma", "def", "example", "calc", "rfl", "Real", "exp",
    "log", "sqrt", "h", "this", "hy", "hy0", "hs", "h1", "h2", "h3", "h4", "n", "hn",
})


class EnclosureTreeRefusal(ValueError):
    """A refusal, not a soundness event: the claim was not shipped."""


def _refuse(msg: str) -> EnclosureTreeRefusal:
    return EnclosureTreeRefusal(f"enclosure_tree REFUSED: {msg}")


def _rat(v, what: str) -> sp.Rational:
    """Exactly-rational coercion; REFUSES floats, sympy Floats, bools and non-rationals."""
    if isinstance(v, bool):
        raise _refuse(f"{what} was given as a bool ({v!r})")
    if isinstance(v, (float, sp.Float)):
        raise _refuse(
            f"{what} was given as a float ({v!r}); a float carries its binary expansion, "
            "not the rational you wrote -- pass a str/int/Fraction/sp.Rational")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    try:
        q = sp.Rational(v)
    except (TypeError, ValueError) as exc:
        raise _refuse(f"{what} = {v!r} is not rational ({exc})") from None
    if not isinstance(q, sp.Rational):
        raise _refuse(f"{what} = {v!r} is not rational")
    return q


def _opt_rat(v, what: str):
    return None if v is None else _rat(v, what)


def _int(v, what: str) -> int:
    if isinstance(v, bool) or not isinstance(v, int):
        raise _refuse(f"{what} = {v!r} is not an int")
    return v


def _F(q: sp.Rational) -> Fraction:
    return Fraction(int(q.p), int(q.q))


def _S(f: Fraction) -> sp.Rational:
    return sp.Rational(f.numerator, f.denominator)


def _check_strict_flag(strict, what: str):
    if strict is not None and not isinstance(strict, bool):
        raise _refuse(f"{what}: strict must be None, True or False, got {strict!r}")
    return strict


def _check_name(name, what: str):
    if name is None:
        return None
    if not isinstance(name, str) or not _IDENT.match(name):
        raise _refuse(f"{what}: theorem name {name!r} is not an ASCII Lean identifier")
    return name


# --- the (unresolved) tree the caller writes -----------------------------------

@dataclass(frozen=True)
class Node:
    """One node of an enclosure tree, as the CALLER writes it (use the ``node_*``
    constructors).  Everything optional is filled in -- and exactly re-checked -- by
    :func:`enclosure_tree_certificate`.  A node may carry its OWN claimed bracket
    (``claim_lo``/``claim_hi``); the certifier refuses any claim the exact fold does not
    imply, and parents then consume the CLAIM (what the emitted theorem states), never a
    tighter private value."""

    op: str
    children: tuple = ()
    const: sp.Rational | None = None            # rat value / log argument / exp point
    name: str | None = None                     # Lean theorem name override
    claim_lo: sp.Rational | None = None
    claim_hi: sp.Rational | None = None
    strict: bool | None = None                  # None = as strong as provable
    order: int | None = None                    # log / exp Taylor order (pinned)
    digits: int | None = None                   # pi rung (pinned)
    exponent: int | None = None                 # pow
    sqrt_digits: int | None = None              # derived sqrt-bracket precision
    factors: tuple | None = None                # log fold: ((multiplicity, log Node), ...)


def _claims(lo, hi, what):
    return _opt_rat(lo, f"{what} lo"), _opt_rat(hi, f"{what} hi")


def node_rat(q) -> Node:
    """A rational constant leaf (emits no theorem: it IS its own bracket)."""
    return Node(op="rat", const=_rat(q, "rational constant"))


def node_pi(*, digits: int | None = None, name: str | None = None, lo=None, hi=None,
            strict: bool | None = None) -> Node:
    """`Real.pi`, bracketed by a rung of Mathlib's ladder.  ``digits=None`` searches the
    ladder (0, 2, 4, 6, 20) for the LEAST rung that carries the instance's claims; the rung
    used is part of the certificate."""
    clo, chi = _claims(lo, hi, "pi")
    return Node(op="pi", digits=digits, name=name, strict=strict, claim_lo=clo, claim_hi=chi)


def node_sqrt(child: Node, *, lo=None, hi=None, name: str | None = None,
              strict: bool | None = None, digits: int | None = None) -> Node:
    """`Real.sqrt child`.  A claimed side is checked EXACTLY against the radicand interval
    by rational squares; an unclaimed side is derived by exact integer square roots on a
    `10^-digits` grid, rounded outward."""
    clo, chi = _claims(lo, hi, "sqrt")
    return Node(op="sqrt", children=(child,), name=name, strict=strict, sqrt_digits=digits,
                claim_lo=clo, claim_hi=chi)


def node_log(q, *, order: int | None = None, factors=None, lo=None, hi=None,
             name: str | None = None, strict: bool | None = None) -> Node:
    """`Real.log q` for a POSITIVE RATIONAL `q`, by one of three routes:

    * ``q = 2`` and no ``factors`` -- the Mathlib atom `Real.log_two_{gt,lt}_d9`;
    * ``factors`` given           -- the fold `log (prod f^c) = sum c log f`; each entry is
      ``(c, f)`` with ``f`` a positive rational (a fresh log atom at ``order``) or an
      existing ``node_log`` Node (so a named atom is consumed, not re-proved);
    * otherwise, ``|1 - q| < 1``  -- the Taylor estimate at ``order``."""
    fac = None
    if factors is not None:
        entries = []
        for entry in factors:
            if not isinstance(entry, (tuple, list)) or len(entry) != 2:
                raise _refuse(f"log fold entry {entry!r} is not a (multiplicity, factor) pair")
            c, f = entry
            if isinstance(f, Node):
                fnode = f
            else:
                fnode = node_log(_rat(f, "log fold factor"), order=order)
            entries.append((c, fnode))
        fac = tuple(entries)
    clo, chi = _claims(lo, hi, "log")
    return Node(op="log", const=_rat(q, "log argument"), order=order, factors=fac,
                name=name, strict=strict, claim_lo=clo, claim_hi=chi)


def node_exp(x, *, order: int | None = None, lo=None, hi=None, name: str | None = None,
             strict: bool | None = None) -> Node:
    """`Real.exp x` at a rational `x` with `0 < |x| <= 1` (`Real.exp_bound`)."""
    clo, chi = _claims(lo, hi, "exp")
    return Node(op="exp", const=_rat(x, "exp point"), order=order, name=name, strict=strict,
                claim_lo=clo, claim_hi=chi)


def node_arctan(child: Node, *, lo=None, hi=None, name: str | None = None,
                strict: bool | None = None) -> Node:
    """`Real.arctan child`: `|arctan t| <= |t|` on the child's box, or, when the child's box
    lies in `[0, 1]`, `t/2 <= arctan t <= t`."""
    clo, chi = _claims(lo, hi, "arctan")
    return Node(op="arctan", children=(child,), name=name, strict=strict,
                claim_lo=clo, claim_hi=chi)


def _composite(op: str, children, name, lo, hi, strict, exponent=None) -> Node:
    clo, chi = _claims(lo, hi, op)
    return Node(op=op, children=tuple(children), name=name, strict=strict, claim_lo=clo,
                claim_hi=chi, exponent=exponent)


def node_add(a: Node, b: Node, *, name=None, lo=None, hi=None, strict=None) -> Node:
    return _composite("add", (a, b), name, lo, hi, strict)


def node_sub(a: Node, b: Node, *, name=None, lo=None, hi=None, strict=None) -> Node:
    return _composite("sub", (a, b), name, lo, hi, strict)


def node_mul(a: Node, b: Node, *, name=None, lo=None, hi=None, strict=None) -> Node:
    return _composite("mul", (a, b), name, lo, hi, strict)


def node_div(a: Node, b: Node, *, name=None, lo=None, hi=None, strict=None) -> Node:
    return _composite("div", (a, b), name, lo, hi, strict)


def node_neg(a: Node, *, name=None, lo=None, hi=None, strict=None) -> Node:
    return _composite("neg", (a,), name, lo, hi, strict)


def node_pow(a: Node, k: int, *, name=None, lo=None, hi=None, strict=None) -> Node:
    return _composite("pow", (a,), name, lo, hi, strict, exponent=k)


# --- the resolved tree (what the certificate carries) --------------------------

@dataclass(frozen=True)
class ResolvedNode:
    """A node with its EXACT rational interval fold and every parameter pinned.

    ``box_lo``/``box_hi`` are what the fold computes from the children's STATED brackets
    (``box_*_open``: the endpoint is not attained, so a strict statement there is free);
    ``lo``/``hi`` are what the emitted theorem STATES, with ``lo_strict``/``hi_strict``
    choosing `<` over `<=` per side.  ``emits`` is False for a rational-constant subtree
    and for a LINEAR node its parent sees through (no claim, no name, not the root)."""

    op: str
    children: tuple
    lo: sp.Rational
    hi: sp.Rational
    lo_strict: bool
    hi_strict: bool
    box_lo: sp.Rational
    box_hi: sp.Rational
    box_lo_open: bool
    box_hi_open: bool
    emits: bool
    is_const: bool
    const: sp.Rational | None = None
    name: str | None = None
    order: int | None = None
    digits: int | None = None
    exponent: int | None = None
    coeffs: tuple | None = None                 # log fold multiplicities, per child
    route: str | None = None                    # log: mathlib2 / taylor / fold; arctan: abs / half
    claimed: bool = False

    @property
    def key(self) -> tuple:
        """Structural identity, for sharing ONE theorem across repeated subtrees (and
        across the instances of one family).  The explicit name is part of it."""
        return (self.op, self.const, self.order, self.digits, self.exponent, self.coeffs,
                self.route, self.lo, self.hi, self.lo_strict, self.hi_strict, self.name,
                self.emits, tuple(c.key for c in self.children))


@dataclass(frozen=True)
class EnclosureTreeCert:
    """One enclosure-tree certificate.

    ``root`` is the resolved tree; ``order`` lists every theorem-emitting node, de-duplicated,
    children before parents.  ``rate_cap`` (when set) adds the `pi`-face rate corollary
    `n <= cap -> (n + 1 : R) <= E`, accepted only when `cap + 1 <= root.lo` EXACTLY.
    ``pi_digits`` / ``order_level`` record the ladder rung and the Taylor level the search
    settled on (``None`` when nothing was free)."""

    root: ResolvedNode
    order: tuple
    rate_cap: int | None = None
    pi_digits: int | None = None
    order_level: int | None = None

    @property
    def lo(self) -> sp.Rational:
        return self.root.lo

    @property
    def hi(self) -> sp.Rational:
        return self.root.hi

    @property
    def slack(self) -> tuple:
        """`(box_lo - lo, hi - box_hi)` at the root; both are >= 0."""
        return self.root.box_lo - self.root.lo, self.root.hi - self.root.box_hi

    @property
    def n_theorems(self) -> int:
        return len(self.order) + (1 if self.rate_cap is not None else 0)


@dataclass(frozen=True)
class LogSqrtCert:
    """The C 4.7 face: `forall y >= y0, log (y + a) <= c * sqrt y`, from `log t <= t - 1` at
    `t = sqrt (y + a)` and `y + a <= k^2 y` on `y >= y0` (`E6Bridge23.lean` `log_add_four_le`;
    `a = 0` is the `E6Bridge16.lean` `log n <= 2 sqrt n` step)."""

    shift: sp.Rational
    floor: sp.Rational
    k: sp.Rational
    c: sp.Rational
    var: str = "y"


# --- exact interval arithmetic --------------------------------------------------

def sqrt_bracket(lo: sp.Rational, hi: sp.Rational, digits: int) -> tuple:
    """An OUTWARD-rounded rational bracket `(s, t)` of `sqrt([lo, hi])` on a `10^-digits`
    grid, by exact integer square roots: `s^2 <= lo` and `hi <= t^2` EXACTLY."""
    if lo < 0:
        raise _refuse(f"sqrt bracket needs a nonnegative radicand, got lo = {lo}")
    scale = 10 ** digits
    a = _F(lo) * scale * scale
    s = isqrt(a.numerator // a.denominator)
    b = _F(hi) * scale * scale
    bc = -((-b.numerator) // b.denominator)          # ceil
    t = isqrt(bc)
    if t * t < bc:
        t += 1
    return sp.Rational(s, scale), sp.Rational(t, scale)


def log_taylor_parts(q: sp.Rational, n: int) -> tuple:
    """`(S, r)` of Mathlib's `abs_log_sub_add_sum_range_le (h : |x| < 1) (n)` at `x = 1 - q`:
    `|S + log q| <= r` with `S = sum_(i<n) x^(i+1)/(i+1)`, `r = |x|^(n+1)/(1 - |x|)`."""
    x = _F(sp.Integer(1) - q)
    if abs(x) >= 1:
        raise _refuse(f"log Taylor route needs |1 - r| < 1, got r = {q}")
    S = sum((x ** (i + 1) / (i + 1) for i in range(n)), Fraction(0))
    r = abs(x) ** (n + 1) / (1 - abs(x))
    return _S(S), _S(r)


def log_taylor_box(q: sp.Rational, n: int) -> tuple:
    """The EXACT order-`n` box of `Real.log q`: `[-S - r, -S + r]`."""
    S, r = log_taylor_parts(q, n)
    return -S - r, -S + r


def exp_taylor_box(x: sp.Rational, n: int) -> tuple:
    """The EXACT order-`n` `Real.exp_bound` box at `x` (the `emit_exp_enclosure.taylor_box`
    arithmetic, re-derived so the two modules can drift only by failing each other's tests)."""
    xf = _F(x)
    S = sum((xf ** m / factorial(m) for m in range(n)), Fraction(0))
    r = abs(xf) ** n * Fraction(n + 1, factorial(n) * n)
    return _S(S - r), _S(S + r)


# --- resolution (the exact self-check) -------------------------------------------

class _Ctx:
    def __init__(self, pi_digits: int, level):
        self.pi_digits = pi_digits
        self.level = level
        self.count = 0


def _box_checks(box_lo, box_hi, lo_open, hi_open):
    def check_lo(q):
        return q <= box_lo, (q < box_lo or (q == box_lo and lo_open))

    def check_hi(q):
        return box_hi <= q, (box_hi < q or (q == box_hi and hi_open))
    return check_lo, check_hi


def _settle(node: Node, what: str, box_lo, box_hi, lo_open: bool, hi_open: bool,
            check_lo=None, check_hi=None):
    """Decide the stated bracket and its per-side strictness EXACTLY, or refuse.

    Returns ``(lo, hi, lo_strict, hi_strict, claimed)``.  ``check_lo(q)`` /
    ``check_hi(q)`` return ``(valid_nonstrict, valid_strict)`` for a candidate endpoint;
    the default compares against the box and its openness."""
    dlo, dhi = _box_checks(box_lo, box_hi, lo_open, hi_open)
    check_lo = check_lo or dlo
    check_hi = check_hi or dhi
    claimed = (node.claim_lo is not None or node.claim_hi is not None
               or node.strict is not None)
    lo = box_lo if node.claim_lo is None else node.claim_lo
    hi = box_hi if node.claim_hi is None else node.claim_hi
    if lo > hi:
        raise _refuse(f"{what}: inverted bracket lo = {lo} > hi = {hi}")
    lo_ns, lo_st = check_lo(lo)
    hi_ns, hi_st = check_hi(hi)
    if node.strict is True:
        if not (lo_st and hi_st):
            raise _refuse(
                f"{what}: a STRICT claim [{lo}, {hi}] needs strict slack (or an open "
                f"endpoint) around the exact fold [{box_lo}, {box_hi}] (box_lo - lo = "
                f"{box_lo - lo}, hi - box_hi = {hi - box_hi}; open = ({lo_open}, "
                f"{hi_open})).  Widen the claim or drop `strict`")
        return lo, hi, True, True, claimed
    if not (lo_ns and hi_ns):
        raise _refuse(
            f"{what}: the claimed bracket [{lo}, {hi}] is NOT implied by the exact interval "
            f"fold [{box_lo}, {box_hi}] (box_lo - lo = {box_lo - lo}, hi - box_hi = "
            f"{hi - box_hi}; both must be >= 0).  Widen the claim; the emitter does not "
            "widen it for you")
    if node.strict is False:
        return lo, hi, False, False, claimed
    return lo, hi, lo_st, hi_st, claimed


def _is_const_op(op: str, children) -> bool:
    if op == "rat":
        return True
    if op in ATOMS or op in ("sqrt", "arctan"):
        return False
    return all(c.is_const for c in children)


def _decide_emits(op, children, name, claimed, is_root, is_const) -> bool:
    if is_const:
        return False
    if is_root or name or claimed:
        return True
    if op in ATOMS or op in ("sqrt", "arctan", "pow"):
        return True
    if op == "mul":
        return not (children[0].is_const or children[1].is_const)
    if op == "div":
        return not children[1].is_const
    return False            # add / sub / neg / scaling: the parent's linarith sees through


def _scale(k: sp.Rational, c: ResolvedNode):
    """The box of `k * c` for a rational constant `k`, with openness (a nonzero scaling
    preserves openness, swapping the sides when `k < 0`)."""
    if k > 0:
        return k * c.lo, k * c.hi, c.lo_strict, c.hi_strict
    return k * c.hi, k * c.lo, c.hi_strict, c.lo_strict


def _resolve(node, ctx: _Ctx, is_root: bool = False) -> ResolvedNode:
    """Resolve one node bottom-up, exactly.  Raises on every refusal."""
    if not isinstance(node, Node):
        raise _refuse(f"expected a Node, got {type(node).__name__}")
    ctx.count += 1
    if ctx.count > MAX_NODES:
        raise _refuse(f"the tree exceeds {MAX_NODES} nodes")
    op = node.op
    if op not in OPS:
        raise _refuse(f"unknown node op {op!r} (expected one of {OPS})")
    what = f"node `{node.name or op}`"
    _check_name(node.name, what)
    _check_strict_flag(node.strict, what)
    if not isinstance(node.children, tuple) or len(node.children) != _ARITY[op]:
        raise _refuse(f"{what}: `{op}` takes {_ARITY[op]} child(ren), got "
                      f"{len(node.children) if isinstance(node.children, tuple) else '?'}")
    # a directly-constructed Node may carry ints / Fractions / floats: normalize EXACTLY
    node = replace(node, claim_lo=_opt_rat(node.claim_lo, f"{what} lo"),
                   claim_hi=_opt_rat(node.claim_hi, f"{what} hi"))

    if op == "rat":
        q = _rat(node.const, "rational constant")
        if node.name or node.claim_lo is not None or node.claim_hi is not None \
                or node.strict is not None:
            raise _refuse(f"{what}: a rational constant carries no content; it takes no "
                          "name or claim")
        return ResolvedNode(op="rat", children=(), lo=q, hi=q, lo_strict=False,
                            hi_strict=False, box_lo=q, box_hi=q, box_lo_open=False,
                            box_hi_open=False, emits=False, is_const=True, const=q)

    if op == "pi":
        digits = node.digits if node.digits is not None else ctx.pi_digits
        if isinstance(digits, bool) or digits not in PI_LADDER:
            raise _refuse(f"{what}: pi precision d{digits} is not on Mathlib's ladder "
                          f"{sorted(PI_LADDER)}")
        blo, bhi = PI_LADDER[digits][:2]
        lo, hi, ls, hs, claimed = _settle(node, what, blo, bhi, True, True)
        return ResolvedNode(op="pi", children=(), lo=lo, hi=hi, lo_strict=ls, hi_strict=hs,
                            box_lo=blo, box_hi=bhi, box_lo_open=True, box_hi_open=True,
                            emits=True, is_const=False, name=node.name, digits=digits,
                            claimed=claimed)

    if op == "log":
        return _resolve_log(node, ctx, what, is_root)

    if op == "exp":
        x = _rat(node.const, "exp point")
        if x == 0:
            raise _refuse(f"{what}: exp 0 = 1 exactly; there is no transcendental content")
        if abs(x) > 1:
            raise _refuse(
                f"{what}: |x| = {abs(x)} > 1 is outside Real.exp_bound's hypothesis (the "
                "halving identity exp x = (exp (x/2))^2 would extend the range; it is a "
                "deliberate follow-on, not applied silently)")
        orders = _order_candidates(node, ctx, DEFAULT_EXP_ORDER, MAX_EXP_ORDER, what, "exp")
        k, (lo, hi, ls, hs, claimed), box = _least_fitting(
            orders, lambda n: exp_taylor_box(x, n), node, what, False, False)
        return ResolvedNode(op="exp", children=(), lo=lo, hi=hi, lo_strict=ls, hi_strict=hs,
                            box_lo=box[0], box_hi=box[1], box_lo_open=False,
                            box_hi_open=False, emits=True, is_const=False, const=x,
                            name=node.name, order=k, claimed=claimed)

    children = tuple(_resolve(c, ctx) for c in node.children)
    is_const = _is_const_op(op, children)
    if is_const and (node.name or node.claim_lo is not None or node.claim_hi is not None
                     or node.strict is not None):
        raise _refuse(f"{what}: a rational-constant subtree carries no transcendental "
                      "content; it takes no name or claim (norm_num evaluates it inline)")

    route = None
    check_lo = check_hi = None
    exponent = None
    grid = None
    if op == "sqrt":
        c = children[0]
        if c.lo < 0:
            raise _refuse(
                f"{what}: the radicand interval [{c.lo}, {c.hi}] is not >= 0, so "
                "Real.sq_sqrt does not apply (sqrt of a negative argument is 0 in Mathlib -- "
                "an enclosure of it would be a phantom)")
        digits = DEFAULT_SQRT_DIGITS if node.sqrt_digits is None else node.sqrt_digits
        digits = _int(digits, f"{what} sqrt digits")
        if digits < 1 or digits > MAX_SQRT_DIGITS:
            raise _refuse(f"{what}: sqrt bracket precision {digits} outside 1..{MAX_SQRT_DIGITS}")
        blo, bhi = sqrt_bracket(c.lo, c.hi, digits)
        lo_open = hi_open = False

        def check_lo(q, c=c):
            if q < 0:
                return True, True                    # q < 0 <= sqrt
            sq = q * q
            return sq <= c.lo, (sq < c.lo or (sq == c.lo and c.lo_strict))

        def check_hi(q, c=c):
            if q < 0:
                return False, False                  # sqrt >= 0 > q
            sq = q * q
            return c.hi <= sq, (c.hi < sq or (c.hi == sq and c.hi_strict))
        grid = digits
    elif op == "arctan":
        c = children[0]
        m = max(abs(c.lo), abs(c.hi))
        abs_box = (-m, m)
        half_ok = c.lo >= 0 and c.hi <= 1
        if half_ok:
            half_box = (c.lo / 2, c.hi)
            route = "half"
            if node.claim_lo is not None or node.claim_hi is not None:
                try:
                    _settle(node, what, abs_box[0], abs_box[1], False, False)
                    route = "abs"           # the cheaper proof already carries the claim
                except EnclosureTreeRefusal:
                    route = "half"
        else:
            route = "abs"
        blo, bhi = half_box if route == "half" else abs_box
        lo_open = hi_open = False
    elif op == "neg":
        c = children[0]
        blo, bhi, lo_open, hi_open = -c.hi, -c.lo, c.hi_strict, c.lo_strict
    elif op == "add":
        a, b = children
        blo, bhi = a.lo + b.lo, a.hi + b.hi
        lo_open, hi_open = a.lo_strict or b.lo_strict, a.hi_strict or b.hi_strict
    elif op == "sub":
        a, b = children
        blo, bhi = a.lo - b.hi, a.hi - b.lo
        lo_open, hi_open = a.lo_strict or b.hi_strict, a.hi_strict or b.lo_strict
    elif op == "mul":
        a, b = children
        if a.is_const and b.is_const:
            blo = bhi = a.lo * b.lo
            lo_open = hi_open = False
        elif a.is_const or b.is_const:
            k, c = (a.lo, b) if a.is_const else (b.lo, a)
            if k == 0:
                raise _refuse(f"{what}: the constant factor 0 annihilates the "
                              "transcendental content")
            blo, bhi, lo_open, hi_open = _scale(k, c)
        else:
            corners = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
            blo, bhi = min(corners), max(corners)
            lo_open = hi_open = False
    elif op == "div":
        a, b = children
        if b.lo <= 0 <= b.hi:
            raise _refuse(
                f"{what}: the denominator interval [{b.lo}, {b.hi}] contains 0, so the "
                "quotient is unbounded -- no rational enclosure exists")
        if b.hi < 0:
            raise _refuse(
                f"{what}: the denominator interval [{b.lo}, {b.hi}] is strictly NEGATIVE; the "
                "emitted `le_div_iff0` route needs `0 < den`.  Write the node as "
                "div(neg(num), neg(den)) instead")
        if a.is_const and b.is_const:
            blo = bhi = a.lo / b.lo
            lo_open = hi_open = False
        elif b.is_const:
            blo, bhi, lo_open, hi_open = _scale(1 / b.lo, a)
        else:
            corners = [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi]
            blo, bhi = min(corners), max(corners)
            lo_open = hi_open = False
    elif op == "pow":
        c = children[0]
        k = node.exponent
        if isinstance(k, bool) or not isinstance(k, int) or k < 2:
            raise _refuse(f"{what}: power exponent {k!r} must be an int >= 2")
        if k > MAX_POW:
            raise _refuse(f"{what}: power exponent {k} exceeds the cap {MAX_POW}")
        if c.lo < 0:
            raise _refuse(
                f"{what}: the base interval [{c.lo}, {c.hi}] is not >= 0 under the power "
                f"{k}; the monotone `pow_le_pow_left0` route needs `0 <= base`.  Split the "
                "sign case explicitly (or write the product with mul)")
        blo, bhi = c.lo ** k, c.hi ** k
        lo_open = hi_open = False
        exponent = k
    else:  # pragma: no cover -- guarded by the OPS check
        raise _refuse(f"unhandled op {op!r}")

    if is_const:
        lo, hi, ls, hs, claimed = blo, bhi, False, False, False
    else:
        lo, hi, ls, hs, claimed = _settle(node, what, blo, bhi, lo_open, hi_open,
                                          check_lo, check_hi)
    emits = _decide_emits(op, children, node.name, claimed, is_root, is_const)
    return ResolvedNode(op=op, children=children, lo=lo, hi=hi, lo_strict=ls, hi_strict=hs,
                        box_lo=blo, box_hi=bhi, box_lo_open=lo_open, box_hi_open=hi_open,
                        emits=emits, is_const=is_const, name=node.name, exponent=exponent,
                        digits=grid, route=route, claimed=claimed)


def _order_candidates(node: Node, ctx: _Ctx, default: int, cap: int, what: str,
                      kind: str) -> list:
    if node.order is not None:
        order = _int(node.order, f"{what} {kind} order")
        if order < 1:
            raise _refuse(f"{what}: {kind} order {order} < 1")
        if order > cap:
            raise _refuse(f"{what}: {kind} order {order} exceeds the cap {cap} "
                          "(the Finset.sum_range_succ unfolding cost cliff)")
        return [order]
    if node.claim_lo is None and node.claim_hi is None and node.strict is not True:
        return [ctx.level if ctx.level is not None else default]
    return list(range(1, cap + 1))


def _least_fitting(orders, box_of, node: Node, what: str, lo_open: bool, hi_open: bool):
    """The LEAST order whose exact box carries the node's claim (the only order, when the
    caller pinned one).  Never widens the claim."""
    last = None
    for k in orders:
        box = box_of(k)
        try:
            settled = _settle(node, what, box[0], box[1], lo_open, hi_open)
        except EnclosureTreeRefusal as exc:
            last = (k, box, exc)
            continue
        return k, settled, box
    k, box, exc = last
    if len(orders) == 1:
        raise exc
    raise _refuse(
        f"{what}: no Taylor order up to {k} has a box carrying the claimed bracket "
        f"[{node.claim_lo}, {node.claim_hi}] -- at order {k} the box is [{box[0]}, {box[1]}].  "
        "Widen the claim")


def _resolve_log(node: Node, ctx: _Ctx, what: str, is_root: bool) -> ResolvedNode:
    q = _rat(node.const, "log argument")
    if q <= 0:
        raise _refuse(f"{what}: log argument r = {q} <= 0 is outside the domain (Mathlib's "
                      "Real.log is log |r| or 0 there -- an enclosure would be a phantom)")
    if q == 1:
        raise _refuse(f"{what}: log 1 = 0 exactly; there is no transcendental content")
    if node.factors is not None:
        parts = node.factors
        if not isinstance(parts, tuple) or not parts:
            raise _refuse(f"{what}: an empty factorisation certifies nothing")
        if len(parts) > MAX_FOLD_FACTORS:
            raise _refuse(f"{what}: {len(parts)} fold factors exceed the cap {MAX_FOLD_FACTORS}")
        prod = sp.Integer(1)
        total = 0
        coeffs = []
        for c, fnode in parts:
            if isinstance(c, bool) or not isinstance(c, int):
                raise _refuse(f"{what}: fold multiplicity {c!r} is not an int")
            if c <= 0:
                raise _refuse(
                    f"{what}: fold multiplicity {c} is not positive; the emitted repeated "
                    "`Real.log_mul` route handles positive integer multiplicities only")
            if c > MAX_FOLD_COEFF:
                raise _refuse(f"{what}: fold multiplicity {c} exceeds the cap {MAX_FOLD_COEFF} "
                              "(each unit is one more `Real.log_mul` rewrite)")
            if not isinstance(fnode, Node) or fnode.op != "log":
                raise _refuse(f"{what}: a fold factor must be a log node, got {fnode!r}")
            f = _rat(fnode.const, "log fold factor")
            if f <= 0:
                raise _refuse(f"{what}: fold factor {f} <= 0 is outside log's domain")
            prod = prod * f ** c
            total += c
            coeffs.append(c)
        if total < 2:
            raise _refuse(f"{what}: a one-log fold is the atom itself; drop `factors`")
        if sp.Rational(prod) != q:
            raise _refuse(
                f"{what}: the factorisation {[(c, fn.const) for c, fn in parts]} multiplies to "
                f"{sp.Rational(prod)}, not to the log argument {q} -- the fold identity "
                "would be false")
        children = tuple(_resolve(fn, ctx) for _c, fn in parts)
        blo = sum((c * ch.lo for c, ch in zip(coeffs, children)), sp.Integer(0))
        bhi = sum((c * ch.hi for c, ch in zip(coeffs, children)), sp.Integer(0))
        lo_open = any(ch.lo_strict for ch in children)
        hi_open = any(ch.hi_strict for ch in children)
        lo, hi, ls, hs, claimed = _settle(node, what, sp.Rational(blo), sp.Rational(bhi),
                                          lo_open, hi_open)
        return ResolvedNode(op="log", children=children, lo=lo, hi=hi, lo_strict=ls,
                            hi_strict=hs, box_lo=sp.Rational(blo), box_hi=sp.Rational(bhi),
                            box_lo_open=lo_open, box_hi_open=hi_open, emits=True,
                            is_const=False, const=q, name=node.name, coeffs=tuple(coeffs),
                            route="fold", claimed=claimed)
    if q == 2:
        if node.order is not None:
            raise _refuse(f"{what}: log 2 is Mathlib's atom `Real.log_two_gt_d9`; it takes no "
                          "Taylor order (use factors for a different route)")
        lo, hi, ls, hs, claimed = _settle(node, what, LOG_TWO_LO, LOG_TWO_HI, True, True)
        return ResolvedNode(op="log", children=(), lo=lo, hi=hi, lo_strict=ls, hi_strict=hs,
                            box_lo=LOG_TWO_LO, box_hi=LOG_TWO_HI, box_lo_open=True,
                            box_hi_open=True, emits=True, is_const=False, const=q,
                            name=node.name, route="mathlib2", claimed=claimed)
    if abs(sp.Integer(1) - q) >= 1:
        raise _refuse(
            f"{what}: |1 - r| = {abs(sp.Integer(1) - q)} >= 1 for r = {q}, so the Taylor "
            "estimate does not apply; supply `factors` folding r into atoms with "
            "|1 - f| < 1 (or the Mathlib atom 2)")
    orders = _order_candidates(node, ctx, DEFAULT_LOG_ORDER, MAX_LOG_ORDER, what, "log")
    k, (lo, hi, ls, hs, claimed), box = _least_fitting(
        orders, lambda n: log_taylor_box(q, n), node, what, False, False)
    return ResolvedNode(op="log", children=(), lo=lo, hi=hi, lo_strict=ls, hi_strict=hs,
                        box_lo=box[0], box_hi=box[1], box_lo_open=False, box_hi_open=False,
                        emits=True, is_const=False, const=q, name=node.name, order=k,
                        route="taylor", claimed=claimed)


def _walk_nodes(node: Node):
    yield node
    for c in node.children:
        if isinstance(c, Node):
            yield from _walk_nodes(c)
    if node.op == "log" and node.factors:
        for _c, fn in node.factors:
            if isinstance(fn, Node):
                yield from _walk_nodes(fn)


def _has_free_pi(root: Node) -> bool:
    return any(n.op == "pi" and n.digits is None for n in _walk_nodes(root))


def _has_free_taylor(root: Node) -> bool:
    for n in _walk_nodes(root):
        if n.op in ("log", "exp") and n.order is None and n.claim_lo is None \
                and n.claim_hi is None and n.strict is not True:
            if n.op == "log" and (n.factors is not None or n.const == 2):
                continue
            return True
    return False


def _emission_order(root: ResolvedNode) -> tuple:
    """Post-order over the theorem-emitting nodes, de-duplicated by structural key: a
    repeated subtree (the `sqrt 5` inside both `sqrt (10 - 2 sqrt 5)` and `sqrt 5 - 1`) gets
    ONE theorem."""
    seen: set = set()
    out: list = []

    def walk(n: ResolvedNode) -> None:
        for c in n.children:
            walk(c)
        if n.emits and n.key not in seen:
            seen.add(n.key)
            out.append(n)

    walk(root)
    return tuple(out)


def enclosure_tree_certificate(root: Node, *, lo=None, hi=None, strict=None,
                               rate_cap=None) -> EnclosureTreeCert:
    """Build (and exactly re-check) an enclosure-tree certificate.

    ``lo``/``hi``/``strict`` override the ROOT node's own claim.  Every refusal of the module
    docstring raises :class:`EnclosureTreeRefusal` (a ``ValueError``); nothing is widened.
    When a `pi` node leaves its rung open, the ladder is searched ASCENDING; when an
    unpinned, unclaimed Taylor atom exists, the global order levels ``ORDER_LEVELS`` are
    searched too.  The FIRST combination that carries every claim and the rate cap is
    recorded in the certificate, so the emitted `Real.pi_gt_dN` and Taylor orders are forced
    by the arithmetic, not chosen by a search at proof time."""
    if not isinstance(root, Node):
        raise _refuse(f"root must be a Node, got {type(root).__name__}")
    _check_strict_flag(strict, "root")
    if lo is not None or hi is not None or strict is not None:
        root = replace(
            root,
            claim_lo=root.claim_lo if lo is None else _rat(lo, "root lo"),
            claim_hi=root.claim_hi if hi is None else _rat(hi, "root hi"),
            strict=root.strict if strict is None else strict,
        )
    if root.op == "rat":
        raise _refuse(
            "a rational-constant tree has no transcendental content; the emitted theorem "
            "would be a reflexive `q <= q` stub, which is exactly the decorative shape the "
            "lint refuses")
    if rate_cap is not None:
        rate_cap = _int(rate_cap, "rate cap")
        if rate_cap < 0:
            raise _refuse(f"rate cap {rate_cap} < 0 (the ladder is indexed by naturals)")
        if rate_cap > MAX_RATE_CAP:
            raise _refuse(f"rate cap {rate_cap} exceeds {MAX_RATE_CAP}")

    free_pi = _has_free_pi(root)
    free_taylor = _has_free_taylor(root)
    rungs = list(PI_DIGITS) if free_pi else [PI_DIGITS[0]]
    levels = list(ORDER_LEVELS) if free_taylor else [None]
    last_exc = None
    for level in levels:
        for d in rungs:
            ctx = _Ctx(d, level)
            try:
                resolved = _resolve(root, ctx, is_root=True)
                if resolved.is_const:
                    raise _refuse(
                        "the tree has no transcendental content (every atom is a rational "
                        "constant), so the emitted theorem would be a reflexive `q <= q` "
                        "stub -- exactly the decorative shape the lint refuses.  Use "
                        "`norm_num` directly")
                if rate_cap is not None and sp.Integer(rate_cap + 1) > resolved.lo:
                    raise _refuse(
                        f"rate cap {rate_cap} is NOT reached: the certified lower bound is "
                        f"{resolved.lo} (~{float(resolved.lo):.6f}) but the corollary needs "
                        f"cap + 1 = {rate_cap + 1} <= lo.  The ladder stops short; the "
                        "emitter does not round up for you")
            except EnclosureTreeRefusal as exc:
                last_exc = exc
                continue
            return EnclosureTreeCert(root=resolved, order=_emission_order(resolved),
                                     rate_cap=rate_cap, pi_digits=d if free_pi else None,
                                     order_level=level if free_taylor else None)
    assert last_exc is not None
    raise last_exc


def log_sqrt_certificate(*, shift=0, floor, k=None, c=None, alpha=None,
                         var: str = "y") -> LogSqrtCert:
    """Certify the C 4.7 face `forall y >= floor, log (y + shift) <= c * sqrt y`, exactly.

    With ``shift = a > 0`` the route needs `y + a <= k^2 y` on `y >= floor`, i.e.
    `(k^2 - 1) * floor >= a` (then `sqrt (y + a) <= k sqrt y`); ``k`` defaults to the least
    INTEGER that works (`k = 3` for `a = 4`, `floor = 1`, the `E6Bridge23` instance), and
    ``c`` to `2k`.  With ``shift = 0`` no `k` is needed and ``c`` defaults to 2 (the
    `E6Bridge16` `log n <= 2 sqrt n` step).  Only `alpha = 1/2` is implemented."""
    if alpha is not None and _rat(alpha, "alpha") != sp.Rational(1, 2):
        raise _refuse(f"log_sqrt: alpha = {alpha} is not 1/2; only the sqrt face has island "
                      "instances (the rpow faces are a follow-on)")
    a = _rat(shift, "log_sqrt shift")
    y0 = _rat(floor, "log_sqrt floor")
    if not isinstance(var, str) or not _IDENT.match(var) or var in _RESERVED:
        raise _refuse(f"log_sqrt: variable name {var!r} is not a usable Lean identifier")
    if a < 0:
        raise _refuse(f"log_sqrt: shift a = {a} < 0 is not this face (log (y + a) with a < 0 "
                      "can leave the domain)")
    if y0 <= 0:
        raise _refuse(f"log_sqrt: floor y0 = {y0} <= 0; sqrt y can be 0 while log (y + a) "
                      "is not bounded above by 0")
    if a == 0:
        kk = sp.Integer(1) if k is None else _rat(k, "log_sqrt k")
        if kk != 1:
            raise _refuse("log_sqrt: with shift 0 the route needs no k (k = 1)")
    else:
        if k is None:
            need = sp.Integer(1) + a / y0                      # k^2 >= 1 + a / y0
            kk = sp.Integer(isqrt(int(sp.floor(need))))
            while kk * kk < need:
                kk += 1
        else:
            kk = _rat(k, "log_sqrt k")
    if kk < 1:
        raise _refuse(f"log_sqrt: k = {kk} < 1 cannot dominate sqrt (y + a) by k sqrt y")
    if (kk * kk - 1) * y0 < a:
        raise _refuse(
            f"log_sqrt: y + {a} <= {kk}^2 y FAILS at the floor y = {y0} "
            f"(({kk}^2 - 1) * {y0} = {(kk * kk - 1) * y0} < {a}); raise k or the floor")
    cc = 2 * kk if c is None else _rat(c, "log_sqrt c")
    if cc < 2 * kk:
        raise _refuse(f"log_sqrt: c = {cc} < 2k = {2 * kk}; the route proves "
                      f"log (y + a) <= 2k sqrt y - 2 and nothing tighter")
    return LogSqrtCert(shift=a, floor=y0, k=kk, c=cc, var=var)


_TREE_KEYS = frozenset({"tree", "lo", "hi", "strict", "rate_cap"})
_LOG_SQRT_KEYS = frozenset({"face", "shift", "floor", "k", "c", "alpha", "var"})


def certify_enclosure_tree_point(family, pt, name):
    """Certify one point: ``(CertifiedInstance, n_checks)``.

    Reads the spec dict from ``family.special[1](pt)``: either ``{"tree": Node, optional
    "lo"/"hi"/"strict"/"rate_cap"}`` or ``{"face": "log_sqrt", "floor": .., optional
    "shift"/"k"/"c"/"alpha"/"var"}``.  Unknown keys are refused (a typo must not silently
    drop a claim).  ``n_checks`` is the number of emitted theorems, each an exact rational
    containment (or implication) the certifier verified."""
    spec = family.special[1](pt)
    if not isinstance(spec, dict):
        raise _refuse(f"the family spec must be a dict, got {type(spec).__name__}")
    if spec.get("face", "tree") == "log_sqrt":
        unknown = set(spec) - _LOG_SQRT_KEYS
        if unknown:
            raise _refuse(f"unknown log_sqrt spec key(s) {sorted(unknown)}")
        args = {k: v for k, v in spec.items() if k != "face"}
        if "floor" not in args:
            raise _refuse("the log_sqrt face needs a `floor`")
        cert = log_sqrt_certificate(**args)
        return CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert), 1
    if spec.get("face", "tree") != "tree":
        raise _refuse(f"unknown face {spec.get('face')!r} (expected 'tree' or 'log_sqrt')")
    unknown = set(spec) - _TREE_KEYS - {"face"}
    if unknown:
        raise _refuse(f"unknown enclosure_tree spec key(s) {sorted(unknown)}")
    if "tree" not in spec:
        raise _refuse("the family spec must supply a `tree` (a Node)")
    tree = spec["tree"]
    if isinstance(tree, Node) and tree.name is not None and tree.name != name:
        raise _refuse(f"the root node is named {tree.name!r} but the instance is {name!r}; "
                      "the root theorem takes the instance name")
    cert = enclosure_tree_certificate(tree, lo=spec.get("lo"), hi=spec.get("hi"),
                                      strict=spec.get("strict"), rate_cap=spec.get("rate_cap"))
    return (CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert),
            cert.n_theorems)


# --- Lean rendering ---------------------------------------------------------------

_PREC = {"add": 65, "sub": 65, "mul": 70, "div": 70}
_SYM = {"add": "+", "sub": "-", "mul": "*", "div": "/"}


def _num(q: sp.Rational) -> str:
    """A rational as a Lean operand (`5`, `(3 / 16)`, `(-3)`, `(-(3 / 16))`)."""
    return rat_lean(q)


def _paren(s: str, need: bool) -> str:
    return f"({s})" if need else s


def _rat_expr(q: sp.Rational, prec: int) -> str:
    """A rational leaf inside an expression, parenthesized only where Lean needs it: a
    fraction `p / q` is a `/` node (precedence 70), a negative is a prefix negation."""
    q = sp.Rational(q)
    if q.q == 1:
        return str(q.p) if q.p >= 0 else _paren(f"-{-q.p}", prec > 0)
    if q.p >= 0:
        return _paren(f"{q.p} / {q.q}", prec > 70)
    return _paren(f"-({-q.p} / {q.q})", prec > 0)


def lean_expr(node: ResolvedNode, prec: int = 0) -> str:
    """The node's expression as Lean source, with the parentheses Lean's precedences need
    (`+`/`-` 65 and `*`/`/` 70, both left-associative; `^` 75; application tightest), so
    `3 * Real.pi * 4000 / 2` and `(Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)`
    come out as a person writes them.  Deterministic."""
    op = node.op
    if op == "rat":
        return _rat_expr(node.const, prec)
    if op == "pi":
        return "Real.pi"
    if op == "log":
        return _paren(f"Real.log {_rat_expr(node.const, 1024)}", prec >= 1024)
    if op == "exp":
        return _paren(f"Real.exp {_rat_expr(node.const, 1024)}", prec >= 1024)
    if op == "sqrt":
        return _paren(f"Real.sqrt {lean_expr(node.children[0], 1024)}", prec >= 1024)
    if op == "arctan":
        return _paren(f"Real.arctan {lean_expr(node.children[0], 1024)}", prec >= 1024)
    if op == "neg":
        inner = f"-{lean_expr(node.children[0], 75)}"
        return _paren(inner, prec > 0)
    if op == "pow":
        s = f"{lean_expr(node.children[0], 76)} ^ {node.exponent}"
        return _paren(s, prec > 75)
    p = _PREC[op]
    a = lean_expr(node.children[0], p)
    b = lean_expr(node.children[1], p + 1)
    return _paren(f"{a} {_SYM[op]} {b}", prec > p)


def _lit(q: sp.Rational) -> str:
    """A rational literal typed in `R`: `(5 : R)`, `(3 / 16 : R)`, `(-3 : R)`."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"({q.p} : ℝ)"
    if q.p >= 0:
        return f"({q.p} / {q.q} : ℝ)"
    return f"(-({-q.p} / {q.q}) : ℝ)"


def _rel(strict: bool) -> str:
    return "<" if strict else "≤"


def _statement(node: ResolvedNode) -> str:
    e = lean_expr(node)
    one = (f"{_lit(node.lo)} {_rel(node.lo_strict)} {e} ∧ "
           f"{e} {_rel(node.hi_strict)} {_lit(node.hi)}")
    if len(one) <= 88:
        return one
    return (f"{_lit(node.lo)} {_rel(node.lo_strict)} {e} ∧\n"
            f"      {e} {_rel(node.hi_strict)} {_lit(node.hi)}")


def _frontier(node: ResolvedNode) -> list:
    """The theorem-emitting descendants a node's proof consumes: its emitting children, and,
    through every non-emitting (linear or constant) child, that child's frontier."""
    out: list = []
    seen: set = set()

    def walk(n: ResolvedNode) -> None:
        for c in n.children:
            if c.emits:
                if c.key not in seen:
                    seen.add(c.key)
                    out.append(c)
            else:
                walk(c)
    walk(node)
    return out


def _obtains(node: ResolvedNode, names: dict) -> tuple:
    lines, hyps = [], []
    for k, f in enumerate(_frontier(node)):
        lines.append(f"  obtain ⟨h{k}lo, h{k}hi⟩ := {names[f.key]}")
        hyps.extend([f"h{k}lo", f"h{k}hi"])
    return lines, hyps


_ARCTAN_ABS_LE = """  have harct : ∀ t : ℝ, |Real.arctan t| ≤ |t| := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg (Real.arctan_nonneg.mpr ht), abs_of_nonneg ht]
      have h := Real.le_tan (Real.arctan_nonneg.mpr ht) (Real.arctan_lt_pi_div_two t)
      rwa [Real.tan_arctan] at h
    · have ht' : (0 : ℝ) ≤ -t := by linarith
      have h := Real.le_tan (Real.arctan_nonneg.mpr ht') (Real.arctan_lt_pi_div_two (-t))
      rw [Real.tan_arctan, Real.arctan_neg] at h
      have hneg : Real.arctan t < 0 := by
        have := Real.arctan_strictMono ht
        simpa [Real.arctan_zero] using this
      rw [abs_of_neg hneg, abs_of_neg ht]
      linarith
"""

_ARCTAN_HALF = """  have hself : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
    intro u hu
    have h := Real.le_tan (Real.arctan_nonneg.mpr hu) (Real.arctan_lt_pi_div_two u)
    rwa [Real.tan_arctan] at h
  have hhalf : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → u / 2 ≤ Real.arctan u := by
    intro u hu0 hu1
    have hderiv : ∀ x : ℝ,
        HasDerivAt (fun x => Real.arctan x - x / 2) (1 / (1 + x ^ 2) - 1 / 2) x :=
      fun x => (Real.hasDerivAt_arctan x).sub ((hasDerivAt_id x).div_const 2)
    have hmono : MonotoneOn (fun x => Real.arctan x - x / 2) (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (continuousOn_of_forall_continuousAt fun x _ => (hderiv x).continuousAt)
        (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have : 1 / 2 ≤ 1 / (1 + x ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      linarith
    have := hmono (Set.left_mem_Icc.mpr zero_le_one) ⟨hu0, hu1⟩ hu0
    simp only [Real.arctan_zero] at this
    linarith
"""


def _by_facts(node: ResolvedNode) -> str:
    """`by norm_num` for a constant, else `by linarith` over the obtained frontier."""
    return "by norm_num" if node.is_const else "by linarith"


def _proof_body(node: ResolvedNode, names: dict) -> str:
    """The frozen tactic skeleton for ONE emitting node, by op."""
    obt, hyps = _obtains(node, names)
    pre = "".join(line + "\n" for line in obt)
    op = node.op

    if op == "pi":
        gt, lt = PI_LADDER[node.digits][2:]
        return f"  constructor <;> linarith [{gt}, {lt}]\n"

    if op == "log" and node.route == "mathlib2":
        return ("  have h1 := Real.log_two_gt_d9\n"
                "  have h2 := Real.log_two_lt_d9\n"
                "  norm_num at h1 h2\n"
                "  constructor <;> linarith\n")

    if op == "log" and node.route == "taylor":
        q = node.const
        x = _num(sp.Integer(1) - q)
        return (f"  have hx : |({x} : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num\n"
                f"  have h := Real.abs_log_sub_add_sum_range_le hx {node.order}\n"
                f"  rw [show (1 : ℝ) - {x} = {_num(q)} by norm_num] at h\n"
                f"  generalize Real.log {_num(q)} = L at h ⊢\n"
                f"  rw [abs_le] at h\n"
                f"  norm_num [Finset.sum_range_succ] at h\n"
                f"  constructor <;> linarith [h.1, h.2]\n")

    if op == "log" and node.route == "fold":
        return pre + _log_fold_body(node)

    if op == "exp":
        x = _num(node.const)
        return (f"  have hx : |({x} : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num\n"
                f"  have hb := Real.exp_bound hx (n := {node.order}) (by norm_num)\n"
                f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb\n"
                f"  rw [abs_le] at hb\n"
                f"  obtain ⟨hb1, hb2⟩ := hb\n"
                f"  constructor\n"
                f"  · norm_num [Nat.factorial] at hb1 ⊢; linarith\n"
                f"  · norm_num [Nat.factorial] at hb2 ⊢; linarith\n")

    if op == "sqrt":
        c = node.children[0]
        arg = lean_expr(c)
        sq = lean_expr(node)
        extra = "".join(f", {h}" for h in hyps)
        return (pre
                + f"  have harg : (0 : ℝ) ≤ {arg} := {_by_facts(c)}\n"
                + f"  have h2 : {sq} ^ 2 = {arg} := Real.sq_sqrt harg\n"
                + f"  have hn : (0 : ℝ) ≤ {sq} := Real.sqrt_nonneg _\n"
                + f"  constructor <;> nlinarith [h2, hn{extra}]\n")

    if op == "arctan":
        c = node.children[0]
        arg = lean_expr(c, 1024)
        if node.route == "half":
            return (pre + _ARCTAN_HALF
                    + f"  have hu0 : (0 : ℝ) ≤ {lean_expr(c)} := {_by_facts(c)}\n"
                    + f"  have hu1 : ({lean_expr(c)} : ℝ) ≤ 1 := {_by_facts(c)}\n"
                    + f"  have ha1 := hhalf {arg} hu0 hu1\n"
                    + f"  have ha2 := hself {arg} hu0\n"
                    + "  constructor <;> linarith\n")
        m = max(abs(node.box_lo), abs(node.box_hi))
        tac = ("by rw [abs_le]; constructor <;> norm_num" if c.is_const
               else "by rw [abs_le]; constructor <;> linarith")
        return (pre + _ARCTAN_ABS_LE
                + f"  have hb : |{lean_expr(c)}| ≤ {_lit(m)} := {tac}\n"
                + f"  have hall : |Real.arctan {arg}| ≤ {_lit(m)} := le_trans (harct _) hb\n"
                + "  obtain ⟨ha1, ha2⟩ := abs_le.mp hall\n"
                + "  constructor <;> linarith\n")

    if op in ("add", "sub", "neg"):
        return pre + "  constructor <;> linarith\n"

    if op == "mul":
        a, b = node.children
        if a.is_const or b.is_const:
            return pre + "  constructor <;> linarith\n"
        ea, eb = lean_expr(a, 66), lean_expr(b, 66)
        alo, ahi, blo, bhi = (_num(v) for v in (a.lo, a.hi, b.lo, b.hi))
        return (pre
                + f"  have hm1 : (0 : ℝ) ≤ ({ea} - {alo}) * ({eb} - {blo}) :=\n"
                + "    mul_nonneg (by linarith) (by linarith)\n"
                + f"  have hm2 : (0 : ℝ) ≤ ({ahi} - {ea}) * ({eb} - {blo}) :=\n"
                + "    mul_nonneg (by linarith) (by linarith)\n"
                + f"  have hm3 : (0 : ℝ) ≤ ({ea} - {alo}) * ({bhi} - {eb}) :=\n"
                + "    mul_nonneg (by linarith) (by linarith)\n"
                + f"  have hm4 : (0 : ℝ) ≤ ({ahi} - {ea}) * ({bhi} - {eb}) :=\n"
                + "    mul_nonneg (by linarith) (by linarith)\n"
                + "  constructor <;> linarith [hm1, hm2, hm3, hm4]\n")

    if op == "div":
        a, b = node.children
        if b.is_const:
            return pre + "  constructor <;> linarith\n"
        eb = lean_expr(b)
        lo_lemma = "lt_div_iff₀" if node.lo_strict else "le_div_iff₀"
        hi_lemma = "div_lt_iff₀" if node.hi_strict else "div_le_iff₀"
        return (pre
                + f"  have hden : (0 : ℝ) < {eb} := by linarith\n"
                + "  constructor\n"
                + f"  · rw [{lo_lemma} hden]\n"
                + "    linarith\n"
                + f"  · rw [{hi_lemma} hden]\n"
                + "    linarith\n")

    if op == "pow":
        c = node.children[0]
        ec = lean_expr(c, 76)
        k = node.exponent
        clo, chi = _num(c.lo), _num(c.hi)
        return (pre
                + f"  have hnn : (0 : ℝ) ≤ {clo} := by norm_num\n"
                + f"  have hup : (0 : ℝ) ≤ {lean_expr(c)} := by linarith\n"
                + f"  have hl : ({clo} : ℝ) ^ {k} ≤ {ec} ^ {k} :=\n"
                + f"    pow_le_pow_left₀ hnn (by linarith) {k}\n"
                + f"  have hh : {ec} ^ {k} ≤ ({chi} : ℝ) ^ {k} :=\n"
                + f"    pow_le_pow_left₀ hup (by linarith) {k}\n"
                + "  constructor <;> linarith\n")

    raise _refuse(f"no tactic skeleton for op {op!r}")  # pragma: no cover


def _log_fold_body(node: ResolvedNode) -> str:
    """`log (prod f_i^c_i) = sum c_i log f_i` by repeated `Real.log_mul`, then a pure
    `linarith` against the factors' own emitted brackets (obtained as the frontier).

    The rewrite runs BACKWARDS (`rw [<- Real.log_mul ..]`) so the argument literal is never
    rewritten inside its own sub-literals (the trap that makes the forward
    `show (3 : R) = 2 * (3/2)` route rewrite the `3` inside `3/2`)."""
    flat: list = []
    for c, ch in zip(node.coeffs, node.children):
        flat.extend([_num(ch.const)] * c)
    sum_txt = " + ".join(f"Real.log {t}" for t in flat)
    lines = [f"  have hfold : Real.log {_num(node.const)} = {sum_txt} := by"]
    acc = flat[0]
    for t in flat[1:]:
        lines.append(f"    rw [← Real.log_mul (by norm_num : ({acc} : ℝ) ≠ 0) "
                     f"(by norm_num : ({t} : ℝ) ≠ 0)]")
        acc = f"{acc} * {t}"
    lines.append("    norm_num")
    lines.append("  rw [hfold]")
    lines.append("  constructor <;> linarith")
    return "\n".join(lines) + "\n"


_ROUTE = {
    "sqrt": "Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares",
    "add": "the exact interval fold (linarith)",
    "sub": "the exact interval fold (linarith)",
    "neg": "the exact interval fold (linarith)",
    "pow": "pow_le_pow_left0 on a nonnegative base",
}


def _route_text(node: ResolvedNode) -> str:
    op = node.op
    if op == "pi":
        gt, lt = PI_LADDER[node.digits][2:]
        return f"Mathlib's pi ladder rung d{node.digits} ({gt}, {lt})"
    if op == "log":
        return {"mathlib2": "Real.log_two_gt_d9 / Real.log_two_lt_d9",
                "taylor": f"the order-{node.order} Taylor estimate "
                          "Real.abs_log_sub_add_sum_range_le (exact rational S and radius)",
                "fold": "the multiplicative fold log (prod f^c) = sum c log f "
                        "(Real.log_mul, backwards)"}[node.route]
    if op == "exp":
        return f"the order-{node.order} Real.exp_bound box (exact rational S and radius)"
    if op == "arctan":
        return ("t/2 <= arctan t <= t on [0, 1] (monotoneOn_of_deriv_nonneg, Real.le_tan)"
                if node.route == "half" else "|arctan t| <= |t| (Real.le_tan)")
    if op == "mul":
        a, b = node.children
        return ("constant scaling (linarith)" if (a.is_const or b.is_const)
                else "the four McCormick corner facts, closed by linarith")
    if op == "div":
        return ("division by a constant (linarith)" if node.children[1].is_const
                else "le_div_iff0 / div_le_iff0 against a certified positive denominator")
    return _ROUTE[op]


def _safe_comment(s: str) -> str:
    return s.replace("-/", "- /").replace("/-", "/ -")


def _header(node: ResolvedNode, nm: str) -> str:
    if node.op == "sqrt":
        c = node.children[0]
        check = (f"Checked exactly against the radicand interval [{c.lo}, {c.hi}] by rational "
                 f"squares (lo^2 vs {c.lo}, {c.hi} vs hi^2)")
    else:
        check = (f"Exact fold [{node.box_lo}, {node.box_hi}], inside the stated bracket with "
                 f"slack ({node.box_lo - node.lo}, {node.hi - node.box_hi})")
    text = (
        f"/-- `{nm}` -- a certified RATIONAL ENCLOSURE of `{lean_expr(node)}`.\n"
        f"    Route: {_route_text(node)}.\n"
        f"    {check}.\n"
        f"    The generator REFUSES a bracket the fold does not imply rather than\n"
        f"    widening it.  A finite arithmetic fact about real constants; nothing\n"
        f"    about RH.  conjecture1_proved = False. -/\n"
    )
    return "/--" + _safe_comment(text[3:-3]) + "-/\n"


def _rate_lemma(cert: EnclosureTreeCert, root_name: str, stmt_name: str) -> str:
    """The D-audit `pi`-face rate corollary, by `linarith` from the root's own certified
    lower bound and `cap + 1 <= lo` (an exact rational fact the certifier checked)."""
    cap = cert.rate_cap
    e = lean_expr(cert.root)
    head = (
        f"/-- `{stmt_name}` -- the RATE COROLLARY of `{root_name}`: every `n <= {cap}`\n"
        f"    satisfies `(n + 1 : R) <= E`, because the certified lower bound\n"
        f"    {cert.root.lo} is at least {cap} + 1 = {cap + 1} EXACTLY.  The generator refuses\n"
        f"    a cap the bound does not reach; it never rounds up.  A finite arithmetic\n"
        f"    fact; nothing about RH.  conjecture1_proved = False. -/\n"
    )
    return (
        "/--" + _safe_comment(head[3:-3]) + "-/\n"
        f"theorem {stmt_name} (n : ℕ) (hn : n ≤ {cap}) :\n"
        f"    (n + 1 : ℝ) ≤ {e} := by\n"
        f"  obtain ⟨hlo, _hhi⟩ := {root_name}\n"
        f"  have hn' : (n : ℝ) ≤ ({cap} : ℝ) := by exact_mod_cast hn\n"
        f"  linarith\n"
    )


def _log_sqrt_theorem(cert: LogSqrtCert, nm: str) -> str:
    y = cert.var
    a, y0, k, c = cert.shift, cert.floor, cert.k, cert.c
    ya = f"{y} + {a}" if a != 0 else y
    head = (
        f"/-- `{nm}` -- the log/sqrt face (C 4.7): `log ({ya}) <= {c} * sqrt {y}` for\n"
        f"    `{y} >= {y0}`, from `log t <= t - 1` at `t = sqrt ({ya})`"
        + (f" and `{y} + {a} <= {k}^2 {y}`" if a != 0 else "") + ".\n"
        f"    An elementary real inequality; nothing about RH.  conjecture1_proved = False. -/\n"
    )
    header = "/--" + _safe_comment(head[3:-3]) + "-/\n"
    hy = f"(hy : {_lit(y0)} ≤ {y})"
    if a == 0:
        return header + (
            f"theorem {nm} {{{y} : ℝ}} {hy} : Real.log {y} ≤ {_num(c)} * Real.sqrt {y} := by\n"
            f"  have hy0 : (0 : ℝ) < {y} := lt_of_lt_of_le (by norm_num) hy\n"
            f"  have hs : (0 : ℝ) < Real.sqrt {y} := Real.sqrt_pos.mpr hy0\n"
            f"  have h1 := Real.log_le_sub_one_of_pos hs\n"
            f"  rw [Real.log_sqrt hy0.le] at h1\n"
            f"  have h4 : (0 : ℝ) ≤ Real.sqrt {y} := hs.le\n"
            f"  linarith\n"
        )
    arg = f"{y} + {_num(a)}"
    kk = _num(k)
    return header + (
        f"theorem {nm} {{{y} : ℝ}} {hy} :\n"
        f"    Real.log ({arg}) ≤ {_num(c)} * Real.sqrt {y} := by\n"
        f"  have h1 : Real.log ({arg}) = 2 * Real.log (Real.sqrt ({arg})) := by\n"
        f"    rw [Real.log_sqrt (by linarith)]; ring\n"
        f"  have h2 : Real.log (Real.sqrt ({arg})) ≤ Real.sqrt ({arg}) - 1 :=\n"
        f"    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))\n"
        f"  have h3 : Real.sqrt ({arg}) ≤ {kk} * Real.sqrt {y} := by\n"
        f"    rw [show ({kk} : ℝ) * Real.sqrt {y} = Real.sqrt ({kk} ^ 2 * {y}) by\n"
        f"      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]\n"
        f"    exact Real.sqrt_le_sqrt (by nlinarith)\n"
        f"  have h4 : (0 : ℝ) ≤ Real.sqrt {y} := Real.sqrt_nonneg {y}\n"
        f"  linarith\n"
    )


@dataclass
class EnclosureTreeEmitter(Emitter):
    """Emit rational two-sided enclosures of expression trees over `{+, -, *, /, ^, sqrt,
    log, exp, pi, arctan, rational constants}` -- one theorem per NON-LINEAR node (atoms,
    square roots, arctangents, products and quotients of two non-constants, powers), per
    named or claimed node, and per root, children first, shared subtrees ONCE across the
    whole family -- plus the optional `pi`-face rate corollary `n <= cap -> (n + 1 : R) <=
    E`, and the `log_sqrt` face.  Each theorem is proved by the frozen per-op skeleton of
    the 48h shapes audit.  No `decide`, no proof hole; the claimed brackets ARE the
    statements and `enclosure_tree_certificate` refuses every claim the exact fold does not
    imply.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "enclosure_tree"

    def emit_units(self, fam, profile: LeanProfile) -> list:
        """ONE unit: the family shares theorems across instances (a later instance consumes
        an earlier one's node by name), so it must not be split across files."""
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple:
        chunks: list = []
        n_thm = 0
        names: dict = {}             # node key -> emitted theorem name (family-wide)
        used: set = set()

        def claim(nm: str) -> None:
            if nm in used:
                raise _refuse(f"duplicate emitted theorem name {nm!r}")
            used.add(nm)

        for inst in fam.instances:
            cert = inst.payload
            nm_root = inst.lean_name
            if isinstance(cert, LogSqrtCert):
                claim(nm_root)
                chunks.append(_log_sqrt_theorem(cert, nm_root))
                n_thm += 1
                continue
            k = 0
            for node in cert.order:
                if node.key in names:
                    continue                      # shared: consumed by name, not re-proved
                if node.key == cert.root.key:
                    nm = nm_root
                elif node.name:
                    nm = node.name
                else:
                    nm = f"{nm_root}_n{k}"
                    k += 1
                claim(nm)
                names[node.key] = nm
                chunks.append(_header(node, nm)
                              + f"theorem {nm} :\n    {_statement(node)} := by\n"
                              + _proof_body(node, names))
                n_thm += 1
            if names[cert.root.key] != nm_root:
                # this instance's root was already proved under another name: alias it
                claim(nm_root)
                chunks.append(
                    f"/-- `{nm_root}` -- the same enclosure as `{names[cert.root.key]}` "
                    "(shared subtree).\n    conjecture1_proved = False. -/\n"
                    f"theorem {nm_root} :\n    {_statement(cert.root)} :=\n"
                    f"  {names[cert.root.key]}\n")
                n_thm += 1
            if cert.rate_cap is not None:
                rate_nm = f"{nm_root}_rate"
                claim(rate_nm)
                chunks.append(_rate_lemma(cert, nm_root, rate_nm))
                n_thm += 1
        return "\n".join(chunks), n_thm


def enclosure_tree_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an enclosure-tree family (kind ``enclosure_tree``).

    ``spec: pt -> {"tree": Node, optional "lo"/"hi"/"strict"/"rate_cap"}`` (the expression
    tree and the CLAIMED root bracket; every atom parameter left open -- pi rung, Taylor
    order, derived sqrt bracket -- is chosen at certify time and recorded in the
    certificate), or ``pt -> {"face": "log_sqrt", "floor": .., ...}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("enclosure_tree", spec),
        constants=dict(constants or {}),
    )

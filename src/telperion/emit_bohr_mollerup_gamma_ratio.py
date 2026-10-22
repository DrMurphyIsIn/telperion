"""Bohr-Mollerup Gamma-ratio emitter (kind ``bohr_mollerup_gamma_ratio``) -- a kernel-checked
rational enclosure ``LO <= Real.Gamma x1 / Real.Gamma x2 <= HI`` for rationals ``0 < x1, x2 < 1``.

The general form of the hand-built CN-1 lemma ``Gamma_ratio_enclosure`` (``2.1753 <= Gamma(3/8) /
Gamma(7/8) <= 2.1755``, ``n = 8000``), ported to Lean v4.32.0 / Mathlib v4.32.0.  No registry kind
touched ``Real.Gamma`` before this one.

THE MATHEMATICS.  Mathlib has ``Real.convexOn_log_Gamma`` and the Bohr-Mollerup inequality
``Real.BohrMollerup.f_add_nat_le``.  From these, for ``n >= 1`` and ``0 < x < 1`` (prelude):

    Gamma(n+1) (n+x)^(x-1)  <=  Gamma(n+x)  <=  Gamma(n) n^x,

and with ``Gamma(n+x) = Gamma(x) prod_{k<n} (x+k)`` the ratio is enclosed by elementary
functions of ``n`` times an EXACT rational ``P``:

    n (n+x1)^(x1-1) / n^x2 * P  <=  Gamma x1 / Gamma x2  <=  n^x1 / (n (n+x2)^(x2-1)) * P,
    P = prod_{k<n} (x2+k)/(x1+k) = gA / gB,   gA = prod (q k + a2),  gB = prod (q k + a1),

where ``q`` is the common denominator of ``x1 = a1/q`` and ``x2 = a2/q``.  The two sides differ
by the factor ``(1+x1/n)^(1-x1) (1+x2/n)^(1-x2) = 1 + O(1/n)``, so the relative width of the
enclosure is about ``(x1(1-x1) + x2(1-x2))/n``: ``n`` buys digits linearly.

THE CERTIFICATE (exact integers, no floats):

* ``gA``, ``gB``: the two range products, DEFINED in Lean as ``C`` blocks of ``K`` (``n = C K``) so
  the kernel's recursion stays shallow; the kernel computes them (GMP ``Nat``), nothing numeric
  about them is trusted from Python;
* four q-th-root brackets at a scale ``S`` for the ``rpow`` factors, each an integer inequality
  the kernel decides (``l1/S <= (n+x1)^(x1-1)``, ``n^x2 <= u2/S``, ``n^x1 <= u3/S``,
  ``l4/S <= (n+x2)^(x2-1)``);
* two ``Nat`` comparisons decided by the kernel, ``LOn u2 gB <= LOd n l1 gA`` and
  ``HId u3 gA <= HIn n l4 gB``, which are exactly ``LO <= n l1 gA/(u2 gB)`` and
  ``u3 gA/(n l4 gB) <= HI``.

The real-number argument (``<name>_aux``) is made ONCE per instance for ABSTRACT ``gA gB : N``
with the products' defining equation and the two comparisons as hypotheses, so no tactic ever
tries to normalise a thousand-digit product (``positivity`` / ``linarith`` / ``field_simp`` hit
``maxRecDepth`` otherwise; this is the idiom the hand-built proof found).

EMITTED LEAN (per instance ``nm``): ``def nm_gA nm_gB : N`` (blocked products),
``nm_gA_eq`` / ``nm_gB_eq`` (``prod_range_chunk`` + ``rfl``), ``nm_P_eq`` (the real product equals
``gA/gB``), ``nm_gB_pos``, ``nm_key_lo`` / ``nm_key_hi`` (``decide +kernel``), ``nm_hA`` ..
``nm_hD`` (the four brackets, ``decide +kernel`` under a once-proved transport lemma),
``nm_aux`` and ``theorem nm : LO <= Real.Gamma x1 / Real.Gamma x2 /\\ ... <= HI``.

REFUSALS (``ValueError`` at certify time, never a printed flag): ``x`` not a rational in the
OPEN interval ``(0, 1)`` (the Bohr-Mollerup bounds need it; reduce by ``Gamma_add_one`` first),
``n`` not a positive multiple of the block size, a non-positive scale, a float anywhere, and --
the load-bearing one -- a claimed ``LO`` above the certified rational lower bound or a claimed
``HI`` below the certified upper bound.  The claim is checked EXACTLY against the same two
``Nat`` inequalities the kernel decides, so a certificate that passes here compiles and one that
fails here is never emitted.  (The CN-1 generator only PRINTED ``key1: False``; REVIEW_E C6.)

NEGATIVE CONTROLS (``negctrl_adapters/adapter_bohr_mollerup_gamma_ratio.py``).  CERTIFICATE_
SENSITIVE: the integers ``l1 u2 u3 l4`` and the two comparisons ARE the witness, so the registered
control forges the WITNESS with the statement unchanged: the Gamma(3/8)/Gamma(7/8) certificate at
``n = 200`` with ``l1`` raised by one (one above the maximal lower bracket) makes ``nm_hA``'s root
inequality a FALSE ``Nat`` fact, and ``decide +kernel`` reports it false.  A second control forges
the CLAIM (``LO`` := the certified upper decimal ``HI``, above the true value, which Layer 1
refuses): ``nm_key_lo`` is then FALSE.  In both cases ``lean`` reports the error and exits 1; the
declarations are still added by error recovery, carrying ``sorryAx``, which is what the harness's
axiom check sees.  The adapter renders both twins with ``decide_rec_depth`` set, so the failure
message is the readable "Tactic `decide` proved that the proposition ... is false"; under the
default depth a failing ``key_lo`` exhausts ``maxRecDepth`` while its message is FORMATTED (the
proposition is short; it names ``gA gB`` without expanding them).

PRELUDE.  :func:`bohr_mollerup_prelude_lean` is the module ``BohrMollerupPrelude`` (Mathlib
only): ``Gamma_add_nat_eq``, ``Gamma_add_le``, ``Gamma_add_ge``, ``Gamma_ratio_bounds``,
``prod_range_chunk``, and the root brackets ``rpow_div_upper`` / ``rpow_rat_neg_div_lower``.
The root brackets are a minimal inline copy of what survey item N1 (``nat_root_bracket_table``)
builds as a general table; once N1 merges this prelude should import N1's and drop its copies.

HONEST SCOPE: an enclosure of one ratio of Gamma values at rational points; it proves nothing
about class numbers and nothing about RH.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

#: Default scale of the four root brackets: 12 decimal digits (the hand-built proof's).
DEFAULT_SCALE = 10 ** 12
#: Default block size of the kernel products (the hand-built proof's; the kernel's recursion
#: depth is bounded by the block, not by ``n``).
DEFAULT_BLOCK = 200
#: Largest ``n`` accepted (one file; about 10 s of kernel time at the hand-built 8000).
MAX_N = 20000
#: Finest decimal resolution used when a claim is not supplied.
MAX_CLAIM_DIGITS = 40

_PRELUDE_NS = "BohrMollerupPrelude"


# --------------------------------------------------------------------------------------
# Exact integer arithmetic.
# --------------------------------------------------------------------------------------


def iroot(x: int, q: int) -> int:
    """``floor(x^(1/q))`` exactly: Newton from above, then an integer fix-up."""
    if x < 0 or q <= 0:
        raise ValueError("iroot needs x >= 0 and q >= 1")
    if x < 2:
        return x
    r = 1 << ((x.bit_length() + q - 1) // q)   # >= the true root
    while True:
        y = ((q - 1) * r + x // r ** (q - 1)) // q
        if y >= r:
            break
        r = y
    while r ** q > x:
        r -= 1
    while (r + 1) ** q <= x:
        r += 1
    return r


def rat_neg_lower(a: int, b: int, p: int, q: int, S: int) -> int:
    """The largest ``L`` with ``L^q a^p <= b^p S^q``, i.e. ``L/S <= (a/b)^(-p/q)``."""
    L = iroot(b ** p * S ** q // a ** p, q)
    assert L ** q * a ** p <= b ** p * S ** q
    return L


def nat_pos_upper(m: int, p: int, q: int, S: int) -> int:
    """The smallest ``U`` with ``m^p S^q <= U^q``, i.e. ``m^(p/q) <= U/S``."""
    X = m ** p * S ** q
    U = iroot(X, q)
    if U ** q < X:
        U += 1
    assert X <= U ** q
    return U


def _frac(v, what: str) -> Fraction:
    """An exact rational from an int, Fraction, sympy Rational or decimal STRING; floats refused."""
    if isinstance(v, bool):
        raise ValueError(f"REFUSED: {what} must be a rational, got a bool")
    if isinstance(v, float):
        raise ValueError(f"REFUSED: {what} = {v!r} is a float; pass an exact rational or a string")
    if isinstance(v, Fraction):
        return v
    if isinstance(v, int):
        return Fraction(v)
    if isinstance(v, str):
        return Fraction(v)
    if isinstance(v, sp.Basic):
        if not (v.is_Rational and v.is_finite):
            raise ValueError(f"REFUSED: {what} = {v} is not a sympy Rational")
        return Fraction(int(v.p), int(v.q))
    raise ValueError(f"REFUSED: {what} = {v!r} has unsupported type {type(v).__name__}")


def _int(v, what: str, lo: int = 1) -> int:
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(f"REFUSED: {what} must be an int, got {v!r}")
    if v < lo:
        raise ValueError(f"REFUSED: {what} = {v} must be >= {lo}")
    return v


def _decimal_floor(x: Fraction, d: int) -> Fraction:
    return Fraction(x.numerator * 10 ** d // x.denominator, 10 ** d)


def _decimal_ceil(x: Fraction, d: int) -> Fraction:
    return Fraction(-((-x.numerator) * 10 ** d // x.denominator), 10 ** d)


def _claim_digits(width: Fraction) -> int:
    """``ceil(-log10 width)``, the decimal resolution the enclosure supports."""
    d = 0
    while d < MAX_CLAIM_DIGITS and Fraction(1, 10 ** d) > width:
        d += 1
    return d


# --------------------------------------------------------------------------------------
# The certificate.
# --------------------------------------------------------------------------------------


@dataclass(frozen=True)
class BohrMollerupGammaRatioCert:
    """Everything the emitted Lean states, as exact integers and rationals.

    ``x1, x2`` are the reduced rationals in ``(0, 1)``; ``q`` their common denominator and
    ``a1, a2`` the numerators over ``q``; ``n = blocks * block``; ``scale`` the bracket scale;
    ``l1, u2, u3, l4`` the four root brackets; ``lo, hi`` the certified rational enclosure
    (``lo = n l1 gA / (u2 gB)``, ``hi = u3 gA / (n l4 gB)``, COMPUTED, kept for reporting -- the
    kernel never sees them); ``claim_lo, claim_hi`` the stated bounds, with
    ``claim_lo <= lo`` and ``hi <= claim_hi`` checked exactly at construction.
    """

    x1: Fraction
    x2: Fraction
    n: int
    blocks: int
    block: int
    scale: int
    q: int
    a1: int
    a2: int
    l1: int
    u2: int
    u3: int
    l4: int
    lo: Fraction
    hi: Fraction
    claim_lo: Fraction
    claim_hi: Fraction

    # The two Nat inequalities the kernel decides, as Python ints (exactly the emitted ones).
    def key_lo_holds(self, gA: int, gB: int) -> bool:
        return (self.claim_lo.numerator * self.u2 * gB
                <= self.claim_lo.denominator * self.n * self.l1 * gA)

    def key_hi_holds(self, gA: int, gB: int) -> bool:
        return (self.claim_hi.denominator * self.u3 * gA
                <= self.claim_hi.numerator * self.n * self.l4 * gB)


def gamma_ratio_products(x1, x2, n: int) -> tuple[int, int, int, int, int]:
    """``(q, a1, a2, gA, gB)``: the common denominator, the numerators over it, and the exact
    products ``gA = prod_{k<n} (q k + a2)``, ``gB = prod_{k<n} (q k + a1)``."""
    x1 = _frac(x1, "x1")
    x2 = _frac(x2, "x2")
    q = lcm(x1.denominator, x2.denominator)
    a1 = x1.numerator * (q // x1.denominator)
    a2 = x2.numerator * (q // x2.denominator)
    gA = 1
    gB = 1
    for k in range(n):
        gA *= q * k + a2
        gB *= q * k + a1
    return q, a1, a2, gA, gB


def bohr_mollerup_gamma_ratio_certificate(
    x1, x2, n: int, *, claim_lo=None, claim_hi=None,
    scale: int = DEFAULT_SCALE, block: int = DEFAULT_BLOCK,
) -> BohrMollerupGammaRatioCert:
    """Build and EXACTLY self-check the certificate of ``claim_lo <= Gamma x1 / Gamma x2 <= claim_hi``.

    When a claim is omitted it defaults to the certified bound rounded outward to the decimal
    resolution of the enclosure (``ceil(-log10(hi - lo))`` digits).  A supplied claim that the
    certificate does not imply is REFUSED (``ValueError``): the check is the same two ``Nat``
    inequalities the kernel decides, so refusal here and kernel rejection coincide.
    """
    x1 = _frac(x1, "x1")
    x2 = _frac(x2, "x2")
    for nm, x in (("x1", x1), ("x2", x2)):
        if not (0 < x < 1):
            raise ValueError(
                f"REFUSED: {nm} = {x} is not in the open interval (0, 1); the Bohr-Mollerup "
                f"bounds need 0 < x < 1 (reduce by Gamma_add_one first)")
    n = _int(n, "n")
    block = _int(block, "block")
    scale = _int(scale, "scale")
    if n > MAX_N:
        raise ValueError(f"REFUSED: n = {n} > MAX_N = {MAX_N} (one file; shard instead)")
    if n % block != 0:
        raise ValueError(f"REFUSED: n = {n} is not a multiple of the block size {block}")
    blocks = n // block

    q, a1, a2, gA, gB = gamma_ratio_products(x1, x2, n)
    # The four root brackets, each about a REDUCED fraction (the Lean statement uses it).
    p1, q1 = x1.numerator, x1.denominator
    p2, q2 = x2.numerator, x2.denominator
    l1 = rat_neg_lower(n * q1 + p1, q1, q1 - p1, q1, scale)   # (n + x1)^(x1 - 1) >= l1/S
    u2 = nat_pos_upper(n, p2, q2, scale)                        # n^x2 <= u2/S
    u3 = nat_pos_upper(n, p1, q1, scale)                        # n^x1 <= u3/S
    l4 = rat_neg_lower(n * q2 + p2, q2, q2 - p2, q2, scale)   # (n + x2)^(x2 - 1) >= l4/S
    lo = Fraction(n * l1 * gA, u2 * gB)
    hi = Fraction(u3 * gA, n * l4 * gB)
    assert lo <= hi
    if claim_lo is None or claim_hi is None:
        d = _claim_digits(hi - lo)
    claim_lo = _decimal_floor(lo, d) if claim_lo is None else _frac(claim_lo, "claim_lo")
    claim_hi = _decimal_ceil(hi, d) if claim_hi is None else _frac(claim_hi, "claim_hi")
    cert = BohrMollerupGammaRatioCert(
        x1=x1, x2=x2, n=n, blocks=blocks, block=block, scale=scale, q=q, a1=a1, a2=a2,
        l1=l1, u2=u2, u3=u3, l4=l4, lo=lo, hi=hi, claim_lo=claim_lo, claim_hi=claim_hi,
    )
    # THE refusal: the claim must be implied by the certificate, exactly.
    if not cert.key_lo_holds(gA, gB):
        raise ValueError(
            f"REFUSED: claim_lo = {claim_lo} ({float(claim_lo):.12g}) is ABOVE the certified "
            f"lower bound lo = {float(lo):.12g} at n = {n}; the kernel comparison key_lo is "
            f"false.  Lower the claim or raise n (width ~ {float(hi - lo):.3e}).")
    if not cert.key_hi_holds(gA, gB):
        raise ValueError(
            f"REFUSED: claim_hi = {claim_hi} ({float(claim_hi):.12g}) is BELOW the certified "
            f"upper bound hi = {float(hi):.12g} at n = {n}; the kernel comparison key_hi is "
            f"false.  Raise the claim or raise n (width ~ {float(hi - lo):.3e}).")
    if claim_lo > claim_hi:
        raise ValueError(f"REFUSED: claim_lo = {claim_lo} > claim_hi = {claim_hi}")
    return cert


def certify_bohr_mollerup_gamma_ratio_point(family, pt, name):
    """``spec = family.special[1](pt)`` is a dict with ``x1``, ``x2``, ``n`` and optional
    ``claim_lo``, ``claim_hi``, ``scale``, ``block``.  Returns ``(CertifiedInstance, n_checks)``;
    ``n_checks = 6`` (the four root brackets and the two kernel comparisons)."""
    spec = dict(family.special[1](pt))
    cert = bohr_mollerup_gamma_ratio_certificate(
        spec.pop("x1"), spec.pop("x2"), spec.pop("n"), **spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 6


# --------------------------------------------------------------------------------------
# Lean rendering.
# --------------------------------------------------------------------------------------


def _decimal_str(x: Fraction) -> str | None:
    """``x`` as a terminating decimal string (``2.174``), or None when it has none."""
    d = x.denominator
    k = 0
    while d % 10 == 0:
        d //= 10
        k += 1
    while d % 2 == 0:
        d //= 2
        k += 1
    while d % 5 == 0:
        d //= 5
        k += 1
    if d != 1 or k == 0:
        return None
    s = f"{x.numerator * 10 ** k // x.denominator:0{k + 1}d}"
    return f"{s[:-k]}.{s[-k:]}"


def _real_rat(x: Fraction) -> str:
    """A nonnegative rational as a real literal: ``(2 : ℝ)``, ``(2.174 : ℝ)``, ``((1 : ℝ) / 3)``.

    Terminating decimals are spelled as decimal literals (the hand-built statement's
    ``2.1753``); other rationals as a quotient of integer literals."""
    x = Fraction(x)
    if x < 0:
        raise ValueError(f"a Gamma ratio of positive arguments is positive; bound {x} < 0")
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    dec = _decimal_str(x)
    if dec is not None:
        return f"({dec} : ℝ)"
    return f"(({x.numerator} : ℝ) / {x.denominator})"


def _gamma_arg(x: Fraction) -> str:
    """The argument of ``Real.Gamma``: ``(3 / 8)`` (elaborated at ℝ by the expected type)."""
    return f"({x.numerator} / {x.denominator})"


def _ratio(c: BohrMollerupGammaRatioCert) -> str:
    return f"Real.Gamma {_gamma_arg(c.x1)} / Real.Gamma {_gamma_arg(c.x2)}"


def _statement(c: BohrMollerupGammaRatioCert) -> str:
    r = _ratio(c)
    return f"{_real_rat(c.claim_lo)} ≤ {r} ∧ {r} ≤ {_real_rat(c.claim_hi)}"


def _x_plus_k(x: Fraction) -> str:
    """``((7 : ℝ) / 8 + k)`` -- the product's factor, spelled as ``Gamma_ratio_bounds`` spells it."""
    return f"(({x.numerator} : ℝ) / {x.denominator} + k)"


def _shift_pow(n: int, x: Fraction) -> str:
    """``((n : ℝ) + a / q) ^ ((a : ℝ) / q - 1)`` -- the ``(n + x)^(x - 1)`` factor."""
    return (f"(({n} : ℝ) + {x.numerator} / {x.denominator}) ^ "
            f"(({x.numerator} : ℝ) / {x.denominator} - 1)")


def _n_pow(n: int, x: Fraction) -> str:
    """``(n : ℝ) ^ ((a : ℝ) / q)`` -- the ``n^x`` factor."""
    return f"({n} : ℝ) ^ (({x.numerator} : ℝ) / {x.denominator})"


def _key_lo(c: BohrMollerupGammaRatioCert, gA: str, gB: str) -> str:
    return (f"{c.claim_lo.numerator} * {c.u2} * {gB} ≤ "
            f"{c.claim_lo.denominator} * {c.n} * {c.l1} * {gA}")


def _key_hi(c: BohrMollerupGammaRatioCert, gA: str, gB: str) -> str:
    return (f"{c.claim_hi.denominator} * {c.u3} * {gA} ≤ "
            f"{c.claim_hi.numerator} * {c.n} * {c.l4} * {gB}")


def _render_instance(c: BohrMollerupGammaRatioCert, nm: str,
                     rec_depth: int | None = None) -> tuple[list[str], int]:
    """The twelve declarations of one instance.  ``rec_depth`` prefixes each of the six
    ``decide +kernel`` lemmas with ``set_option maxRecDepth <rec_depth> in``; the emitted proofs do
    not need it (the kernel's depth is bounded by the block), but a FAILING ``key_lo`` / ``key_hi``
    formats its message under the elaborator's default depth and runs out while doing so (a failing
    root bracket does not), so the negative controls set it to record a readable rejection."""
    P = _PRELUDE_NS
    opt = f"set_option maxRecDepth {rec_depth} in" if rec_depth is not None else None

    def decide_lemma(doc: str | None, head: str) -> None:
        if opt is not None:
            L.append(opt)
        if doc is not None:
            L.append(doc)
        L.append(head)

    n, C, K, q, S = c.n, c.blocks, c.block, c.q, c.scale
    x1, x2 = c.x1, c.x2
    p1, q1 = x1.numerator, x1.denominator
    p2, q2 = x2.numerator, x2.denominator
    gA, gB = f"{nm}_gA", f"{nm}_gB"
    prod_lhs = (f"(∏ k ∈ Finset.range {n}, {_x_plus_k(x2)} / {_x_plus_k(x1)})")
    stmt = _statement(c)
    ratio = _ratio(c)
    L: list[str] = []
    L.append(f"/-! ### `{nm}`: `{_real_rat(c.claim_lo)} ≤ Γ({x1}) / Γ({x2}) ≤ {_real_rat(c.claim_hi)}` "
             f"at `n = {n}` (`{C}` blocks of `{K}`), brackets at scale `{S}` -/")
    L.append("")
    L.append(f"/-- `∏_{{k<{n}}} ({q} k + {c.a2})`, in `{C}` blocks of `{K}`. Only the kernel evaluates it. -/")
    L.append(f"def {gA} : ℕ :=")
    L.append(f"  ∏ c ∈ Finset.range {C}, ∏ j ∈ Finset.range {K}, ({q} * ({K} * c + j) + {c.a2})")
    L.append("")
    L.append(f"/-- `∏_{{k<{n}}} ({q} k + {c.a1})`, in `{C}` blocks of `{K}`. -/")
    L.append(f"def {gB} : ℕ :=")
    L.append(f"  ∏ c ∈ Finset.range {C}, ∏ j ∈ Finset.range {K}, ({q} * ({K} * c + j) + {c.a1})")
    L.append("")
    L.append(f"lemma {gA}_eq : (∏ k ∈ Finset.range {n}, ({q} * k + {c.a2})) = {gA} := by")
    L.append(f"  rw [show ({n} : ℕ) = {C} * {K} from rfl, {P}.prod_range_chunk]")
    L.append("  rfl")
    L.append("")
    L.append(f"lemma {gB}_eq : (∏ k ∈ Finset.range {n}, ({q} * k + {c.a1})) = {gB} := by")
    L.append(f"  rw [show ({n} : ℕ) = {C} * {K} from rfl, {P}.prod_range_chunk]")
    L.append("  rfl")
    L.append("")
    L.append(f"lemma {nm}_P_eq : {prod_lhs} = ({gA} : ℝ) / {gB} := by")
    L.append(f"  rw [← {gA}_eq, ← {gB}_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]")
    L.append("  refine Finset.prod_congr rfl fun k _ => ?_")
    L.append(f"  have h1 : ({p1} : ℝ) / {q1} + k ≠ 0 := by positivity")
    L.append(f"  have h1' : ({q} : ℝ) * k + {c.a1} ≠ 0 := by positivity")
    L.append("  push_cast")
    L.append("  field_simp")
    L.append("  ring")
    L.append("")
    L.append(f"lemma {gB}_pos : 0 < {gB} := by")
    L.append(f"  unfold {gB}")
    L.append("  exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by omega")
    L.append("")
    decide_lemma("/-- `LOn u2 gB ≤ LOd n l1 gA`: the lower claim against the certified lower bound. -/",
                 f"lemma {nm}_key_lo : {_key_lo(c, gA, gB)} := by")
    L.append("  decide +kernel")
    L.append("")
    decide_lemma("/-- `HId u3 gA ≤ HIn n l4 gB`: the upper claim against the certified upper bound. -/",
                 f"lemma {nm}_key_hi : {_key_hi(c, gA, gB)} := by")
    L.append("  decide +kernel")
    L.append("")
    # The four root brackets (scale S), each a kernel-decided Nat fact under a transport lemma.
    decide_lemma(None, f"lemma {nm}_hA : ({c.l1} : ℝ) / {S} ≤ {_shift_pow(n, x1)} := by")
    L.append(f"  have := {P}.rpow_rat_neg_div_lower {n * q1 + p1} {q1} {q1 - p1} {q1} {c.l1} {S}")
    L.append("    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)")
    L.append("  convert this using 2")
    L.append("  all_goals norm_num")
    L.append("")
    decide_lemma(None, f"lemma {nm}_hB : {_n_pow(n, x2)} ≤ ({c.u2} : ℝ) / {S} := by")
    L.append(f"  have := {P}.rpow_div_upper {n} {p2} {q2} {c.u2} {S} (by norm_num) (by norm_num)")
    L.append("    (by decide +kernel)")
    L.append("  convert this using 2")
    L.append("  all_goals norm_num")
    L.append("")
    decide_lemma(None, f"lemma {nm}_hC : {_n_pow(n, x1)} ≤ ({c.u3} : ℝ) / {S} := by")
    L.append(f"  have := {P}.rpow_div_upper {n} {p1} {q1} {c.u3} {S} (by norm_num) (by norm_num)")
    L.append("    (by decide +kernel)")
    L.append("  convert this using 2")
    L.append("  all_goals norm_num")
    L.append("")
    decide_lemma(None, f"lemma {nm}_hD : ({c.l4} : ℝ) / {S} ≤ {_shift_pow(n, x2)} := by")
    L.append(f"  have := {P}.rpow_rat_neg_div_lower {n * q2 + p2} {q2} {q2 - p2} {q2} {c.l4} {S}")
    L.append("    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)")
    L.append("  convert this using 2")
    L.append("  all_goals norm_num")
    L.append("")
    # The real-number argument for ABSTRACT gA gB.
    L.append(f"/-- The real-number argument for abstract `gA gB : ℕ`, so that no tactic tries to")
    L.append(f"evaluate the products. -/")
    L.append(f"theorem {nm}_aux (gA gB : ℕ) (gB_pos : 0 < gB)")
    L.append(f"    (P_eq : {prod_lhs} = (gA : ℝ) / gB)")
    L.append(f"    (key_lo : {_key_lo(c, 'gA', 'gB')})")
    L.append(f"    (key_hi : {_key_hi(c, 'gA', 'gB')}) :")
    L.append(f"    {stmt} := by")
    L.append(f"  obtain ⟨hlo, hhi⟩ := {P}.Gamma_ratio_bounds {n} (by norm_num)")
    L.append(f"    (x₁ := {p1} / {q1}) (x₂ := {p2} / {q2}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    L.append("  rw [P_eq] at hlo hhi")
    L.append("  clear P_eq")
    L.append("  push_cast at hlo hhi")
    L.append("  have hgA : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA")
    L.append("  have hgB : (0 : ℝ) < gB := Nat.cast_pos.mpr gB_pos")
    L.append(f"  have hY : (0 : ℝ) < {_n_pow(n, x2)} := by positivity")
    L.append(f"  have hD' : (0 : ℝ) < {_shift_pow(n, x2)} := by positivity")
    L.append(f"  have hkey1 : ({c.claim_lo.numerator} : ℝ) * {c.u2} * gB ≤ "
             f"{c.claim_lo.denominator} * {n} * {c.l1} * gA := by")
    L.append("    exact_mod_cast key_lo")
    L.append(f"  have hkey2 : ({c.claim_hi.denominator} : ℝ) * {c.u3} * gA ≤ "
             f"{c.claim_hi.numerator} * {n} * {c.l4} * gB := by")
    L.append("    exact_mod_cast key_hi")
    L.append("  clear key_lo key_hi gB_pos")
    L.append("  constructor")
    L.append(f"  · calc {_real_rat(c.claim_lo)}")
    L.append(f"        ≤ ({n} : ℝ) * (({c.l1} : ℝ) / {S}) / (({c.u2} : ℝ) / {S}) * ((gA : ℝ) / gB) := by")
    L.append(f"          rw [show ({n} : ℝ) * (({c.l1} : ℝ) / {S}) / (({c.u2} : ℝ) / {S}) * ((gA : ℝ) / gB)")
    L.append(f"              = ({n} * {c.l1} * gA) / ({c.u2} * gB) by field_simp]")
    L.append("          rw [le_div_iff₀ (by positivity)]")
    L.append("          linarith")
    L.append(f"      _ ≤ ({n} : ℝ) * {_shift_pow(n, x1)} / {_n_pow(n, x2)} * ((gA : ℝ) / gB) := by")
    L.append("          gcongr")
    L.append(f"          · exact {nm}_hA")
    L.append(f"          · exact {nm}_hB")
    L.append(f"      _ ≤ {ratio} := hlo")
    L.append(f"  · calc {ratio}")
    L.append(f"        ≤ {_n_pow(n, x1)} / (({n} : ℝ) * {_shift_pow(n, x2)}) * ((gA : ℝ) / gB) := hhi")
    L.append(f"      _ ≤ (({c.u3} : ℝ) / {S}) / (({n} : ℝ) * (({c.l4} : ℝ) / {S})) * ((gA : ℝ) / gB) := by")
    L.append("          gcongr")
    L.append(f"          · exact {nm}_hC")
    L.append(f"          · exact {nm}_hD")
    L.append(f"      _ ≤ {_real_rat(c.claim_hi)} := by")
    L.append(f"          rw [show (({c.u3} : ℝ) / {S}) / (({n} : ℝ) * (({c.l4} : ℝ) / {S})) * ((gA : ℝ) / gB)")
    L.append(f"              = ({c.u3} * gA) / ({n} * {c.l4} * gB) by field_simp]")
    L.append("          rw [div_le_iff₀ (by positivity)]")
    L.append("          linarith")
    L.append("")
    L.append(f"/-- `{_real_rat(c.claim_lo)} ≤ Γ({x1}) / Γ({x2}) ≤ {_real_rat(c.claim_hi)}`, about Mathlib's "
             f"`Real.Gamma`. -/")
    L.append(f"theorem {nm} :")
    L.append(f"    {stmt} :=")
    L.append(f"  {nm}_aux {gA} {gB} {gB}_pos {nm}_P_eq {nm}_key_lo {nm}_key_hi")
    L.append("")
    # gA_eq, gB_eq, P_eq, gB_pos, key_lo, key_hi, hA..hD, aux, the theorem: 12.
    return L, 12


@dataclass
class BohrMollerupGammaRatioEmitter(Emitter):
    """Emit blocked products, kernel comparisons, root brackets and the enclosure
    ``LO ≤ Real.Gamma x1 / Real.Gamma x2 ≤ HI``, against the ``BohrMollerupPrelude`` module
    (import it, or splice :func:`bohr_mollerup_prelude_body`)."""

    #: When set, each of the six ``decide +kernel`` lemmas is prefixed with
    #: ``set_option maxRecDepth <n> in``.  Off by default (the proofs do not need it); the negative
    #: controls turn it on so a failing ``key_lo`` / ``key_hi`` can format its message.
    decide_rec_depth: int | None = None

    def __post_init__(self):
        self.kind = "bohr_mollerup_gamma_ratio"
        self.requires_prelude = (
            f"{_PRELUDE_NS}.Gamma_ratio_bounds",
            f"{_PRELUDE_NS}.prod_range_chunk",
            f"{_PRELUDE_NS}.rpow_div_upper",
            f"{_PRELUDE_NS}.rpow_rat_neg_div_lower",
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: BohrMollerupGammaRatioCert = inst.payload  # type: ignore[assignment]
            L, n = _render_instance(cert, inst.lean_name, self.decide_rec_depth)
            lines.extend(L)
            lines.append(self.emit_gate(inst.lean_name, _statement(cert)))
            n_thm += n
        return "\n".join(lines) + "\n", n_thm


def bohr_mollerup_gamma_ratio_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Bohr-Mollerup Gamma-ratio family (kind ``bohr_mollerup_gamma_ratio``).

    ``spec: pt -> dict(x1=.., x2=.., n=.., claim_lo=.., claim_hi=.., scale=.., block=..)``
    (``claim_*``, ``scale`` and ``block`` optional).  Certification computes the products and
    brackets exactly and REFUSES a claim they do not imply."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("bohr_mollerup_gamma_ratio", spec),
        constants=dict(constants or {}),
    )


# --------------------------------------------------------------------------------------
# The prelude (single source; examples/bohr_mollerup_gamma_ratio/generate.py writes it).
# --------------------------------------------------------------------------------------


def bohr_mollerup_prelude_lean() -> str:
    """The ``BohrMollerupPrelude`` module as a complete Lean file (``import Mathlib`` first)."""
    return _PRELUDE


def bohr_mollerup_prelude_body() -> str:
    """The prelude without its ``import`` line, for splicing after the imports of a
    self-contained file (the negative-control harness's ``prelude``)."""
    return _PRELUDE.replace("import Mathlib\n", "", 1)


_PRELUDE = r'''import Mathlib

/-!
# BohrMollerupPrelude -- Bohr-Mollerup brackets for `Real.Gamma` at rational points

The once-proved part of Telperion's `bohr_mollerup_gamma_ratio` emitter.  Ported from the
hand-built CN-1 modules `GammaBounds.lean`, `GammaRatio.lean` and `RpowBounds.lean`
(github.com/DrMurphyIsIn/tenth-discriminant, Lean v4.34.1 / Mathlib d13f23b) to Lean v4.32.0 /
Mathlib v4.32.0.  Mathlib only.

Mathlib has `Real.convexOn_log_Gamma` (log-convexity of `Γ` on `(0, ∞)`) and the Bohr-Mollerup
inequality `Real.BohrMollerup.f_add_nat_le`.  From these, for `n ≥ 1` and `0 < x < 1`:

* `Gamma_add_le`:  `Γ(n + x) ≤ Γ(n) n^x`                     (two-point convexity at `n`, `n+1`);
* `Gamma_add_ge`:  `Γ(n+1) (n+x)^(x-1) ≤ Γ(n + x)`            (three-point convexity at `n+x`, `n+1+x`);
* `Gamma_add_nat_eq`: `Γ(n + x) = Γ(x) ∏_{k<n} (x + k)`;
* `Gamma_ratio_bounds`: for `0 < x₁, x₂ < 1`,
  `n (n+x₁)^(x₁-1) / n^x₂ · P ≤ Γ(x₁)/Γ(x₂) ≤ n^x₁ / (n (n+x₂)^(x₂-1)) · P`,
  `P = ∏_{k<n} (x₂+k)/(x₁+k)`; the two sides differ by the factor `(1+x₁/n)^(1-x₁) (1+x₂/n)^(1-x₂)`.

The kernel decides integer inequalities; two lemmas transport them to real `rpow` bounds:

* `rpow_div_upper`: `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`;
* `rpow_rat_neg_div_lower`: `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)`.

These two are a minimal inline copy of the general root-bracket prelude of the
`nat_root_bracket_table` kind; once that kind lands this module should import it instead.

`prod_range_chunk` splits a range product into `C` blocks of `K`, so that each kernel
evaluation stays shallow.

Nothing here is about class numbers or about RH.  conjecture1_proved = False.
-/

set_option autoImplicit false

namespace BohrMollerupPrelude

open Real

/-- `Γ(n + x) = Γ(x) ∏_{k<n} (x + k)` for `x > 0`. -/
lemma Gamma_add_nat_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma ((n : ℝ) + x) = Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ,
      show (n : ℝ) + 1 + x = ((n : ℝ) + x) + 1 by ring, Gamma_add_one (by positivity)]
    ring

lemma log_Gamma_add_one {y : ℝ} (hy : 0 < y) :
    log (Gamma (y + 1)) = log (Gamma y) + log y := by
  rw [Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm]

/-- Upper bound: `Γ(n + x) ≤ Γ(n) n^x` for `n ≠ 0`, `0 < x ≤ 1`. -/
lemma Gamma_add_le (n : ℕ) (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Gamma ((n : ℝ) + x) ≤ Gamma n * (n : ℝ) ^ x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h := Real.BohrMollerup.f_add_nat_le (f := log ∘ Gamma) convexOn_log_Gamma
    (fun {y} hy => log_Gamma_add_one hy) hn hx hx1
  simp only [Function.comp_apply] at h
  have hG : 0 < Gamma ((n : ℝ) + x) := Gamma_pos_of_pos (by positivity)
  have hGn : 0 < Gamma n := Gamma_pos_of_pos hn'
  rw [← exp_log hG, ← exp_log (by positivity : 0 < Gamma n * (n : ℝ) ^ x)]
  apply exp_le_exp.mpr
  rw [log_mul hGn.ne' (rpow_pos_of_pos hn' x).ne', log_rpow hn']
  linarith

/-- Lower bound: `Γ(n+1) (n + x)^(x - 1) ≤ Γ(n + x)` for `0 < x < 1`. -/
lemma Gamma_add_ge (n : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Gamma ((n : ℝ) + 1) * ((n : ℝ) + x) ^ (x - 1) ≤ Gamma ((n : ℝ) + x) := by
  have hnx : (0 : ℝ) < n + x := by positivity
  have hnx1 : (0 : ℝ) < n + 1 + x := by positivity
  have hc := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hnx) (Set.mem_Ioi.mpr hnx1) hx.le
    (by linarith : 0 ≤ 1 - x) (by ring : x + (1 - x) = 1)
  simp only [Function.comp_apply, smul_eq_mul] at hc
  rw [show x * ((n : ℝ) + x) + (1 - x) * ((n : ℝ) + 1 + x) = n + 1 by ring] at hc
  have h2 : log (Gamma ((n : ℝ) + 1 + x)) = log (Gamma (n + x)) + log (n + x) := by
    rw [show (n : ℝ) + 1 + x = (n + x) + 1 by ring]
    exact log_Gamma_add_one hnx
  rw [h2] at hc
  have hG := Gamma_pos_of_pos hnx
  have hG1 : 0 < Gamma ((n : ℝ) + 1) := Gamma_pos_of_pos (by positivity)
  rw [← exp_log hG, ← exp_log (by positivity : 0 < Gamma ((n : ℝ) + 1) * ((n : ℝ) + x) ^ (x - 1))]
  apply exp_le_exp.mpr
  rw [log_mul hG1.ne' (rpow_pos_of_pos hnx _).ne', log_rpow hnx]
  linarith

/-- The ratio `Γ(x₁)/Γ(x₂)` enclosed by elementary functions of `n` times the exact rational
`P = ∏_{k<n} (x₂+k)/(x₁+k)`. -/
theorem Gamma_ratio_bounds (n : ℕ) (hn : n ≠ 0) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁' : x₁ < 1)
    (hx₂ : 0 < x₂) (hx₂' : x₂ < 1) :
    (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) / (n : ℝ) ^ x₂ * (∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k))
        ≤ Gamma x₁ / Gamma x₂ ∧
    Gamma x₁ / Gamma x₂ ≤ (n : ℝ) ^ x₁ / ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1))
        * (∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hP1 : 0 < ∏ k ∈ Finset.range n, (x₁ + k) := Finset.prod_pos fun k _ => by positivity
  have hP2 : 0 < ∏ k ∈ Finset.range n, (x₂ + k) := Finset.prod_pos fun k _ => by positivity
  have hP : 0 < ∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k) := Finset.prod_pos fun k _ => by positivity
  have hG2 := Gamma_pos_of_pos hx₂
  have hGn := Gamma_pos_of_pos hn'
  have hGn1 : 0 < Gamma ((n : ℝ) + x₁) := Gamma_pos_of_pos (by positivity)
  have hGn2 : 0 < Gamma ((n : ℝ) + x₂) := Gamma_pos_of_pos (by positivity)
  have e1 := Gamma_add_nat_eq hx₁ n
  have e2 := Gamma_add_nat_eq hx₂ n
  have hratio : Gamma x₁ / Gamma x₂
      = Gamma ((n : ℝ) + x₁) / Gamma ((n : ℝ) + x₂) * ∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k) := by
    rw [Finset.prod_div_distrib, e1, e2]
    field_simp
    try ring
  have hA := Gamma_add_ge n hx₁ hx₁'
  rw [Gamma_add_one hn'.ne'] at hA
  have hB := Gamma_add_le n hn hx₂ hx₂'.le
  have hC := Gamma_add_le n hn hx₁ hx₁'.le
  have hD := Gamma_add_ge n hx₂ hx₂'
  rw [Gamma_add_one hn'.ne'] at hD
  rw [hratio]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hP.le
    rw [div_le_div_iff₀ (by positivity) hGn2]
    calc (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) * Gamma ((n : ℝ) + x₂)
        ≤ (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) * (Gamma n * (n : ℝ) ^ x₂) := by gcongr
      _ = ((n : ℝ) * Gamma n * ((n : ℝ) + x₁) ^ (x₁ - 1)) * (n : ℝ) ^ x₂ := by ring
      _ ≤ Gamma ((n : ℝ) + x₁) * (n : ℝ) ^ x₂ := by gcongr
  · apply mul_le_mul_of_nonneg_right _ hP.le
    rw [div_le_div_iff₀ hGn2 (by positivity)]
    calc Gamma ((n : ℝ) + x₁) * ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1))
        ≤ (Gamma n * (n : ℝ) ^ x₁) * ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1)) := by gcongr
      _ = (n : ℝ) ^ x₁ * ((n : ℝ) * Gamma n * ((n : ℝ) + x₂) ^ (x₂ - 1)) := by ring
      _ ≤ (n : ℝ) ^ x₁ * Gamma ((n : ℝ) + x₂) := by gcongr

/-! ### Root brackets (a minimal copy of the `nat_root_bracket_table` prelude) -/

/-- `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`. -/
lemma rpow_div_upper (m p q U S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hU : m ^ p * S ^ q ≤ U ^ q) : (m : ℝ) ^ ((p : ℝ) / q) ≤ (U : ℝ) / S := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast hU

/-- `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)`. -/
lemma rpow_rat_neg_div_lower (a b p q L S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * a ^ p ≤ b ^ p * S ^ q) : (L : ℝ) / S ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ (-((p : ℝ) / q))) ^ q = (b : ℝ) ^ p / (a : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hab.le, Real.rpow_natCast, div_pow, inv_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hL

/-! ### Chunking -/

/-- A range product over `C * K` terms as `C` blocks of `K`. -/
lemma prod_range_chunk {M : Type*} [CommMonoid M] (f : ℕ → M) (C K : ℕ) :
    ∏ i ∈ Finset.range (C * K), f i
      = ∏ c ∈ Finset.range C, ∏ n ∈ Finset.range K, f (K * c + n) := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.prod_range_succ, ← ih, show (C + 1) * K = C * K + K by ring, Finset.prod_range_add,
      mul_comm K C]

end BohrMollerupPrelude
'''


if __name__ == "__main__":
    # --- self-test: the hand-built instance's numbers, a refusal, and the emitted Lean ---
    c = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 8000)
    print("n = 8000:", c.l1, c.u2, c.u3, c.l4)
    print(f"  enclosure [{float(c.lo):.9f}, {float(c.hi):.9f}]  width {float(c.hi - c.lo):.3e}")
    print(f"  claim {c.claim_lo} .. {c.claim_hi}")
    assert (c.l1, c.u2, c.u3, c.l4) == (3635432077, 2601379650496946, 29084308668980, 325168010868)
    try:
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 8000, claim_lo="2.1754", claim_hi="2.1755")
        raise SystemExit("ERROR: the C6 control (LO = 2.1754) was NOT refused")
    except ValueError as e:
        print("  correctly REFUSED:", e)
    c = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 400)
    L, _ = _render_instance(c, "gamma_3_8_over_7_8")
    print("\n".join(L))

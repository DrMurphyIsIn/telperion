"""nat_root_bracket_table emitter (kind ``nat_root_bracket_table``) -- kernel-checked rational
brackets of a rational power ``m^(±p/q)``, singly and as blocked range-sum tables.

The shape (CN-1 emitter survey phase 2, item N1; the hand-built template is the CN-1
formalization's ``CN1/Numerics/RpowBounds.lean`` + the generated ``ZetaTables.lean`` and the
rational-base lemma of ``GammaRatio.lean``).  A real bracket ``L/S <= x <= U/S`` of
``x = m^(-p/q)`` is EXACTLY the pair of natural-number facts

    L^q * m^p <= S^q        and        S^q <= U^q * m^p,

which the Lean kernel decides on literals (``decide +kernel``; ``Nat.pow``/``Nat.mul``/``Nat.ble``
are GMP-accelerated in the kernel).  Once-proved transport lemmas in the ``NatRootBracket``
prelude (:func:`nat_root_bracket_prelude_lean`) lift each fact to the real ``rpow`` bound:

* natural base, negative exponent:  ``rpow_neg_div_lower/upper``  (``L/S <= m^(-p/q) <= U/S``);
* natural base, positive exponent:  ``rpow_div_lower/upper``      (``L^q <= m^p S^q <= U^q``);
* rational base ``a/b``, either sign: ``rpow_rat_[neg_]div_lower/upper``.

Two faces share one certificate kind:

* **single** (the ``K = 1`` face): one bracket of one power, three theorems per instance
  (``<n>_lo_fact``, ``<n>_hi_fact`` by ``decide +kernel``; ``<n>`` the real conjunction);
* **table** (the new face): for ``sigma = p/q > 0`` and ``M = C * K``, per block ``c < C`` two
  ``List ℕ`` of ``K`` brackets of ``(K*c + n + 1)^(-p/q)`` at scale ``S``, a kernel-decided
  ``∀ n < K`` fact per list, a kernel-decided block sum per list, and the two real theorems

      <n>_lo : L_tot / S <= ∑ i ∈ range M, ((i:ℝ) + 1)^(-(p/q))      <n>_hi : ... <= U_tot / S

  assembled by ``sum_block_lo_neg/hi_neg`` (a block of brackets bounds a block of the sum),
  ``sum_range_chunk`` (``range (C*K)`` as ``C`` blocks of ``K``) and ``linarith``.  The kernel's
  recursion depth is bounded by the block size ``K``, never by ``M``.

Python computes every bracket in EXACT integer arithmetic: the integer ``q``-th root is Newton's
method on integers (``nat_iroot``; no floats, no decrement loop), and every emitted fact is
re-checked exactly before emission (Layer 1).  The kernel re-decides each fact (Layer 2), so
nothing numeric is trusted from Python; a forged table entry or a forged ``U := L`` makes the
corresponding ``_fact`` false and the kernel rejects it.

Trust: ``decide +kernel`` only; no ``native_decide``, no ``sorry``, no ``axiom``, no heartbeat
or recursion-depth overrides (the default block of 200 needs none on Lean v4.32.0; see the
design note for the measured limits).

``conjecture1_proved = False``.  These are finite arithmetic facts about rational powers and
their partial sums; nothing here is about RH or class numbers.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

#: Default scale (10 decimal digits), the CN-1 ZetaTables choice.
DEFAULT_SCALE = 10 ** 10
#: Default block size: known to work on v4.34.1 (CN-1) and re-measured on v4.32.0.
DEFAULT_BLOCK = 200
#: Largest block size accepted.  Measured on Lean v4.32.0 / Mathlib v4.32.0 (design note,
#: "Depth measurement"): the `∀ n < K` fact and the range-K sum both pass with the default
#: maxRecDepth for K = 200, 300, 500, 1000, 1500; at K = 2000 the `List ℕ` literal itself
#: exceeds the elaborator's recursion depth (default and 4000).  The cap is the largest
#: measured-good value, not beyond it.
MAX_BLOCK = 1500
#: Largest number of blocks in one table (one file; sharding across files is future work).
MAX_BLOCKS = 64

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


# --------------------------------------------------------------------------------------
# Exact integer arithmetic.
# --------------------------------------------------------------------------------------

def nat_iroot(x: int, q: int) -> int:
    """``floor(x ** (1/q))`` for naturals ``x``, ``q >= 1`` by integer Newton iteration.

    Starts from the power of two ``2^ceil(bits/q) >= x^(1/q)`` and iterates
    ``r <- ((q-1) r + x // r^(q-1)) // q``, which decreases monotonically to the floor root;
    the result is then verified exactly (``r^q <= x < (r+1)^q``).  No floats anywhere."""
    if x < 0 or q < 1:
        raise ValueError(f"nat_iroot needs x >= 0 and q >= 1, got x={x}, q={q}")
    if x < 2:
        return x
    if q == 1:
        return x
    r = 1 << ((x.bit_length() + q - 1) // q)
    while True:
        nr = ((q - 1) * r + x // r ** (q - 1)) // q
        if nr >= r:
            break
        r = nr
    # Newton from above lands on the floor root; the two fix-up loops are a guard that runs
    # at most once each (they are not the algorithm).
    while r ** q > x:
        r -= 1
    while (r + 1) ** q <= x:
        r += 1
    assert r ** q <= x < (r + 1) ** q
    return r


def nat_root_bracket(num: int, den: int, p: int, q: int, scale: int, sign: int) -> tuple[int, int]:
    """The tightest ``(lo, hi)`` with ``lo/S <= (num/den)^(sign * p/q) <= hi/S``, as naturals.

    For ``sign = -1`` the facts are ``lo^q num^p <= den^p S^q <= hi^q num^p``; for ``sign = +1``
    they are ``lo^q den^p <= num^p S^q <= hi^q den^p`` (``den = 1`` is the natural-base case).
    ``hi - lo <= 1``, with equality iff the power is not exactly ``lo/S``."""
    n, d = (num, den) if sign > 0 else (den, num)
    target = n ** p * scale ** q           # lo^q * d^p <= target <= hi^q * d^p
    X = target // d ** p
    lo = nat_iroot(X, q)
    hi = lo if lo ** q * d ** p == target else lo + 1
    assert lo ** q * d ** p <= target <= hi ** q * d ** p
    assert hi - lo <= 1
    return lo, hi


# --------------------------------------------------------------------------------------
# Certificates.
# --------------------------------------------------------------------------------------

@dataclass(frozen=True)
class NatRootBracketCert:
    """One bracket ``lo/scale <= (num/den)^(sign * p/q) <= hi/scale`` (the single face).

    All fields are Python ints; ``den == 1`` selects the natural-base lemmas.  The two
    kernel-decided facts are ``lo^q * A <= B`` and ``B <= hi^q * A`` with ``(A, B) =
    (num^p, den^p scale^q)`` for ``sign = -1`` and ``(den^p, num^p scale^q)`` for ``sign = +1``."""

    num: int
    den: int
    p: int
    q: int
    sign: int
    scale: int
    lo: int
    hi: int

    @property
    def face(self) -> str:
        return "single"


@dataclass(frozen=True)
class NatRootBracketTableCert:
    """Blocked brackets of ``(i + 1)^(-p/q)`` for ``i < n_blocks * block`` (the table face).

    ``lo_blocks[c][n]`` and ``hi_blocks[c][n]`` bracket ``(block*c + n + 1)^(-p/q)`` at ``scale``;
    ``lo_sums``/``hi_sums`` are the per-block sums and ``lo_total``/``hi_total`` their totals,
    so ``lo_total/scale <= ∑_{i<M} (i+1)^(-p/q) <= hi_total/scale``."""

    p: int
    q: int
    scale: int
    block: int
    n_blocks: int
    lo_blocks: tuple[tuple[int, ...], ...]
    hi_blocks: tuple[tuple[int, ...], ...]
    lo_sums: tuple[int, ...]
    hi_sums: tuple[int, ...]
    lo_total: int
    hi_total: int

    @property
    def face(self) -> str:
        return "table"

    @property
    def terms(self) -> int:
        return self.block * self.n_blocks


def _nat(v, what: str, *, minimum: int = 0) -> int:
    """An exact natural (``>= minimum``) from an int / sympy Integer / Fraction with
    denominator 1; floats and non-integers are REFUSED."""
    if isinstance(v, bool):
        raise ValueError(f"nat_root_bracket_table REFUSED: {what} is a bool")
    if isinstance(v, (float, sp.Float)):
        raise ValueError(f"nat_root_bracket_table REFUSED: {what} is a float ({v!r}); "
                         "give an exact integer")
    if isinstance(v, Fraction):
        if v.denominator != 1:
            raise ValueError(f"nat_root_bracket_table REFUSED: {what} = {v} is not an integer")
        v = v.numerator
    elif isinstance(v, sp.Basic):
        if not v.is_Integer:
            raise ValueError(f"nat_root_bracket_table REFUSED: {what} = {v} is not an integer")
        v = int(v)
    elif not isinstance(v, int):
        raise ValueError(f"nat_root_bracket_table REFUSED: {what} = {v!r} is not an integer")
    if v < minimum:
        raise ValueError(f"nat_root_bracket_table REFUSED: {what} = {v} is below {minimum}")
    return int(v)


def _base(base) -> tuple[int, int]:
    """``(num, den)`` in lowest terms, both ``>= 1``, from an int, a ``(num, den)`` pair, a
    ``Fraction`` or a sympy Rational."""
    if isinstance(base, (float, sp.Float)):
        raise ValueError(f"nat_root_bracket_table REFUSED: base {base!r} is a float")
    if isinstance(base, tuple):
        if len(base) != 2:
            raise ValueError(f"nat_root_bracket_table REFUSED: base pair {base!r} is not (num, den)")
        num, den = _nat(base[0], "base numerator"), _nat(base[1], "base denominator")
    elif isinstance(base, Fraction):
        num, den = base.numerator, base.denominator
    elif isinstance(base, sp.Basic):
        if not base.is_Rational:
            raise ValueError(f"nat_root_bracket_table REFUSED: base {base} is not rational")
        num, den = int(base.p), int(base.q)
    else:
        num, den = _nat(base, "base"), 1
    if num <= 0 or den <= 0:
        raise ValueError(f"nat_root_bracket_table REFUSED: base {num}/{den} must be positive "
                         "(a zero or negative base carries no rpow content for these lemmas)")
    f = Fraction(num, den)
    return f.numerator, f.denominator


def nat_root_bracket_certificate(base, p, q, *, scale: int = DEFAULT_SCALE, sign: int = -1,
                                 lo=None, hi=None) -> NatRootBracketCert:
    """Certify ``lo/scale <= base^(sign * p/q) <= hi/scale`` (the single face).

    ``base`` is a positive integer, a ``(num, den)`` pair or an exact rational; ``p, q >= 1``;
    ``sign`` is ``-1`` (default) or ``+1``; ``scale >= 1``.  When ``lo``/``hi`` are omitted the
    tightest naturals are computed; a supplied endpoint is CHECKED exactly against the same
    integer fact the kernel will decide and REFUSED if it fails (the forge case) -- a supplied
    endpoint may be looser than the tightest one, never tighter."""
    num, den = _base(base)
    p = _nat(p, "exponent numerator p", minimum=1)
    q = _nat(q, "root index q", minimum=1)
    S = _nat(scale, "scale", minimum=1)
    if isinstance(sign, bool) or not isinstance(sign, int) or sign not in (-1, 1):
        raise ValueError(f"nat_root_bracket_table REFUSED: sign must be -1 or +1, got {sign!r}")
    tlo, thi = nat_root_bracket(num, den, p, q, S, sign)
    n, d = (num, den) if sign > 0 else (den, num)
    target = n ** p * S ** q
    L = tlo if lo is None else _nat(lo, "claimed lo")
    U = thi if hi is None else _nat(hi, "claimed hi")
    if not (L ** q * d ** p <= target):
        raise ValueError(
            f"nat_root_bracket_table REFUSED: claimed lo = {L} fails {L}^{q} * {d}^{p} <= "
            f"{n}^{p} * {S}^{q} (the tightest valid lo is {tlo}); the kernel's _lo_fact would be false")
    if not (target <= U ** q * d ** p):
        raise ValueError(
            f"nat_root_bracket_table REFUSED: claimed hi = {U} fails {n}^{p} * {S}^{q} <= "
            f"{U}^{q} * {d}^{p} (the tightest valid hi is {thi}); the kernel's _hi_fact would be false")
    return NatRootBracketCert(num=num, den=den, p=p, q=q, sign=sign, scale=S, lo=L, hi=U)


def nat_root_bracket_table_certificate(p, q, terms, *, scale: int = DEFAULT_SCALE,
                                       block: int = DEFAULT_BLOCK) -> NatRootBracketTableCert:
    """Certify the blocked table for ``∑_{i < terms} (i + 1)^(-p/q)`` at ``scale`` in blocks of
    ``block`` (the table face; negative exponent, the PROVED CN-1 transport).

    REFUSES ``p < 1``, ``q < 1``, ``scale < 1``, ``block < 1``, ``block > MAX_BLOCK`` (the
    measured kernel-depth cap), ``terms`` not a positive multiple of ``block``, and more than
    ``MAX_BLOCKS`` blocks."""
    p = _nat(p, "exponent numerator p", minimum=1)
    q = _nat(q, "root index q", minimum=1)
    S = _nat(scale, "scale", minimum=1)
    K = _nat(block, "block size", minimum=1)
    M = _nat(terms, "number of terms", minimum=1)
    if K > MAX_BLOCK:
        raise ValueError(f"nat_root_bracket_table REFUSED: block size {K} exceeds the measured "
                         f"kernel-depth cap MAX_BLOCK = {MAX_BLOCK}")
    if M % K != 0:
        raise ValueError(f"nat_root_bracket_table REFUSED: terms = {M} is not a multiple of the "
                         f"block size {K} (the range sum is chunked as C * K)")
    C = M // K
    if C > MAX_BLOCKS:
        raise ValueError(f"nat_root_bracket_table REFUSED: {C} blocks exceed MAX_BLOCKS = "
                         f"{MAX_BLOCKS}; split the sum across files")
    lo_blocks, hi_blocks, lo_sums, hi_sums = [], [], [], []
    for c in range(C):
        los, his = [], []
        for n in range(K):
            m = K * c + n + 1
            lo, hi = nat_root_bracket(m, 1, p, q, S, -1)
            # The exact facts the kernel will decide, re-checked here (Layer 1).
            assert lo ** q * m ** p <= S ** q <= hi ** q * m ** p
            los.append(lo)
            his.append(hi)
        lo_blocks.append(tuple(los))
        hi_blocks.append(tuple(his))
        lo_sums.append(sum(los))
        hi_sums.append(sum(his))
    return NatRootBracketTableCert(
        p=p, q=q, scale=S, block=K, n_blocks=C,
        lo_blocks=tuple(lo_blocks), hi_blocks=tuple(hi_blocks),
        lo_sums=tuple(lo_sums), hi_sums=tuple(hi_sums),
        lo_total=sum(lo_sums), hi_total=sum(hi_sums))


def certify_nat_root_bracket_table_point(family, pt, name):
    """``spec = family.special[1](pt)`` is a dict.  Table face: ``p, q, terms`` and optional
    ``scale, block``.  Single face: ``base, p, q`` and optional ``scale, sign, lo, hi``.
    Returns ``(CertifiedInstance, n_checks)`` with ``n_checks`` the number of kernel-decided
    facts (2 for a single bracket; 4 per block for a table)."""
    spec = dict(family.special[1](pt))
    if "terms" in spec:
        cert = nat_root_bracket_table_certificate(spec.pop("p"), spec.pop("q"), spec.pop("terms"),
                                                  **spec)
        n_checks = 4 * cert.n_blocks
    else:
        cert = nat_root_bracket_certificate(spec.pop("base"), spec.pop("p"), spec.pop("q"), **spec)
        n_checks = 2
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


# --------------------------------------------------------------------------------------
# Lean rendering.
# --------------------------------------------------------------------------------------

def _exponent(p: int, q: int, sign: int) -> str:
    """The exponent as the prelude lemmas state it: ``-((p : ℝ) / q)`` or ``((p : ℝ) / q)``.
    A consumer must use this SAME expression (or `convert ... using 2 <;> norm_num`)."""
    return f"(-(({p} : ℝ) / {q}))" if sign < 0 else f"(({p} : ℝ) / {q})"


def _power(cert: NatRootBracketCert) -> str:
    base = f"({cert.num} : ℝ)" if cert.den == 1 else f"(({cert.num} : ℝ) / {cert.den})"
    return f"{base} ^ {_exponent(cert.p, cert.q, cert.sign)}"


def _single_statement(cert: NatRootBracketCert) -> str:
    x = _power(cert)
    return f"({cert.lo} : ℝ) / {cert.scale} ≤ {x} ∧ {x} ≤ ({cert.hi} : ℝ) / {cert.scale}"


def _single_facts(cert: NatRootBracketCert) -> tuple[str, str]:
    """The two ℕ facts exactly as the prelude lemma hypotheses state them."""
    num, den, p, q, S, L, U = cert.num, cert.den, cert.p, cert.q, cert.scale, cert.lo, cert.hi
    if den == 1:
        if cert.sign < 0:   # rpow_neg_div_lower/upper
            return (f"{L} ^ {q} * {num} ^ {p} ≤ {S} ^ {q}", f"{S} ^ {q} ≤ {U} ^ {q} * {num} ^ {p}")
        return (f"{L} ^ {q} ≤ {num} ^ {p} * {S} ^ {q}", f"{num} ^ {p} * {S} ^ {q} ≤ {U} ^ {q}")
    if cert.sign < 0:       # rpow_rat_neg_div_lower/upper
        return (f"{L} ^ {q} * {num} ^ {p} ≤ {den} ^ {p} * {S} ^ {q}",
                f"{den} ^ {p} * {S} ^ {q} ≤ {U} ^ {q} * {num} ^ {p}")
    return (f"{L} ^ {q} * {den} ^ {p} ≤ {num} ^ {p} * {S} ^ {q}",
            f"{num} ^ {p} * {S} ^ {q} ≤ {U} ^ {q} * {den} ^ {p}")


def _render_single(cert: NatRootBracketCert, nm: str) -> tuple[list[str], int]:
    L: list[str] = []
    lo_fact, hi_fact = _single_facts(cert)
    base_txt = f"{cert.num}" if cert.den == 1 else f"{cert.num}/{cert.den}"
    L.append(f"-- {nm}: nat_root_bracket_table single bracket of ({base_txt})^({'-' if cert.sign < 0 else ''}"
             f"{cert.p}/{cert.q}) at scale {cert.scale}; the two ℕ facts are kernel-decided "
             "and the prelude lemmas lift them to ℝ.  conjecture1_proved = False.")
    L.append(f"theorem {nm}_lo_fact : {lo_fact} := by decide +kernel")
    L.append(f"theorem {nm}_hi_fact : {hi_fact} := by decide +kernel")
    if cert.den == 1:
        lem = "rpow_neg_div" if cert.sign < 0 else "rpow_div"
        pos = "(by norm_num) " * (3 if cert.sign < 0 else 2)
        args = f"{cert.num} {cert.p} {cert.q}"
    else:
        lem = "rpow_rat_neg_div" if cert.sign < 0 else "rpow_rat_div"
        pos = "(by norm_num) " * 4
        args = f"{cert.num} {cert.den} {cert.p} {cert.q}"
    L.append(
        f"theorem {nm} : {_single_statement(cert)} := by\n"
        f"  have h1 := {lem}_lower {args} {cert.lo} {cert.scale} {pos}{nm}_lo_fact\n"
        f"  have h2 := {lem}_upper {args} {cert.hi} {cert.scale} {pos}{nm}_hi_fact\n"
        f"  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩")
    return L, 3


def _lean_list(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def _table_sum(cert: NatRootBracketTableCert) -> str:
    return (f"∑ i ∈ Finset.range {cert.terms}, ((i : ℝ) + 1) ^ "
            f"{_exponent(cert.p, cert.q, -1)}")


def _table_statement(cert: NatRootBracketTableCert) -> str:
    s = _table_sum(cert)
    return f"({cert.lo_total} : ℝ) / {cert.scale} ≤ {s} ∧ {s} ≤ ({cert.hi_total} : ℝ) / {cert.scale}"


def _render_table_side(cert: NatRootBracketTableCert, nm: str, side: str) -> str:
    p, q, S, K, C = cert.p, cert.q, cert.scale, cert.block, cert.n_blocks
    e = _exponent(p, q, -1)
    lemma = f"sum_block_{side}_neg"
    tot = cert.lo_total if side == "lo" else cert.hi_total
    s = _table_sum(cert)
    stmt = f"({tot} : ℝ) / {S} ≤ {s}" if side == "lo" else f"{s} ≤ ({tot} : ℝ) / {S}"
    out = [f"theorem {nm}_{side} : {stmt} := by",
           f"  set f : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ {e} with hf",
           f"  have hf' : ∀ i, f i = ((i : ℝ) + 1) ^ {e} := fun i => by rw [hf]"]
    for c in range(C):
        out.append(f"  have h{c} := {lemma} f {e} {p} {q} {S} {K} ({K} * {c}) (by norm_num) "
                   f"(by norm_num) rfl hf' {nm}_{side}_{c} {nm}_{side}_{c}_fact")
        out.append(f"  rw [{nm}_{side}_{c}_sum] at h{c}")
    out.append(f"  rw [show ({C * K} : ℕ) = {C} * {K} from rfl, sum_range_chunk f {C} {K}]")
    out.append("  rw [" + ", ".join(["Finset.sum_range_succ"] * C) + ", Finset.sum_range_zero, zero_add]")
    out.append("  push_cast at " + " ".join(f"h{c}" for c in range(C)) + " ⊢")
    out.append("  linarith")
    return "\n".join(out)


def _render_table(cert: NatRootBracketTableCert, nm: str) -> tuple[list[str], int]:
    p, q, S, K, C = cert.p, cert.q, cert.scale, cert.block, cert.n_blocks
    L: list[str] = []
    n_thm = 0
    L.append(f"-- {nm}: nat_root_bracket_table for ∑_(i<{cert.terms}) (i+1)^(-{p}/{q}) at scale {S} "
             f"in {C} blocks of {K}: per block two List ℕ of brackets, two kernel-decided "
             "∀-facts, two kernel-decided block sums; the prelude transports them to ℝ.  "
             "conjecture1_proved = False.")
    for c in range(C):
        lo, hi = f"{nm}_lo_{c}", f"{nm}_hi_{c}"
        L.append(f"def {lo} : List ℕ := {_lean_list(cert.lo_blocks[c])}")
        L.append(f"def {hi} : List ℕ := {_lean_list(cert.hi_blocks[c])}")
        L.append(f"theorem {lo}_fact : ∀ n < {K}, ({lo}.getD n 0) ^ {q} * ({K} * {c} + n + 1) ^ {p} "
                 f"≤ {S} ^ {q} := by\n  decide +kernel")
        L.append(f"theorem {hi}_fact : ∀ n < {K}, {S} ^ {q} ≤ ({hi}.getD n 0) ^ {q} * "
                 f"({K} * {c} + n + 1) ^ {p} := by\n  decide +kernel")
        L.append(f"theorem {lo}_sum : ∑ n ∈ Finset.range {K}, {lo}.getD n 0 = {cert.lo_sums[c]} := by\n"
                 "  decide +kernel")
        L.append(f"theorem {hi}_sum : ∑ n ∈ Finset.range {K}, {hi}.getD n 0 = {cert.hi_sums[c]} := by\n"
                 "  decide +kernel")
        n_thm += 4
    L.append(_render_table_side(cert, nm, "lo"))
    L.append(_render_table_side(cert, nm, "hi"))
    L.append(f"/-- `{nm}`: the kernel-checked bracket of the partial sum (exact-evaluated pre-emission). -/\n"
             f"theorem {nm} : {_table_statement(cert)} := ⟨{nm}_lo, {nm}_hi⟩")
    n_thm += 3
    return L, n_thm


def _statement(cert) -> str:
    """The instance's final theorem type, single-sourced for the statement gate."""
    if isinstance(cert, NatRootBracketTableCert):
        return _table_statement(cert)
    return _single_statement(cert)


@dataclass
class NatRootBracketTableEmitter(Emitter):
    """Emit kernel-decided ℕ root-bracket facts (single brackets and blocked ``List ℕ`` tables)
    and their real ``rpow`` transports, against the ``NatRootBracket`` prelude (import it, or
    splice :func:`nat_root_bracket_prelude_body`)."""

    def __post_init__(self):
        self.kind = "nat_root_bracket_table"
        self.requires_prelude = (
            "NatRootBracket.rpow_neg_div_lower",
            "NatRootBracket.sum_block_lo_neg",
            "NatRootBracket.sum_range_chunk",
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open NatRootBracket", ""]
        n_thm = 0
        for inst in fam.instances:
            cert = inst.payload
            if not _IDENT.match(inst.lean_name):
                raise ValueError(f"nat_root_bracket_table: bad Lean name {inst.lean_name!r}")
            if isinstance(cert, NatRootBracketTableCert):
                L, n = _render_table(cert, inst.lean_name)
            elif isinstance(cert, NatRootBracketCert):
                L, n = _render_single(cert, inst.lean_name)
            else:
                raise TypeError(f"nat_root_bracket_table: unexpected payload {type(cert).__name__}")
            lines.extend(L)
            lines.append(self.emit_gate(inst.lean_name, _statement(cert)))
            n_thm += n
        return "\n".join(lines) + "\n", n_thm


def nat_root_bracket_table_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a nat-root-bracket family (kind ``nat_root_bracket_table``).

    ``spec: pt -> dict``.  Table face: ``dict(p=, q=, terms=, scale=, block=)``; single face:
    ``dict(base=, p=, q=, scale=, sign=, lo=, hi=)`` (``scale``, ``block``, ``sign``, ``lo``,
    ``hi`` optional).  Certification computes every bracket exactly in Python; the kernel
    re-decides every emitted fact."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("nat_root_bracket_table", spec),
        constants=dict(constants or {}),
    )


def nat_root_bracket_prelude_lean() -> str:
    """The full ``NatRootBracket.lean`` module text (header, ``import Mathlib``, body)."""
    return _PRELUDE


def nat_root_bracket_prelude_body() -> str:
    """The prelude without its ``import`` line, for splicing after the imports of a
    self-contained file (the negative-control harness's ``prelude``)."""
    return _PRELUDE.replace("import Mathlib\n", "", 1)


# The NatRootBracket prelude (single source; examples/nat_root_bracket_table/generate.py writes it).
_PRELUDE = r'''/-
NatRootBracket -- the once-proved transport lemmas behind Telperion's
`nat_root_bracket_table` emitter.

Ported from the hand-built CN-1 formalization (tenth-discriminant, CN1/Numerics/RpowBounds.lean
and the rational-base lemma of CN1/Numerics/GammaRatio.lean; Lean v4.34.1 / Mathlib d13f23b) to
Lean v4.32.0 / Mathlib v4.32.0.  Mathlib only.  The statements are unchanged; the three
rational-base variants that CN-1 did not need (`rpow_rat_neg_div_upper`, `rpow_rat_div_lower`,
`rpow_rat_div_upper`) are added by the same proof.

The kernel decides integer inequalities on literals (`decide +kernel`, GMP-accelerated `Nat`);
these lemmas transport them to real `rpow` brackets:

* `rpow_div_lower/upper`:          `L^q ≤ m^p S^q`      gives `L/S ≤ m^(p/q)`;
                                    `m^p S^q ≤ U^q`      gives `m^(p/q) ≤ U/S`;
* `rpow_neg_div_lower/upper`:      `L^q m^p ≤ S^q`      gives `L/S ≤ m^(-p/q)`;
                                    `S^q ≤ U^q m^p`      gives `m^(-p/q) ≤ U/S`;
* `rpow_rat_div_lower/upper`:      `L^q b^p ≤ a^p S^q`  gives `L/S ≤ (a/b)^(p/q)`;
                                    `a^p S^q ≤ U^q b^p`  gives `(a/b)^(p/q) ≤ U/S`;
* `rpow_rat_neg_div_lower/upper`:  `L^q a^p ≤ b^p S^q`  gives `L/S ≤ (a/b)^(-p/q)`;
                                    `b^p S^q ≤ U^q a^p`  gives `(a/b)^(-p/q) ≤ U/S`;
* `sum_block_lo_neg/hi_neg`: a block of `K` such brackets, read from a `List ℕ` by `getD`,
  bounds a block of the range sum `∑ (i+1)^(-p/q)`;
* `sum_range_chunk`: a range sum over `C * K` terms as `C` blocks of `K`.

conjecture1_proved = False.
-/
import Mathlib

set_option autoImplicit false

namespace NatRootBracket

/-- `L^q ≤ m^p S^q` gives `L/S ≤ m^(p/q)`. -/
lemma rpow_div_lower (m p q L S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q ≤ m ^ p * S ^ q) : (L : ℝ) / S ≤ (m : ℝ) ^ ((p : ℝ) / q) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow, div_le_iff₀ (by positivity)]
  exact_mod_cast hL

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

/-- `L^q m^p ≤ S^q` gives `L/S ≤ m^(-p/q)` (for `0 < m`). -/
lemma rpow_neg_div_lower (m p q L S : ℕ) (hm : 0 < m) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * m ^ p ≤ S ^ q) : (L : ℝ) / S ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hm'.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ (-((p : ℝ) / q))) ^ q = 1 / (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hm'.le, Real.rpow_natCast, one_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hL

/-- `S^q ≤ U^q m^p` gives `m^(-p/q) ≤ U/S` (for `0 < m`). -/
lemma rpow_neg_div_upper (m p q U S : ℕ) (hm : 0 < m) (hq : 0 < q) (hS : 0 < S)
    (hU : S ^ q ≤ U ^ q * m ^ p) : (m : ℝ) ^ (-((p : ℝ) / q)) ≤ (U : ℝ) / S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hm'.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ (-((p : ℝ) / q))) ^ q = 1 / (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hm'.le, Real.rpow_natCast, one_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hU

/-- `L^q b^p ≤ a^p S^q` gives `L/S ≤ (a/b)^(p/q)` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_div_lower (a b p q L S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * b ^ p ≤ a ^ p * S ^ q) : (L : ℝ) / S ≤ ((a : ℝ) / b) ^ ((p : ℝ) / q) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ ((p : ℝ) / q) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ ((p : ℝ) / q)) ^ q = (a : ℝ) ^ p / (b : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, div_mul_cancel₀ _ hq', Real.rpow_natCast,
      div_pow]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hL

/-- `a^p S^q ≤ U^q b^p` gives `(a/b)^(p/q) ≤ U/S` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_div_upper (a b p q U S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hU : a ^ p * S ^ q ≤ U ^ q * b ^ p) : ((a : ℝ) / b) ^ ((p : ℝ) / q) ≤ (U : ℝ) / S := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ ((p : ℝ) / q) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ ((p : ℝ) / q)) ^ q = (a : ℝ) ^ p / (b : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, div_mul_cancel₀ _ hq', Real.rpow_natCast,
      div_pow]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hU

/-- `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)` (for `0 < a`, `0 < b`). -/
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

/-- `b^p S^q ≤ U^q a^p` gives `(a/b)^(-p/q) ≤ U/S` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_neg_div_upper (a b p q U S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hU : b ^ p * S ^ q ≤ U ^ q * a ^ p) : ((a : ℝ) / b) ^ (-((p : ℝ) / q)) ≤ (U : ℝ) / S := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ (-((p : ℝ) / q))) ^ q = (b : ℝ) ^ p / (a : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hab.le, Real.rpow_natCast, div_pow, inv_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hU

/-- A range sum over `C * K` terms as `C` blocks of `K`. -/
lemma sum_range_chunk {M : Type*} [AddCommMonoid M] (f : ℕ → M) (C K : ℕ) :
    ∑ i ∈ Finset.range (C * K), f i
      = ∑ c ∈ Finset.range C, ∑ n ∈ Finset.range K, f (K * c + n) := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.sum_range_succ, ← ih, show (C + 1) * K = C * K + K by ring, Finset.sum_range_add,
      mul_comm K C]

/-- Transport of a block of lower brackets to a block of a real range sum (negative exponent
`e = -p/q`).  `f` is the summand, `base` the block offset. -/
lemma sum_block_lo_neg (f : ℕ → ℝ) (e : ℝ) (p q S K base : ℕ) (hq : 0 < q) (hS : 0 < S)
    (he : e = -((p : ℝ) / q)) (hf : ∀ i, f i = ((i : ℝ) + 1) ^ e) (lo : List ℕ)
    (h : ∀ n < K, (lo.getD n 0) ^ q * (base + n + 1) ^ p ≤ S ^ q) :
    ((∑ n ∈ Finset.range K, lo.getD n 0 : ℕ) : ℝ) / S ≤ ∑ n ∈ Finset.range K, f (base + n) := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : n < K := Finset.mem_range.mp hn
  have := rpow_neg_div_lower (base + n + 1) p q (lo.getD n 0) S (by omega) hq hS (h n hn')
  have hcast : ((base + n : ℕ) : ℝ) + 1 = ((base + n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hf, he, hcast]
  exact this

/-- Transport of a block of upper brackets to a block of a real range sum (negative exponent
`e = -p/q`). -/
lemma sum_block_hi_neg (f : ℕ → ℝ) (e : ℝ) (p q S K base : ℕ) (hq : 0 < q) (hS : 0 < S)
    (he : e = -((p : ℝ) / q)) (hf : ∀ i, f i = ((i : ℝ) + 1) ^ e) (hi : List ℕ)
    (h : ∀ n < K, S ^ q ≤ (hi.getD n 0) ^ q * (base + n + 1) ^ p) :
    ∑ n ∈ Finset.range K, f (base + n) ≤ ((∑ n ∈ Finset.range K, hi.getD n 0 : ℕ) : ℝ) / S := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : n < K := Finset.mem_range.mp hn
  have := rpow_neg_div_upper (base + n + 1) p q (hi.getD n 0) S (by omega) hq hS (h n hn')
  have hcast : ((base + n : ℕ) : ℝ) + 1 = ((base + n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hf, he, hcast]
  exact this

end NatRootBracket
'''

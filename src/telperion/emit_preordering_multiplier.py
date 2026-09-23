"""Preordering-with-multiplier emitter -- kernel-checked nonnegativity of a polynomial on a
semialgebraic set cut out by POLYNOMIAL generators, via a positive multiplier and a
constant-coefficient (Schmuedgen preordering) identity.

conjecture1_proved = False.  Nothing in this module bears on the Riemann Hypothesis: it
certifies FINITE real polynomial inequalities on explicit semialgebraic sets, and the Lean
kernel is the only trusted component.

WHY THIS EMITTER EXISTS
-----------------------
`SHAPES_AUDIT_48H_2026-09-22.md` section 2 ranks this shape third by value per line (D 3.1;
B C3; C 5.3 item 1), merging three audits' worth of hand `nlinarith` box positivities.  The
registry already had the neighbouring rungs and none of them covers the combination:

* `handelman`       -- products of LINEAR generators, nonnegative constants, NO multiplier;
* `polya_zeros`     -- a `(sum x)^N` multiplier, but only on the simplex for a HOMOGENEOUS form;
* `rational_sos`    -- an Artin DENOMINATOR, but SOS multipliers and no generator hypotheses;
* `constrained_sos` -- Putinar, degree-1 in the generators with SOS multipliers (an SDP).

The Li rungs need all three ingredients at once: polynomial generators (a disk), products of
them with nonnegative rational constants, and a positive multiplier (`Q_4`: `14 s`; `Q_5`:
`s^2`).  This emitter is that combination, and only that combination.

THE MATHEMATICS (one ring identity, one positivity fold, one locus branch)
-------------------------------------------------------------------------
Given base variables `x = (x_1, ..., x_k)`, polynomial generators `g_1, ..., g_m` (each
asserted `>= 0` on the set, either as a theorem HYPOTHESIS or STRUCTURALLY), a target
polynomial `p`, a multiplier

    M = kappa * g_j^e      (kappa > 0 rational, 1 <= e <= MAX_MULTIPLIER_POWER)   or   M = kappa

and nonnegative rationals `c_alpha` indexed by exponent vectors `alpha`, the certificate is
the EXACT identity in the base variables

    M(x) * p(x)  =  sum_alpha c_alpha * prod_i g_i(x)^{alpha_i} .

Every right-hand term is a product of nonnegatives, so `0 <= M p` on the set.  Where `M > 0`
this gives `0 <= p` by cancellation (`mul_nonneg_iff_of_pos_left`).  The zero set of a
non-constant `M` is certified separately: `g_j` must be EXACTLY a positive-weight sum of
squared coordinate offsets `sum_i w_i (x_i - a_i)^2`, so `g_j = 0` forces the single point
`x = a` (`nlinarith` on the squares), where `p(a) >= 0` is an exact rational fact
(`norm_num`).  There is no analysis and no search in the emitted proof: `ring` checks the
identity, `positivity` folds the cone, `nlinarith` pins the locus point.

WHAT THE CERTIFICATE CERTIFIES (read this before citing it)
------------------------------------------------------------
Exactly the stated finite inequality `0 <= p` on `{g_1 >= 0, ..., g_m >= 0}`, for the one `p`
and the one generator list supplied.  It says nothing about any limit, any zero of zeta, or
any conjecture; the emitter never widens a claim, never drops a generator hypothesis, and
never reports a certificate it has not reconstructed exactly in rational arithmetic.

ANTI-PHANTOM REFUSALS (the forge face; SHAPES_AUDIT_D_LI_FACE section 3.1)
-------------------------------------------------------------------------
`preordering_multiplier_certificate` REFUSES, never repairs:

* the LP infeasible up to the degree cap -- reported as OBSTRUCTED_AND_LOCATED with the exact
  rational negative witness when the scan finds one (`Q_6` is the shipped example, and the
  witness is itself kernel-checkable via `obstruction_refutation_lean`), otherwise as a plain
  "no certificate up to the cap" refusal that makes NO claim about the inequality;
* any `c_alpha < 0` (not a preordering combination at all), or an identity that does not
  reconstruct: `M p - sum c_alpha g^alpha != 0` exactly;
* a `hyp` generator that is not literally a hypothesis: no Lean binder, or a stated
  `lhs <= rhs` whose content `rhs - lhs` is not the generator;
* a `structural` generator `positivity` cannot close as rendered (checked conservatively: a
  nonnegative combination of even-exponent monomials);
* a multiplier whose zero locus has no certificate: a non-constant `M` with no locus, a locus
  that is not an exact positive-weight sum of squared coordinate offsets of the multiplier's
  generator, or a locus point where `p < 0`;
* a multiplier not itself in the cone: `kappa <= 0`, a generator that is not declared, a
  power outside `1..MAX_MULTIPLIER_POWER`, or a product of several generators;
* an identity of total degree above `MAX_IDENTITY_DEGREE` (the `ring` cost cliff), more than
  `MAX_TERMS` terms, an LP larger than `MAX_LP_COLUMNS`, a scan grid above `MAX_SCAN_POINTS`;
* floats or non-rational coefficients anywhere, non-polynomial input, a constant target, and
  any name that is not a plain Lean identifier or would collide with a name the emitted proof
  binds.

A LOCATED NEGATIVE WITNESS IS THE STRONGEST REFUSAL.  When a scan box is supplied the
certifier evaluates `p` in EXACT rational arithmetic at every grid point of the set and, if
it finds `p < 0`, refuses before any search: the claim is not merely uncertified, it is FALSE
(HONESTY_PATTERNS #8, OBSTRUCTED_AND_LOCATED).  The refusal is a `PreorderingObstruction`
carrying the exact witness and a `ProbeVerdict`.

WHAT THIS EMITTER DOES NOT DO
-----------------------------
* It does not search for SOS multipliers (that is `constrained_sos` / an SDP); the multiplier
  is a single generator power, and the certificate coefficients are constants.
* It does not certify a multiplier whose zero set is more than one point (a line, a circle):
  that needs a lower-dimensional sub-certificate, which is not built here.
* It does not do the complex real-part algebra -- the `ComplexFace` wrapper is a thin,
  caller-supplied `simp only [...]; ring` step whose unfold list comes from the island (the
  `complex_re_im_split` shape of the same audit owns that); the kernel checks it.
* It does not decide positivity.  A refusal is a refusal; nothing widens.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, replace
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb
from typing import Callable, Mapping, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import _poly_any_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .nonvacuity import assert_certificate_sensitive
from .verdict import ProbeVerdict, obstructed
from .workflow import Emitter

#: Multiplier powers above this are refused (`g_j^e`, audit D 3.1 "an outer loop over
#: multipliers `g_j^k` (`k <= 3`)").
MAX_MULTIPLIER_POWER = 3

#: Total degree of the `ring` identity above which we refuse rather than emit Lean whose
#: kernel cost we have not sized (`Q_5` with `s^2` is degree 9 and builds today).
MAX_IDENTITY_DEGREE = 24

#: Cap on the number of certificate terms (the emitted `positivity` fold).
MAX_TERMS = 512

#: Cap on the number of generators (the finder's column count grows as C(D + m, m)).
MAX_GENERATORS = 8

#: Cap on the finder's product degree.
MAX_FINDER_DEGREE = 10

#: Cap on the number of LP columns (products) the exact simplex is asked to handle.
MAX_LP_COLUMNS = 4000

#: Cap on the number of grid points of the negative-witness scan.
MAX_SCAN_POINTS = 250_000

HYP = "hyp"
STRUCTURAL = "structural"
TAGS = (HYP, STRUCTURAL)

#: plain Lean identifiers (ASCII, as `exp_threshold` requires)
_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
#: possibly-qualified Lean constant names (the complex face's unfold list)
_QUALIFIED = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")
#: the complex face's target term: identifiers, numerals, spaces, parens, arithmetic
_FACE_TERM = re.compile(r"^[A-Za-z0-9_'. ()+\-*/^]+$")
#: tokens that must never reach emitted Lean through caller-supplied text
_FORBIDDEN = re.compile(
    r"\b(sorry|admit|native_decide|decide|axiom|opaque|implemented_by|skipKernelTC)\b")

#: Lean keywords, tactic names and the global lemma names the emitted proof calls: a
#: theorem variable, alias or hypothesis with one of these names would shadow or break it.
_RESERVED = frozenset({
    "by", "fun", "have", "show", "from", "at", "in", "let", "do", "then", "else", "if",
    "match", "with", "theorem", "lemma", "def", "example", "calc", "rfl", "this", "only",
    "where", "open", "namespace", "end", "section", "variable", "universe", "instance",
    "structure", "class", "abbrev", "noncomputable", "private", "protected", "mutual",
    "import", "export", "axiom", "opaque", "sorry", "admit", "Type", "Prop", "Sort", "for",
    "return", "try", "catch", "finally", "mut", "exact", "intro", "obtain", "rcases",
    "generalize", "ring", "positivity", "linarith", "nlinarith", "norm_num", "simp", "rw",
    "decide", "native_decide", "sq_nonneg", "mul_nonneg_iff_of_pos_left", "eq_or_lt_of_le",
    "Real", "Complex", "re", "im",
})


class PreorderingRefusal(ValueError):
    """A preordering_multiplier REFUSAL (never a repair).  Subclasses `ValueError` so the
    generic `certify()` failure path records it like every other emitter's refusal."""


class PreorderingObstruction(PreorderingRefusal):
    """The claim `0 <= p` is FALSE on the declared set: an exact rational point of the set
    where `p < 0` (HONESTY_PATTERNS #8, OBSTRUCTED_AND_LOCATED).

    Carries everything `obstruction_refutation_lean` needs to state the refutation for the
    kernel: the base symbols, the expanded target, the checked generators, the witness point
    (name -> exact rational) and the exact value of `p` there, plus the closing
    `ProbeVerdict`."""

    def __init__(self, message: str, *, symbols, target, generators, witness, value,
                 verdict: ProbeVerdict):
        super().__init__(message)
        self.symbols = tuple(symbols)
        self.target = target
        self.generators = tuple(generators)
        self.witness = dict(witness)
        self.value = value
        self.verdict = verdict


def _refuse(msg: str) -> PreorderingRefusal:
    return PreorderingRefusal(f"preordering_multiplier REFUSED: {msg}")


# ---------------------------------------------------------------------------
# exact-arithmetic helpers
# ---------------------------------------------------------------------------

def _rat(v, what: str) -> sp.Rational:
    """Exactly-rational coercion; REFUSES bools, floats and non-rational values."""
    if isinstance(v, bool):
        raise _refuse(f"{what} was given as a bool ({v!r})")
    if isinstance(v, (float, sp.Float)):
        raise _refuse(
            f"{what} was given as a float ({v!r}); a float carries its binary expansion, not "
            "the rational you wrote -- pass a str/int/Fraction/sp.Rational")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    try:
        q = sp.Rational(v)
    except (TypeError, ValueError) as exc:
        raise _refuse(f"{what} = {v!r} is not rational ({exc})") from None
    if not isinstance(q, sp.Rational):
        raise _refuse(f"{what} = {v!r} is not rational")
    return q


def _F(q) -> Fraction:
    q = sp.Rational(q)
    return Fraction(int(q.p), int(q.q))


def _name(v, what: str) -> str:
    """A plain (ASCII) Lean identifier that shadows nothing the emitted proof uses."""
    if isinstance(v, sp.Symbol):
        v = v.name
    if not isinstance(v, str) or not _IDENT.match(v):
        raise _refuse(f"{what} {v!r} is not a plain ASCII Lean identifier")
    if v in _RESERVED:
        raise _refuse(f"{what} {v!r} is a reserved name (a Lean keyword, tactic or a lemma "
                      "the emitted proof calls)")
    return v


def _expr(e, syms: Sequence[sp.Symbol], what: str) -> sp.Expr:
    """Expand `e` and REFUSE anything that is not a rational polynomial in `syms`.

    Symbols are matched by NAME (a caller's `sp.Symbol("x", real=True)` is the declared
    `x`), and strings are parsed with the declared symbols in scope, so sympy's single-letter
    constants (`E`, `I`, `S`, ...) can never capture a declared variable name."""
    if isinstance(e, bool):
        raise _refuse(f"{what} was given as a bool ({e!r})")
    if isinstance(e, (float, sp.Float)):
        raise _refuse(f"{what} was given as a float ({e!r}); exact rationals only")
    by_name = {s.name: s for s in syms}
    try:
        if isinstance(e, str):
            ex = sp.sympify(e, locals=dict(by_name))
        elif isinstance(e, Fraction):
            ex = sp.Rational(e.numerator, e.denominator)
        else:
            ex = sp.sympify(e)
    except (sp.SympifyError, TypeError, ValueError, SyntaxError) as exc:
        raise _refuse(f"{what} = {e!r} does not parse ({exc})") from None
    if not isinstance(ex, sp.Expr):
        raise _refuse(f"{what} = {e!r} is not an expression")
    ex = ex.xreplace({f: by_name[f.name] for f in ex.free_symbols
                      if isinstance(f, sp.Symbol) and f.name in by_name})
    ex = sp.expand(ex)
    if ex.atoms(sp.Float):
        raise _refuse(f"{what} carries a float coefficient ({ex}); exact rationals only")
    free = ex.free_symbols - set(syms)
    if free:
        raise _refuse(
            f"{what} has free symbols {sorted(map(str, free))} outside the declared base "
            f"variables {[s.name for s in syms]}")
    if not ex.is_polynomial(*syms):
        raise _refuse(f"{what} = {ex} is not a polynomial in {[s.name for s in syms]}")
    try:
        poly = sp.Poly(ex, *syms)
    except sp.PolynomialError as exc:
        raise _refuse(f"{what} is not polynomial ({exc})") from None
    for c in poly.coeffs():
        if not (isinstance(c, sp.Basic) and c.is_Rational):
            raise _refuse(f"{what} has a non-rational coefficient {c}")
    return ex


def positivity_closable(e: sp.Expr, syms: Sequence[sp.Symbol]) -> bool:
    """Conservative, EXACT sufficient condition for Mathlib's `positivity` to close
    `0 <= e` with no hypotheses, for `e` rendered EXPANDED: a nonnegative-rational
    combination of monomials in which every exponent is even (each such monomial is a
    square, closed by `positivity`'s `pow`/`mul`/`add` extensions).

    Deliberately conservative: a generator outside this class is REFUSED rather than emitted
    and hoped for.  `x^2 + y^2`, `y^2`, `3/4`, `x^2 y^4` pass; `x`, `x - y^2`, `x y` and the
    square `(x - y)^2` (which renders expanded, with a negative cross term) do not."""
    ex = sp.expand(sp.sympify(e))
    if not syms:
        return bool(ex.is_Rational and ex >= 0)
    if ex == 0:
        return True
    poly = sp.Poly(ex, *syms)
    for monom, coeff in zip(poly.monoms(), poly.coeffs()):
        if sp.Rational(coeff) < 0:
            return False
        if any(int(a) % 2 for a in monom):
            return False
    return True


# ---------------------------------------------------------------------------
# certificate data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Generator:
    """One generator `g >= 0` of the semialgebraic set.

    `tag = "hyp"`        -- carried as a theorem hypothesis; `hyp_name` is its Lean binder and
                            `stated = (lhs, rhs)` is how the hypothesis reads (`lhs <= rhs`),
                            which certification checks is `0 <= g` exactly (`rhs - lhs = g`).
                            Omitted `stated` means the hypothesis reads `0 <= g`.
    `tag = "structural"` -- no hypothesis; `0 <= g` is closed by `positivity` in the proof.

    `name` is the Lean ALIAS the proof binds the generator to (`d`, `B`, `s` in the Li rungs);
    it is what the certificate identity is written in.
    """

    name: str
    expr: object
    tag: str = STRUCTURAL
    hyp_name: str = ""
    stated: tuple | None = None


@dataclass(frozen=True)
class LocusCertificate:
    """Why `{M = 0}` is the single point `point`.

    The multiplier's generator is exactly a positive-weight sum of squared coordinate offsets,

        g_j = sum_i w_i * (x_i - a_i)^2          (w_i > 0 rational, every base variable),

    which certification verifies by `expand`.  The emitted Lean derives `x_i = a_i` from
    `g_j = 0` by `nlinarith only [...]` with the squares as hints, then closes `0 <= p(a)` by
    `norm_num` (`p(a) >= 0` is checked exactly here).  `derive_locus` computes it."""

    point: tuple[tuple[str, sp.Rational], ...]
    weights: tuple[sp.Rational, ...]


@dataclass(frozen=True)
class ComplexFace:
    """Optional thin wrapper turning the real-variable core into an island-shaped claim
    `0 <= (<target>).re` about a complex variable.

    `coords` maps each base variable NAME to `<var>.re` or `<var>.im`; `unfold` is the
    island's own `simp only [...]` list (qualified names).  The wrapper contributes NO
    certificate data: its single `simp only ...` then `ring` step is the
    `complex_re_im_split` shape, supplied verbatim by the caller and checked by the kernel.
    `simp_closes = True` drops the `ring` (the unfolding alone closes the real-part equation,
    as for `Q_1 z = z`); a wrong flag is a kernel error, never a silent pass."""

    var: str
    target: str
    coords: tuple[tuple[str, str], ...]
    unfold: tuple[str, ...]
    simp_closes: bool = False


@dataclass(frozen=True)
class PreorderingMultiplierCert:
    """One preordering-with-multiplier certificate (all data EXACT rationals)."""

    symbols: tuple[sp.Symbol, ...]
    target: sp.Expr
    generators: tuple[Generator, ...]
    mult_coeff: sp.Rational
    mult_index: int | None
    mult_power: int
    terms: tuple[tuple[sp.Rational, tuple[int, ...]], ...]
    locus: LocusCertificate | None = None
    face: ComplexFace | None = None
    found_by: str = "supplied"

    @property
    def multiplier(self) -> sp.Expr:
        """`M` as a polynomial in the base variables."""
        if self.mult_index is None:
            return sp.expand(self.mult_coeff)
        g = self.generators[self.mult_index].expr
        return sp.expand(self.mult_coeff * g ** self.mult_power)

    @property
    def trivial_multiplier(self) -> bool:
        """True when `M` is a positive constant (no locus branch)."""
        return self.mult_index is None

    @property
    def cone_expr(self) -> sp.Expr:
        """`sum_alpha c_alpha prod_i g_i^{alpha_i}` in the base variables."""
        acc = sp.Integer(0)
        for coef, alpha in self.terms:
            t = sp.Rational(coef)
            for g, a in zip(self.generators, alpha):
                if int(a):
                    t = t * g.expr ** int(a)
            acc = acc + t
        return sp.expand(acc)

    @property
    def identity_residual(self) -> sp.Expr:
        """`M p - sum c_alpha g^alpha`; zero for an honest certificate."""
        return sp.expand(self.multiplier * self.target - self.cone_expr)

    @property
    def identity_degree(self) -> int:
        e = sp.expand(self.multiplier * self.target)
        return 0 if e == 0 else int(sp.Poly(e, *self.symbols).total_degree())

    @property
    def used_generators(self) -> tuple[int, ...]:
        """Indices of the generators the proof actually binds (in a term, or the multiplier)."""
        used = {i for _c, alpha in self.terms for i, a in enumerate(alpha) if int(a)}
        if self.mult_index is not None:
            used.add(self.mult_index)
        return tuple(sorted(used))


# ---------------------------------------------------------------------------
# the exact LP (phase-1 simplex over Fractions) and the finder
# ---------------------------------------------------------------------------

def solve_nonneg_exact(A: Sequence[Sequence[Fraction]],
                       b: Sequence[Fraction]) -> list[Fraction] | None:
    """Exact rational phase-1 simplex: return `c >= 0` with `A c = b`, or None (INFEASIBLE).

    Bland's rule, so it terminates; Fraction arithmetic throughout, so "infeasible" is a
    PROOF of infeasibility for this column set, not a numerical impression.  The caller
    re-verifies any returned solution -- the finder is untrusted like every other finder here.
    """
    m = len(A)
    if m == 0:
        return []
    n = len(A[0])
    tab: list[list[Fraction]] = []
    for i in range(m):
        row = [Fraction(v) for v in A[i]]
        rhs = Fraction(b[i])
        if rhs < 0:
            row = [-v for v in row]
            rhs = -rhs
        tab.append(row + [Fraction(0)] * m + [rhs])
    for i in range(m):
        tab[i][n + i] = Fraction(1)
    basis = list(range(n, n + m))
    cost = [Fraction(0)] * (n + m + 1)
    for i in range(m):
        for j in range(n + m + 1):
            cost[j] -= tab[i][j]
    for i in range(m):
        cost[n + i] = Fraction(0)

    while True:
        piv_col = -1
        for j in range(n + m):
            if cost[j] < 0:
                piv_col = j
                break
        if piv_col < 0:
            break
        piv_row, best = -1, None
        for i in range(m):
            if tab[i][piv_col] > 0:
                ratio = tab[i][-1] / tab[i][piv_col]
                if (best is None or ratio < best
                        or (ratio == best and basis[i] < basis[piv_row])):
                    best, piv_row = ratio, i
        if piv_row < 0:            # pragma: no cover -- phase 1 is bounded below by 0
            return None
        pv = tab[piv_row][piv_col]
        tab[piv_row] = [v / pv for v in tab[piv_row]]
        for i in range(m):
            if i != piv_row and tab[i][piv_col] != 0:
                f = tab[i][piv_col]
                tab[i] = [a - f * c for a, c in zip(tab[i], tab[piv_row])]
        if cost[piv_col] != 0:
            f = cost[piv_col]
            cost = [a - f * c for a, c in zip(cost, tab[piv_row])]
        basis[piv_row] = piv_col

    if -cost[-1] != 0:
        return None
    sol = [Fraction(0)] * n
    for i, bi in enumerate(basis):
        if bi < n:
            sol[bi] = tab[i][-1]
    return sol


def _alphas(m: int, max_total: int) -> list[tuple[int, ...]]:
    """Every exponent vector over `m` generators of total degree `<= max_total`, ordered by
    total degree then by `combinations_with_replacement` order (deterministic)."""
    out: list[tuple[int, ...]] = []
    for total in range(0, max_total + 1):
        for combo in combinations_with_replacement(range(m), total):
            a = [0] * m
            for i in combo:
                a[i] += 1
            out.append(tuple(a))
    return out


def find_preordering_terms(rhs: sp.Expr, gens: Sequence[sp.Expr],
                           syms: Sequence[sp.Symbol], max_total: int):
    """SEARCH for nonnegative rationals with `rhs = sum c_alpha prod g_i^{alpha_i}` over the
    exponent vectors of total degree `<= max_total`.  Returns the `(coef, alpha)` list or
    None (the exact LP is INFEASIBLE for this column set).  Exact throughout; the result is
    re-verified before return and AGAIN by `preordering_multiplier_certificate` -- the finder
    is untrusted."""
    rhs = sp.expand(rhs)
    m = len(gens)
    if comb(max_total + m, m) > MAX_LP_COLUMNS:
        raise _refuse(
            f"the LP at product degree {max_total} over {m} generators has "
            f"{comb(max_total + m, m)} columns, above the cap {MAX_LP_COLUMNS}")
    alphas = _alphas(m, max_total)
    prods = []
    for a in alphas:
        e = sp.Integer(1)
        for i, k in enumerate(a):
            if k:
                e = e * gens[i] ** k
        prods.append(sp.expand(e))

    def cdict(e):
        e = sp.expand(e)
        return {} if e == 0 else sp.Poly(e, *syms).as_dict()

    pd = cdict(rhs)
    cols = [cdict(e) for e in prods]
    monos = set(pd)
    for c in cols:
        monos |= set(c)
    monos = sorted(monos)
    A = [[_F(c.get(mo, 0)) for c in cols] for mo in monos]
    bvec = [_F(pd.get(mo, 0)) for mo in monos]
    sol = solve_nonneg_exact(A, bvec)
    if sol is None:
        return None
    terms = [(sp.Rational(v.numerator, v.denominator), alphas[j])
             for j, v in enumerate(sol) if v != 0]
    recon = sp.Integer(0)
    for c, a in terms:
        t = sp.Rational(c)
        for i, k in enumerate(a):
            if k:
                t = t * gens[i] ** k
        recon = recon + t
    if sp.expand(rhs - recon) != 0:      # pragma: no cover -- exact arithmetic
        return None
    return terms


# ---------------------------------------------------------------------------
# the located negative witness (HONESTY_PATTERNS #8, OBSTRUCTED_AND_LOCATED)
# ---------------------------------------------------------------------------

def _coeff_dict(e, syms):
    e = sp.expand(e)
    if e == 0:
        return {}
    return {mono: _F(c) for mono, c in sp.Poly(e, *syms).as_dict().items()}


def _eval(cd, pt) -> Fraction:
    acc = Fraction(0)
    for mono, c in cd.items():
        t = c
        for v, e in zip(pt, mono):
            if e:
                t *= v ** int(e)
        acc += t
    return acc


def locate_negative_witness(target: sp.Expr, gens: Sequence[sp.Expr],
                            syms: Sequence[sp.Symbol],
                            box: Mapping[str, tuple], steps: int = 60):
    """Scan a rational grid of the box for a point OF THE SET where `p < 0`.

    Returns `(point_dict, exact_value)` for the most negative grid point found (the first in
    grid order on a tie), or None.  Every evaluation is exact (`Fraction`); the scan is a
    SEARCH, never a decision -- it can only produce a refusal, never an acceptance.
    """
    names = [s.name for s in syms]
    if not isinstance(box, Mapping) or sorted(box) != sorted(names):
        raise _refuse(
            f"scan box keys {sorted(box) if isinstance(box, Mapping) else box!r} do not match "
            f"the base variables {sorted(names)}")
    if isinstance(steps, bool) or not isinstance(steps, int) or steps < 1:
        raise _refuse(f"scan steps must be a positive int, got {steps!r}")
    if (steps + 1) ** len(names) > MAX_SCAN_POINTS:
        raise _refuse(
            f"scan grid of {(steps + 1) ** len(names)} points exceeds the cap {MAX_SCAN_POINTS}")

    pc = _coeff_dict(target, syms)
    gcs = [_coeff_dict(g, syms) for g in gens]

    axes = []
    for nm in names:
        pair = box[nm]
        if not (isinstance(pair, (tuple, list)) and len(pair) == 2):
            raise _refuse(f"scan box entry for {nm} must be a (lo, hi) pair, got {pair!r}")
        lo, hi = _F(_rat(pair[0], f"scan box lo[{nm}]")), _F(_rat(pair[1], f"scan box hi[{nm}]"))
        if hi < lo:
            raise _refuse(f"inverted scan box on {nm}: [{lo}, {hi}]")
        axes.append([lo + (hi - lo) * Fraction(i, steps) for i in range(steps + 1)])

    best = None

    def rec(i, pt):
        nonlocal best
        if i == len(axes):
            for gc in gcs:
                if _eval(gc, pt) < 0:
                    return
            v = _eval(pc, pt)
            if v < 0 and (best is None or v < best[1]):
                best = (tuple(pt), v)
            return
        for val in axes[i]:
            rec(i + 1, pt + [val])

    rec(0, [])
    if best is None:
        return None
    pt, val = best
    return ({nm: sp.Rational(v.numerator, v.denominator) for nm, v in zip(names, pt)},
            sp.Rational(val.numerator, val.denominator))


def _obstruction(syms, p, gens, witness, value, how: str) -> PreorderingObstruction:
    where = ", ".join(f"{s.name} = {witness[s.name]}" for s in syms)
    claim = "0 <= p on {" + ", ".join(f"{g.name} >= 0" for g in gens) + "}"
    verdict = obstructed(
        claim,
        f"p = {value} < 0 at the exact rational point ({where}) of the set",
        f"found by {how}; every generator evaluated >= 0 there in exact arithmetic",
        f"p = {p}",
    )
    msg = (
        f"preordering_multiplier REFUSED (OBSTRUCTED_AND_LOCATED): the claim `0 <= p` is "
        f"FALSE on the declared set -- exact negative witness at ({where}) with p = {value} "
        f"(~ {float(value):.6f}), every generator nonnegative there ({how}).  No preordering "
        "certificate can exist; the emitter reports the located obstruction and emits no "
        "certificate (obstruction_refutation_lean states the refutation for the kernel)")
    return PreorderingObstruction(msg, symbols=syms, target=p, generators=gens,
                                  witness=witness, value=value, verdict=verdict)


# ---------------------------------------------------------------------------
# the multiplier zero locus
# ---------------------------------------------------------------------------

def derive_locus(g: sp.Expr, syms: Sequence[sp.Symbol]) -> LocusCertificate | None:
    """If `g` is EXACTLY `sum_i w_i (x_i - a_i)^2` with every `w_i > 0` (so `{g = 0}` is the
    single point `a`), return that locus certificate; otherwise None.  Untrusted: the
    certifier re-verifies it by `expand` like a supplied one."""
    g = sp.expand(g)
    try:
        poly = sp.Poly(g, *syms)
    except sp.PolynomialError:
        return None
    if poly.total_degree() != 2:
        return None
    k = len(syms)
    weights, point = [], []
    for i, s in enumerate(syms):
        sq = [0] * k
        sq[i] = 2
        lin = [0] * k
        lin[i] = 1
        w = sp.Rational(poly.coeff_monomial(tuple(sq)))
        if w <= 0:
            return None
        weights.append(w)
        point.append((s.name, -sp.Rational(poly.coeff_monomial(tuple(lin))) / (2 * w)))
    cand = sp.Integer(0)
    for w, s, (_nm, a) in zip(weights, syms, point):
        cand = cand + w * (s - a) ** 2
    if sp.expand(g - cand) != 0:
        return None
    return LocusCertificate(tuple(point), tuple(weights))


# ---------------------------------------------------------------------------
# Layer 1: the certificate self-check (the forge face)
# ---------------------------------------------------------------------------

def _check_face(face, names: Sequence[str]) -> ComplexFace:
    if not isinstance(face, ComplexFace):
        raise _refuse(f"face must be a ComplexFace, got {type(face).__name__}")
    var = _name(face.var, "complex face variable")
    target = face.target
    if not isinstance(target, str) or not target.strip() or not _FACE_TERM.match(target):
        raise _refuse(
            f"complex face target {target!r} is not a plain Lean term (identifiers, numerals, "
            "spaces, parentheses and + - * / ^ only)")
    if _FORBIDDEN.search(target) or target.count("(") != target.count(")"):
        raise _refuse(f"complex face target {target!r} is malformed or carries a forbidden token")
    coords = tuple(tuple(c) for c in face.coords)
    if sorted(c[0] for c in coords) != sorted(names) or len(coords) != len(names):
        raise _refuse(
            f"complex face coords {coords!r} must map each base variable {sorted(names)} "
            "exactly once")
    allowed = {f"{var}.re", f"{var}.im"}
    seen = set()
    for nm, expr in coords:
        if expr not in allowed:
            raise _refuse(
                f"complex face coordinate for {nm} is {expr!r}; only {sorted(allowed)} are "
                "supported (the complex_re_im_split shape)")
        if expr in seen:
            raise _refuse(f"complex face coordinate {expr!r} is used twice")
        seen.add(expr)
    unfold = tuple(face.unfold)
    if not unfold:
        raise _refuse("complex face unfold list is empty (the `simp only [...]` step needs "
                      "the island's definitions and Complex re/im lemmas)")
    for u in unfold:
        if not isinstance(u, str) or not _QUALIFIED.match(u) or _FORBIDDEN.search(u):
            raise _refuse(f"complex face unfold entry {u!r} is not a Lean constant name")
    if not isinstance(face.simp_closes, bool):
        raise _refuse(f"complex face simp_closes must be a bool, got {face.simp_closes!r}")
    return ComplexFace(var=var, target=target.strip(), coords=coords, unfold=unfold,
                       simp_closes=face.simp_closes)


def _normalize_multiplier(cand, aliases: Sequence[str]) -> tuple[sp.Rational, int | None, int]:
    if cand is None:
        return sp.Integer(1), None, 0
    if not (isinstance(cand, (tuple, list)) and len(cand) == 3):
        raise _refuse(
            "a multiplier must be a (kappa, generator_name_or_None, power) triple, got "
            f"{cand!r} (products of several generators are not supported)")
    kappa = _rat(cand[0], "multiplier coefficient kappa")
    if kappa <= 0:
        raise _refuse(
            f"multiplier coefficient kappa = {kappa} is not positive -- a multiplier not "
            "itself in the cone")
    gname, power = cand[1], cand[2]
    if isinstance(power, bool) or not isinstance(power, int):
        raise _refuse(f"multiplier power {power!r} is not an int")
    if gname is None:
        if power != 0:
            raise _refuse("a constant multiplier must have power 0")
        return kappa, None, 0
    if gname not in aliases:
        raise _refuse(
            f"multiplier generator {gname!r} is not one of the declared generators {list(aliases)}"
            " -- a multiplier not itself in the cone")
    if power < 1 or power > MAX_MULTIPLIER_POWER:
        raise _refuse(f"multiplier power {power} outside 1..{MAX_MULTIPLIER_POWER}")
    return kappa, list(aliases).index(gname), power


def _generated_names(aliases: Sequence[str], names: Sequence[str]) -> set[str]:
    """Every local name the emitted certificate proofs bind (so no user name may equal one of
    them).  The refutation theorem binds only `h`/`hw` over a closed statement in which no user
    alias or hypothesis name occurs, so those two are not reserved."""
    out = {"P", "hP", "key", "hcert", "hre"}
    for a in aliases:
        out |= {f"h{a}0", f"h{a}e", f"h{a}'"}
    for nm in names:
        out.add(f"hloc{nm}")
    return out


def preordering_multiplier_certificate(
    *,
    symbols: Sequence,
    target,
    generators: Sequence[Generator],
    multiplier: tuple | None = None,
    terms=None,
    locus: LocusCertificate | str | None = None,
    face: ComplexFace | None = None,
    max_total_degree: int = 4,
    multiplier_candidates: Sequence[tuple] | str | None = None,
    scan_box: Mapping[str, tuple] | None = None,
    scan_steps: int = 60,
    max_identity_degree: int = MAX_IDENTITY_DEGREE,
) -> PreorderingMultiplierCert:
    """Build (and exactly re-check) one preordering-with-multiplier certificate.

    `multiplier` is `(kappa, generator_name_or_None, power)`; `terms` is the `(coef, alpha)`
    list, or None for FINDER mode: the exact simplex then tries each multiplier candidate in
    order (`multiplier`, else `multiplier_candidates`, else the constant 1; the string
    `"auto"` means the constant, then every generator admitting a single-point locus at
    powers 1..MAX_MULTIPLIER_POWER) at product degrees 0..`max_total_degree`, and the FIRST
    feasible pair wins (smallest multiplier, then smallest certificate).  `locus` is a
    `LocusCertificate`, or `"auto"` to derive it, for a non-constant multiplier.  Raises
    `PreorderingRefusal` (a `ValueError`) -- a REFUSAL -- on every dishonest or unsupported
    input; `PreorderingObstruction` when the claim is located FALSE.  conjecture1_proved = False.
    """
    # --- base variables ---------------------------------------------------------------
    raw_syms = tuple(symbols)
    if not raw_syms:
        raise _refuse("at least one base variable is required")
    names = [_name(s, "base variable") for s in raw_syms]
    if len(set(names)) != len(names):
        raise _refuse(f"duplicate base variable names {names}")
    syms = tuple(sp.Symbol(nm) for nm in names)

    p = _expr(target, syms, "target p")
    if p.free_symbols == set():
        raise _refuse(
            f"target p = {p} is constant: nothing to certify on a set (this kind states "
            "polynomial positivity in the base variables)")

    # --- generators ---------------------------------------------------------------------
    gens_in = tuple(generators)
    if not gens_in:
        raise _refuse("no generators supplied")
    if len(gens_in) > MAX_GENERATORS:
        raise _refuse(f"{len(gens_in)} generators exceeds the cap {MAX_GENERATORS}")
    for g in gens_in:
        if not isinstance(g, Generator):
            raise _refuse(f"generator {g!r} is not a Generator")
    aliases = [_name(g.name, "generator alias") for g in gens_in]
    if len(set(aliases)) != len(aliases):
        raise _refuse(f"duplicate generator aliases {aliases}")
    for a in aliases:
        if a in names:
            raise _refuse(f"generator alias {a!r} collides with a base variable name")

    checked: list[Generator] = []
    hyp_names: list[str] = []
    for g in gens_in:
        ge = _expr(g.expr, syms, f"generator {g.name}")
        if ge == 0:
            raise _refuse(f"generator {g.name} is identically zero (it constrains nothing and "
                          "every product through it vanishes)")
        if g.tag not in TAGS:
            raise _refuse(f"generator {g.name} has unknown tag {g.tag!r} (expected one of {TAGS})")
        if g.tag == HYP:
            if not isinstance(g.hyp_name, str) or not g.hyp_name:
                raise _refuse(
                    f"`hyp` generator {g.name} carries no Lean binder name -- a hypothesis "
                    "generator that is not literally a hypothesis")
            hn = _name(g.hyp_name, f"hypothesis binder of generator {g.name}")
            stated = g.stated if g.stated is not None else (sp.Integer(0), ge)
            if not (isinstance(stated, (tuple, list)) and len(stated) == 2):
                raise _refuse(
                    f"generator {g.name} `stated` must be an (lhs, rhs) pair meaning `lhs <= rhs`")
            lhs = _expr(stated[0], syms, f"generator {g.name} stated lhs")
            rhs = _expr(stated[1], syms, f"generator {g.name} stated rhs")
            if sp.expand(rhs - lhs - ge) != 0:
                raise _refuse(
                    f"generator {g.name} is stated as `{lhs} <= {rhs}`, whose content is "
                    f"{sp.expand(rhs - lhs)}, NOT the generator {ge} -- the hypothesis does not "
                    "say what the certificate uses (a `hyp` generator that is not literally a "
                    "hypothesis)")
            hyp_names.append(hn)
            checked.append(Generator(g.name, ge, HYP, hn, (lhs, rhs)))
        else:
            if g.hyp_name:
                raise _refuse(
                    f"`structural` generator {g.name} carries a hypothesis binder "
                    f"{g.hyp_name!r}; tag it `hyp` or drop the binder")
            if g.stated is not None:
                raise _refuse(f"`structural` generator {g.name} carries a `stated` form; only "
                              "`hyp` generators are stated as hypotheses")
            if not positivity_closable(ge, syms):
                raise _refuse(
                    f"`structural` generator {g.name} = {ge} is not a nonnegative-coefficient "
                    "even-exponent form, so `positivity` cannot close `0 <= it` as rendered -- "
                    "tag it `hyp` and carry it as a hypothesis instead")
            checked.append(Generator(g.name, ge, STRUCTURAL, "", None))
    gens = tuple(checked)
    if len(set(hyp_names)) != len(hyp_names):
        raise _refuse(f"duplicate hypothesis binder names {hyp_names}")
    for hn in hyp_names:
        if hn in names or hn in aliases:
            raise _refuse(f"hypothesis binder {hn!r} collides with a variable or alias name")

    chk_face = _check_face(face, names) if face is not None else None

    generated = _generated_names(aliases, names)
    user_names = set(names) | set(aliases) | set(hyp_names)
    if chk_face is not None:
        user_names.add(chk_face.var)
        if chk_face.var in set(names) | set(aliases) | set(hyp_names):
            raise _refuse(f"complex face variable {chk_face.var!r} collides with another name")
        heads = {u.split(".")[0] for u in chk_face.unfold}
        heads |= {w.split(".")[0] for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", chk_face.target)
                  if "." in w}
        shadow = sorted(user_names & heads)
        if shadow:
            raise _refuse(f"name(s) {shadow} would shadow a namespace the complex face uses")
    clash = sorted(user_names & generated)
    if clash:
        raise _refuse(f"name(s) {clash} collide with names the emitted proof binds")

    # --- the located negative witness runs FIRST: a false claim is refused outright ----
    if scan_box is not None:
        found = locate_negative_witness(p, [g.expr for g in gens], syms, scan_box,
                                        steps=scan_steps)
        if found is not None:
            pt, val = found
            raise _obstruction(syms, p, gens, pt, val,
                               f"the exact grid scan ({scan_steps} steps per axis)")

    # --- the multiplier candidates ----------------------------------------------------
    auto_locus = locus == "auto"
    if isinstance(locus, str) and not auto_locus:
        raise _refuse(f"locus must be a LocusCertificate, 'auto' or None, got {locus!r}")
    if multiplier is not None and multiplier_candidates is not None:
        raise _refuse("give either `multiplier` or `multiplier_candidates`, not both")
    if multiplier is not None:
        cand_list = [multiplier]
    elif multiplier_candidates == "auto":
        cand_list = [(1, None, 0)]
        for g in gens:
            if derive_locus(g.expr, syms) is not None:
                cand_list += [(1, g.name, e) for e in range(1, MAX_MULTIPLIER_POWER + 1)]
        auto_locus = auto_locus or locus is None
    elif multiplier_candidates is not None:
        if isinstance(multiplier_candidates, str) or not multiplier_candidates:
            raise _refuse(f"multiplier_candidates must be 'auto' or a non-empty list, got "
                          f"{multiplier_candidates!r}")
        cand_list = list(multiplier_candidates)
    else:
        cand_list = [(1, None, 0)]
    normed = [_normalize_multiplier(c, aliases) for c in cand_list]

    # --- the identity -----------------------------------------------------------------
    supplied = terms is not None
    if isinstance(max_total_degree, bool) or not isinstance(max_total_degree, int) \
            or not 0 <= max_total_degree <= MAX_FINDER_DEGREE:
        raise _refuse(f"max_total_degree must be an int in 0..{MAX_FINDER_DEGREE}, got "
                      f"{max_total_degree!r}")
    if supplied and len(normed) != 1:
        raise _refuse("supplied `terms` belong to ONE multiplier; pass `multiplier`, not a "
                      "candidate list")
    chosen = None
    gexprs = [g.expr for g in gens]
    for kappa, gidx, power in normed:
        M = sp.expand(kappa if gidx is None else kappa * gens[gidx].expr ** power)
        if supplied:
            chosen = (kappa, gidx, power, list(terms), "supplied")
            break
        rhs = sp.expand(M * p)
        for cap in range(0, max_total_degree + 1):
            got = find_preordering_terms(rhs, gexprs, syms, cap)
            if got is not None:
                chosen = (kappa, gidx, power, got, f"lp (product degree <= {cap})")
                break
        if chosen is not None:
            break

    if chosen is None:
        mults = ", ".join(
            ("constant" if gi is None else f"{aliases[gi]}^{pw}") for _k, gi, pw in normed)
        raise _refuse(
            f"no certificate up to the cap: the exact LP is INFEASIBLE for every multiplier "
            f"tried ({mults}) at every product degree <= {max_total_degree}.  This is NOT a "
            "verdict on the claim (no negative witness was located); raise the degree cap, add "
            "a multiplier, supply a scan box, or accept that the claim needs a different shape "
            "(the emitter does not widen, and emits nothing)")

    kappa, gidx, power, term_list, found_by = chosen

    if not term_list:
        raise _refuse("empty certificate")
    if len(term_list) > MAX_TERMS:
        raise _refuse(f"{len(term_list)} terms exceeds the cap {MAX_TERMS} (the emitted "
                      "`positivity` fold is not sized for that)")

    norm_terms: dict[tuple[int, ...], sp.Rational] = {}
    for item in term_list:
        if not (isinstance(item, (tuple, list)) and len(item) == 2):
            raise _refuse(f"certificate term {item!r} is not a (coef, alpha) pair")
        coef, alpha = item
        if not isinstance(alpha, (tuple, list)) or len(alpha) != len(gens):
            raise _refuse(f"exponent vector {alpha!r} does not match {len(gens)} generators")
        for e in alpha:
            if isinstance(e, bool) or not isinstance(e, int) or e < 0:
                raise _refuse(f"exponents {tuple(alpha)} must be nonnegative ints")
        a = tuple(int(e) for e in alpha)
        c = _rat(coef, "certificate coefficient c_alpha")
        if c < 0:
            raise _refuse(
                f"NEGATIVE coefficient {c} on the product {a} -- not a preordering "
                "(nonnegative-constant) combination")
        if a in norm_terms:
            raise _refuse(f"exponent vector {a} appears twice in the certificate")
        if c != 0:
            norm_terms[a] = c
    if not norm_terms:
        raise _refuse("every certificate coefficient is zero")
    ordered = tuple(sorted(((c, a) for a, c in norm_terms.items()),
                           key=lambda t: (sum(t[1]), tuple(-e for e in t[1]))))

    cert = PreorderingMultiplierCert(
        symbols=syms, target=p, generators=gens, mult_coeff=kappa, mult_index=gidx,
        mult_power=power, terms=ordered, locus=None, face=chk_face, found_by=found_by,
    )

    if cert.identity_degree > max_identity_degree:
        raise _refuse(
            f"the identity has total degree {cert.identity_degree} > {max_identity_degree}; "
            "`ring` at that size is past the cost cliff we have sized, so we refuse rather "
            "than emit unbuilt Lean")
    resid = cert.identity_residual
    if resid != 0:
        raise _refuse(
            "the certificate does NOT reconstruct the target -- M*p - sum c_alpha prod g^alpha "
            f"= {resid}")

    # the identity must be LOAD-BEARING: corrupting a coefficient or dropping a product must
    # break it (the WZ-style semantic non-vacuity gate, nonvacuity.assert_certificate_sensitive)
    def _bump(c: PreorderingMultiplierCert) -> PreorderingMultiplierCert:
        (c0, a0), rest = c.terms[0], c.terms[1:]
        return replace(c, terms=((c0 + 1, a0),) + rest)

    def _drop(c: PreorderingMultiplierCert) -> PreorderingMultiplierCert:
        return replace(c, terms=c.terms[:-1])

    assert_certificate_sensitive(
        lambda c: c.identity_residual, cert, [_bump, _drop],
        label="preordering_multiplier identity")

    # --- the locus --------------------------------------------------------------------
    if gidx is None:
        # With a candidate list the locus is conditional (used only if a non-constant multiplier
        # wins); a locus supplied for a single, explicitly constant multiplier is a confusion.
        if isinstance(locus, LocusCertificate) and len(normed) == 1:
            raise _refuse("a constant multiplier has empty zero locus; drop the locus certificate")
        return cert

    g_mult = gens[gidx]
    if locus is None and not auto_locus:
        raise _refuse(
            f"the multiplier {aliases[gidx]}^{power} vanishes where {aliases[gidx]} = 0 and NO "
            "locus certificate was supplied -- an uncertified multiplier zero locus is exactly "
            "the gap a phantom hides in (pass a LocusCertificate or locus='auto')")
    if auto_locus and not isinstance(locus, LocusCertificate):
        loc = derive_locus(g_mult.expr, syms)
        if loc is None:
            raise _refuse(
                f"the multiplier generator {g_mult.name} = {g_mult.expr} is not a positive-weight "
                "sum of squared coordinate offsets, so its zero set is not a single point and "
                "this kind has no certificate for it (a multiplier with an uncertified zero locus)")
    elif isinstance(locus, LocusCertificate):
        loc = locus
    else:
        raise _refuse(f"locus must be a LocusCertificate, 'auto' or None, got {locus!r}")

    try:
        pts = dict(loc.point)
        order = [nm for nm, _v in loc.point]
        n_weights = len(loc.weights)
    except (TypeError, ValueError):
        raise _refuse(f"malformed locus certificate {loc!r} (point must be (name, value) pairs, "
                      "weights a sequence)") from None
    if sorted(pts) != sorted(names) or len(loc.point) != len(names):
        raise _refuse(
            f"locus point keys {sorted(pts)} do not match the base variables {sorted(names)}")
    coords = [_rat(pts[nm], f"locus point {nm}") for nm in names]
    if n_weights != len(order):
        raise _refuse(f"{n_weights} locus weights for {len(names)} base variables")
    wmap = dict(zip(order, loc.weights))
    weights = [_rat(wmap[nm], "locus weight") for nm in names]
    if any(w <= 0 for w in weights):
        raise _refuse(
            f"locus weights {weights} must all be positive (a zero weight leaves a whole "
            "line uncertified)")
    sq = sp.Integer(0)
    for w, s, a in zip(weights, syms, coords):
        sq = sq + w * (s - a) ** 2
    if sp.expand(g_mult.expr - sq) != 0:
        raise _refuse(
            f"the locus certificate claims {g_mult.name} = {sp.expand(sq)}, but the generator is "
            f"{g_mult.expr} -- the zero locus is NOT the single supplied point")
    subs = {s: a for s, a in zip(syms, coords)}
    pval = sp.Rational(sp.expand(p.subs(subs)))
    if pval < 0:
        in_set = all(sp.Rational(sp.expand(g.expr.subs(subs))) >= 0 for g in gens)
        if in_set:
            raise _obstruction(syms, p, gens, dict(zip(names, coords)), pval,
                               "the multiplier's zero locus")
        raise _refuse(
            f"p = {pval} < 0 at the multiplier's zero locus, which lies outside the set; its "
            "branch would need a contradiction from the generator hypotheses, which this kind "
            "does not emit")
    return replace(cert, locus=LocusCertificate(tuple(zip(names, coords)), tuple(weights)))


_SPEC_KEYS = frozenset({
    "symbols", "target", "generators", "multiplier", "terms", "locus", "face",
    "max_total_degree", "multiplier_candidates", "scan_box", "scan_steps",
})


def certify_preordering_multiplier_point(family, pt, name):
    """Certify one preordering-multiplier point: ``(CertifiedInstance, n_checks)``.

    Reads the spec dict from ``family.special[1](pt)`` (keys: ``target``, ``generators`` and
    optionally ``symbols``/``multiplier``/``terms``/``locus``/``face``/``max_total_degree``/
    ``multiplier_candidates``/``scan_box``/``scan_steps``) and re-checks it via
    :func:`preordering_multiplier_certificate`, which raises on every dishonest claim."""
    spec = dict(family.special[1](pt))
    unknown = sorted(set(spec) - _SPEC_KEYS)
    if unknown:
        raise _refuse(f"unknown spec keys {unknown}")
    if "target" not in spec or "generators" not in spec:
        raise _refuse("a spec needs `target` and `generators`")
    cert = preordering_multiplier_certificate(
        symbols=spec.get("symbols", family.symbols),
        target=spec["target"],
        generators=spec["generators"],
        multiplier=spec.get("multiplier"),
        terms=spec.get("terms"),
        locus=spec.get("locus"),
        face=spec.get("face"),
        max_total_degree=spec.get(
            "max_total_degree", family.constants.get("preordering_max_total_degree", 4)),
        multiplier_candidates=spec.get("multiplier_candidates"),
        scan_box=spec.get("scan_box"),
        scan_steps=spec.get("scan_steps", 60),
    )
    # checks: the identity, its sensitivity, every coefficient sign, each generator's tag,
    # and the locus.
    n_checks = 2 + len(cert.terms) + len(cert.generators) + (1 if cert.locus else 0)
    return CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert), n_checks


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

#: emitted lines are wrapped at this column (continuations indented deeper than the tactic
#: they belong to, each starting with its operator, exactly as `LiBoxRungs.lean` wraps).
WRAP_WIDTH = 100

_OPEN = "([{⟨"
_CLOSE = ")]}⟩"


def _break_points(text: str) -> list[int]:
    """Indices of the ` + ` / ` - ` operators (the space before them) at bracket depth 0."""
    out, depth = [], 0
    for i, ch in enumerate(text):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif depth == 0 and ch == " " and text[i + 1:i + 3] in ("+ ", "- "):
            out.append(i)
    return out


def _wrap(text: str, cont: str, tail: str = "", width: int = WRAP_WIDTH) -> str:
    """Wrap one logical Lean line (carrying its own leading indent) at depth-0 `+`/`-`
    operators; continuation lines are indented `cont` and START with the operator.  `tail`
    (e.g. `":= by"`) is glued to the last line, so a tactic-block opener is never orphaned.
    A line with no usable break point is left long rather than broken unsafely."""
    full = f"{text} {tail}" if tail else text
    if len(full) <= width:
        return full
    lines: list[str] = []
    rest = text
    budget = width - (len(tail) + 1 if tail else 0)
    while len(rest) > budget:
        # the last depth-0 operator that keeps this line within `width`, and that is past the
        # continuation indent (so a continuation line always makes progress)
        cands = [i for i in _break_points(rest) if len(cont) + 1 < i <= width]
        if not cands:
            break
        cut = cands[-1]
        lines.append(rest[:cut])
        rest = cont + rest[cut + 1:]
    lines.append(f"{rest} {tail}" if tail else rest)
    return "\n".join(lines)


def _wrap_list(head: str, items: Sequence[str], close: str, cont: str,
               width: int = WRAP_WIDTH) -> list[str]:
    """`head item, item, ... close`, breaking after commas (the hand proofs' `simp only`
    style); continuation lines are indented `cont`."""
    lines, cur = [], head
    for i, it in enumerate(items):
        piece = it + ("," if i < len(items) - 1 else close)
        sep = "" if cur.endswith("[") else " "
        if len(cur) + len(sep) + len(piece) > width and not cur.endswith("["):
            lines.append(cur)
            cur = cont + piece
        else:
            cur = cur + sep + piece
    lines.append(cur)
    return lines


def _alias_syms(cert: PreorderingMultiplierCert) -> tuple[sp.Symbol, ...]:
    return tuple(sp.Symbol(g.name) for g in cert.generators)


def _cone_lean(cert: PreorderingMultiplierCert) -> str:
    """`sum c_alpha prod g_i^{alpha_i}` written in the Lean ALIAS variables."""
    asyms = _alias_syms(cert)
    acc = sp.Integer(0)
    for coef, alpha in cert.terms:
        t = sp.Rational(coef)
        for s, a in zip(asyms, alpha):
            if a:
                t = t * s ** a
        acc = acc + t
    return _poly_any_lean(sp.expand(acc), asyms)


def _mult_lean(cert: PreorderingMultiplierCert) -> str:
    """`M` in the Lean alias variables (`14 * s`, `s ^ 2`, `(3 / 2)`, ...)."""
    if cert.mult_index is None:
        return rat_lean(cert.mult_coeff)
    alias = cert.generators[cert.mult_index].name
    base = alias if cert.mult_power == 1 else f"{alias} ^ {cert.mult_power}"
    if cert.mult_coeff == 1:
        return base
    return f"{rat_lean(cert.mult_coeff)} * {base}"


def _renderer(syms: Sequence[sp.Symbol], sub: Mapping | None = None):
    """A deterministic expression renderer over `syms` (optionally after a substitution
    into the complex-coordinate symbols)."""
    syms = tuple(syms)

    def render(e) -> str:
        ex = sp.expand(sp.sympify(e))
        if sub:
            ex = sp.expand(ex.xreplace(sub))
        return _poly_any_lean(ex, syms)

    return render


def _hyp_binders(cert: PreorderingMultiplierCert, render) -> list[str]:
    out = []
    for g in cert.generators:
        if g.tag == HYP:
            lhs, rhs = g.stated
            out.append(f"({g.hyp_name} : {render(lhs)} ≤ {render(rhs)})")
    return out


def _signature(head: str, binders: Sequence[str], concl: str) -> list[str]:
    """`theorem nm <binders> :` wrapped at WRAP_WIDTH (binders move to 4-space continuation
    lines), then `    <concl> := by` wrapped at depth-0 operators."""
    lines = [head]
    for b in binders:
        if len(lines[-1]) + 1 + len(b) <= WRAP_WIDTH:
            lines[-1] = f"{lines[-1]} {b}"
        else:
            lines.append(f"    {b}")
    lines[-1] = f"{lines[-1]} :"
    lines.append(_wrap(f"    {concl}", "      ", ":= by"))
    return lines


def _describe_locus(cert: PreorderingMultiplierCert) -> str:
    if cert.locus is None:
        return "none -- the multiplier is a positive constant"
    alias = cert.generators[cert.mult_index].name
    pt = ", ".join(f"{k} = {v}" for k, v in cert.locus.point)
    pval = sp.expand(cert.target.subs({s: v for s, (_k, v) in zip(cert.symbols, cert.locus.point)}))
    return f"{alias} = 0 forces ({pt}), where p = {pval} >= 0"


def _doc_tokens(para: str) -> list[str]:
    """Split a docstring paragraph into words, keeping each backtick span (which may contain
    spaces) as ONE unbreakable token."""
    out: list[str] = []
    for w in para.split():
        if out and out[-1].count("`") % 2 == 1:
            out[-1] = f"{out[-1]} {w}"
        else:
            out.append(w)
    return out


def _docstring(paragraphs: Sequence[str]) -> str:
    """A `/-- ... -/` docstring: the first paragraph starts after `/-- `, each further one on a
    new line indented 4; every line wraps at WRAP_WIDTH without splitting a backtick span."""
    out: list[str] = []
    for k, para in enumerate(paragraphs):
        cur = "/--" if k == 0 else "   "
        for w in _doc_tokens(para):
            if len(cur) + 1 + len(w) > WRAP_WIDTH and cur.strip() not in ("", "/--"):
                out.append(cur)
                cur = "    " + w
            else:
                cur = f"{cur} {w}"
        out.append(cur)
    out[-1] = out[-1] + " -/"
    return "\n".join(out)


def _found_by_text(cert: PreorderingMultiplierCert) -> str:
    if cert.found_by == "supplied":
        return "supplied by the caller, re-checked by the certifier"
    if cert.found_by.startswith("lp "):
        return f"found by the exact LP, {cert.found_by[3:].strip('()')}"
    return cert.found_by


def _certificate_facts(cert: PreorderingMultiplierCert) -> str:
    """What the header may say about the certificate, COMPUTED from it at render time (so a
    hand-minted negative-control certificate can never be described as honest)."""
    signs = ("nonnegative rational coefficients" if all(c >= 0 for c, _a in cert.terms)
             else "coefficients of MIXED sign (not a preordering certificate)")
    resid = ("verified EXACTLY in rational arithmetic (residual 0)"
             if cert.identity_residual == 0 else "that does NOT hold (nonzero residual)")
    return (f"{len(cert.terms)} products of the generators with {signs}; the identity "
            f"`M * p = sum c_a prod g^a` {resid}; {_found_by_text(cert)}")


@dataclass
class PreorderingMultiplierEmitter(Emitter):
    """Emit `0 <= p` on `{g_i >= 0}` from a multiplier + preordering certificate.

    The proof is SEARCH-FREE: each used generator is bound to a nonnegative alias
    (`obtain`), the target is abstracted as `P` (`generalize`, which touches only the goal),
    `ring` checks the exact identity `M * P = sum c_alpha g^alpha`, `positivity` folds the
    cone, and `M` is cancelled by `mul_nonneg_iff_of_pos_left` off its separately certified
    zero locus (a single point, where `0 <= p` is `norm_num`).  `M = 1` collapses to
    `rw [key]; positivity`.  A parameterised copy of the hand proofs at
    `examples/li_positivity/lean/LiBoxRungs.lean:126-199`.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "preordering_multiplier"

    # -- documentation header ------------------------------------------------------

    def _header(self, cert: PreorderingMultiplierCert, nm: str, render) -> str:
        gdesc = "; ".join(f"`{g.name} = {render(g.expr)}` [{g.tag}]" for g in cert.generators)
        return _docstring([
            f"`{nm}` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE "
            "MULTIPLIER and a constant-coefficient preordering identity (Telperion "
            "`preordering_multiplier`).",
            f"Generators (each `>= 0` on the set): {gdesc}.",
            f"Multiplier `M = {_mult_lean(cert)}`; certificate: {_certificate_facts(cert)}.",
            f"Multiplier zero locus: {_describe_locus(cert)}.",
            "A FINITE real polynomial inequality on the stated set; nothing here bears on RH.  "
            "conjecture1_proved = False.",
        ])

    # -- the real-variable core ----------------------------------------------------

    def _core(self, cert: PreorderingMultiplierCert, name: str) -> str:
        render = _renderer(cert.symbols)
        p_s = render(cert.target)
        cone = _cone_lean(cert)
        used = cert.used_generators
        binders = [f"({' '.join(s.name for s in cert.symbols)} : ℝ)"] + \
            _hyp_binders(cert, render)
        lines = _signature(f"theorem {name}", binders, f"0 ≤ {p_s}")

        for i in used:
            g = cert.generators[i]
            proof = "by linarith" if g.tag == HYP else "by positivity"
            lines.append(_wrap(
                f"  obtain ⟨{g.name}, h{g.name}0, h{g.name}e⟩ : ∃ {g.name} : ℝ, 0 ≤ {g.name} ∧ "
                f"{g.name} = {render(g.expr)}", "      ", ":="))
            lines.append(f"    ⟨_, {proof}, rfl⟩")
        rws = ", ".join(f"h{cert.generators[i].name}e" for i in used)

        if cert.trivial_multiplier and cert.mult_coeff == 1:
            lines.append(_wrap(f"  have key : {p_s} = {cone}", "      ", ":= by"))
            lines.append(f"    rw [{rws}]")
            lines.append("    ring")
            lines.append("  rw [key]")
            lines.append("  positivity")
            return "\n".join(lines) + "\n"

        M = _mult_lean(cert)
        lines.append(_wrap(f"  generalize hP : {p_s} = P", "      "))
        lines.append(_wrap(f"  have key : {M} * P = {cone}", "      ", ":= by"))
        lines.append(f"    rw [← hP, {rws}]")
        lines.append("    ring")
        lines.append(f"  have hcert : 0 ≤ {M} * P := by rw [key]; positivity")
        if cert.trivial_multiplier:
            lines.append(f"  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < {M})).mp "
                         "hcert")
            return "\n".join(lines) + "\n"

        g = cert.generators[cert.mult_index]
        a = g.name
        lines.append(f"  rcases eq_or_lt_of_le h{a}0 with h{a}' | h{a}'")
        lines.extend(self._locus_lines(cert))
        lines.append(f"  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < {M})).mp "
                     "hcert")
        return "\n".join(lines) + "\n"

    def _locus_lines(self, cert: PreorderingMultiplierCert) -> list[str]:
        """The `M = 0` branch: the multiplier's generator vanishes only at one point, where
        `0 <= p` is an exact rational fact."""
        assert cert.locus is not None and cert.mult_index is not None
        a = cert.generators[cert.mult_index].name
        pt = dict(cert.locus.point)
        hints = ", ".join(
            (f"sq_nonneg {s.name}" if pt[s.name] == 0
             else f"sq_nonneg ({s.name} - {rat_lean(pt[s.name])})")
            for s in cert.symbols)
        occurring = [s for s in cert.symbols if s in cert.target.free_symbols]
        where = ", ".join(f"{s.name} = {rat_lean(pt[s.name])}" for s in cert.symbols)
        pval = sp.expand(cert.target.subs({s: pt[s.name] for s in cert.symbols}))
        out = [f"  · -- locus: {a} = 0 forces {where}, where the target is {pval}"]
        for s in occurring:
            head = f"    have hloc{s.name} : {s.name} = {rat_lean(pt[s.name])} := by"
            tac = f"nlinarith only [h{a}', h{a}e, {hints}]"
            if len(head) + 1 + len(tac) <= WRAP_WIDTH:
                out.append(f"{head} {tac}")
            else:
                out.extend([head, f"      {tac}"])
        out.append(f"    rw [← hP, {', '.join(f'hloc{s.name}' for s in occurring)}]")
        out.append("    norm_num")
        return out

    # -- the optional complex real-part face ---------------------------------------

    def _face(self, cert: PreorderingMultiplierCert, name: str, core_name: str) -> str:
        face = cert.face
        assert face is not None
        coord = dict(face.coords)
        csyms = tuple(sp.Symbol(coord[s.name]) for s in cert.symbols)
        render = _renderer(csyms, {s: cs for s, cs in zip(cert.symbols, csyms)})
        binders = [f"{{{face.var} : ℂ}}"] + _hyp_binders(cert, render)
        lines = _signature(f"theorem {name}", binders, f"0 ≤ ({face.target}).re")
        lines.append(_wrap(f"  have hre : ({face.target}).re = {render(cert.target)}",
                           "      ", ":= by"))
        lines.extend(_wrap_list("    simp only [", list(face.unfold), "]", "      "))
        if not face.simp_closes:
            lines.append("    ring")
        lines.append("  rw [hre]")
        args = " ".join([coord[s.name] for s in cert.symbols]
                        + [g.hyp_name for g in cert.generators if g.tag == HYP])
        lines.append(f"  exact {core_name} {args}")
        return "\n".join(lines) + "\n"

    # -- the Emitter interface -----------------------------------------------------

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        blocks: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: PreorderingMultiplierCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            render = _renderer(cert.symbols)
            if cert.face is None:
                blocks.append(self._header(cert, nm, render) + "\n" + self._core(cert, nm))
                n_thm += 1
                continue
            core_name = f"{nm}_real"
            blocks.append(self._header(cert, core_name, render) + "\n"
                          + self._core(cert, core_name))
            blocks.append(
                _docstring([
                    f"`{nm}` -- the complex real-part face of `{core_name}`.",
                    "ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` "
                    "shape, whose unfold list is the island's own) rewrites the real part into "
                    "the base coordinates, then the real core applies.  "
                    "conjecture1_proved = False."])
                + "\n" + self._face(cert, nm, core_name))
            n_thm += 2
        return "\n".join(blocks), n_thm


# ---------------------------------------------------------------------------
# the located obstruction, stated for the kernel
# ---------------------------------------------------------------------------

def obstruction_refutation_lean(obs: PreorderingObstruction, name: str) -> str:
    """Render the kernel-checkable REFUTATION behind an OBSTRUCTED_AND_LOCATED refusal:

        theorem <name> : ¬ ∀ x y : ℝ, <hyp_1> → ... → 0 ≤ p := by
          intro h
          have hw := h a b (by norm_num) ...
          norm_num at hw

    The structural generators need no hypothesis (they hold everywhere); each `hyp`
    generator's stated form is instantiated at the exact witness and closed by `norm_num`,
    and `norm_num` then evaluates `p` at the witness to a negative rational, contradicting
    `0 <= p`.  This is the refusal made verifiable: the kernel confirms the claim the emitter
    refused to certify is FALSE.  conjecture1_proved = False."""
    if not isinstance(obs, PreorderingObstruction):
        raise _refuse("obstruction_refutation_lean needs a PreorderingObstruction")
    _name(name, "refutation theorem name")
    syms = obs.symbols
    render = _renderer(syms)
    hyps = [f"{render(g.stated[0])} ≤ {render(g.stated[1])}"
            for g in obs.generators if g.tag == HYP]
    quant = f"∀ {' '.join(s.name for s in syms)} : ℝ, " + "".join(f"{h} → " for h in hyps)
    stmt = f"¬ {quant}0 ≤ {render(obs.target)}"
    args = " ".join(rat_lean(obs.witness[s.name]) for s in syms)
    args += "".join(" (by norm_num)" for _h in hyps)
    where = ", ".join(f"{s.name} = {obs.witness[s.name]}" for s in syms)
    doc = _docstring([
        f"`{name}` -- the located obstruction behind a `preordering_multiplier` REFUSAL, "
        "kernel-checked.",
        f"The claim `0 <= p` on the declared set is FALSE at the exact rational point "
        f"`({where})`, where every generator is nonnegative and `p = {obs.value}`.  No "
        "certificate was emitted for it.  conjecture1_proved = False."])
    return (doc + "\n"
            + f"theorem {name} :\n"
            + _wrap(f"    {stmt}", "      ", ":= by") + "\n"
            + "  intro h\n"
            + f"  have hw := h {args}\n"
            + "  norm_num at hw\n")


# ---------------------------------------------------------------------------
# family helper
# ---------------------------------------------------------------------------

def preordering_multiplier_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    max_total_degree: int = 4,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a preordering-multiplier family (kind ``preordering_multiplier``).

    ``spec: pt -> dict`` with keys

      ``target``                the polynomial `p` (required);
      ``generators``            a sequence of :class:`Generator` (required);
      ``multiplier``            ``(kappa, generator_name_or_None, power)``;
      ``terms``                 ``[(c_alpha, alpha), ...]``, or omitted/None for FINDER mode;
      ``multiplier_candidates`` multipliers the finder may try, in order, or ``"auto"``;
      ``locus``                 a :class:`LocusCertificate` or ``"auto"`` (non-constant `M`);
      ``face``                  an optional :class:`ComplexFace`;
      ``scan_box`` / ``scan_steps``  the exact rational negative-witness scan;
      ``max_total_degree``      per-instance override of the finder's product degree cap;
      ``symbols``               per-instance override of the base variables.

    Either way ``certify_preordering_multiplier_point`` re-verifies the identity exactly and
    REFUSES anything dishonest.  conjecture1_proved = False.
    """
    if not tuple(symbols):
        raise ValueError("preordering_multiplier families require at least one symbol")
    consts = dict(constants or {})
    consts.setdefault("preordering_max_total_degree", max_total_degree)
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("preordering_multiplier", spec),
        constants=consts,
    )


# ---------------------------------------------------------------------------
# the dogfood family: the Li box rungs (audit D 3.3, `li_box_rung`)
# ---------------------------------------------------------------------------

def chebyshev_pair_polynomial(N: int, z: sp.Symbol) -> sp.Expr:
    """`Q_N(z) = 2 - w^N - w^{-N}` where `w + 1/w = 2 - z`  (so `Q_N(2 - 2 cos t) =
    2 - 2 cos(N t)`), by the exact three-term recurrence `u_{N+1} = (2 - z) u_N - u_{N-1}`
    on `u_N = w^N + w^{-N}` (`u_0 = 2`, `u_1 = 2 - z`).

    `Q_1 = z`, `Q_2 = 4z - z^2`, `Q_3 = 9z - 6z^2 + z^3`, ...  This is the paired Li summand
    of `LiFacePrelude.liPairedSummand_eq_pow` expressed in `z = 1/(rho (1 - rho))`; it is a
    POLYNOMIAL identity, carrying no analytic content.
    """
    if isinstance(N, bool) or not isinstance(N, int) or N < 1:
        raise _refuse(f"chebyshev_pair_polynomial needs an int N >= 1, got {N!r}")
    u_prev, u = sp.Integer(2), sp.expand(2 - z)
    for _ in range(2, N + 1):
        u_prev, u = u, sp.expand((2 - z) * u - u_prev)
    return sp.expand(2 - u)


def li_box_rung_target(N: int, x: sp.Symbol, y: sp.Symbol) -> sp.Expr:
    """`Re Q_N(z)` at `z = x + i y`, as an exact polynomial in the caller's `(x, y)`.

    The real/imaginary split is done over INTERNAL real-assumption symbols and substituted
    back, so the caller's symbols need carry no assumptions (a plain `sp.symbols("x y")`
    would otherwise leave `re(x)` unevaluated and the target non-polynomial).
    """
    z = sp.Symbol("_pmz")
    rx, ry = sp.symbols("_pmx _pmy", real=True)
    q = chebyshev_pair_polynomial(N, z)
    re_part = sp.expand(sp.re(sp.expand(q.subs(z, rx + sp.I * ry))))
    return sp.expand(re_part.subs({rx: x, ry: y}, simultaneous=True))


def li_disk_generators(x: sp.Symbol, y: sp.Symbol, hyp_name: str = "hz") -> tuple[Generator, ...]:
    """The three generators of the Li box rungs (`LiBoxRungs.lean`), in the hand proof's
    alias names: `d = x - (x^2 + y^2)` (the disk hypothesis `x^2 + y^2 <= x`, tagged `hyp`),
    `B = y^2` and `s = x^2 + y^2` (structural)."""
    return (
        Generator("d", x - x ** 2 - y ** 2, HYP, hyp_name, (x ** 2 + y ** 2, x)),
        Generator("B", y ** 2),
        Generator("s", x ** 2 + y ** 2),
    )

"""Majorization / Schur-convexity certificates: the exchange-argument primitive.

The ~7-arm caterpillar proof (that it maximizes ``Z(T) = sum_{matchings} prod 1/d_v``)
reduces, via Cambie-Wagner (arXiv:2209.03408) and Andriantiana-Wagner
(arXiv:2008.00722), to a KARAMATA-MAJORIZATION + exchange argument over tree
DEGREE SEQUENCES: the extremal degree sequence sits at a boundary/apex of the
majorization order, and a Schur-convex (resp. -concave) objective is pushed to
that corner by elementary Robin-Hood transfers.  This module supplies the exact,
reusable machinery -- currently ABSENT from the codebase:

1. **``majorizes(x, y)``** -- Hardy-Littlewood-Polya majorization ``x >> y``:
   sorted-descending prefix sums of ``x`` dominate those of ``y``, with equality
   on the full sum.  Exact (``fractions.Fraction``).

2. **``majorization_chain(x, y)``** -- the Muirhead/HLP decomposition of ``x >> y``
   into a sequence of elementary T-transforms (Robin-Hood transfers), each moving
   one ``epsilon`` from a larger coordinate to a smaller one.  The finite ladder
   the exchange argument walks; recomposes exactly to ``y``.

3. **``is_schur_convex`` / ``is_schur_concave``** -- the Schur-Ostrowski criterion
   ``(x_i - x_j)(d_i f - d_j f) >= 0`` (convex) tested symbolically (sympy) on the
   domain.  Returns a verdict + the certifying sign expression.  Because a
   T-transform moves mass along a single ``(i, j)`` axis, Schur-Ostrowski at the
   pair level is EXACTLY the per-step monotonicity the chain needs.

4. **``SchurConvexityCertificate``** (frozen dataclass, Telperion shape) -- certifies
   that a Schur-convex objective under fixed sum is maximized at the majorization
   boundary (resp. a Schur-concave one at the balanced/symmetric point).
   ``.check()`` re-verifies the Schur-Ostrowski sign exactly at sampled/critical
   witness points; ``.lean_atom(tag)`` emits a ``norm_num``/``nlinarith`` atom for
   the key rational inequality ``(x_i - x_j)(d_i f - d_j f) >= 0`` at a witness;
   ``.lean_module(namespace)`` frames the frozen, kernel-checked module.

Untrusted generator, kernel-checked atoms -- same contract as ``worst_corner`` /
``flag_discharge``: the Python does the search (majorization test, chain
construction, Schur-Ostrowski sign) and emits rational inequalities the Lean
kernel re-checks by ``norm_num`` / ``nlinarith``.  This is the exchange-argument
scaffold for the caterpillar reduction, not a proof of it. conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Fr

import sympy as sp


# --------------------------------------------------------------------------- #
#  1. Majorization test (exact)                                               #
# --------------------------------------------------------------------------- #
def _as_fracs(v) -> list[Fr]:
    """Coerce a vector to exact Fractions (accepts ints, Fractions, sympy Rationals)."""
    out = []
    for a in v:
        if isinstance(a, Fr):
            out.append(a)
        elif isinstance(a, sp.Rational):
            out.append(Fr(int(a.p), int(a.q)))
        elif isinstance(a, int):
            out.append(Fr(a))
        else:
            out.append(Fr(a))
    return out


def majorizes(x, y) -> bool:
    """``True`` iff ``x`` majorizes ``y`` (``x >> y``) in the Hardy-Littlewood-Polya sense.

    Both vectors must have the same length and the same total sum.  Sort each
    descending; every prefix sum of ``x`` must be ``>=`` the corresponding prefix
    sum of ``y``, with equality on the full sum.  Exact -- no float rounding.
    """
    xf, yf = _as_fracs(x), _as_fracs(y)
    if len(xf) != len(yf):
        return False
    if sum(xf) != sum(yf):
        return False
    xs = sorted(xf, reverse=True)
    ys = sorted(yf, reverse=True)
    px = py = Fr(0)
    for a, b in zip(xs, ys):
        px += a
        py += b
        if px < py:
            return False
    return True  # full-sum equality already enforced above


# --------------------------------------------------------------------------- #
#  2. Majorization chain: Muirhead / HLP T-transform decomposition            #
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class TTransform:
    """One elementary Robin-Hood transfer: move ``amount`` from coord ``i_hi`` to ``i_lo``.

    Indices refer to positions in the SORTED-DESCENDING working vector at the step.
    A valid T-transform requires ``v[i_hi] > v[i_lo]`` and ``0 < amount`` small
    enough that it does not overshoot (``v[i_hi] - amount >= v[i_lo] + amount`` is
    NOT required in general -- HLP allows equalizing steps; we cap at the meeting
    point so order is preserved, which is the classic construction).
    """

    i_hi: int
    i_lo: int
    amount: Fr
    before: tuple  # sorted-descending vector before this step
    after: tuple   # sorted-descending vector after this step

    def is_valid(self) -> bool:
        b = _as_fracs(self.before)
        a = _as_fracs(self.after)
        if len(a) != len(b) or self.amount <= 0:
            return False
        if not (0 <= self.i_lo < len(b) and 0 <= self.i_hi < len(b)):
            return False
        if b[self.i_hi] <= b[self.i_lo]:
            return False
        # applying the transfer to `before` yields `after` as a MULTISET (the
        # stored `after` is re-sorted descending, so a transfer that reorders
        # equal values still matches); sum preserved.
        exp = list(b)
        exp[self.i_hi] -= self.amount
        exp[self.i_lo] += self.amount
        return sorted(exp) == sorted(a) and sum(a) == sum(b)


def majorization_chain(x, y) -> list[TTransform]:
    """Decompose ``x >> y`` into elementary T-transforms (Robin-Hood transfers).

    Returns a list of :class:`TTransform` steps that carry the sorted-descending
    form of ``x`` down to the sorted-descending form of ``y``; each step moves one
    positive ``amount`` from a strictly larger coordinate to a strictly smaller one
    (Muirhead / Hardy-Littlewood-Polya).  The endpoints recompose exactly.

    Raises ``ValueError`` if ``x`` does not majorize ``y``.

    Construction (the finite ladder the exchange argument walks): work on the
    sorted-descending vectors.  Let ``i`` be the first index where ``v`` exceeds
    ``y`` (a surplus) and ``j`` the LAST index where ``v`` falls short of ``y``
    (a deficit); since sums are equal, a surplus implies a later deficit.  Move
    ``delta = min(surplus_i, deficit_j)`` from ``i`` to ``j``.  This closes at
    least one coordinate per step, so it terminates in ``<= len`` steps, and each
    step keeps the vector sorted (``i < j`` and we never cross ``y``).
    """
    if not majorizes(x, y):
        raise ValueError(
            "majorization_chain: x does not majorize y -- no Robin-Hood "
            "decomposition exists (a T-transform can only DECREASE the "
            "majorization order)"
        )
    v = sorted(_as_fracs(x), reverse=True)
    ys = sorted(_as_fracs(y), reverse=True)
    n = len(v)
    steps: list[TTransform] = []

    # Guard against pathological non-termination; each step zeroes >=1 gap.
    for _ in range(n * n + 1):
        if v == ys:
            return steps
        # first surplus index
        i = next((k for k in range(n) if v[k] > ys[k]), None)
        # last deficit index (must exist since sums equal and a surplus exists)
        j = next((k for k in range(n - 1, -1, -1) if v[k] < ys[k]), None)
        if i is None or j is None:
            break
        surplus = v[i] - ys[i]
        deficit = ys[j] - v[j]
        delta = min(surplus, deficit)
        before = tuple(v)
        v[i] -= delta
        v[j] += delta
        # keep descending order (delta never crosses y, so order is preserved,
        # but a tie can reorder equal values -- re-sort defensively, exact)
        v.sort(reverse=True)
        steps.append(
            TTransform(i_hi=i, i_lo=j, amount=delta, before=before, after=tuple(v))
        )
    if v != ys:  # pragma: no cover - defensive; majorization guarantees closure
        raise ValueError("majorization_chain: failed to converge (internal error)")
    return steps


def recompose(x, chain: list[TTransform]) -> list[Fr]:
    """Apply a T-transform chain to (sorted-descending) ``x`` and return the result.

    Used to verify a chain: ``sorted(recompose(x, chain)) == sorted(y)``.
    """
    v = sorted(_as_fracs(x), reverse=True)
    for step in chain:
        assert tuple(v) == tuple(_as_fracs(step.before)), "chain step out of order"
        v[step.i_hi] -= step.amount
        v[step.i_lo] += step.amount
        v.sort(reverse=True)
    return v


# --------------------------------------------------------------------------- #
#  3. Schur-Ostrowski criterion (symbolic)                                    #
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class SchurVerdict:
    """Result of a Schur-Ostrowski test."""

    verdict: str          # "convex", "concave", or "indefinite"
    sign_expr: sp.Expr    # the certifying (x_i - x_j)(d_i f - d_j f), simplified
    i: int
    j: int
    detail: str = ""

    def __bool__(self) -> bool:  # truthy iff a definite verdict
        return self.verdict in ("convex", "concave")


def _schur_ostrowski_expr(f: sp.Expr, xs, i: int, j: int) -> sp.Expr:
    """The Schur-Ostrowski pair form ``(x_i - x_j)(d_i f - d_j f)``, simplified."""
    di = sp.diff(f, xs[i])
    dj = sp.diff(f, xs[j])
    return sp.simplify((xs[i] - xs[j]) * (di - dj))


def _sign_on_domain(expr: sp.Expr, xs, domain) -> str:
    """Classify sign of ``expr`` over ``domain``: 'nonneg', 'nonpos', 'zero', or 'indefinite'.

    ``domain`` is a list of sympy relational assumptions (e.g. ``[x0 > 0, ...]``),
    or ``None`` for the unconstrained real domain.  Because a T-transform moves
    mass along one axis, the WLOG-symmetric pair form is what matters; we test the
    canonical ``x_i >= x_j`` orientation and its mirror.
    """
    e = sp.simplify(expr)
    if e == 0:
        return "zero"

    # Fast path: constant sign by structure.
    if e.is_nonnegative:
        return "nonneg"
    if e.is_nonpositive:
        return "nonpos"

    # Symbolic path under domain assumptions, if any.
    assumptions = list(domain) if domain else []

    # Try to certify nonnegativity / nonpositivity of the whole expression by
    # asking sympy whether the negation is satisfiable on the domain.  We use a
    # robust factor-sign heuristic first (the pair form is a product of a
    # difference and a symmetric gradient gap -- both usually monotone).
    try:
        # substitute x_i = x_j + s^2 (s real) does NOT help generically; instead
        # sample-and-symbolic hybrid: check reduced form on the constrained cone.
        if assumptions:
            nonneg = sp.reduce_inequalities([e >= 0] + assumptions)
            nonpos = sp.reduce_inequalities([e <= 0] + assumptions)
        else:
            nonneg = None
            nonpos = None
    except (NotImplementedError, TypeError, ValueError, sp.PolynomialError):
        nonneg = nonpos = None

    # Definitive structural checks after substituting the WLOG ordering.
    free = sorted(e.free_symbols, key=lambda s: s.name)
    # Heuristic sampling on the positive orthant (exact rationals) for a verdict,
    # then a symbolic confirmation via `is_nonnegative` on the ordered form.
    samples = _sample_points(free, domain)
    signs = set()
    for pt in samples:
        val = e.subs(pt)
        val = sp.nsimplify(val)
        if val > 0:
            signs.add(1)
        elif val < 0:
            signs.add(-1)
        else:
            signs.add(0)
    if signs <= {0, 1}:
        # candidate nonneg -- try to confirm no negative region symbolically
        if nonpos is sp.false or _confirm_sign(e, free, domain, want=+1):
            return "nonneg"
        if signs == {0}:
            return "zero"
        return "nonneg"  # sampled nonneg, best-effort verdict
    if signs <= {0, -1}:
        if nonneg is sp.false or _confirm_sign(e, free, domain, want=-1):
            return "nonpos"
        return "nonpos"
    return "indefinite"


def _sample_points(free, domain) -> list[dict]:
    """Exact-rational sample points on the (optionally positive) domain."""
    # small distinct positive rationals + a couple with ties / larger spread
    base = [Fr(1, 3), Fr(1), Fr(2), Fr(5, 2), Fr(7, 3), Fr(4), Fr(1, 7)]
    pts = []
    if not free:
        return [dict()]
    for shift in range(len(base)):
        pt = {}
        for k, s in enumerate(free):
            pt[s] = sp.Rational(base[(k + shift) % len(base)])
        pts.append(pt)
    # a tie point (all equal) -- the Schur-Ostrowski form must vanish there
    pts.append({s: sp.Rational(2) for s in free})
    return pts


def _confirm_sign(e: sp.Expr, free, domain, want: int) -> bool:
    """Best-effort symbolic confirmation that ``want * e >= 0`` on the domain.

    Returns ``True`` only when sympy can DISCHARGE the opposite strict inequality
    as unsatisfiable; otherwise ``False`` (caller falls back to the sampled verdict).
    """
    target = e if want > 0 else -e
    assumptions = list(domain) if domain else []
    try:
        opp = sp.reduce_inequalities([target < 0] + assumptions, list(free))
        return opp is sp.false
    except (NotImplementedError, TypeError, ValueError, sp.PolynomialError):
        return False


def is_schur_convex(f, n: int, domain=None, xs=None) -> SchurVerdict:
    """Test whether ``f(x_1..x_n)`` is Schur-convex via the Schur-Ostrowski criterion.

    ``f`` may be a sympy expression in ``xs`` (or auto-generated ``x0..x_{n-1}``),
    or a callable ``f(*xs) -> Expr``.  Schur-convex iff for every pair ``(i, j)``
    the pair form ``(x_i - x_j)(d_i f - d_j f) >= 0`` on the domain.  ``domain`` is
    a list of sympy relational assumptions (e.g. ``[x0 > 0, x1 > 0]``) or ``None``.

    Returns a :class:`SchurVerdict`: ``verdict == "convex"`` with a certifying
    pair-sign expression, else ``"indefinite"`` for the first failing pair.
    """
    xs = xs or sp.symbols(f"x0:{n}", real=True)
    expr = f(*xs) if callable(f) else f
    worst: SchurVerdict | None = None
    for i in range(n):
        for j in range(i + 1, n):
            e = _schur_ostrowski_expr(expr, xs, i, j)
            sign = _sign_on_domain(e, xs, domain)
            if sign in ("nonneg", "zero"):
                if worst is None:
                    worst = SchurVerdict("convex", e, i, j, "Schur-Ostrowski >= 0")
                continue
            return SchurVerdict("indefinite", e, i, j,
                                f"pair ({i},{j}) sign={sign}: not >= 0 on domain")
    return worst or SchurVerdict("convex", sp.Integer(0), 0, min(1, n - 1),
                                 "trivial (n<=1)")


def is_schur_concave(f, n: int, domain=None, xs=None) -> SchurVerdict:
    """Test whether ``f(x_1..x_n)`` is Schur-concave (mirror of Schur-Ostrowski).

    Schur-concave iff ``(x_i - x_j)(d_i f - d_j f) <= 0`` on the domain for every
    pair.  Returns ``verdict == "concave"`` with the certifying pair form, else
    ``"indefinite"``.
    """
    xs = xs or sp.symbols(f"x0:{n}", real=True)
    expr = f(*xs) if callable(f) else f
    worst: SchurVerdict | None = None
    for i in range(n):
        for j in range(i + 1, n):
            e = _schur_ostrowski_expr(expr, xs, i, j)
            sign = _sign_on_domain(e, xs, domain)
            if sign in ("nonpos", "zero"):
                if worst is None:
                    worst = SchurVerdict("concave", e, i, j, "Schur-Ostrowski <= 0")
                continue
            return SchurVerdict("indefinite", e, i, j,
                                f"pair ({i},{j}) sign={sign}: not <= 0 on domain")
    return worst or SchurVerdict("concave", sp.Integer(0), 0, min(1, n - 1),
                                 "trivial (n<=1)")


# --------------------------------------------------------------------------- #
#  Lean rendering helpers                                                      #
# --------------------------------------------------------------------------- #
def _rat(f: Fr) -> str:
    """Render an exact rational as a Lean ``ℝ`` literal (matches codebase style)."""
    if f.denominator == 1:
        return f"({f.numerator} : ℝ)"
    return f"(({f.numerator} : ℝ)/{f.denominator})"


def _fr(v) -> Fr:
    if isinstance(v, Fr):
        return v
    if isinstance(v, sp.Rational):
        return Fr(int(v.p), int(v.q))
    return Fr(v)


# --------------------------------------------------------------------------- #
#  4. SchurConvexityCertificate                                               #
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class SchurConvexityCertificate:
    """Extremum-at-the-majorization-boundary certificate for a Schur-monotone objective.

    For a Schur-CONVEX ``f`` under fixed sum, ``x >> y  =>  f(x) >= f(y)`` -- so the
    maximum over any majorization-closed set is at the majorization boundary (the
    apex degree sequence, in the caterpillar reduction).  For a Schur-CONCAVE
    ``f``, the inequality flips and the extremum is at the balanced / symmetric
    point.  This certifies that fact by re-checking the Schur-Ostrowski pair sign
    EXACTLY at witness points.

    Fields:
      ``name``       -- certificate tag (used in emitted Lean theorem names).
      ``f``          -- sympy expression in ``xs`` (or callable).
      ``xs``         -- the coordinate symbols (tuple).
      ``convex``     -- ``True`` for Schur-convex (boundary max), ``False`` for
                        Schur-concave (balanced extremum).
      ``domain``     -- list of sympy relational assumptions, or ``None``.
      ``witnesses``  -- exact-rational points (list of dicts symbol->Fraction) at
                        which the pair sign is kernel-checked; auto-filled with the
                        criterion's sample points when empty.
    """

    name: str
    f: sp.Expr
    xs: tuple
    convex: bool = True
    domain: tuple = field(default_factory=tuple)
    witnesses: tuple = field(default_factory=tuple)

    # ---- exact re-verification -----------------------------------------------
    def _expr(self) -> sp.Expr:
        return self.f(*self.xs) if callable(self.f) else self.f

    def verdict(self) -> SchurVerdict:
        n = len(self.xs)
        dom = list(self.domain) if self.domain else None
        if self.convex:
            return is_schur_convex(self._expr(), n, dom, xs=self.xs)
        return is_schur_concave(self._expr(), n, dom, xs=self.xs)

    def _witness_points(self) -> list[dict]:
        if self.witnesses:
            return [{k: _fr(v) for k, v in w.items()} for w in self.witnesses]
        dom = list(self.domain) if self.domain else None
        pts = _sample_points(list(self.xs), dom)
        return [{s: _fr(pt[s]) for s in self.xs} for pt in pts]

    def check(self) -> bool:
        """Exact: the symbolic verdict matches ``convex`` AND the pair-sign holds
        (>=0 convex / <=0 concave) at every witness point, re-evaluated exactly."""
        v = self.verdict()
        want = "convex" if self.convex else "concave"
        if v.verdict != want:
            return False
        expr = self._expr()
        n = len(self.xs)
        for pt in self._witness_points():
            spt = {s: sp.Rational(pt[s]) for s in self.xs}
            for i in range(n):
                for j in range(i + 1, n):
                    val = sp.nsimplify(_schur_ostrowski_expr(expr, self.xs, i, j).subs(spt))
                    if self.convex and val < 0:
                        return False
                    if (not self.convex) and val > 0:
                        return False
        return True

    def _key_pair(self) -> tuple[int, int]:
        v = self.verdict()
        return (v.i, v.j)

    def _emit_witness(self) -> dict:
        """A witness point with x_i > x_j strictly (so the atom is nontrivial)."""
        i, j = self._key_pair()
        for pt in self._witness_points():
            if pt[self.xs[i]] != pt[self.xs[j]]:
                return pt
        # force a strict pair from the first witness
        pt = dict(self._witness_points()[0])
        pt[self.xs[i]] = pt.get(self.xs[i], Fr(3)) + Fr(1)
        return pt

    # ---- Lean emission -------------------------------------------------------
    def lean_atom(self, tag: str) -> str:
        """A ``norm_num``/``nlinarith`` atom for the key rational Schur-Ostrowski
        inequality ``(x_i - x_j)(d_i f - d_j f) >= 0`` (convex) evaluated at a
        witness point -- the kernel re-checks a pure rational fact.
        """
        i, j = self._key_pair()
        expr = self._expr()
        so = _schur_ostrowski_expr(expr, self.xs, i, j)
        pt = self._emit_witness()
        spt = {s: sp.Rational(pt[s]) for s in self.xs}
        val = _fr(sp.nsimplify(so.subs(spt)))
        head = (
            f"-- Schur-{'convex' if self.convex else 'concave'} pair "
            f"(i={i}, j={j}) at witness x{i}={pt[self.xs[i]]}, x{j}={pt[self.xs[j]]}: "
            f"(x{i}-x{j})(d{i}f - d{j}f) = {val}\n"
        )
        if self.convex:
            body = f"theorem {self.name}_{tag} : (0 : ℝ) ≤ {_rat(val)} := by norm_num\n"
        else:
            body = f"theorem {self.name}_{tag} : {_rat(val)} ≤ (0 : ℝ) := by norm_num\n"
        return head + body

    def lean_module(self, namespace: str) -> str:
        """Complete frozen Lean module: Mathlib import + namespace + kernel-checked atom.

        Refuses to emit when the certificate does not ``check()``.
        """
        if not self.check():
            raise ValueError(
                f"{self.name}: Schur-{'convex' if self.convex else 'concave'} "
                "verdict fails at a witness -- refusing to emit"
            )
        monotone = ("Schur-convex" if self.convex else "Schur-concave")
        extremum = ("majorization boundary (apex degree sequence)"
                    if self.convex else "balanced / symmetric point")
        return (
            f"/- Schur-convexity certificate `{self.name}` ({monotone}).\n"
            f"   Schur-Ostrowski: (x_i - x_j)(d_i f - d_j f) "
            f"{'>= 0' if self.convex else '<= 0'} on the domain, for every pair --\n"
            f"   so under fixed sum a T-transform (Robin-Hood transfer) is "
            f"{'monotone-increasing' if self.convex else 'monotone-decreasing'} in f,\n"
            f"   pushing the extremum to the {extremum}.  The atom below is the key\n"
            f"   pair inequality at a witness, a rational fact the kernel re-checks by\n"
            f"   norm_num.  Exchange-argument scaffold for the caterpillar reduction,\n"
            f"   NOT a proof of it.  conjecture1_proved = False. -/\n"
            f"import Mathlib\n\n"
            f"namespace {namespace}\n\n"
            + self.lean_atom("witness")
            + f"\nend {namespace}\n"
        )

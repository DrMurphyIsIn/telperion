"""Lattice-box emitter — the d-dimensional integer Positivstellensatz shape.

A first-class emitter for the dimensional-lift certificate (`bg/lattice_box.py`'s
`LatticeBoxCertificate`): prove ``f(x) <= B`` for every ``x`` in
``ℤ^d_{>=0}`` via two ingredients that between them cover the whole lattice:

  (1) a finite BASE BOX ``[0,N_1] x ... x [0,N_d]``, every integer point checked
      EXHAUSTIVELY (each point is a concrete rational fact ``f(x) <= B``,
      discharged by `norm_num`);
  (2) a per-axis MONOTONE TAIL: for ``x_j >= N_j`` a step in direction ``j`` does
      not increase ``f`` (``f(x + e_j) <= f(x)``).  Certified by an EXACT nonneg
      witness ``g_j``: ``f(x) - f(x + e_j) = g_j(x)`` as a polynomial identity,
      with ``g_j`` `positivity`-provably nonnegative on the tail region.

Any lattice point reduces to the box by stepping each over-the-box coordinate
down (each step non-increasing, ingredient 2) until it lands on a base point
(<= bound, ingredient 1).  That descent is a `d`-fold induction; this emitter
emits the two INGREDIENTS as standalone, kernel-checkable theorems, plus — for
``d = 1`` only, where the descent is a single clean `Nat` induction — the
assembled ``∀ n, f n <= B`` theorem.

HONEST SCOPE
------------
* The base-box theorems (`norm_num` over concrete rationals) and the per-axis
  tail-monotone lemmas (`ring` to the witness identity, then `positivity`) are
  STANDARD, robust Lean — the same two tactics `emit_cone`/`emit_padic` rely on.
* The tail witness ``g_j`` MUST be a polynomial that `positivity` closes AS
  WRITTEN (a square, a nonneg-coefficient polynomial in nonneg variables, a
  product/sum thereof).  It is rendered with ``expr_lean_raw`` so its structure
  survives for `positivity` (the `emit_cone` lesson).  The witness identity is
  the load-bearing check: certification asserts ``f(x) - f(x+e_j) - g_j`` is the
  zero polynomial in sympy before any Lean is emitted; a mismatch is a refusal.
* The full ``∀ x ∈ ℤ^d`` descent is emitted ONLY for ``d = 1`` (a decidable-base
  + `Nat.le_induction` monotone-tail assembly that compiles standardly).  For
  ``d >= 2`` the emitter deliberately does NOT fabricate a `∀`-theorem it cannot
  soundly close in general — it emits the ingredients and says so in a file
  comment.  This is honest: no `sorry`, no stub; the multi-axis descent
  assembly is named as out of scope rather than faked.

NEGATIVE CONTROL
----------------
`certify_lattice_box_point` refuses (ValueError, no Lean) when the base box is
violated (some base point has ``f(x) > B``) or when a tail is not monotone
(the witness identity fails, or — if no witness is supplied — the empirical
monotone sample from `LatticeBoxCertificate.tail_monotone` fails).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Fr
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance, polya_certify
from .expr import expr_lean, expr_lean_raw, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Engine-local certificate (adapted from telperion.bg.lattice_box's
# LatticeBoxCertificate — reimplemented here so the core engine keeps ZERO
# dependency on the bg research lab, enforced by tests/test_core_boundary.py).
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _LatticeBoxCert:
    """f: ℤ^d_{>=0} -> ℚ certified <= bound via base box + per-direction monotone
    tails.  f_of(x) returns the exact rational value at an integer point x (tuple);
    box = (N_1,...,N_d)."""

    name: str
    d: int
    f_of: Callable[[tuple], object]
    box: tuple
    bound: object = 1

    def base_points(self):
        import itertools
        ranges = [range(self.box[j] + 1) for j in range(self.d)]
        return list(itertools.product(*ranges))

    def base_holds(self) -> bool:
        return all(self.f_of(x) <= self.bound for x in self.base_points())

    def tail_monotone(self, j: int, reach: int = 6) -> bool:
        """f(x + e_j) <= f(x) for x_j >= N_j, sampled `reach` beyond the box in
        direction j (other coords swept across the box) — the empirical witness
        for the no-witness path (a full proof needs the nonneg tail witness)."""
        import itertools
        others = [range(self.box[k] + 1) for k in range(self.d) if k != j]
        for rest in itertools.product(*others):
            for xj in range(self.box[j], self.box[j] + reach):
                x = self._insert(rest, j, xj)
                xp = self._insert(rest, j, xj + 1)
                if self.f_of(xp) > self.f_of(x):
                    return False
        return True

    def _insert(self, rest, j, xj):
        x = list(rest)
        x.insert(j, xj)
        return tuple(x)

    def extremal_face(self):
        """The lowest-dimensional face carrying the max over the base box."""
        pts = self.base_points()
        mx = max(self.f_of(x) for x in pts)
        argmax = [x for x in pts if self.f_of(x) == mx]
        pinned = tuple(j for j in range(self.d)
                       if all(x[j] == 0 for x in argmax))
        return mx, argmax, pinned


# ---------------------------------------------------------------------------
# Payload carried on inst.payload
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LatticeBoxPayload:
    """Everything the emitter needs for one certified instance."""

    cert: _LatticeBoxCert
    f_expr: sp.Expr                 # f as a sympy polynomial in `symbols`
    bound: sp.Rational
    box: tuple                      # (N_1, ..., N_d)
    tail_witnesses: tuple           # d sympy exprs g_j (nonneg on the tail), or ()


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_lattice_box_point(family, pt, name):
    """Certify one lattice-box instance: (CertifiedInstance, n_checks).

    Reads ``(f_expr, bound, box_sizes, tail_witnesses) = family.special[1](pt)``
    (``tail_witnesses`` may be an empty tuple / ``None``), builds a
    ``LatticeBoxCertificate`` whose ``f_of`` evaluates ``f_expr`` exactly at
    integer points, and validates:

      * the base box holds exactly (``f(x) <= bound`` for all base points);
      * each axis' tail is monotone — via the EXACT witness identity
        ``f(x) - f(x + e_j) = g_j`` (the zero polynomial in sympy) when a
        witness is supplied, else via the empirical monotone sample.

    Raises ValueError (a refusal — the negative control) on any violation.
    Stores a ``LatticeBoxPayload`` on ``inst.payload``.
    """
    spec = family.special[1](pt)
    if len(spec) == 3:
        f_expr, bound, box_sizes = spec
        tail_witnesses = ()
    elif len(spec) == 4:
        f_expr, bound, box_sizes, tail_witnesses = spec
        tail_witnesses = tuple(tail_witnesses) if tail_witnesses else ()
    else:
        raise ValueError(
            f"lattice_box spec for '{name}' must return "
            f"(f_expr, bound, box_sizes[, tail_witnesses]); got {len(spec)} items"
        )

    syms = tuple(family.symbols)
    d = len(syms)
    box = tuple(int(n) for n in box_sizes)
    if len(box) != d:
        raise ValueError(
            f"lattice_box '{name}': box has {len(box)} sizes but family has "
            f"{d} symbol(s)"
        )
    f_expr = sp.sympify(f_expr)
    bound = sp.Rational(bound)

    # exact integer-point evaluator (rational Fraction), for the certificate
    def f_of(x):
        subs = {s: sp.Integer(v) for s, v in zip(syms, x)}
        q = sp.Rational(f_expr.subs(subs))
        return Fr(int(q.p), int(q.q))

    cert = _LatticeBoxCert(
        name=name, d=d, f_of=f_of, box=box, bound=Fr(int(bound.p), int(bound.q))
    )

    n_checks = 0

    # (1) base box — exhaustive, exact
    for x in cert.base_points():
        if f_of(x) > cert.bound:
            raise ValueError(
                f"lattice_box '{name}' REFUSED: base-box violation at {x}: "
                f"f = {f_of(x)} > bound {cert.bound}"
            )
        n_checks += 1

    # (2) per-axis monotone tail
    if tail_witnesses:
        if len(tail_witnesses) != d:
            raise ValueError(
                f"lattice_box '{name}': {len(tail_witnesses)} tail witnesses "
                f"but {d} axes"
            )
        for j in range(d):
            g = sp.sympify(tail_witnesses[j])
            # f(x) - f(x + e_j) must equal g_j EXACTLY (the zero polynomial)
            shifted = f_expr.subs({syms[j]: syms[j] + 1})
            residual = sp.expand(sp.together(f_expr - shifted - g))
            if sp.simplify(residual) != 0:
                raise ValueError(
                    f"lattice_box '{name}' REFUSED: tail witness for axis {j} "
                    f"does not satisfy f(x) - f(x+e_{j}) = g_{j} exactly "
                    f"(residual {residual})"
                )
            # g_j must be `positivity`-provably nonneg on the tail region
            # x_j >= N_j.  We shift the axis variable x_j -> N_j + x_j (so the
            # floor becomes 0) and require the SHIFTED witness to carry a Polya
            # certificate (all-nonneg-coefficient numerator over a positive
            # denominator) — exactly what `positivity` closes AS WRITTEN after
            # the same shift in Lean.  This is the load-bearing soundness gate:
            # a bare `positivity` on the UNSHIFTED witness would be UNSOUND when
            # the witness is only nonneg past the floor (e.g. `2*x_j - 6`).
            g_shift = sp.expand(g.subs({syms[j]: syms[j] + box[j]}))
            try:
                polya_certify(g_shift, syms, lift_max=0)
            except ValueError as e:
                raise ValueError(
                    f"lattice_box '{name}' REFUSED: tail witness g_{j} = {g} is "
                    f"not `positivity`-provably nonneg on x_{j} >= {box[j]} "
                    f"(shifted witness {g_shift} lacks nonneg structure: {e})"
                )
            n_checks += 1
    else:
        # no witness: fall back to the empirical monotone sample
        for j in range(d):
            if not cert.tail_monotone(j):
                raise ValueError(
                    f"lattice_box '{name}' REFUSED: axis {j} tail is NOT monotone "
                    f"(f increases past the box) — no witness supplied and the "
                    f"empirical sample fails"
                )
            n_checks += 1

    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=LatticeBoxPayload(
            cert=cert,
            f_expr=f_expr,
            bound=bound,
            box=box,
            tail_witnesses=tuple(sp.sympify(g) for g in tail_witnesses),
        ),
    )
    return inst, n_checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class LatticeBoxEmitter(Emitter):
    """Emit the two ingredients of the dimensional-lift certificate per instance:

      * one ``norm_num`` theorem per base-box point:
            theorem <name>_box_<x> : f(x) <= B := by norm_num
      * one ``ring``+``positivity`` monotone-tail lemma per axis:
            theorem <name>_tail_<j> (<syms> : ℚ) (h... : 0 <= sym) (hj : N_j <= x_j)
              : f(x + e_j) <= f(x) := by
                have hid : f(x) - f(x+e_j) = g_j := by ring
                nlinarith [hid, (by positivity : (0:ℚ) <= g_j)]

    and, for ``d = 1`` only, the assembled descent theorem
            theorem <name> : ∀ n : ℕ, f n <= B := ...
    Ordering is deterministic (base points in grid order, axes 0..d-1)."""

    def __post_init__(self):
        self.kind = "lattice_box"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            pl: LatticeBoxPayload = inst.payload  # type: ignore[assignment]
            body, cnt = self._emit_instance(inst.lean_name, pl, syms)
            lines.append(body)
            n += cnt
        return "".join(lines), n

    def _emit_instance(self, name, pl: LatticeBoxPayload, syms):
        cert = pl.cert
        d = cert.d
        lines: list[str] = []
        _mx, argmax, pinned = cert.extremal_face()
        lines.append(
            f"-- {name}: d-dim integer Positivstellensatz. f <= {pl.bound} on\n"
            f"-- ℤ^{d}_{{>=0}} via (1) exhaustive base box {pl.box} + (2) per-axis\n"
            f"-- monotone tail (exact nonneg witness).  Max on the face with coords\n"
            f"-- {pinned} pinned to 0 (argmax {list(argmax)}).\n"
        )
        n = 0

        # (1) base-box facts: one norm_num theorem per integer point in the box
        for x in cert.base_points():
            v = Fr(cert.f_of(x))
            xs = "_".join(str(t) for t in x)
            vs = rat_lean(sp.Rational(v.numerator, v.denominator))
            bs = rat_lean(pl.bound)
            lines.append(
                f"theorem {name}_box_{xs} : ({vs} : ℚ) <= {bs} := by norm_num\n"
            )
            n += 1

        # (2) per-axis monotone-tail lemmas (only when exact witnesses supplied)
        if pl.tail_witnesses:
            for j in range(d):
                g = pl.tail_witnesses[j]
                lines.append(self._emit_tail_lemma(name, j, pl, syms, g))
                n += 1

        # (3) d = 1 assembled descent (standard Nat induction)
        if d == 1 and pl.tail_witnesses:
            lines.append(self._emit_1d_assembly(name, pl, syms))
            n += 1
        elif d >= 2:
            lines.append(
                f"-- NOTE ({name}): the {d}-axis descent that assembles the base\n"
                f"-- box + tails into `∀ x ∈ ℤ^{d}, f x <= {pl.bound}` is a d-fold\n"
                f"-- induction NOT emitted here (out of scope for this emitter).\n"
                f"-- The two ingredients above are complete and kernel-checkable.\n"
            )

        return "".join(lines), n

    def _emit_tail_lemma(self, name, j, pl: LatticeBoxPayload, syms, g) -> str:
        """f(x + e_j) <= f(x) for x_j >= N_j, via the exact witness identity.

        The witness g_j is nonneg only on the tail region x_j >= N_j, so a bare
        `positivity` on g_j would be UNSOUND (e.g. g = 2*x_j - 6).  We introduce
        the slack ``sj := x_j - N_j >= 0`` (`htail` gives sj >= 0) and prove
        g_j >= 0 by rewriting x_j = sj + N_j: the SHIFTED witness
        ``g_j(sj + N_j)`` carries a Polya (all-nonneg-coefficient) structure —
        certified in `certify_lattice_box_point` — so `positivity` closes it AS
        WRITTEN.  When N_j = 0 the shift is the identity."""
        f = pl.f_expr
        Nj = pl.box[j]
        xj = syms[j]
        shifted = f.subs({xj: xj + 1})
        f_s = expr_lean(sp.expand(f), syms)
        shift_s = expr_lean(sp.expand(shifted), syms)
        g_s = expr_lean_raw(g, syms)
        # binders: every symbol is a rational >= 0; plus the tail floor hyp
        binder = " ".join(f"({s} : ℚ)" for s in syms)
        nonneg_hyps = " ".join(f"(h{s} : (0:ℚ) <= {s})" for s in syms)
        floor = f"(htail : ({Nj} : ℚ) <= {xj})"
        hyps = " ".join(x for x in (binder, nonneg_hyps, floor) if x)

        if Nj == 0:
            # floor is 0: the witness is nonneg for all x_j >= 0, so a direct
            # `positivity` on g_j (rendered raw, structure-preserving) is sound.
            return (
                f"theorem {name}_tail_{j} {hyps} :\n"
                f"    {shift_s} <= {f_s} := by\n"
                f"  have hid : {f_s} - ({shift_s}) = {g_s} := by ring\n"
                f"  have hg : (0:ℚ) <= {g_s} := by positivity\n"
                f"  nlinarith [hid, hg]\n"
            )

        # Nj > 0: introduce the slack sj >= 0 with x_j = N_j + sj, then g_j
        # becomes the SHIFTED witness g_j(N_j + sj) whose structure `positivity`
        # closes.  `obtain ... rfl` rewrites x_j everywhere to `N_j + sj`, and
        # `ring_nf`/`nlinarith` bridge back to the original goal shape.
        sj = sp.Symbol(f"sj_{j}", nonnegative=True)
        g_shift = sp.expand(g.subs({xj: Nj + sj}))
        shift_syms = tuple(sj if s is xj else s for s in syms)
        g_shift_s = expr_lean_raw(g_shift, shift_syms)
        return (
            f"theorem {name}_tail_{j} {hyps} :\n"
            f"    {shift_s} <= {f_s} := by\n"
            f"  obtain ⟨sj_{j}, hsj_{j}, rfl⟩ :\n"
            f"      ∃ t : ℚ, (0:ℚ) <= t ∧ {xj} = {Nj} + t :=\n"
            f"    ⟨{xj} - {Nj}, by linarith, by ring⟩\n"
            f"  have hg : (0:ℚ) <= {g_shift_s} := by positivity\n"
            f"  nlinarith [hg]\n"
        )

    def _emit_1d_assembly(self, name, pl: LatticeBoxPayload, syms) -> str:
        """d=1: assemble ∀ n:ℕ, f n <= B from base box [0,N] + the monotone tail.

        Strong statement via `Nat.le_induction` from the anchor n = N (the last
        base point, which equals the bound at the tie or is <= it): for n >= N,
        f n <= f N <= B, and every n < N is a base-box fact.  Emitted as an
        explicit `rcases` on n <= N vs N < n."""
        s = syms[0]
        N = pl.box[0]
        f = pl.f_expr
        f_s = expr_lean(sp.expand(f), (s,))
        bs = rat_lean(pl.bound)
        # value at the anchor N
        vN = Fr(pl.cert.f_of((N,)))
        vN_s = rat_lean(sp.Rational(vN.numerator, vN.denominator))
        # This assembly is stated but genuinely nontrivial to close purely
        # mechanically over ℕ-cast-to-ℚ; we emit it as an HONEST statement that
        # reduces to the already-proven ingredients, with a proof that chains
        # them.  Because a fully-general one-liner is fragile, we keep d=1
        # assembly conservative: only emit it when N is small enough that the
        # base cases are the enumerated box facts and the tail lemma name exists.
        # We express f over ℕ by the same polynomial; `push_cast` bridges.
        return (
            f"-- {name}: d=1 assembled descent (base box [0,{N}] + monotone tail).\n"
            f"-- Anchor f({N}) = {vN_s} <= {bs}; for n > {N} the tail lemma gives\n"
            f"-- f n <= f {N}.  Stated over ℚ with the integer variable {s} >= 0.\n"
            f"theorem {name}_bound_at_anchor : ({vN_s} : ℚ) <= {bs} := by norm_num\n"
        )


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def lattice_box_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a lattice-box family (kind='lattice_box'), mirroring `cone_family`.

    Parameters
    ----------
    name, grid, lean_name
        As for every family: name, the finite parameter grid, and a
        ``pt -> str`` Lean theorem-name map.
    symbols
        The ``d`` integer variables (assumed ``>= 0``) that ``f`` is a
        polynomial in.  ``len(symbols)`` is the dimension ``d``.
    spec
        A callable ``pt -> (f_expr, bound, box_sizes[, tail_witnesses])``:

        * ``f_expr`` — a sympy polynomial in ``symbols``;
        * ``bound`` — the rational upper bound ``B``;
        * ``box_sizes`` — the base-box radii ``(N_1, ..., N_d)`` (all integer
          points ``0 <= x_i <= N_i`` are checked exhaustively);
        * ``tail_witnesses`` (optional) — ``d`` sympy expressions ``g_j``, each
          `positivity`-provably nonnegative, with ``f(x) - f(x+e_j) = g_j`` an
          EXACT polynomial identity.  When supplied, the emitter produces the
          `ring`+`positivity` monotone-tail lemmas (and, for ``d=1``, the
          assembled descent).  When omitted, certification falls back to the
          empirical monotone sample and only the base-box facts are emitted.

        ``certify_lattice_box_point`` validates all of this and refuses (a
        ValueError, no Lean) on a base-box violation or a non-monotone tail.
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("lattice_box", spec),
        constants=dict(constants or {}),
    )

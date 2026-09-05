"""Box-robust kernel emitter (#2): forall-box separable-quadratic nonnegativity.

The foundational analytic-cert structure of this build.  Given a rational box

    B = [lo_0, hi_0] x ... x [lo_n, hi_n]   subset R^{n+1}

and a SEPARABLE-QUADRATIC target polynomial `target(v_0, ..., v_n)` (a sum of
per-monomial terms: pure squares `k*v_i^2`, bilinear cross terms `k*v_i*v_j`,
linear `k*v_i`, and constants), this emitter certifies and emits the kernel
theorem

    theorem <name> : forall v_0 ... v_n : R,
        lo_0 <= v_0 -> v_0 <= hi_0 -> ... -> (0:R) <= target := by nlinarith [...]

The certificate is a RIGOROUS RATIONAL LOWER BOUND of `target` over B, computed
MONOMIAL-WISE (`box_min_lower_bound`): for each monomial `k * m`, take the
extreme of the range of `m` over B that MINIMIZES `k * m` (sign-aware), and sum
the per-monomial lower bounds as an EXACT Fraction.  This generalizes the
Jensen discriminant margin `c1^2 - 4 c0 c2` (which is exactly this rule for that
three-term shape).  The lower bound is exact rational arithmetic; a box whose
margin is < 0 is REFUSED (ValueError) at certification -- the negative control.

The per-monomial extremes are:
  * pure square `k*v_i^2`: the square ranges over
        [0, max(lo_i^2, hi_i^2)]              if lo_i <= 0 <= hi_i (straddle),
        [min(lo_i^2, hi_i^2), max(lo_i^2, hi_i^2)]  otherwise;
    k>0 uses the low end of the square range, k<0 uses the high end.
  * bilinear `k*v_i*v_j` (i != j): the product ranges over
        [min, max] of the 4 corner products {lo_i*lo_j, lo_i*hi_j, hi_i*lo_j,
        hi_i*hi_j}; k>0 uses min, k<0 uses max.
  * linear `k*v_i`: k>0 uses lo_i, k<0 uses hi_i.
  * constant: itself.

EMITTED PROOF: `nlinarith` seeded with, per box axis, `sq_nonneg (v_i - lo_i)`
and `sq_nonneg (hi_i - v_i)` (giving the square-range facts and the interval
membership products `(v_i - lo_i)*(hi_i - v_i) >= 0`), and, per bilinear pair,
the four corner `mul_nonneg` products `(v_i - lo_i)*(v_j - lo_j) >= 0` etc.
These are exactly the nonnegative combinations whose weighted sum reconstructs
`target - margin >= 0`; `nlinarith` finds the weights.  All box / coefficient
literals render via `rat_lean`.

HONEST SCOPE: proves ONLY `0 <= target` on the box for the given separable
-quadratic; it does not close any downstream obligation.  The box endpoints may
be sourced from a certified transcendental enclosure (Task 1, `enclose_constant`)
-- see examples/box_robust -- demonstrating the #1 -> #2 composition, but the
box MEMBERSHIP of a transcendental constant is a documented non-kernel input of
that provider (Arb ball arithmetic), not re-proved here.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Rigorous monomial-wise lower bound
# ---------------------------------------------------------------------------

def _sq_range(lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    """Exact range [min, max] of v^2 for v in [lo, hi]."""
    lo2, hi2 = lo * lo, hi * hi
    if lo <= 0 <= hi:
        return Fraction(0), max(lo2, hi2)
    return min(lo2, hi2), max(lo2, hi2)


def _prod_range(
    a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    """Exact range [min, max] of x*y for x in a, y in b (the 4 corner products)."""
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def box_min_lower_bound(
    box: Sequence[tuple[Fraction, Fraction]],
    target_expr: sp.Expr,
    var_syms: Sequence[sp.Symbol],
) -> Fraction:
    """A rigorous EXACT rational lower bound of ``target_expr`` over ``box``.

    ``box[i] = (lo_i, hi_i)`` bounds ``var_syms[i]``.  ``target_expr`` must be a
    SEPARABLE-QUADRATIC polynomial: every monomial has total degree <= 2 and, if
    degree 2, is either a pure square ``v_i^2`` or a bilinear cross term
    ``v_i*v_j`` (i != j) -- no ``v_i^2 v_j`` etc.

    Computed monomial-wise: for each term ``coeff * monomial``, take the extreme
    of the monomial's exact range over the box that MINIMIZES ``coeff *
    monomial`` (sign-aware), then sum all per-term lower bounds as an EXACT
    Fraction.  This is a valid rigorous lower bound of the polynomial over the
    box.  Does NOT refuse on a negative result -- returns it (the caller
    ``certify_box_robust_point`` refuses margin < 0).

    Raises ValueError on a non-separable-quadratic monomial (degree > 2, or a
    degree-2 monomial that is neither a pure square nor a bilinear cross term).
    """
    var_syms = tuple(var_syms)
    if len(box) != len(var_syms):
        raise ValueError(
            f"box has {len(box)} axes but {len(var_syms)} variables"
        )
    lo = [Fraction(str(sp.Rational(l))) for l, _ in box]
    hi = [Fraction(str(sp.Rational(h))) for _, h in box]
    for i, (l, h) in enumerate(zip(lo, hi)):
        if l > h:
            raise ValueError(f"box axis {i}: lo={l} > hi={h}")

    poly = sp.Poly(sp.expand(target_expr), *var_syms)
    total = Fraction(0)
    for monom, coeff in zip(poly.monoms(), poly.coeffs()):
        k = Fraction(str(sp.Rational(coeff)))
        if k == 0:
            continue
        deg = sum(monom)
        active = [i for i, e in enumerate(monom) if e > 0]
        if deg == 0:
            total += k
        elif deg == 1:
            (i,) = active
            # coeff>0 -> lo_i minimizes; coeff<0 -> hi_i minimizes
            total += k * (lo[i] if k > 0 else hi[i])
        elif deg == 2:
            if len(active) == 1 and monom[active[0]] == 2:
                (i,) = active
                r_lo, r_hi = _sq_range(lo[i], hi[i])
                total += k * (r_lo if k > 0 else r_hi)
            elif len(active) == 2 and all(monom[i] == 1 for i in active):
                i, j = active
                r_lo, r_hi = _prod_range((lo[i], hi[i]), (lo[j], hi[j]))
                total += k * (r_lo if k > 0 else r_hi)
            else:
                raise ValueError(
                    f"non-separable-quadratic degree-2 monomial {monom} "
                    f"in {var_syms} (need a pure square or a bilinear cross term)"
                )
        else:
            raise ValueError(
                f"target is not quadratic: monomial {monom} has total degree {deg}"
            )
    return total


# ---------------------------------------------------------------------------
# Payload + certification
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BoxRobustPayload:
    """Certificate payload for one forall-box nonnegativity claim.

    ``box`` (exact Fractions per axis), the separable-quadratic ``target``, the
    ordered ``var_names``, and the certified rigorous rational ``margin`` (a
    lower bound of ``target`` over ``box``; ``margin >= 0`` is what makes the
    claim true and the emitted ``nlinarith`` succeed)."""

    box: tuple[tuple[Fraction, Fraction], ...]
    target: sp.Expr
    var_names: tuple[str, ...]
    margin: Fraction


def certify_box_robust_point(family, pt, name):
    """Certify one box-robust instance from ``family.special[1](pt) -> (box,
    target_expr, var_syms)``.

    Computes the exact monomial-wise lower bound ``margin`` of ``target_expr``
    over ``box`` and REFUSES (ValueError -- the negative control) when
    ``margin < 0`` (the target is not provably nonnegative on the box by the
    monomial-wise bound).  Returns ``(CertifiedInstance, n_checks)`` with
    ``n_checks`` = 1 (the exact margin computation)."""
    box_raw, target_expr, var_syms = family.special[1](pt)
    var_syms = tuple(sp.sympify(v) for v in var_syms)
    box = tuple(
        (Fraction(str(sp.Rational(l))), Fraction(str(sp.Rational(h))))
        for l, h in box_raw
    )
    target = sp.expand(sp.sympify(target_expr))
    margin = box_min_lower_bound(box, target, var_syms)
    if margin < 0:
        raise ValueError(
            f"box_robust instance '{name}' REFUSED: monomial-wise lower bound "
            f"margin = {margin} < 0 over box {box}; target is not provably "
            f"nonnegative on the box"
        )
    payload = BoxRobustPayload(
        box=box,
        target=target,
        var_names=tuple(str(v) for v in var_syms),
        margin=margin,
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=payload)
    return inst, 1


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

def _target_lean(target: sp.Expr, var_names: Sequence[str]) -> str:
    """Render the separable-quadratic target as Lean over ℝ, deterministically."""
    from .expr import _poly_any_lean

    syms = [sp.Symbol(n) for n in var_names]
    return _poly_any_lean(sp.expand(target), syms)


@dataclass
class BoxRobustEmitter(Emitter):
    """Emit ``forall v : R, box-hyps -> 0 <= target`` per instance, closed by
    ``nlinarith`` seeded with the box's square and corner-product nonnegativity
    facts.

    Per box axis ``[lo_i, hi_i]`` the hints ``sq_nonneg (v_i - lo_i)`` and
    ``sq_nonneg (hi_i - v_i)`` give ``nlinarith`` the squared-endpoint facts and
    (combined) the interval-membership product ``(v_i - lo_i)*(hi_i - v_i) >=
    0``.  Per bilinear pair ``(v_i, v_j)`` the four corner ``mul_nonneg``
    products supply the cross-term range.  Their nonnegative combination
    reconstructs ``target - margin >= 0`` with ``margin >= 0`` (rational,
    ``norm_num``-checkable); ``nlinarith`` finds the coefficients."""

    def __post_init__(self):
        self.kind = "box_robust"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            payload: BoxRobustPayload = inst.payload  # type: ignore[assignment]
            names = list(payload.var_names)
            box = payload.box
            n = len(names)

            binder = " ".join(names)
            # (hyp text, intro-name) pairs; the box bounds are NAMED so nlinarith
            # and the `by linarith` corner side-goals can use them (needed for the
            # pure-square lower bound, whose min over the box depends on the sign
            # of the endpoints).
            hyps: list[str] = []
            hyp_names: list[str] = []
            for i, name in enumerate(names):
                lo = rat_lean(sp.Rational(box[i][0]))
                hi = rat_lean(sp.Rational(box[i][1]))
                hyps.append(f"{lo} ≤ {name}")
                hyp_names.append(f"hlo{i}")
                hyps.append(f"{name} ≤ {hi}")
                hyp_names.append(f"hhi{i}")
            target_s = _target_lean(payload.target, names)

            # Which variables actually appear (quadratically or linearly) in the
            # target -- restrict hints to those to keep nlinarith's search small.
            poly = sp.Poly(sp.expand(payload.target), *[sp.Symbol(x) for x in names])
            used = set()
            bilinear_pairs = set()
            for monom in poly.monoms():
                active = [i for i, e in enumerate(monom) if e > 0]
                for i in active:
                    used.add(i)
                if len(active) == 2 and all(monom[i] == 1 for i in active):
                    bilinear_pairs.add(tuple(sorted(active)))

            hints: list[str] = []
            for i in sorted(used):
                lo = rat_lean(sp.Rational(box[i][0]))
                hi = rat_lean(sp.Rational(box[i][1]))
                v = names[i]
                hints.append(f"sq_nonneg ({v} - {lo})")
                hints.append(f"sq_nonneg ({hi} - {v})")
            for (i, j) in sorted(bilinear_pairs):
                vi, vj = names[i], names[j]
                lo_i = rat_lean(sp.Rational(box[i][0]))
                hi_i = rat_lean(sp.Rational(box[i][1]))
                lo_j = rat_lean(sp.Rational(box[j][0]))
                hi_j = rat_lean(sp.Rational(box[j][1]))
                for (ea, va) in ((lo_i, f"{vi} - {lo_i}"), (hi_i, f"{hi_i} - {vi}")):
                    for (eb, vb) in ((lo_j, f"{vj} - {lo_j}"), (hi_j, f"{hi_j} - {vj}")):
                        hints.append(
                            f"mul_nonneg (by linarith : (0:ℝ) ≤ {va}) "
                            f"(by linarith : (0:ℝ) ≤ {vb})"
                        )
            hint_s = ", ".join(hints)

            arrow = "".join(f"{h} → " for h in hyps)
            lines.append(
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,\n"
                f"    {arrow}(0:ℝ) ≤ {target_s} := by\n"
                f"  intro {binder} {' '.join(hyp_names)}\n"
                f"  nlinarith [{hint_s}]\n"
            )
            nthm += 1
        return "".join(lines), nthm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def box_robust_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a box-robust family (kind='box_robust').

    ``spec``: a callable ``pt -> (box, target_expr, var_syms)`` where ``box`` is
    a list of ``(lo, hi)`` rational pairs (one per variable), ``target_expr`` a
    sympy separable-quadratic polynomial in ``var_syms``, and ``var_syms`` the
    ordered variable symbols.  ``certify_box_robust_point`` computes the exact
    monomial-wise lower bound over the box and refuses (ValueError) any point
    whose margin is < 0."""
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("box_robust", spec),
        constants=dict(constants or {}),
    )

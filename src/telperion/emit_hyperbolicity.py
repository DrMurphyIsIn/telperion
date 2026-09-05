"""Hyperbolicity emitter (#3, d=2): real-rootedness of a quadratic over a box.

For a rational box of quadratic coefficients `[a0, a1, a2]` (constant -> leading),
this emitter certifies and emits the kernel theorem

    theorem <name> : forall a0 a1 a2 : R,
        (box bounds on a0, a1, a2) ->
        (C a2 * X^2 + C a1 * X + C a0).roots.card = 2

i.e. EVERY quadratic whose coefficients lie in the box is real-rooted (its `roots`
multiset -- roots counted with multiplicity -- has cardinality exactly 2 = the
degree; the double-root case is carried by the multiplicity).  This is the d=2
"hyperbolicity" / real-rootedness certificate: a polynomial is hyperbolic iff all
its roots are real.

CERTIFICATE (two facts, both box-robust):
  * `a2 != 0` on the box -- provable only when the leading-coefficient box does NOT
    straddle 0.  We store `leading_sign` (+ if lo > 0, - if hi < 0) and emit the
    matching `ne_of_gt` / `ne_of_lt` from the box bound.
  * `0 <= a1^2 - 4*a2*a0` (the discriminant) on the box -- a rigorous rational lower
    bound `discrim_margin` computed MONOMIAL-WISE by `box_min_lower_bound` (#2) over
    the box.  A box whose margin is <= 0 is REFUSED (ValueError, the negative
    control): the discriminant is not provably nonnegative there, so real-rootedness
    is not certified.

These chain into the prelude bridge lemma

    hyperbolic_deg2_of_discrim_nonneg (a b c : R) (ha : a != 0)
        (h : 0 <= b^2 - 4*a*c) :
        (C a * X^2 + C b * X + C c).roots.card = 2

applied as `hyperbolic_deg2_of_discrim_nonneg a2 a1 a0 ha hdisc` (bridge `a=a2`,
`b=a1`, `c=a0`).  The discriminant fact is discharged by `nlinarith` seeded with the
same box `sq_nonneg` / corner `mul_nonneg` hints as #2 (`box_min_lower_bound`'s hint
structure); `ha` is discharged from the box's sign bound.

HONEST SCOPE: only d=2 is supported (raises a clear error otherwise).  Proves ONLY
real-rootedness of the quadratic on the box; it does not order the roots or close any
downstream obligation.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .emit_box_robust import box_min_lower_bound
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Payload + certification
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class HyperbolicityPayload:
    """Certificate payload for one forall-box real-rootedness claim.

    ``coeff_box`` gives the rational bounds ``(lo_i, hi_i)`` for each coefficient
    ``a_i`` in order ``[a0 .. ad]`` (constant -> leading).  ``degree`` is ``d`` (only
    ``2`` is supported).  ``discrim_margin`` is the certified rigorous rational lower
    bound of the discriminant ``a1^2 - 4*a2*a0`` over the box (``> 0`` is what makes
    the claim provable).  ``leading_sign`` is ``+1`` if the leading-coefficient box is
    all-positive (``lo > 0``) or ``-1`` if all-negative (``hi < 0``) -- the sign used
    to emit the ``a2 != 0`` fact."""

    coeff_box: tuple[tuple[Fraction, Fraction], ...]
    degree: int
    discrim_margin: Fraction
    leading_sign: int


def certify_hyperbolicity_point(family, pt, name):
    """Certify one hyperbolicity instance from ``family.special[1](pt) ->
    (coeff_box, degree)``.

    ``coeff_box`` = list of ``(lo, hi)`` rational pairs for ``[a0 .. ad]``.  For
    ``d = 2`` the polynomial is ``a2*X^2 + a1*X + a0`` and the discriminant target is
    ``a1^2 - 4*a2*a0``; the margin is the exact monomial-wise lower bound
    (`box_min_lower_bound`) over the box.  REFUSES (ValueError -- the negative
    control) when the margin is ``<= 0`` (discriminant not provably nonnegative) OR
    when the leading-coefficient (``a2``) box straddles 0 (``a2 != 0`` unprovable).
    Only ``d = 2`` is supported; any other degree raises a clear error.  Returns
    ``(CertifiedInstance, n_checks)`` with ``n_checks = 2`` (margin + leading sign)."""
    coeff_box_raw, degree = family.special[1](pt)
    if degree != 2:
        raise ValueError(
            f"hyperbolicity instance '{name}': only degree d=2 is supported, "
            f"got d={degree}"
        )
    box = tuple(
        (Fraction(str(sp.Rational(l))), Fraction(str(sp.Rational(h))))
        for l, h in coeff_box_raw
    )
    if len(box) != degree + 1:
        raise ValueError(
            f"hyperbolicity instance '{name}': degree {degree} needs {degree + 1} "
            f"coefficient bounds [a0..a{degree}], got {len(box)}"
        )
    (a0_lo, a0_hi), (a1_lo, a1_hi), (a2_lo, a2_hi) = box
    for i, (lo, hi) in enumerate(box):
        if lo > hi:
            raise ValueError(
                f"hyperbolicity instance '{name}': coeff a{i} box lo={lo} > hi={hi}"
            )
    # Leading-coefficient sign: must not straddle 0 (else a2 != 0 is unprovable).
    if a2_lo > 0:
        leading_sign = 1
    elif a2_hi < 0:
        leading_sign = -1
    else:
        raise ValueError(
            f"hyperbolicity instance '{name}' REFUSED: leading-coefficient box "
            f"[{a2_lo}, {a2_hi}] straddles 0; cannot prove a2 != 0 (negative control)"
        )
    # Discriminant margin: rigorous monomial-wise lower bound of a1^2 - 4*a2*a0
    # over the box, in the box-variable order (a0, a1, a2).
    a0, a1, a2 = sp.symbols("a0 a1 a2")
    discrim = a1 ** 2 - 4 * a2 * a0
    margin = box_min_lower_bound(box, discrim, (a0, a1, a2))
    if margin <= 0:
        raise ValueError(
            f"hyperbolicity instance '{name}' REFUSED: discriminant lower bound "
            f"margin = {margin} <= 0 over box {box}; a1^2 - 4*a2*a0 is not provably "
            f"nonnegative on the box (negative control)"
        )
    payload = HyperbolicityPayload(
        coeff_box=box,
        degree=degree,
        discrim_margin=margin,
        leading_sign=leading_sign,
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=payload)
    return inst, 2


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class HyperbolicityEmitter(Emitter):
    """Emit ``forall a0 a1 a2 : R, box-hyps -> (C a2*X^2 + C a1*X + C a0).roots.card
    = 2`` per instance, closed by the prelude bridge lemma.

    The proof establishes ``ha : a2 != 0`` from the box sign (``ne_of_gt`` /
    ``ne_of_lt`` via the leading-coefficient bound) and ``hdisc : 0 <= a1^2 - 4*a2*a0``
    by ``nlinarith`` seeded with the box's ``sq_nonneg`` / corner ``mul_nonneg`` facts
    (the #2 box-robust hint structure), then applies
    ``hyperbolic_deg2_of_discrim_nonneg a2 a1 a0 ha hdisc``.  A statement-match gate is
    appended, single-sourced with the theorem type string."""

    def __post_init__(self):
        self.kind = "hyperbolicity"
        self.requires_prelude = ("hyperbolic_deg2_of_discrim_nonneg",)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            payload: HyperbolicityPayload = inst.payload  # type: ignore[assignment]
            if payload.degree != 2:  # defensive; certify already guards this
                raise ValueError(
                    f"hyperbolicity emitter: only d=2 supported, got {payload.degree}"
                )
            box = payload.coeff_box
            names = ["a0", "a1", "a2"]
            (a0_lo, a0_hi), (a1_lo, a1_hi), (a2_lo, a2_hi) = box

            # Box hypotheses (all three axes named so nlinarith / the a2!=0 proof
            # can use them).
            hyps: list[str] = []
            hyp_names: list[str] = []
            for i, nm in enumerate(names):
                lo = rat_lean(sp.Rational(box[i][0]))
                hi = rat_lean(sp.Rational(box[i][1]))
                hyps.append(f"{lo} ≤ {nm}")
                hyp_names.append(f"hlo{i}")
                hyps.append(f"{nm} ≤ {hi}")
                hyp_names.append(f"hhi{i}")
            arrow = "".join(f"{h} → " for h in hyps)

            # The polynomial and the roots.card target type (single-sourced).
            poly = "Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0"
            thm_type = f"∀ a0 a1 a2 : ℝ, {arrow}({poly}).roots.card = 2"

            # a2 != 0 from the box sign (leading-coeff bound named hlo2 / hhi2 is in
            # scope, so `linarith` derives 0 < a2 or a2 < 0).
            if payload.leading_sign > 0:
                ha_proof = (
                    "  have ha : a2 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < a2)\n"
                )
            else:
                ha_proof = (
                    "  have ha : a2 ≠ 0 := ne_of_lt (by linarith : a2 < (0:ℝ))\n"
                )

            # Discriminant nonneg via box-robust nlinarith (same hint structure as #2).
            # Discriminant target a1^2 - 4*a2*a0; monomials touch a0, a1, a2 and the
            # bilinear pair (a0, a2).
            hints: list[str] = []
            for i, nm in enumerate(names):
                lo = rat_lean(sp.Rational(box[i][0]))
                hi = rat_lean(sp.Rational(box[i][1]))
                hints.append(f"sq_nonneg ({nm} - {lo})")
                hints.append(f"sq_nonneg ({hi} - {nm})")
            # bilinear corner products for (a0, a2) -- the -4*a2*a0 cross term.
            a0_lo_s, a0_hi_s = rat_lean(sp.Rational(a0_lo)), rat_lean(sp.Rational(a0_hi))
            a2_lo_s, a2_hi_s = rat_lean(sp.Rational(a2_lo)), rat_lean(sp.Rational(a2_hi))
            for (va) in (f"a0 - {a0_lo_s}", f"{a0_hi_s} - a0"):
                for (vb) in (f"a2 - {a2_lo_s}", f"{a2_hi_s} - a2"):
                    hints.append(
                        f"mul_nonneg (by linarith : (0:ℝ) ≤ {va}) "
                        f"(by linarith : (0:ℝ) ≤ {vb})"
                    )
            hint_s = ", ".join(hints)

            lines.append(
                f"theorem {inst.lean_name} : {thm_type} := by\n"
                f"  intro a0 a1 a2 {' '.join(hyp_names)}\n"
                f"{ha_proof}"
                f"  have hdisc : (0:ℝ) ≤ a1 ^ 2 - 4 * a2 * a0 := by\n"
                f"    nlinarith [{hint_s}]\n"
                f"  exact hyperbolic_deg2_of_discrim_nonneg a2 a1 a0 ha hdisc\n"
            )
            gate = self.emit_gate(inst.lean_name, thm_type)
            if gate:
                lines.append(gate)
            nthm += 1
        return "".join(lines), nthm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def hyperbolicity_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a hyperbolicity family (kind='hyperbolicity').

    ``spec``: a callable ``pt -> (coeff_box, degree)`` where ``coeff_box`` is a list of
    ``(lo, hi)`` rational pairs for ``[a0 .. ad]`` (constant -> leading) and ``degree``
    is ``d`` (only ``d = 2`` is supported).  ``certify_hyperbolicity_point`` computes
    the exact discriminant lower bound over the box and refuses (ValueError) any point
    whose margin is ``<= 0`` or whose leading-coefficient box straddles 0."""
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("hyperbolicity", spec),
        constants=dict(constants or {}),
    )

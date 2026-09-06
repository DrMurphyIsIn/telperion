"""Turan-box convenience emitter (#5): log-concavity a1^2 >= a0*a2 over a rational box.

DESIGN A (DRY delegation): `turan_box_family` returns a ``box_robust``-KIND
family whose ``special`` inner spec translates the user's three interval-enclosed
sequence values ``(a0_box, a1_box, a2_box)`` into the canonical box-robust
triple ``(box, target, var_syms)`` with ``target = a1**2 - a0*a2``.  No new
kind registration, no new certify dispatch, no new emitter class -- everything
flows through the existing #2 (box_robust) machinery end to end, including the
``certify_box_robust_point`` refusal gate (margin < 0 raises ValueError, wrapped
by ``certify()`` into CertificationError), the ``BoxRobustEmitter``, and the
statement-match gate.

API:

    turan_box_family(name, symbols, grid, lean_name, spec)

where ``spec(pt) -> (a0_box, a1_box, a2_box)`` and each box is a
``(Fraction, Fraction)`` (lo, hi) pair.  The emitted theorem is:

    theorem <name> : forall a0 a1 a2 : R,
        lo0 <= a0 -> a0 <= hi0 ->
        lo1 <= a1 -> a1 <= hi1 ->
        lo2 <= a2 -> a2 <= hi2 ->
        (0:R) <= a1^2 - a0*a2

discharged by ``nlinarith`` via the #2 infrastructure.  The exact rational
margin ``a1^2 - a0*a2 >= margin`` is verified by ``box_min_lower_bound`` over
``[a0_box, a1_box, a2_box]``; a triple with margin < 0 is REFUSED (the negative
control).

HONEST SCOPE: certifies ONLY ``0 <= a1^2 - a0*a2`` on the box; does not prove
the sequence is log-concave in any broader sense or close any downstream
obligation.  conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .emit_box_robust import box_robust_family
from .family import GridSpec, InequalityFamily


# Fixed symbolic names for the three sequence-value variables.
_a0, _a1, _a2 = sp.symbols("a0 a1 a2")
_TARGET = _a1 ** 2 - _a0 * _a2


def _make_inner_spec(user_spec: Callable) -> Callable:
    """Wrap ``user_spec(pt) -> (a0_box, a1_box, a2_box)`` into the box_robust
    inner-spec signature ``pt -> (box, target_expr, var_syms)``."""

    def inner(pt):
        a0_box, a1_box, a2_box = user_spec(pt)
        # Normalise each box endpoint to Fraction for exact arithmetic.
        def _frac(x):
            if isinstance(x, Fraction):
                return x
            return Fraction(str(sp.Rational(x)))

        box = [
            (_frac(a0_box[0]), _frac(a0_box[1])),
            (_frac(a1_box[0]), _frac(a1_box[1])),
            (_frac(a2_box[0]), _frac(a2_box[1])),
        ]
        return box, _TARGET, (_a0, _a1, _a2)

    return inner


def turan_box_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Turan-box (log-concavity) family delegating to box_robust (#2).

    ``spec``: a callable ``pt -> (a0_box, a1_box, a2_box)`` where each box is a
    ``(lo, hi)`` pair of rationals (Fraction or anything coercible to
    ``sp.Rational``).  The certified target is ``a1**2 - a0*a2``; a triple whose
    monomial-wise lower bound is < 0 is REFUSED by ``certify()`` with a
    CertificationError.

    The returned family has ``special = ("box_robust", inner_spec)`` so it is
    processed entirely by the box_robust certification and emission path -- no
    separate kind registration is needed."""
    inner_spec = _make_inner_spec(spec)
    return box_robust_family(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        spec=inner_spec,
        constants=constants,
    )

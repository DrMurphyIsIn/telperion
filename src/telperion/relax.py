"""The relaxation probe: is this family's truth SMOOTH or ARITHMETIC?

The origin campaign's decisive strategic insight came from relaxing an integer
parameter to a continuous one and discovering the relaxation VIOLATES the
bound (Φ(c* = 3.82) = 1.00004 > 1) — proving no smooth certificate could ever
close the claim and redirecting the whole effort toward integrality.  This
probe automates the maneuver for any integer grid axis:

* interpolate the axis continuously between consecutive grid values;
* adversarially minimize the claim over (symbols × fractional axis values),
  exactly;
* verdict ARITHMETIC with an exact fractional witness if the relaxation goes
  negative — the family is true only BECAUSE the axis is integral; stop
  hunting for analytic certificates (lifting/SOS certify over the reals and
  can never see integrality) and reach for the arithmetic tools (symbolic
  tails, unimodality, `decide`);
* verdict SMOOTH-SO-FAR otherwise — analytic certificates remain viable
  (evidence, not proof).
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .family import InequalityFamily
from .hunt import HuntResult, hunt_minimum


@dataclass(frozen=True)
class RelaxationVerdict:
    axis: str
    verdict: str                 # "ARITHMETIC" | "SMOOTH_SO_FAR"
    witness: dict | None         # exact fractional point where the claim fails
    witness_value: sp.Rational | None
    segments_checked: int

    def render(self) -> str:
        if self.verdict == "ARITHMETIC":
            wit = ", ".join(f"{k} = {v}" for k, v in self.witness.items())
            return (
                f"ARITHMETIC: the continuous relaxation of axis {self.axis!r} "
                f"violates the claim ({self.witness_value} at {wit}). The family "
                "is true only because the axis is integral — no smooth "
                "certificate (Polya lift, SOS) can close it; use arithmetic "
                "tools (symbolic tails, unimodality, decide)."
            )
        return (
            f"SMOOTH-SO-FAR: no violation found on {self.segments_checked} "
            f"interpolated segment(s) of axis {self.axis!r} — analytic "
            "certificates remain viable (evidence, not proof)."
        )


def relax_probe(
    family: InequalityFamily,
    axis: str,
    iters: int = 200,
    seed: int = 0,
) -> RelaxationVerdict:
    """Hunt the continuous interpolation of an integer grid axis for exact
    violations.  Direct families; target(pt) must accept a sympy Rational for
    the axis value (it already does if the target is built symbolically)."""
    if family.kind != "direct":
        raise ValueError("relax_probe supports direct families in v1")
    axes = dict(family.grid.axes)
    if axis not in axes:
        raise ValueError(f"no grid axis {axis!r}")
    values = sorted(v for v in axes[axis] if isinstance(v, int))
    other_axes = [(n, vs) for n, vs in family.grid.axes if n != axis]

    def other_points(i=0, acc=None):
        acc = acc or {}
        if i == len(other_axes):
            yield dict(acc)
            return
        n, vs = other_axes[i]
        for v in vs:
            acc[n] = v
            yield from other_points(i + 1, acc)
        acc.pop(n, None)

    theta = sp.Symbol("_theta", nonnegative=True)
    segments = 0
    for a0, a1 in zip(values, values[1:]):
        for opt in other_points():
            segments += 1
            pt = dict(opt)
            pt[axis] = sp.Integer(a0) + theta * (a1 - a0)
            expr = family.target(pt)
            res: HuntResult = hunt_minimum(
                expr,
                tuple(family.symbols) + (theta,),
                iters=iters,
                seed=seed + segments,
                hi={theta: sp.Integer(1)},
            )
            if res.is_disproof:
                wit = dict(res.argmin)
                frac = wit.pop("_theta")
                wit[axis] = a0 + frac * (a1 - a0)
                return RelaxationVerdict(
                    axis=axis,
                    verdict="ARITHMETIC",
                    witness=wit,
                    witness_value=res.minimum,
                    segments_checked=segments,
                )
    return RelaxationVerdict(
        axis=axis,
        verdict="SMOOTH_SO_FAR",
        witness=None,
        witness_value=None,
        segments_checked=segments,
    )

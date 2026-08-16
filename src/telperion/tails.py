"""Symbolic-tail families: claims of the shape "for all K ≥ K₀".

Half of asymptotic combinatorics certifies a finite table plus an
eventually-true tail (the origin campaign's shedding lemmas: four families
each proven for K ≥ 40, finite table below).  A `TailFrom` axis makes that a
first-class shape: the axis contributes its explicit finite values as ordinary
grid points, plus ONE symbolic instance where the axis value is ``K₀ + t``
with ``t`` a fresh nonnegative symbol — the tail certificate is then an
ordinary Polya certificate over the extended symbol set (t is just another
nonnegative variable; lifting applies to it like any other).

`TailNatEmitter` wraps the tail certificate as the ℕ-quantified statement
``∀ K : ℕ, K₀ ≤ K → 0 ≤ f(K)`` via the `Nat.cast_sub` reparameterization
(t := (K − K₀ : ℕ) cast to ℝ) — the same proven adapter shape as Kind 2,
threading the family's other real symbols through unchanged.
Direct families, v1.
"""


from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .certify import CertifiedFamily
from .expr import expr_lean_factored
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile, render
from .workflow import Emitter

TAIL_SKELETON = """theorem «name» «binders» :
    0 ≤ «nat_body» := by
  have e : ((K : ℝ) - «k0») = ((K - «k0» : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hK]
    ring
  rw [e]
  have himg : (0 : ℝ) ≤ ((K - «k0» : ℕ) : ℝ) := by positivity
  exact «base_name» «call»
"""





@dataclass(frozen=True)
class TailFrom:
    """Axis values: the explicit range [lo, threshold) plus the symbolic tail
    K = threshold + t.  `lo` defaults to threshold (tail only)."""

    threshold: int
    lo: int | None = None

    def explicit_values(self) -> list[int]:
        lo = self.threshold if self.lo is None else self.lo
        return list(range(lo, self.threshold))


TAIL_SENTINEL = "__tail__"


def tail_family(
    name: str,
    axis: str,
    tail: TailFrom,
    symbols,
    target,
    lean_name,
    other_axes=(),
    **kwargs,
) -> InequalityFamily:
    """Build a direct family whose ``axis`` runs over tail.explicit_values()
    plus the symbolic tail.  ``target(pt)`` receives pt[axis] as either an int
    or the sympy expression K₀ + t; ``lean_name(pt)`` likewise (the sentinel
    value pt["__tail__"] = True marks the tail instance)."""
    t = sp.Symbol(f"t_{axis}", nonnegative=True)
    values = tail.explicit_values() + [TAIL_SENTINEL]

    def wrapped_target(pt):
        pt2 = dict(pt)
        if pt2[axis] == TAIL_SENTINEL:
            pt2[axis] = tail.threshold + t
            pt2[TAIL_SENTINEL] = True
        else:
            # sp.Integer so int/int in the user's target stays exact (a bare
            # python 3/4 is a float — the certifier would refuse it)
            pt2[axis] = sp.Integer(pt2[axis])
            pt2[TAIL_SENTINEL] = False
        return target(pt2)

    def wrapped_name(pt):
        pt2 = dict(pt)
        if pt2[axis] == TAIL_SENTINEL:
            pt2[axis] = f"ge{tail.threshold}"
            pt2[TAIL_SENTINEL] = True
        else:
            pt2[TAIL_SENTINEL] = False
        return lean_name(pt2)

    return InequalityFamily(
        name=name,
        symbols=tuple(symbols) + (t,),
        grid=GridSpec(list(other_axes) + [(axis, values)]),
        lean_name=wrapped_name,
        target=wrapped_target,
        **kwargs,
    )


@dataclass
class TailNatEmitter(Emitter):
    """The ℕ-quantified tail theorem: for the (single) tail instance, restate
    over (K : ℕ) with K₀ ≤ K via t := ((K − K₀ : ℕ) : ℝ).  Pair with
    DirectPolyaEmitter (which emits the per-value and symbolic-tail
    certificates this adapter delegates to)."""

    axis: str = "K"
    threshold: int = 0

    def __post_init__(self):
        self.kind = "tail_nat"

    def emit_units(self, fam: CertifiedFamily, profile: LeanProfile):
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        import re

        t = sp.Symbol(f"t_{self.axis}", nonnegative=True)
        tails = [
            inst
            for inst in fam.instances
            if inst.point.get(self.axis) == TAIL_SENTINEL
        ]
        out = []
        k0 = self.threshold
        others = tuple(s for s in fam.family.symbols if s != t)
        for inst in tails:
            body = expr_lean_factored(inst.corners[0].expr, fam.family.symbols)
            nat_body = re.sub(rf"\bt_{self.axis}\b", f"((K : ℝ) - {k0})", body)
            other_binders = (
                f"({' '.join(str(s) for s in others)} : ℝ) "
                + " ".join(f"(h{s} : 0 ≤ {s})" for s in others)
                + " "
                if others
                else ""
            )
            image = f"((K - {k0} : ℕ) : ℝ)"
            # base binder order (from _binders): all symbols, then all hyps
            call = " ".join(
                [str(s) for s in others]
                + [image]
                + [f"h{s}" for s in others]
                + ["himg"]
            )
            out.append(
                render(
                    profile.skeletons.get("tail_nat", TAIL_SKELETON),
                    {
                        "name": f"{inst.lean_name}_nat",
                        "binders": f"{other_binders}(K : ℕ) (hK : {k0} ≤ K)",
                        "nat_body": nat_body,
                        "k0": str(k0),
                        "base_name": inst.lean_name,
                        "call": call,
                    },
                )
            )
        return "\n".join(out), len(tails)

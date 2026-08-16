"""Family definitions: the user-facing description of an inequality family.

A family is a finite grid of instances.  Each instance is either a DIRECT claim
(``0 <= target``) over nonnegative real symbols, or a BILINEAR BOX claim
(``before <= after`` on a rectangle in two bound variables, reduced to four
corner certificates).  Everything downstream — certification, validation,
emission — consumes this one description.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Iterator, Mapping, Sequence

import sympy as sp

GridPoint = Mapping[str, int]


@dataclass(frozen=True)
class GridSpec:
    """Finite discrete parameter grid, e.g. ``axes=(("cA", range(6)), ("cb", range(6)))``."""

    axes: tuple[tuple[str, tuple[int, ...]], ...]

    def __init__(self, axes: Sequence[tuple[str, Sequence[int]]]):
        object.__setattr__(
            self, "axes", tuple((name, tuple(vals)) for name, vals in axes)
        )

    def points(self) -> Iterator[GridPoint]:
        def rec(i: int, acc: dict[str, int]) -> Iterator[GridPoint]:
            if i == len(self.axes):
                yield dict(acc)
                return
            name, vals = self.axes[i]
            for v in vals:
                acc[name] = v
                yield from rec(i + 1, acc)
            acc.pop(name, None)

        yield from rec(0, {})

    def size(self) -> int:
        n = 1
        for _, vals in self.axes:
            n *= len(vals)
        return n


@dataclass(frozen=True)
class BoxAxis:
    """One axis of a bilinear box: the bound symbol, its corner values, and the
    lower-bound hypothesis shape.

    ``lo``/``hi`` are sympy expressions in the family's continuous symbols.
    ``lo_is_floor=True`` states the hypothesis as ``lo <= s`` (a floor);
    otherwise the hypothesis is ``0 <= s`` and ``lo`` must be 0.
    """

    symbol: sp.Symbol
    lo: sp.Expr
    hi: sp.Expr
    lo_is_floor: bool = False

    def __post_init__(self):
        if not self.lo_is_floor and sp.simplify(self.lo) != 0:
            raise ValueError(
                f"BoxAxis({self.symbol}): lo must be 0 unless lo_is_floor=True"
            )


@dataclass(frozen=True)
class InequalityFamily:
    """A grid-indexed family of rational-function inequalities.

    Exactly one of ``target`` (direct: ``0 <= target(pt)``) or the pair
    ``before``/``after`` (bilinear box: ``before(pt) <= after(pt)`` on
    ``box(pt)``) must be supplied.  All expressions are in ``symbols``
    (assumed ``>= 0``) plus, for the bilinear kind, the two box symbols.

    ``lean_name`` maps a grid point to the Lean theorem base name.
    ``den_atoms`` optionally lists the denominator atoms whose ``!= 0``
    hypotheses ``field_simp`` will need, in the syntactic form it will see;
    when omitted they are derived from the certified denominators.
    """

    name: str
    symbols: tuple[sp.Symbol, ...]
    grid: GridSpec
    lean_name: Callable[[GridPoint], str]
    constants: Mapping[str, sp.Rational] = field(default_factory=dict)
    target: Callable[[GridPoint], sp.Expr] | None = None
    equation: Callable[[GridPoint], tuple[sp.Expr, sp.Expr]] | None = None
    # Witness-search claims (the per-residue comparator pattern): candidates(pt)
    # yields (label, expr) pairs; the claim is EXISTENTIAL — some candidate
    # certifies 0 <= expr.  The certifier records the winning label (the
    # deloading_winner_table pattern); the emitted theorem states the found
    # witness concretely.
    witnesses: Callable[[GridPoint], Sequence[tuple[str, sp.Expr]]] | None = None
    witnesses_complete: bool = False   # declared-complete candidate space:
                                       # exhaustion becomes PROVEN impossibility
    before: Callable[[GridPoint], sp.Expr] | None = None
    after: Callable[[GridPoint], sp.Expr] | None = None
    box: Callable[[GridPoint], tuple[BoxAxis, BoxAxis]] | None = None
    den_atoms: Callable[[GridPoint], Sequence[sp.Expr]] | None = None
    auto_lift: int = 0        # max Polya-lift exponent tried on numerator refusals
    auto_subdivide: int = 0   # max box-bisection depth on corner refusals
    # The honesty declarations (the origin campaign's overclaim trap):
    # ties(pt) -> substitution dicts where the claim MUST be exactly tight; the
    # certifier asserts both the target and the certificate numerator vanish
    # there exactly (a certificate with positive slack at a declared tie is
    # refused as an overclaim).  anchors(pt) -> (substitution, exact value)
    # pairs pinning the pipeline to known evaluations.
    ties: Callable[[GridPoint], Sequence[Mapping]] | None = None
    anchors: Callable[[GridPoint], Sequence[tuple[Mapping, sp.Rational]]] | None = None
    # The dual-engine discipline (the pi(T(3,3,3)) = 19683/256 pattern): an
    # INDEPENDENT, non-sympy implementation of the target —
    # independent_target(pt, point) with point a {symbol name: Fraction} dict,
    # returning a Fraction.  Certification cross-checks it exactly at seeded
    # rational points; a disagreement between the two engines is a refusal.
    independent_target: Callable[..., object] | None = None

    def __post_init__(self):
        modes = [
            self.target is not None,
            self.before is not None and self.after is not None,
            self.equation is not None,
            self.witnesses is not None,
        ]
        if sum(modes) != 1:
            raise ValueError(
                "supply exactly one of `target`, (`before`, `after`), "
                "`equation`, or `witnesses`"
            )
        if modes[1] and self.box is None:
            raise ValueError("bilinear families require `box`")

    @property
    def kind(self) -> str:
        if self.target is not None:
            return "direct"
        if self.equation is not None:
            return "equation"
        if self.witnesses is not None:
            return "witness"
        return "bilinear"

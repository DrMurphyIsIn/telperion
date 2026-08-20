"""Nullstellensatz / ideal-membership emitter — a polynomial VANISHES on the
variety of an ideal, certified by explicit cofactors.

Where every other Telperion emitter proves an INEQUALITY, this one proves an
EQUALITY on an algebraic variety — a distinct capability class.  If

    p ≡ Σ_i h_i · g_i      (exact identity),

i.e. `p` lies in the ideal `⟨g_1, …, g_m⟩` with cofactors `h_i`, then `p`
vanishes wherever all the generators vanish:

    ∀ x, (g_1(x) = 0 ∧ … ∧ g_m(x) = 0) → p(x) = 0.

The finite witness is the cofactor tuple `(h_1, …, h_m)` — exactly what a Gröbner
reduction produces.  Telperion COMPUTES it (via `sympy.reduced`, reducing `p` by
the generators) and verifies the remainder is zero; a `p` that does NOT reduce to
zero is not certified as an ideal member and is REFUSED.

The emitted Lean is a single, maximally-robust tactic — Mathlib's
`linear_combination`, which is exactly the ideal-membership checker (it closes
`p = 0` iff `p − Σ h_i·(g_i − 0)` ring-reduces to zero):

    theorem <name> : ∀ x y : ℝ, g_1 = 0 → … → g_m = 0 → p = 0 := by
      intro x y h_1 … h_m
      linear_combination h_1 * (h₁-cofactor) + … + h_m * (h_m-cofactor)

A wrong cofactor makes the linear combination fail — the false certificate cannot
compile (and is already refused at certification).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def certify_nullstellensatz_point(family, pt, name):
    """Certify one ideal-membership instance: (CertifiedInstance, n_checks).

    Reads (p, gens) = family.special[1](pt): the target `p` and the ideal
    generators `gens`.  Reduces `p` by the generators (`sympy.reduced`) to obtain
    cofactors and a remainder; certifies membership iff the remainder is zero and
    `p = Σ h_i g_i` exactly.  Raises ValueError (a refusal) when `p` is not in the
    ideal — no Lean is emitted for a non-member."""
    p, gens = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    gens = [sp.expand(sp.sympify(g)) for g in gens]
    syms = tuple(family.symbols)
    if not gens:
        raise ValueError(
            f"nullstellensatz instance '{name}' REFUSED: no generators")

    try:
        cofactors, remainder = sp.reduced(p, gens, *syms)
    except Exception as e:  # pragma: no cover — sympy domain failure = refusal
        raise ValueError(
            f"nullstellensatz instance '{name}' REFUSED: reduction failed ({e})"
        ) from e
    if sp.expand(remainder) != 0:
        raise ValueError(
            f"nullstellensatz instance '{name}' REFUSED: p does not reduce to 0 "
            f"modulo the generators (remainder {sp.expand(remainder)}) — p is not "
            "in the ideal ⟨g_1, …, g_m⟩")
    checks = 1
    if sp.expand(p - sum(h * g for h, g in zip(cofactors, gens))) != 0:
        raise ValueError(
            f"nullstellensatz instance '{name}' REFUSED: cofactors do not "
            "reproduce p exactly")
    checks += 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, gens, [sp.expand(h) for h in cofactors]),
    )
    return inst, checks


@dataclass
class NullstellensatzEmitter(Emitter):
    """Emit `∀x, (⋀ g_i = 0) → p = 0` from ideal-membership cofactors
    `p = Σ h_i g_i`, via a single `linear_combination Σ h_i * (hyp_i)`.
    Deterministic order: grid order."""

    def __post_init__(self):
        self.kind = "nullstellensatz"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            p, gens, cofactors = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            hyp_names = [f"hg{i}" for i in range(1, len(gens) + 1)]
            hyp_arrows = "".join(
                f" {expr_lean(sp.expand(g), syms)} = 0 →" for g in gens)
            # linear_combination hg1 * (cofactor_1) + …  (cofactor may be 0/neg)
            combo = " + ".join(
                f"({expr_lean(sp.expand(h), syms)}) * {hn}"
                for h, hn in zip(cofactors, hyp_names))

            lines.append(
                f"-- {inst.lean_name}: Nullstellensatz certificate  p = Σ h_i·g_i "
                f"(ideal membership) — p vanishes on the variety.\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{hyp_arrows} "
                f"{p_s} = 0 := by\n"
                f"  intro {binder} {' '.join(hyp_names)}\n"
                f"  linear_combination {combo}\n"
            )
            n += 1
        return "\n".join(lines), n


def nullstellensatz_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Nullstellensatz / ideal-membership family (kind='nullstellensatz').

    spec: ``pt -> (p, gens)`` — the target polynomial `p` and the ideal
    generators `gens`.  ``certify_nullstellensatz_point`` reduces `p` by the
    generators, certifies membership iff the remainder is zero, and emits
    ``∀x, (⋀ g_i = 0) → p = 0``.  A `p` not in the ideal is refused.
    """
    if not tuple(symbols):
        raise ValueError("Nullstellensatz families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("nullstellensatz", spec),
        constants=dict(constants or {}),
    )

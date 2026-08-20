"""Infeasibility / Nullstellensatz-refutation emitter — a polynomial system has
NO solution.

Where `NullstellensatzEmitter` proves a polynomial VANISHES on a variety, this
one proves the variety is EMPTY: the system `{g_1 = 0, …, g_m = 0}` has no common
zero.  It is the logical DUAL — a certificate of NON-existence, the bedrock of
formal verification ("no counterexample / bad state exists").

By the Nullstellensatz, `{g_j = 0}` is unsatisfiable exactly when `1` lies in the
ideal `⟨g_1, …, g_m⟩`:

    1 ≡ Σ_j λ_j · g_j      (exact identity).

The finite witness is the cofactor tuple `(λ_1, …, λ_m)`.  Telperion COMPUTES it
by undetermined coefficients — searching for polynomial `λ_j` of increasing
degree whose combination equals `1` (a linear solve over the coefficient
unknowns).  A system for which no such refutation is found (e.g. a satisfiable
one) is REFUSED.

The emitted Lean derives the contradiction directly — assume every generator
vanishes, then `linear_combination` turns the certificate into `1 = 0`, which
`norm_num` refutes:

    theorem <name> : ∀ x y : ℝ, g_1 = 0 → … → g_m = 0 → False := by
      intro x y e_1 … e_m
      have contra : (1:ℝ) = 0 := by linear_combination λ_1*e_1 + … + λ_m*e_m
      exact absurd contra (by norm_num)

A wrong cofactor makes the `linear_combination` fail — the false refutation
cannot compile (and is already refused at certification).

NOTE: this is the *ideal-theoretic* refutation (no common zero over ℂ ⊇ ℝ).  A
system infeasible only over ℝ by positivity (e.g. `x² + 1 = 0`) needs the
Positivstellensatz (SOS) refutation — a separate, planned emitter.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations_with_replacement
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _monomials(syms, deg: int) -> list[sp.Expr]:
    """All monomials in `syms` of total degree ≤ `deg`."""
    monos = [sp.Integer(1)]
    for d in range(1, deg + 1):
        for combo in combinations_with_replacement(syms, d):
            monos.append(sp.prod(combo))
    return monos


def find_refutation(constraints, syms, max_deg: int = 3):
    """Search for rational cofactors ``λ_j`` with ``Σ λ_j g_j = 1`` (a
    Nullstellensatz refutation), by undetermined coefficients up to ``max_deg``.
    Returns ``(cofactors, degree)`` or ``(None, None)``."""
    syms = list(syms)
    for D in range(0, max_deg + 1):
        allc, lam = [], []
        for j, h in enumerate(constraints):
            monos = _monomials(syms, D)
            cs = [sp.Symbol(f"_lam{j}_{k}") for k in range(len(monos))]
            allc += cs
            lam.append(sum(c * m for c, m in zip(cs, monos)))
        expr = sp.expand(sum(l * h for l, h in zip(lam, constraints)) - 1)
        eqs = sp.Poly(expr, *syms).coeffs()
        sol = sp.solve(eqs, allc, dict=True)
        if sol:
            subs = sol[0]
            lam_s = [sp.expand(l.subs(subs).subs({c: 0 for c in allc}))
                     for l in lam]
            if sp.expand(sum(l * h for l, h in zip(lam_s, constraints)) - 1) == 0:
                return lam_s, D
    return None, None


def certify_infeasible_point(family, pt, name):
    """Certify one infeasibility instance: (CertifiedInstance, n_checks).

    Reads constraints = family.special[1](pt): the generators `g_j` claimed to
    have no common zero.  Searches for a Nullstellensatz refutation
    ``1 = Σ λ_j g_j`` and verifies it exactly.  Raises ValueError (a refusal)
    when no refutation is found — the system may be satisfiable, or need a higher
    degree / the Positivstellensatz (SOS) refutation."""
    constraints = [sp.expand(sp.sympify(g)) for g in family.special[1](pt)]
    syms = tuple(family.symbols)
    if not constraints:
        raise ValueError(f"infeasible instance '{name}' REFUSED: no constraints")

    max_deg = int(family.constants.get("max_deg", 3))
    cofactors, deg = find_refutation(constraints, syms, max_deg=max_deg)
    if cofactors is None:
        raise ValueError(
            f"infeasible instance '{name}' REFUSED: no Nullstellensatz refutation "
            f"1 = Σ λ_j g_j found up to degree {max_deg} — the system may be "
            "satisfiable, or need a higher degree / the SOS Positivstellensatz")
    if sp.expand(sum(l * g for l, g in zip(cofactors, constraints)) - 1) != 0:
        raise ValueError(
            f"infeasible instance '{name}' REFUSED: cofactors do not combine to 1")
    checks = 2

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(constraints, [sp.expand(c) for c in cofactors]),
    )
    return inst, checks


@dataclass
class InfeasibilityEmitter(Emitter):
    """Emit `∀x, (⋀ g_j = 0) → False` from a Nullstellensatz refutation
    `1 = Σ λ_j g_j`: `linear_combination` turns it into `1 = 0`, `norm_num`
    refutes.  Deterministic order: grid order."""

    def __post_init__(self):
        self.kind = "infeasible"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            constraints, cofactors = inst.payload  # type: ignore[misc]
            hyp_names = [f"e{i}" for i in range(1, len(constraints) + 1)]
            hyp_arrows = "".join(
                f" {expr_lean(sp.expand(g), syms)} = 0 →" for g in constraints)
            combo = " + ".join(
                f"({expr_lean(sp.expand(lam), syms)}) * {hn}"
                for lam, hn in zip(cofactors, hyp_names)
                if sp.expand(lam) != 0) or "0"

            lines.append(
                f"-- {inst.lean_name}: infeasibility (Nullstellensatz refutation) "
                f"— the system {{g_j = 0}} has NO common solution (1 = Σ λ_j g_j).\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{hyp_arrows} "
                f"False := by\n"
                f"  intro {binder} {' '.join(hyp_names)}\n"
                f"  have contra : (1:ℝ) = 0 := by linear_combination {combo}\n"
                f"  exact absurd contra (by norm_num)\n"
            )
            n += 1
        return "\n".join(lines), n


def infeasible_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    max_deg: int = 3,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an infeasibility / Nullstellensatz-refutation family (kind='infeasible').

    spec: ``pt -> constraints`` — the generators `g_j` claimed to have no common
    zero.  ``certify_infeasible_point`` searches for a refutation
    ``1 = Σ λ_j g_j`` up to ``max_deg`` and refuses if none is found.
    """
    if not tuple(symbols):
        raise ValueError("infeasibility families require at least one symbol")
    consts = dict(constants or {})
    consts.setdefault("max_deg", max_deg)
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("infeasible", spec),
        constants=consts,
    )

"""Cone / Farkas emitter — target as a nonnegative combination of a basis.

A first-class emitter for the linear-Positivstellensatz certificate shape
(`cone.py`'s exactly-solvable core): given a target expression and a basis of
POSITIVITY-PROVABLE nonnegative expressions `b_i`, find exact rational weights
`λ_i ≥ 0` with

    target ≡ Σ λ_i · b_i      (exact identity),

so `0 ≤ target` follows.  The certificate is the weight vector; the emitted Lean
is robust and hypothesis-free:

    theorem <name> : (0:ℝ) ≤ <target> := by
      have hid : <target> = <Σ λ_i b_i> := by ring
      rw [hid]; positivity

`ring` discharges the exact identity; `positivity` closes the nonnegative
combination (each `λ_i` a nonneg rational literal, each `b_i` nonneg by
structure).  This is distinct from DirectPolya: the basis is an ARBITRARY set of
nonneg building blocks the caller supplies (squares, nonneg monomials, products,
…), not a single num/den form.

NEGATIVE CONTROL: a target NOT in the cone is refused at certification — with a
FarkasDual (an exact functional proving impossibility over this basis).  An
overcomplete basis is solved exactly by vertex enumeration, so refusal now
means genuine non-membership.  No Lean is ever emitted for a non-member.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .cone import ConeCombination, cone_combination, cone_decide
from .expr import expr_lean, expr_lean_raw, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_cone_point(family, pt, name):
    """Certify one cone instance: (CertifiedInstance, n_checks).

    Reads (target, basis) = family.special[1](pt), solves for exact nonneg
    weights via cone_combination, and stores the ConeCombination on the
    instance payload.  Raises ValueError (a refusal) when the target is not a
    nonnegative combination — attaching the FarkasDual impossibility reason
    when one is found.
    """
    target, basis = family.special[1](pt)
    target = sp.sympify(target)
    basis = tuple(sp.sympify(b) for b in basis)
    syms = tuple(family.symbols)

    cc = cone_combination(target, basis, syms)
    if cc is None:
        decided = cone_decide(target, basis, syms)
        reason = (decided.render() if decided is not None
                  else "no nonnegative combination over this basis (vertex "
                       "enumeration found none)")
        raise ValueError(
            f"cone instance '{name}' REFUSED: target is not a nonnegative "
            f"combination of the basis. {reason}"
        )
    # exact self-check (cone_combination already verifies, re-assert loudly)
    if sp.simplify(sp.together(target - cc.as_expr())) != 0:
        raise ValueError(
            f"cone instance '{name}' REFUSED: weight vector does not reproduce "
            "the target exactly"
        )
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=cc,
    )
    return inst, len(basis)


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class ConeFarkasEmitter(Emitter):
    """Emit `0 ≤ target` as a nonnegative combination of a positivity-provable
    basis.  One theorem per certified instance:

        theorem <name> : (0:ℝ) ≤ <target> := by
          have hid : <target> = <Σ λ_i b_i> := by ring
          rw [hid]; positivity

    The basis elements MUST be `positivity`-provable nonnegative (squares,
    nonneg monomials, products/sums thereof) — the exact requirement is
    documented at the family constructor.  Deterministic ordering: grid order,
    basis order as supplied."""

    def __post_init__(self):
        self.kind = "cone"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        # Bind the free variables with an explicit ∀ (and `intro` them) rather
        # than lean on autoImplicit — so the theorem compiles under
        # `autoImplicit false`, consistent with every other emitter.
        binder = " ".join(str(s) for s in syms)
        forall = f"∀ {binder} : ℝ, " if syms else ""
        intro = f"  intro {binder}\n" if syms else ""
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            cc: ConeCombination = inst.payload  # type: ignore[assignment]
            target_expr = cc.as_expr()
            target_s = expr_lean(sp.expand(target_expr), syms)
            terms = []
            for w, b in zip(cc.weights, cc.basis):
                # Drop zero-weight terms: they contribute nothing to the identity
                # and a `0 * b` term would force `positivity` to prove `b` nonneg
                # (which fails for a zero-weighted element that is not itself
                # positivity-provable, e.g. a cross term `x*y`).
                if w == 0:
                    continue
                # Render the basis element AS WRITTEN (not expanded) so
                # `positivity` recognizes its nonneg structure (e.g. a square
                # `(x - y)^2`, which expands to `x^2 - 2*x*y + y^2` that
                # positivity cannot handle).  `ring` still discharges the
                # identity regardless of form.
                terms.append(f"{rat_lean(w)} * ({expr_lean_raw(b, syms)})")
            combo_s = " + ".join(terms) if terms else "0"
            lines.append(
                f"theorem {inst.lean_name} : {forall}(0:ℝ) ≤ {target_s} := by\n"
                f"{intro}"
                f"  have hid : {target_s} = {combo_s} := by ring\n"
                f"  rw [hid]; positivity\n"
            )
            n += 1
        return "".join(lines), n


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def cone_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a cone/Farkas family (kind='cone').

    Parameters
    ----------
    name, grid, lean_name
        As for every family: name, the finite parameter grid, and a
        ``pt -> str`` Lean theorem-name map.
    symbols
        The free (real) variables the target and basis are polynomials in.
    spec
        A callable ``pt -> (target, basis)`` where ``target`` is a sympy
        expression and ``basis`` a sequence of POSITIVITY-PROVABLE nonnegative
        sympy expressions.  ``certify_cone_point`` solves ``target = Σ λ_i b_i``
        with ``λ_i ≥ 0`` exactly, and refuses (with a Farkas dual) otherwise —
        no Lean is emitted for a non-member.
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("cone", spec),
        constants=dict(constants or {}),
    )

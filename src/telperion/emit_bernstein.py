"""Bernstein-basis positivity emitter — `0 ≤ p(x)` on a closed interval `[a, b]`
via nonnegative Bernstein coefficients.

A univariate polynomial written in the degree-`n` Bernstein basis over `[a, b]`,

    p(x) = Σ_{i=0}^{n} β_i · C(n,i) · (x−a)^i · (b−x)^{n-i} / (b−a)^n,

is nonnegative on `[a, b]` as soon as every `β_i ≥ 0`, because each basis element
is a product of the nonnegative factors `(x−a) ≥ 0` and `(b−x) ≥ 0` there.  This
is the univariate, interval specialization of Handelman positivity, on the fixed
Bernstein basis of the two interval constraints.

Telperion FINDS the certificate: it extracts the Bernstein coefficients by exact
linear solve, ELEVATING the degree `n` (from `deg p` up to `n_max`) until all
coefficients are nonnegative — the Bernstein enclosure sharpens with `n`, and for
a polynomial strictly positive on `[a, b]` some finite `n` succeeds (the
control-point convex-hull property).  A polynomial that is not strictly positive
there (e.g. touching zero at an interior point) is refused — its Bernstein
coefficients never all turn nonnegative.

Emitted Lean is robust and hypothesis-driven — each basis element is nonnegative
by a `mul_nonneg`/`pow_nonneg` fold over `0 ≤ x−a` and `0 ≤ b−x`, `ring` closes
the identity, and `linarith` sums the nonnegative pieces:

    theorem <name> : ∀ x : ℝ, a ≤ x → x ≤ b → (0:ℝ) ≤ p := by
      intro x hlo hhi
      have hxa : (0:ℝ) ≤ x - a := by linarith
      have hbx : (0:ℝ) ≤ b - x := by linarith
      have t0 : (0:ℝ) ≤ β₀ * (C * (x-a)^0 * (b-x)^n) := ...
      …
      have hid : (p : ℝ) = <Σ βᵢ·basisᵢ> := by ring
      rw [hid]; linarith
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def find_bernstein_certificate(p, a, b, x, n_max: int = 8):
    """Find a nonnegative-Bernstein-coefficient certificate for `0 ≤ p` on
    `[a, b]`, elevating the degree up to `n_max`.  Returns `(n, betas)` (the
    degree and the nonnegative rational coefficient list) or None."""
    p = sp.expand(sp.sympify(p))
    a, b = sp.nsimplify(a), sp.nsimplify(b)
    deg = sp.Poly(p, x).degree() if p != 0 else 0
    for n in range(max(deg, 1), n_max + 1):
        betas = sp.symbols(f"_bern0:{n + 1}")
        basis = [sp.binomial(n, i) * (x - a) ** i * (b - x) ** (n - i) / (b - a) ** n
                 for i in range(n + 1)]
        diff = sp.Poly(sp.expand(sum(be * ba for be, ba in zip(betas, basis)) - p), x)
        sol = sp.solve(diff.coeffs(), betas, dict=True)
        if not sol:
            continue
        vals = [sp.nsimplify(sol[0].get(be, 0)) for be in betas]
        if all(v.is_number and v >= 0 for v in vals):
            recon = sum(v * ba for v, ba in zip(vals, basis))
            if sp.expand(recon - p) == 0:
                return n, [sp.Rational(v) for v in vals]
    return None


def certify_bernstein_point(family, pt, name):
    """Certify one Bernstein instance: (CertifiedInstance, n_checks).

    Reads (p, a, b) = family.special[1](pt): the target `p` and the interval
    endpoints.  Finds nonnegative Bernstein coefficients (elevating the degree);
    raises ValueError (a refusal) when none are found — `p` is not certifiably
    strictly positive on `[a, b]` at this `n_max`."""
    p, a, b = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    syms = tuple(family.symbols)
    if len(syms) != 1:
        raise ValueError(
            f"bernstein instance '{name}' REFUSED: univariate only "
            f"(got {len(syms)} symbols)")
    x = syms[0]
    a, b = sp.nsimplify(a), sp.nsimplify(b)
    if not (b - a).is_positive:
        raise ValueError(
            f"bernstein instance '{name}' REFUSED: need a < b (got [{a}, {b}])")
    n_max = int(family.constants.get("bernstein_n_max", 8))
    found = find_bernstein_certificate(p, a, b, x, n_max=n_max)
    if found is None:
        raise ValueError(
            f"bernstein instance '{name}' REFUSED: no nonnegative-Bernstein "
            f"certificate on [{a}, {b}] up to degree {n_max} — p is not "
            "(certifiably) strictly positive there")
    n, betas = found
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, a, b, n, betas),
    )
    return inst, n + 1


@dataclass
class BernsteinEmitter(Emitter):
    """Emit `0 ≤ p` on `[a, b]` from nonnegative Bernstein coefficients.  Each
    basis element is nonnegative by a `mul_nonneg`/`pow_nonneg` fold over
    `0 ≤ x−a` and `0 ≤ b−x`; `ring` closes the identity; `linarith` sums.
    Deterministic order: grid order."""

    def __post_init__(self):
        self.kind = "bernstein"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        x = syms[0]
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            p, a, b, n, betas = inst.payload  # type: ignore[misc]
            xa = expr_lean(sp.expand(x - a), syms)
            bx = expr_lean(sp.expand(b - a - (x - a)), syms)  # = b - x
            p_s = expr_lean(sp.expand(p), syms)
            a_s, b_s = rat_lean(a), rat_lean(b)

            haves, summands = [], []
            for i, beta in enumerate(betas):
                if beta == 0:
                    continue
                coef = sp.binomial(n, i) / (b - a) ** n  # the C(n,i)/(b-a)^n scalar
                # term = beta * coef * (x-a)^i * (b-x)^(n-i)
                scalar = rat_lean(sp.Rational(beta) * sp.Rational(coef))
                factors = [scalar]
                proof = f"(by norm_num : (0:ℝ) ≤ {scalar})"
                if i > 0:
                    factors.append(f"({xa})^{i}")
                    proof = f"mul_nonneg ({proof}) (pow_nonneg hxa {i})"
                if n - i > 0:
                    factors.append(f"({bx})^{n - i}")
                    proof = f"mul_nonneg ({proof}) (pow_nonneg hbx {n - i})"
                term = " * ".join(factors)
                haves.append(f"  have t{i} : (0:ℝ) ≤ {term} := {proof}")
                summands.append(term)
            rhs = " + ".join(summands) if summands else "0"

            lines.append(
                f"-- {inst.lean_name}: Bernstein-basis positivity (degree {n}) — "
                f"nonnegative Bernstein coefficients on [{a}, {b}].\n"
                f"theorem {inst.lean_name} : ∀ {x} : ℝ, {a_s} ≤ {x} → {x} ≤ {b_s} "
                f"→ (0:ℝ) ≤ {p_s} := by\n"
                f"  intro {x} hlo hhi\n"
                f"  have hxa : (0:ℝ) ≤ {xa} := by linarith\n"
                f"  have hbx : (0:ℝ) ≤ {bx} := by linarith\n"
                + "\n".join(haves) + "\n"
                f"  have hid : ({p_s} : ℝ) = {rhs} := by ring\n"
                f"  rw [hid]; linarith\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def bernstein_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    n_max: int = 8,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Bernstein-positivity family (kind='bernstein').

    spec: ``pt -> (p, a, b)`` — the univariate target `p` and the interval
    endpoints `a < b` (claim ``0 ≤ p`` on ``[a, b]``).  ``certify_bernstein_point``
    finds nonnegative Bernstein coefficients (elevating the degree up to
    ``n_max``) and refuses if none exist.
    """
    if len(tuple(symbols)) != 1:
        raise ValueError("Bernstein families are univariate (exactly one symbol)")
    consts = dict(constants or {})
    consts.setdefault("bernstein_n_max", n_max)
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("bernstein", spec),
        constants=consts,
    )

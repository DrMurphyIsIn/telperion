"""Sturm strict-interval-positivity emitter — `0 < p(x)` for all `x ∈ [a, b]`,
with a Sturm sequence as the exact decision oracle.

Sturm's theorem counts the real roots of a univariate polynomial in an interval
by the sign variations of its Sturm sequence at the endpoints.  Its practical
use — proving a polynomial has NO root in `[a, b]`, hence is strictly one-signed
there — is exactly root exclusion.  This emitter delivers that:

  1. the Sturm sequence (exact, in sympy) certifies `p` has no root in `[a, b]`
     and `p(a) > 0` — so `p > 0` throughout (the DECISION oracle; a polynomial
     with a root in the interval, or negative somewhere, is refused);
  2. a rational floor `0 < γ ≤ min_{[a,b]} p` is found, and `p − γ ≥ 0` on
     `[a, b]` is certified in the Bernstein basis (the nonnegative-coefficient
     interval certificate — `p − γ` is strictly positive, so it succeeds);
  3. the emitted Lean combines them: `0 ≤ p − γ` (Bernstein) and `0 < γ`
     (`norm_num`) give `0 < p` by `linarith`.

This is the robustly kernel-checkable half of Sturm — root exclusion / strict
positivity.  The other half, an EXACT real-root COUNT emitted as a theorem, needs
Sturm's theorem in Mathlib (not yet available) and is out of scope here; the
Sturm sequence is used only as the exact oracle that makes the certificate
principled (and provides the negative control).

Emitted Lean (γ the rational floor, with `p − γ = Σ βᵢ·Bernsteinᵢ`):

    theorem <name> : ∀ x : ℝ, a ≤ x → x ≤ b → (0:ℝ) < p := by
      intro x hlo hhi
      have hxa : (0:ℝ) ≤ x - a := by linarith
      have hbx : (0:ℝ) ≤ b - x := by linarith
      have t0 : (0:ℝ) ≤ β₀·… := …
      …
      have hpg : (0:ℝ) ≤ p − γ := by
        have hid : (p − γ : ℝ) = Σ βᵢ·Bernsteinᵢ := by ring
        rw [hid]; linarith
      linarith   -- 0 < γ and 0 ≤ p − γ ⟹ 0 < p
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .emit_bernstein import find_bernstein_certificate
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _sturm_roots_in(p, a, b, x) -> int:
    """Number of real roots of `p` in `(a, b]` by Sturm sign variations."""
    seq = sp.sturm(sp.Poly(p, x))

    def V(t):
        signs = [sp.sign(poly.eval(t)) for poly in seq]
        signs = [s for s in signs if s != 0]
        return sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])

    return int(V(a) - V(b))


def _gamma_ladder():
    """Rational floor candidates `γ` (descending), for `0 < γ ≤ min p`."""
    out = [sp.Rational(k, 8) for k in range(7, 0, -1)]
    out += [sp.Rational(1, 16), sp.Rational(1, 32), sp.Rational(1, 64),
            sp.Rational(1, 256), sp.Rational(1, 1024)]
    return out


def certify_sturm_positive_point(family, pt, name):
    """Certify one strict-interval-positivity instance: (CertifiedInstance, checks).

    Reads (p, a, b) = family.special[1](pt).  Uses the Sturm sequence to require
    `p` has no root in `[a, b]` and `p(a) > 0` (else refuse — the negative
    control), then finds a rational floor `γ` and a Bernstein certificate for
    `p − γ ≥ 0`.  Raises ValueError (a refusal) if `p` is not certifiably
    strictly positive on `[a, b]`."""
    p, a, b = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    syms = tuple(family.symbols)
    if len(syms) != 1:
        raise ValueError(
            f"sturm_positive '{name}' REFUSED: univariate only "
            f"(got {len(syms)} symbols)")
    x = syms[0]
    a, b = sp.nsimplify(a), sp.nsimplify(b)
    if not (b - a).is_positive:
        raise ValueError(f"sturm_positive '{name}' REFUSED: need a < b")
    if sp.Poly(p, x).degree() < 1:
        # constant: positive iff the constant is > 0
        if not (p > 0):
            raise ValueError(
                f"sturm_positive '{name}' REFUSED: constant {p} is not positive")
        # trivially strictly positive; a degenerate but valid case
        n_max = int(family.constants.get("sturm_n_max", 8))
        found = find_bernstein_certificate(p, a, b, x, n_max=n_max)
        inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                                 payload=(p, a, b, sp.Integer(0), found))
        return inst, 2

    if _sturm_roots_in(p, a, b, x) != 0:
        raise ValueError(
            f"sturm_positive '{name}' REFUSED: Sturm finds a real root of p in "
            f"[{a}, {b}] — p is not strictly positive (root exclusion fails)")
    if not (p.subs(x, a) > 0):
        raise ValueError(
            f"sturm_positive '{name}' REFUSED: p({a}) = {p.subs(x, a)} ≤ 0 — no "
            "root in the interval but p is negative there")

    n_max = int(family.constants.get("sturm_n_max", 8))
    for gamma in _gamma_ladder():
        found = find_bernstein_certificate(sp.expand(p - gamma), a, b, x, n_max=n_max)
        if found is not None:
            inst = CertifiedInstance(
                point=dict(pt), lean_name=name, corners=(),
                payload=(p, a, b, gamma, found),
            )
            return inst, found[0] + 2
    raise ValueError(
        f"sturm_positive '{name}' REFUSED: p has no root in [{a}, {b}] but no "
        "rational floor γ with a Bernstein certificate for p − γ was found")


@dataclass
class SturmPositiveEmitter(Emitter):
    """Emit `0 < p` on `[a, b]` from a Sturm root-exclusion + a Bernstein
    certificate for `p − γ ≥ 0` (`γ > 0` the rational floor).  Deterministic
    order: grid order."""

    def __post_init__(self):
        self.kind = "sturm_positive"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        x = syms[0]
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            p, a, b, gamma, found = inst.payload  # type: ignore[misc]
            n, betas = found
            xa = expr_lean(sp.expand(x - a), syms)
            bx = expr_lean(sp.expand(b - a - (x - a)), syms)  # = b - x
            p_s = expr_lean(sp.expand(p), syms)
            pg_s = expr_lean(sp.expand(p - gamma), syms)
            a_s, b_s, g_s = rat_lean(a), rat_lean(b), rat_lean(gamma)

            haves, summands = [], []
            for i, beta in enumerate(betas):
                if beta == 0:
                    continue
                coef = sp.binomial(n, i) / (b - a) ** n
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
                f"-- {inst.lean_name}: Sturm strict-interval positivity — 0 < p on "
                f"[{a}, {b}] (Sturm excludes roots; Bernstein bounds p − {gamma} ≥ 0).\n"
                f"theorem {inst.lean_name} : ∀ {x} : ℝ, {a_s} ≤ {x} → {x} ≤ {b_s} "
                f"→ (0:ℝ) < {p_s} := by\n"
                f"  intro {x} hlo hhi\n"
                f"  have hxa : (0:ℝ) ≤ {xa} := by linarith\n"
                f"  have hbx : (0:ℝ) ≤ {bx} := by linarith\n"
                + "\n".join(haves) + "\n"
                f"  have hpg : (0:ℝ) ≤ {pg_s} := by\n"
                f"    have hid : ({pg_s} : ℝ) = {rhs} := by ring\n"
                f"    rw [hid]; linarith\n"
                f"  have hg : (0:ℝ) < {g_s} := by norm_num\n"
                f"  linarith\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def sturm_positive_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    n_max: int = 8,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Sturm strict-interval-positivity family (kind='sturm_positive').

    spec: ``pt -> (p, a, b)`` — the univariate target `p` and interval endpoints
    `a < b` (claim ``0 < p`` on ``[a, b]``).  ``certify_sturm_positive_point``
    uses the Sturm sequence to exclude roots (refusing if any lies in the
    interval) and a Bernstein certificate for ``p − γ ≥ 0``.
    """
    if len(tuple(symbols)) != 1:
        raise ValueError("Sturm-positivity families are univariate (one symbol)")
    consts = dict(constants or {})
    consts.setdefault("sturm_n_max", n_max)
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("sturm_positive", spec),
        constants=consts,
    )

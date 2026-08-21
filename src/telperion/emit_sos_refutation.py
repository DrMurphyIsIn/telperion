"""SOS-Positivstellensatz refutation emitter — a semialgebraic system is
unsatisfiable OVER ℝ, closing the real-only gap the ideal-theoretic refutation
(`InfeasibilityEmitter`) leaves open.

A system `{g_i ≥ 0} ∪ {h_j = 0}` has no real solution exactly when the
Positivstellensatz produces a certificate

    −1 ≡ σ_0 + Σ_i σ_i·g_i + Σ_j λ_j·h_j      (exact identity),

with `σ_0, σ_i` sums of squares and `λ_j` arbitrary polynomials.  On the feasible
set every `σ_j ≥ 0`, every `g_i ≥ 0`, and every `h_j = 0`, so the right side is
`≥ 0` while it equals `−1` — a contradiction.  This reaches systems that are
infeasible only by POSITIVITY (e.g. `x² + 1 = 0`, which has complex roots, so
`1 ∉ ⟨x²+1⟩` — no ideal refutation exists — but `−1 = x² + (−1)(x²+1)` with the
SOS `σ₀ = x²` refutes it over ℝ).

Telperion is the CERTIFICATE CHECKER: the SOS multipliers and the `λ_j` are
supplied; certification verifies the identity exactly and every square
coefficient nonnegative.  The emitted Lean derives the contradiction:

    theorem <name> : ∀ x : ℝ, 0 ≤ g_1 → … → h_1 = 0 → … → False := by
      intro x hg_1 … he_1 …
      have s0 : (0:ℝ) ≤ σ_0 := by positivity
      have t1 : (0:ℝ) ≤ (σ_1)*(g_1) := mul_nonneg (by positivity) hg_1
      …
      have key : (-1:ℝ) = σ_0 + (σ_1)*(g_1) + … := by linear_combination λ_1*he_1 + …
      linarith
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, expr_lean_raw, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _sos_expr(terms) -> sp.Expr:
    return sum((sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in terms), sp.Integer(0))


def _check_sos(terms, where, name) -> int:
    n = 0
    for c, _b in terms:
        cr = sp.nsimplify(c)
        if not cr.is_rational or cr < 0:
            raise ValueError(
                f"sos_refutation instance '{name}' REFUSED: {where} has a "
                f"non-nonnegative-rational coefficient {c} — not a sum of squares")
        n += 1
    return n


def certify_sos_refutation_point(family, pt, name):
    """Certify one SOS-refutation instance: (CertifiedInstance, n_checks).

    Reads (sigma0, ineqs, eqs) = family.special[1](pt): the SOS term list
    ``sigma0`` for σ₀, ``ineqs`` as ``(g_i, sigma_i, hyp_name)`` (constraint
    ``g_i ≥ 0``, its SOS multiplier, its hypothesis name), and ``eqs`` as
    ``(h_j, lambda_j, hyp_name)`` (equality ``h_j = 0``, its polynomial multiplier,
    its hypothesis name).  Verifies ``−1 = σ₀ + Σ σ_i g_i + Σ λ_j h_j`` exactly
    with every SOS coefficient nonnegative; refuses otherwise."""
    sigma0, ineqs, eqs = family.special[1](pt)
    syms = tuple(family.symbols)

    if sigma0 is None:
        # FINDER mode: ineqs are (g_i, hyp), eqs are (h_j, hyp); SEARCH the
        # SOS multipliers σ and free multipliers λ that refute over ℝ.
        from .sdp_finder import find_sos_refutation
        half_deg = int(family.constants.get("sos_refutation_half_deg", 1))
        found = find_sos_refutation(
            [g for g, _h in ineqs], [h for h, _h in eqs], syms, half_deg=half_deg)
        if found is None:
            raise ValueError(
                f"sos_refutation instance '{name}' REFUSED: no SOS-Positivstellensatz "
                f"refutation (half-degree {half_deg}) found or rationalized — the "
                "system may be satisfiable over ℝ, or need a higher degree")
        f_sigma0, f_ineqs, f_eqs = found
        sigma0 = f_sigma0
        ineqs = [(g, sig, hyp) for (g, hyp), (_g2, sig) in zip(ineqs, f_ineqs)]
        eqs = [(h, lam, hyp) for (h, hyp), (_h2, lam) in zip(eqs, f_eqs)]

    checks = _check_sos(sigma0, "σ₀", name)
    recon = _sos_expr(sigma0)
    for g, sig, _h in ineqs:
        checks += _check_sos(sig, "an SOS multiplier", name)
        recon += sp.sympify(g) * _sos_expr(sig)
    for h, lam, _h in eqs:
        recon += sp.sympify(h) * sp.sympify(lam)

    if sp.expand(recon - (-1)) != 0:
        raise ValueError(
            f"sos_refutation instance '{name}' REFUSED: certificate does not equal "
            f"−1 — σ₀ + Σσ_ig_i + Σλ_jh_j + 1 = {sp.expand(recon + 1)}")
    checks += 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(list(sigma0), list(ineqs), list(eqs)),
    )
    return inst, checks


@dataclass
class SOSRefutationEmitter(Emitter):
    """Emit `∀x, (⋀ g_i ≥ 0) → (⋀ h_j = 0) → False` from an SOS-Positivstellensatz
    certificate `−1 = σ₀ + Σσ_ig_i + Σλ_jh_j`.  Deterministic order: grid order."""

    def __post_init__(self):
        self.kind = "sos_refutation"

    def _render_sos(self, terms, syms):
        parts = [f"{rat_lean(sp.nsimplify(c))} * ({expr_lean_raw(sp.sympify(b), syms)})^2"
                 for c, b in terms]
        return " + ".join(parts) if parts else "0"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            sigma0, ineqs, eqs = inst.payload  # type: ignore[misc]
            sigma0_s = self._render_sos(sigma0, syms)
            ineq_hyps = [(f"hg{i}", expr_lean(sp.expand(sp.sympify(g)), syms),
                          self._render_sos(sig, syms))
                         for i, (g, sig, _h) in enumerate(ineqs, 1)]
            eq_hyps = [(f"he{j}", expr_lean(sp.expand(sp.sympify(h)), syms),
                        expr_lean(sp.expand(sp.sympify(lam)), syms))
                       for j, (h, lam, _h) in enumerate(eqs, 1)]

            arrows = "".join(f" (0:ℝ) ≤ {gs} →" for _n, gs, _s in ineq_hyps)
            arrows += "".join(f" {hs} = 0 →" for _n, hs, _l in eq_hyps)
            intro = " ".join([hn for hn, _g, _s in ineq_hyps]
                             + [hn for hn, _h, _l in eq_hyps])

            haves, summands = [], []
            if sigma0:
                haves.append(f"  have s0 : (0:ℝ) ≤ {sigma0_s} := by positivity")
                summands.append(sigma0_s)
            for i, (hn, gs, ss) in enumerate(ineq_hyps, 1):
                term = f"({ss}) * ({gs})"
                haves.append(
                    f"  have t{i} : (0:ℝ) ≤ {term} := mul_nonneg (by positivity) {hn}")
                summands.append(term)
            key_rhs = " + ".join(summands) if summands else "0"
            combo = " + ".join(f"({ls}) * {hn}" for hn, _h, ls in eq_hyps) or "0"

            lines.append(
                f"-- {inst.lean_name}: SOS-Positivstellensatz refutation — the "
                f"system is unsatisfiable over ℝ (−1 = σ₀ + Σσ_ig_i + Σλ_jh_j).\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{arrows} False := by\n"
                f"  intro {binder} {intro}\n"
                + "\n".join(haves) + "\n"
                f"  have key : (-1:ℝ) = {key_rhs} := by linear_combination {combo}\n"
                f"  linarith\n"
            )
            n += 1
        return "\n".join(lines), n


def sos_refutation_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an SOS-Positivstellensatz refutation family (kind='sos_refutation').

    spec: ``pt -> (sigma0, ineqs, eqs)`` — the SOS term list for σ₀, the
    inequality constraints ``(g_i, sigma_i, hyp_name)`` with SOS multipliers, and
    the equality constraints ``(h_j, lambda_j, hyp_name)`` with polynomial
    multipliers.  ``certify_sos_refutation_point`` verifies
    ``−1 = σ₀ + Σσ_ig_i + Σλ_jh_j`` exactly and refuses otherwise.
    """
    if not tuple(symbols):
        raise ValueError("SOS-refutation families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("sos_refutation", spec),
        constants=dict(constants or {}),
    )

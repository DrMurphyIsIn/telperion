"""Real-Nullstellensatz emitter — a polynomial vanishes on the REAL variety of an
ideal.

The ordinary `NullstellensatzEmitter` proves `p = 0` on the (complex) variety
`V(g) = {g_k = 0}`.  A polynomial can vanish on the REAL points without lying in
the ideal (e.g. `x` vanishes on the real variety of `x² + y²` — which is just the
origin — yet `x ∉ ⟨x²+y²⟩`).  The Real Nullstellensatz certifies exactly this: `p`
vanishes on the real variety iff, for some `m` and sum of squares `s`,

    p^{2m} + s ≡ Σ_k h_k·g_k      (i.e.  p^{2m} + s ∈ ⟨g_1, …, g_n⟩).

Telperion is given `p`, the multiplicity `m`, and the SOS `s`, and COMPUTES the
cofactors `h_k` by Gröbner reduction of `p^{2m} + s` (a nonzero remainder is a
refusal).  The emitted Lean derives `p = 0`: on the variety the ideal side is
`0`, so `p^{2m} = −s ≤ 0`; but `p^{2m} = (p^m)² ≥ 0`, forcing `p^{2m} = 0` and
hence `p = 0`:

    theorem <name> : ∀ x y : ℝ, g_1 = 0 → … → g_n = 0 → p = 0 := by
      intro x y e_1 … e_n
      have hpow : (0:ℝ) ≤ p^(2m) := by positivity
      have hsos : (0:ℝ) ≤ s := by positivity
      have key : p^(2m) + s = 0 := by linear_combination h_1*e_1 + … + h_n*e_n
      have hz : p^(2m) = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp hz
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


def certify_real_nullstellensatz_point(family, pt, name):
    """Certify one real-Nullstellensatz instance: (CertifiedInstance, n_checks).

    Reads (p, m, sos, gens) = family.special[1](pt): the target `p`, the
    multiplicity `m` (so the even power is `2m`), the SOS term list `sos` for `s`,
    and the ideal generators `gens`.  Reduces ``p^{2m} + s`` by the generators;
    certifies iff the remainder is zero (membership) and every SOS coefficient is
    nonnegative.  Refuses otherwise — `p` is not certified to vanish on the real
    variety by this `(m, s)`."""
    p, m, sos, gens = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    m = int(m)
    gens = [sp.expand(sp.sympify(g)) for g in gens]
    syms = tuple(family.symbols)
    if m < 1:
        raise ValueError(f"real_nullstellensatz '{name}' REFUSED: m must be ≥ 1")
    for c, _b in sos:
        if not sp.nsimplify(c).is_rational or sp.nsimplify(c) < 0:
            raise ValueError(
                f"real_nullstellensatz '{name}' REFUSED: SOS coefficient {c} is not "
                "a nonnegative rational")

    s = _sos_expr(sos)
    S = sp.expand(p ** (2 * m) + s)
    try:
        cofactors, remainder = sp.reduced(S, gens, *syms)
    except Exception as e:  # pragma: no cover
        raise ValueError(
            f"real_nullstellensatz '{name}' REFUSED: reduction failed ({e})") from e
    if sp.expand(remainder) != 0:
        raise ValueError(
            f"real_nullstellensatz '{name}' REFUSED: p^(2m) + s does not reduce to "
            f"0 modulo the generators (remainder {sp.expand(remainder)}) — not in "
            "the ideal for this (m, s)")
    checks = 2

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, m, list(sos), gens, [sp.expand(c) for c in cofactors]),
    )
    return inst, checks


@dataclass
class RealNullstellensatzEmitter(Emitter):
    """Emit `∀x, (⋀ g_k = 0) → p = 0` on the REAL variety from a real-Nullstellensatz
    certificate `p^{2m} + s = Σ h_k g_k` (`s` a sum of squares).  Deterministic
    order: grid order."""

    def __post_init__(self):
        self.kind = "real_nullstellensatz"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            p, m, sos, gens, cofactors = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            exp = 2 * m
            pow_s = f"({p_s})^{exp}"
            s_s = " + ".join(
                f"{rat_lean(sp.nsimplify(c))} * ({expr_lean_raw(sp.sympify(b), syms)})^2"
                for c, b in sos) or "0"
            hyp_names = [f"e{i}" for i in range(1, len(gens) + 1)]
            arrows = "".join(
                f" {expr_lean(sp.expand(g), syms)} = 0 →" for g in gens)
            combo = " + ".join(
                f"({expr_lean(sp.expand(h), syms)}) * {hn}"
                for h, hn in zip(cofactors, hyp_names) if sp.expand(h) != 0) or "0"

            lines.append(
                f"-- {inst.lean_name}: Real-Nullstellensatz certificate  p^(2m) + s "
                f"= Σ h_k·g_k (s a sum of squares) — p vanishes on the REAL variety.\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{arrows} "
                f"{p_s} = 0 := by\n"
                f"  intro {binder} {' '.join(hyp_names)}\n"
                f"  have hpow : (0:ℝ) ≤ {pow_s} := by positivity\n"
                f"  have hsos : (0:ℝ) ≤ {s_s} := by positivity\n"
                f"  have key : {pow_s} + ({s_s}) = 0 := by linear_combination {combo}\n"
                f"  have hz : {pow_s} = 0 := by linarith\n"
                f"  exact (pow_eq_zero_iff (by norm_num)).mp hz\n"
            )
            n += 1
        return "\n".join(lines), n


def real_nullstellensatz_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a real-Nullstellensatz family (kind='real_nullstellensatz').

    spec: ``pt -> (p, m, sos, gens)`` — the target `p`, multiplicity `m` (even
    power `2m`), the SOS term list `sos` for `s`, and the ideal generators `gens`.
    ``certify_real_nullstellensatz_point`` reduces ``p^{2m} + s`` by the generators
    and refuses if it is not in the ideal.
    """
    if not tuple(symbols):
        raise ValueError("real-Nullstellensatz families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("real_nullstellensatz", spec),
        constants=dict(constants or {}),
    )

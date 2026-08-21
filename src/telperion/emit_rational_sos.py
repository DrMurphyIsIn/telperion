"""Rational-SOS (Artin / Reznick denominator) emitter — `0 ≤ p` for a polynomial
that is nonnegative but NOT a sum of squares.

Hilbert showed nonnegativity and sum-of-squares diverge (the Motzkin polynomial
`x⁴y² + x²y⁴ − 3x²y² + 1 ≥ 0` is the minimal example: nonnegative, not SOS).
Artin's positivity theorem restores the bridge with a DENOMINATOR: a nonnegative
`p` becomes SOS after multiplying by a strictly-positive `q`,

    q · p ≡ Σ_i d_i · ℓ_i²      (exact identity),   q > 0,

so `0 ≤ q·p` and, dividing by the strictly-positive `q`, `0 ≤ p`.  This reaches
the whole nonnegative-but-not-SOS class the plain `SOSEmitter` cannot.

Telperion FINDS the certificate: it searches a ladder of strictly-positive
multipliers `q` (products of `(1 + xᵢ²)` and small SOS forms — each `positivity`-
provably `> 0`) until `q·p` has an EXACT rational SOS decomposition (the shared
SDP + robust rationalization).  A supplied `q` (finder off) is also accepted.
Untrusted-by-verification: the identity `q·p = Σ d_iℓ_i²` is re-checked exactly.

Emitted Lean is robust — `positivity` proves `0 < q` and closes the SOS after a
`ring` rewrite, then `nlinarith` divides out the positive multiplier:

    theorem <name> : ∀ x y : ℝ, (0:ℝ) ≤ p := by
      intro x y
      have hq : (0:ℝ) < q := by positivity
      have hqp : (0:ℝ) ≤ q * p := by
        have h : q * p = Σ d_iℓ_i² := by ring
        rw [h]; positivity
      nlinarith [hqp, mul_pos hq (by linarith : (0:ℝ) < -p)]  -- only if p<0 (by_contra)
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


def _positive_multipliers(syms):
    """A ladder of `positivity`-provably strictly-positive multipliers `q`, in
    increasing complexity.  Each is a product/sum of `1` and squares, so
    `positivity` proves `0 < q`."""
    ones = [sp.Integer(1) + s ** 2 for s in syms]
    cands = [sp.Integer(1)]                                   # trivial (p is SOS)
    cands.append(sp.Integer(1) + sum(s ** 2 for s in syms))   # 1 + Σxᵢ²
    prod = sp.Integer(1)
    for o in ones:
        prod *= o
    cands.append(sp.expand(prod))                             # ∏(1+xᵢ²)
    cands.append(sp.expand((sp.Integer(1) + sum(s ** 2 for s in syms)) ** 2))
    return cands


def find_rational_sos(p, syms, half_deg_extra: int = 0):
    """Search for `(q, sos_terms)` with `q·p = Σ dᵢℓᵢ²`, `q` strictly positive.
    Returns the multiplier and its SOS term list, or None."""
    from .sdp_finder import _monomials_upto, _solve

    p = sp.expand(sp.sympify(p))
    syms = tuple(syms)
    for q in _positive_multipliers(syms):
        qp = sp.expand(q * p)
        d = sp.Poly(qp, *syms).total_degree() if qp != 0 else 0
        half = d // 2 + half_deg_extra
        res = _solve(qp, [(sp.Integer(1), _monomials_upto(syms, half))], [], syms)
        if res is None:
            continue
        sos = res[0][0]
        if sp.expand(sum(c * b ** 2 for c, b in sos) - qp) == 0:
            return q, [(sp.Rational(c), sp.expand(b)) for c, b in sos]
    return None


def certify_rational_sos_point(family, pt, name):
    """Certify one rational-SOS instance: (CertifiedInstance, n_checks).

    Reads (p, q, sos) = family.special[1](pt).  If `q` or `sos` is None, SEARCHES
    for the Artin multiplier and SOS.  Verifies `q·p = Σ dᵢℓᵢ²` exactly with every
    `dᵢ ≥ 0`; raises ValueError (a refusal) otherwise."""
    p, q, sos = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    syms = tuple(family.symbols)

    if q is None or sos is None:
        he = int(family.constants.get("rational_sos_half_deg_extra", 0))
        found = find_rational_sos(p, syms, half_deg_extra=he)
        if found is None:
            raise ValueError(
                f"rational_sos instance '{name}' REFUSED: no strictly-positive "
                "multiplier q with q·p an exact rational SOS was found — p may be "
                "negative somewhere, or needs a richer multiplier ladder")
        q, sos = found

    q = sp.expand(sp.sympify(q))
    for c, _b in sos:
        if not sp.nsimplify(c).is_rational or sp.nsimplify(c) < 0:
            raise ValueError(
                f"rational_sos instance '{name}' REFUSED: SOS coefficient {c} is "
                "not a nonnegative rational")
    if sp.expand(q * p - sum(sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in sos)) != 0:
        raise ValueError(
            f"rational_sos instance '{name}' REFUSED: q·p ≠ Σ dᵢℓᵢ² "
            f"(off by {sp.expand(q * p - sum(sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in sos))})")
    checks = 1 + len(sos)

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, q, [(sp.Rational(c), sp.expand(b)) for c, b in sos]),
    )
    return inst, checks


@dataclass
class RationalSOSEmitter(Emitter):
    """Emit `0 ≤ p` from an Artin denominator certificate `q·p = Σ dᵢℓᵢ²`,
    `q > 0`: `positivity` proves `0 < q` and closes the SOS, `nlinarith` divides
    out `q`.  Deterministic order: grid order."""

    def __post_init__(self):
        self.kind = "rational_sos"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            p, q, sos = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            q_s = expr_lean_raw(q, syms)
            qp_s = expr_lean(sp.expand(q * p), syms)
            sos_s = " + ".join(
                f"{rat_lean(c)} * ({expr_lean_raw(b, syms)})^2" for c, b in sos
            ) or "0"

            lines.append(
                f"-- {inst.lean_name}: rational-SOS (Artin denominator) — 0 ≤ p via "
                f"q·p = Σ dᵢℓᵢ² with q = {q} > 0 (reaches nonneg-but-not-SOS p).\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ, (0:ℝ) ≤ {p_s} := by\n"
                f"  intro {binder}\n"
                f"  have hq : (0:ℝ) < {q_s} := by positivity\n"
                f"  have hqp : (0:ℝ) ≤ {qp_s} := by\n"
                f"    have h : ({qp_s} : ℝ) = {sos_s} := by ring\n"
                f"    rw [h]; positivity\n"
                f"  by_contra hlt\n"
                f"  push_neg at hlt\n"
                f"  nlinarith [hqp, mul_pos hq (by linarith : (0:ℝ) < -({p_s}))]\n"
            )
            n += 1
        return "\n".join(lines), n


def rational_sos_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a rational-SOS / Artin-denominator family (kind='rational_sos').

    spec: ``pt -> (p, q, sos)`` — the target `p`, a strictly-positive multiplier
    `q`, and the SOS term list for `q·p`.  Return ``q=None, sos=None`` for FINDER
    mode (Telperion searches the multiplier + SOS).  ``certify_rational_sos_point``
    verifies ``q·p = Σ dᵢℓᵢ²`` exactly and refuses otherwise.
    """
    if not tuple(symbols):
        raise ValueError("rational-SOS families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("rational_sos", spec),
        constants=dict(constants or {}),
    )

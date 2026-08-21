"""Pólya-with-zeros emitter — homogeneous Pólya certificates that TOLERATE
zeros on faces (Castle–Powers–Reznick 2011, "Pólya's theorem with zeros",
J. Symbolic Comput. 46(9) 1039–1048).

`lift.py`'s inhomogeneous lift `num · (1 + Σxᵢ)^N` certifies STRICT positivity
only: a zero anywhere on the closed orthant means no finite N works, so every
tie-touching claim is refused there.  The homogeneous certificate

    (x₁ + … + x_n)^N · p  =  Q,      every coefficient of Q ≥ 0,

is sound on `{xᵢ ≥ 0, Σxᵢ > 0}` and EXISTS for nonnegative forms whose zero
set is a union of FACES of the orthant (CPR Theorem 2 characterizes exactly
when; their Theorem 3 bounds N by the residual facial margins, which do not
vanish at the tie).  This is the tie-safe lift: `x·y·(x² − xy + y²)` vanishes
on both faces yet lifts at N = 1, while `(x − y)²` — whose zero ray x = y is
NOT a face — admits no exponent at ANY N, and is refused with that reason.

Telperion is the certificate CHECKER: given `N`, the expansion is verified
exactly in rational arithmetic (all coefficients ≥ 0), and refused otherwise.
The FINDER (`terms = None` mode) searches N = 0, 1, …, max_n; on a miss it
runs the facial obstruction diagnostic so a structural impossibility (an
interior zero, a negative value) is reported as such rather than as "gave up".
The obstruction check is a SUFFICIENT condition for non-existence — sampling
the all-ones point of every face — not a complete CPR Theorem 2 decision.

Emitted Lean is hypothesis-driven and matches the Handelman tactic shapes:
each monomial of Q is nonnegative by a `mul_nonneg`/`pow_nonneg` fold, `ring`
closes the identity `(Σxᵢ)^N · p = Q`, `pow_pos` gives `0 < (Σxᵢ)^N`, and
`nlinarith` divides out the positive factor:

    theorem <name> : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 < x + y → (0:ℝ) ≤ p := by
      intro x y h1 h2 hs
      have hpow : (0:ℝ) < (x + y)^N := pow_pos hs N
      have t1 : (0:ℝ) ≤ c₁ * x^a * y^b := mul_nonneg …
      …
      have hid : (x + y)^N * (p) = t₁ + … := by ring
      have hkey : (0:ℝ) ≤ (x + y)^N * (p) := by rw [hid]; linarith
      nlinarith [hkey, hpow]
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _lift_terms(p, syms, n):
    """Sorted (coef, exps) monomials of (Σsyms)^n · p, or None on a negative
    coefficient.  Deterministic: graded-lex over the exponent vectors."""
    q = sp.expand(sp.Add(*syms) ** n * p)
    if q == 0:
        return []
    poly = sp.Poly(q, *syms)
    terms = sorted(poly.as_dict().items())
    out = []
    for exps, coef in terms:
        c = sp.nsimplify(coef)
        if not c.is_rational:
            return None
        if c < 0:
            return None
        if c != 0:
            out.append((c, tuple(int(a) for a in exps)))
    return out


def find_polya_zeros_certificate(p, syms, max_n: int) -> int | None:
    """Smallest N ≤ max_n with (Σsyms)^N · p all-nonneg-rational coefficients,
    or None.  Exact and deterministic; the certifier re-verifies regardless
    (the finder is untrusted)."""
    p = sp.expand(sp.sympify(p))
    syms = tuple(syms)
    for n in range(max_n + 1):
        if _lift_terms(p, syms, n) is not None:
            return n
    return None


def polya_zeros_obstruction(p, syms) -> str | None:
    """Sufficient-condition diagnostic for WHY no Pólya exponent can exist.

    Samples the all-ones (relative-interior) point of every face of the
    orthant.  If `p` restricted to a face is not identically zero yet vanishes
    there, the zero set leaves the face lattice — by Castle–Powers–Reznick
    Theorem 2 no exponent works at ANY N.  A negative sample refutes
    nonnegativity outright.  Returns a reason string, or None (which is NOT a
    proof a certificate exists — only that this check found no obstruction)."""
    p = sp.expand(sp.sympify(p))
    syms = tuple(syms)
    for size in range(len(syms), 0, -1):
        for face in combinations(syms, size):
            off = {s: 0 for s in syms if s not in face}
            pf = sp.expand(p.subs(off))
            if pf == 0:
                continue
            val = pf.subs({s: 1 for s in face})
            if val < 0:
                return (f"p is negative ({val}) at the all-ones point of face "
                        f"{face} — not nonnegative on the orthant")
            if val == 0:
                return (f"p vanishes at the relative-interior (all-ones) point "
                        f"of face {face} without vanishing identically on it — "
                        "the zero set is not a union of faces, so by "
                        "Castle–Powers–Reznick Theorem 2 no Pólya exponent "
                        "exists at ANY N")
    return None


def certify_polya_zeros_point(family, pt, name):
    """Certify one Pólya-with-zeros instance: (CertifiedInstance, n_checks).

    Reads (p, N) = family.special[1](pt).  With integer N ≥ 0 the expansion
    `(Σsyms)^N · p` is verified to have all-nonnegative rational coefficients;
    refused otherwise.  FINDER mode: N = None searches N ≤ max_n
    (constant ``polya_zeros_max_n``), and a miss is reported through
    `polya_zeros_obstruction` when the impossibility is structural."""
    p, n = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    syms = tuple(family.symbols)
    if n is None:
        max_n = int(family.constants.get("polya_zeros_max_n", 8))
        n = find_polya_zeros_certificate(p, syms, max_n)
        if n is None:
            reason = polya_zeros_obstruction(p, syms)
            if reason is not None:
                raise ValueError(
                    f"polya_zeros instance '{name}' REFUSED: {reason}")
            raise ValueError(
                f"polya_zeros instance '{name}' REFUSED: no Pólya-with-zeros "
                f"certificate up to N = {max_n} — a near-tight claim may need "
                "a larger exponent, or genuinely lack one (CPR Theorem 2)")
    if int(n) != n or n < 0:
        raise ValueError(
            f"polya_zeros instance '{name}' REFUSED: exponent N = {n} must be "
            "a nonnegative integer")
    n = int(n)
    terms = _lift_terms(p, syms, n)
    if terms is None:
        raise ValueError(
            f"polya_zeros instance '{name}' REFUSED: (Σsyms)^{n} · p has a "
            "negative or irrational coefficient — not a Pólya-with-zeros "
            "certificate at this N")
    checks = len(terms) + 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, n, list(terms)),
    )
    return inst, checks


@dataclass
class PolyaZerosEmitter(Emitter):
    """Emit `0 ≤ p` on `{xᵢ ≥ 0, Σxᵢ > 0}` from a Pólya-with-zeros certificate
    `(Σxᵢ)^N · p = Q`, all Q-coefficients ≥ 0.  Each monomial is nonnegative
    by a `mul_nonneg`/`pow_nonneg` fold; `ring` closes the identity; `pow_pos`
    plus `nlinarith` divide out the positive factor.  Deterministic order:
    grid, then graded-lex monomials."""

    def __post_init__(self):
        self.kind = "polya_zeros"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        sum_s = " + ".join(str(s) for s in syms)
        lines: list[str] = []
        n_thms = 0
        for inst in fam.instances:
            p, n, terms = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            hyps = [f"h{i}" for i in range(1, len(syms) + 1)]
            hyp_arrows = "".join(f" (0:ℝ) ≤ {s} →" for s in syms)

            haves, summands = [], []
            for j, (coef, exps) in enumerate(terms, start=1):
                factors = [rat_lean(sp.nsimplify(coef))]
                proof = f"(by norm_num : (0:ℝ) ≤ {rat_lean(sp.nsimplify(coef))})"
                for s, h, a in zip(syms, hyps, exps):
                    if a == 0:
                        continue
                    factors.append(f"({s})^{a}")
                    proof = f"mul_nonneg ({proof}) (pow_nonneg {h} {a})"
                term_s = " * ".join(factors)
                haves.append(f"  have t{j} : (0:ℝ) ≤ {term_s} := {proof}")
                summands.append(term_s)
            rhs = " + ".join(summands) or "0"

            lines.append(
                f"-- {inst.lean_name}: Pólya-with-zeros certificate  "
                f"(Σxᵢ)^{n} · p = Q with all Q-coefficients ≥ 0 (CPR 2011) — "
                f"nonnegativity with zeros allowed on faces.\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{hyp_arrows} "
                f"(0:ℝ) < {sum_s} → (0:ℝ) ≤ {p_s} := by\n"
                f"  intro {binder} {' '.join(hyps)} hs\n"
                f"  have hpow : (0:ℝ) < ({sum_s})^{n} := pow_pos hs {n}\n"
                + ("\n".join(haves) + "\n" if haves else "")
                + f"  have hid : ({sum_s})^{n} * ({p_s}) = {rhs} := by ring\n"
                f"  have hkey : (0:ℝ) ≤ ({sum_s})^{n} * ({p_s}) := by rw [hid]"
                + ("; linarith\n" if haves else "\n")
                + f"  nlinarith [hkey, hpow]\n"
            )
            n_thms += 1
        return "\n".join(lines), n_thms


def polya_zeros_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    max_n: int = 8,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Pólya-with-zeros family (kind='polya_zeros').

    spec: ``pt -> (p, N)`` — the target polynomial and the Pólya exponent.
    FINDER mode: return ``N = None`` and Telperion searches N ≤ ``max_n``
    (`find_polya_zeros_certificate`), reporting structural obstructions via
    `polya_zeros_obstruction` on a miss.  Either way the certifier verifies
    the expansion exactly and refuses otherwise.
    """
    if not tuple(symbols):
        raise ValueError("Pólya-with-zeros families require at least one symbol")
    consts = dict(constants or {})
    consts.setdefault("polya_zeros_max_n", max_n)
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("polya_zeros", spec),
        constants=consts,
    )

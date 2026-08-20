"""Handelman-Positivstellensatz emitter — nonnegativity of a polynomial on a
POLYTOPE `{ℓ_1 ≥ 0, …, ℓ_m ≥ 0}` via a nonnegative combination of PRODUCTS of the
defining linear forms.

Handelman's theorem: a polynomial strictly positive on a polytope is

    p ≡ Σ_α c_α · ∏_i ℓ_i^{α_i}      (exact identity),   every c_α ≥ 0,

a nonnegative combination of products of the constraints.  Where `ConstrainedSOS`
(Putinar) multiplies each constraint by an SOS, Handelman multiplies PRODUCTS of
constraints by nonnegative CONSTANTS — no SDP, only the LP-feasible cone of
constraint-monomials.  It is the polytope specialization the linear-arithmetic
world lives in (each product `∏ ℓ_i^{α_i} ≥ 0` because every `ℓ_i ≥ 0`).

Telperion is the CERTIFICATE CHECKER: the exponent vectors and their nonnegative
coefficients are supplied (an LP produces them); certification verifies the
identity EXACTLY in rational arithmetic and every coefficient nonnegative — a
decomposition that fails to reconstruct `p`, or carries a negative coefficient,
is REFUSED.

Emitted Lean is robust and hypothesis-driven — each product term is nonnegative
by `mul_nonneg`/`pow_nonneg` folded over the constraint hypotheses, `ring`
discharges the identity, and `linarith` sums the nonnegative pieces:

    theorem <name> : ∀ x y : ℝ, 0 ≤ ℓ_1 → … → 0 ≤ ℓ_m → (0:ℝ) ≤ p := by
      intro x y h_1 … h_m
      have t1 : (0:ℝ) ≤ c_1 * ℓ_1^{a} * ℓ_2^{b} := mul_nonneg (mul_nonneg
        (by norm_num) (pow_nonneg h_1 a)) (pow_nonneg h_2 b)
      …
      have hid : (p : ℝ) = c_1*ℓ_1^{a}*ℓ_2^{b} + … := by ring
      rw [hid]; linarith
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, combinations_with_replacement
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _term_expr(coef, exps, constraints) -> sp.Expr:
    """coef · ∏ ℓ_i^{α_i} from a coefficient and an exponent vector."""
    acc = sp.nsimplify(coef)
    for (g, _hyp), a in zip(constraints, exps):
        acc *= sp.sympify(g) ** int(a)
    return acc


def find_handelman_certificate(p, constraint_exprs, syms, max_deg: int = 2):
    """SEARCH for a Handelman certificate: nonnegative `c_α` and exponent vectors
    `α` (total degree ≤ `max_deg`) with `p = Σ c_α ∏ ℓ_i^{α_i}`.  Returns a
    ``terms`` list of ``(coef, exps)`` or ``None``.

    Exact and sympy-only (no SDP/LP dependency): the products up to degree
    `max_deg` span a cone, and a nonnegative representation — if one exists — has
    a BASIC-FEASIBLE form supported on ≤ rank(A) products.  So enumerate column
    subsets, solve `A c = b` exactly, and keep the first nonnegative solution.
    The result is exactly verified before return; a wrong search never yields a
    certificate (the certifier re-verifies regardless — the finder is untrusted).
    """
    p = sp.expand(sp.sympify(p))
    gens = [sp.expand(sp.sympify(g)) for g in constraint_exprs]
    m = len(gens)
    syms = tuple(syms)

    products, seen = [], set()          # (alpha, product-expr), α total-deg ≤ D
    for total in range(0, max_deg + 1):
        for combo in combinations_with_replacement(range(m), total):
            alpha = [0] * m
            for i in combo:
                alpha[i] += 1
            alpha = tuple(alpha)
            if alpha in seen:
                continue
            seen.add(alpha)
            expr = sp.Integer(1)
            for i, a in enumerate(alpha):
                expr *= gens[i] ** a
            products.append((alpha, sp.expand(expr)))

    def cdict(e):
        return sp.Poly(e, *syms).as_dict() if sp.expand(e) != 0 else {}

    monos = set(cdict(p))
    for _a, e in products:
        monos |= set(cdict(e))
    monos = sorted(monos)
    A = sp.Matrix([[cdict(e).get(mono, 0) for _a, e in products] for mono in monos])
    b = sp.Matrix([cdict(p).get(mono, 0) for mono in monos])
    n = len(products)
    xs = sp.symbols(f"_hlm0:{n}")
    for k in range(1, min(n, len(monos)) + 1):
        for S in combinations(range(n), k):
            sol = sp.linsolve((A[:, list(S)], b), [xs[j] for j in S])
            if not sol:
                continue
            vals = list(sol)[0]
            if any(not v.is_number for v in vals) or any(v < 0 for v in vals):
                continue
            terms = [(sp.Rational(v), products[j][0])
                     for j, v in zip(S, vals) if v != 0]
            recon = sum((sp.Rational(c) * sp.prod([gens[i] ** a
                        for i, a in enumerate(al)]) for c, al in terms), sp.Integer(0))
            if sp.expand(p - recon) == 0:
                return terms
    return None


def certify_handelman_point(family, pt, name):
    """Certify one Handelman instance: (CertifiedInstance, n_checks).

    Reads (p, constraints, terms) = family.special[1](pt): the target `p`, the
    linear constraints `constraints` as ``(ℓ_i, hyp_name)`` pairs, and ``terms``
    as ``(coef, exps)`` where ``exps`` is a nonnegative-integer exponent vector
    aligned with ``constraints`` (the product ``coef · ∏ ℓ_i^{exps_i}``).
    Verifies ``p = Σ coef · ∏ ℓ_i^{α_i}`` exactly with every ``coef`` a
    nonnegative rational; refuses otherwise — no Lean for a non-certificate."""
    p, constraints, terms = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    syms = tuple(family.symbols)
    if terms is None:
        # FINDER mode: search for the certificate instead of checking a supplied one.
        max_deg = int(family.constants.get("handelman_max_deg", 2))
        terms = find_handelman_certificate(
            p, [g for g, _h in constraints], syms, max_deg=max_deg)
        if terms is None:
            raise ValueError(
                f"handelman instance '{name}' REFUSED: no Handelman certificate "
                f"(nonneg combination of constraint products up to degree "
                f"{max_deg}) found — p may not be positive on the polytope, or "
                "needs a higher degree")
    if not terms:
        raise ValueError(f"handelman instance '{name}' REFUSED: empty certificate")

    checks = 0
    recon = sp.Integer(0)
    for coef, exps in terms:
        cr = sp.nsimplify(coef)
        if not cr.is_rational:
            raise ValueError(
                f"handelman instance '{name}' REFUSED: coefficient {coef} is not "
                "rational")
        if cr < 0:
            raise ValueError(
                f"handelman instance '{name}' REFUSED: NEGATIVE coefficient "
                f"{coef} — not a nonnegative combination")
        if len(exps) != len(constraints):
            raise ValueError(
                f"handelman instance '{name}' REFUSED: exponent vector {exps} "
                f"does not match {len(constraints)} constraints")
        if any((int(a) != a or a < 0) for a in exps):
            raise ValueError(
                f"handelman instance '{name}' REFUSED: exponents {exps} must be "
                "nonnegative integers")
        recon += _term_expr(coef, exps, constraints)
        checks += 1

    if sp.expand(p - recon) != 0:
        raise ValueError(
            f"handelman instance '{name}' REFUSED: certificate does not "
            f"reconstruct the target — p - Σ c_α ∏ℓ^α = {sp.expand(p - recon)}")
    checks += 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, list(constraints), list(terms)),
    )
    return inst, checks


@dataclass
class HandelmanEmitter(Emitter):
    """Emit `0 ≤ p` on a polytope from a Handelman certificate
    `p = Σ c_α ∏ ℓ_i^{α_i}`.  Each product term is nonnegative by a
    `mul_nonneg`/`pow_nonneg` fold over the constraint hypotheses; `ring`
    closes the identity; `linarith` sums.  Deterministic order: grid, then terms
    as supplied."""

    def __post_init__(self):
        self.kind = "handelman"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            p, constraints, terms = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            hyps = [(hyp, expr_lean(sp.expand(sp.sympify(g)), syms))
                    for g, hyp in constraints]
            hyp_arrows = "".join(f" (0:ℝ) ≤ {gs} →" for _h, gs in hyps)
            intro_hyps = " ".join(h for h, _g in hyps)

            haves, summands = [], []
            for j, (coef, exps) in enumerate(terms, start=1):
                # rendered term:  c * (ℓ_1)^a1 * (ℓ_2)^a2 * …   (left-assoc)
                factors = [rat_lean(sp.nsimplify(coef))]
                proof = f"(by norm_num : (0:ℝ) ≤ {rat_lean(sp.nsimplify(coef))})"
                for (h, gs), a in zip(hyps, exps):
                    if int(a) == 0:
                        continue
                    factors.append(f"({gs})^{int(a)}")
                    proof = f"mul_nonneg ({proof}) (pow_nonneg {h} {int(a)})"
                term_s = " * ".join(factors)
                haves.append(f"  have t{j} : (0:ℝ) ≤ {term_s} := {proof}")
                summands.append(term_s)
            rhs = " + ".join(summands)

            lines.append(
                f"-- {inst.lean_name}: Handelman certificate  p = Σ c_α ∏ ℓ_i^α "
                f"(nonneg combination of constraint products) on the polytope.\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{hyp_arrows} "
                f"(0:ℝ) ≤ {p_s} := by\n"
                f"  intro {binder} {intro_hyps}\n"
                + "\n".join(haves) + "\n"
                f"  have hid : ({p_s} : ℝ) = {rhs} := by ring\n"
                f"  rw [hid]; linarith\n"
            )
            n += 1
        return "\n".join(lines), n


def handelman_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    max_deg: int = 2,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Handelman family (kind='handelman').

    spec: ``pt -> (p, constraints, terms)`` where ``constraints`` is a list of
    ``(ℓ_i, hyp_name)`` linear constraints (``ℓ_i ≥ 0`` defines the polytope) and
    ``terms`` a list of ``(coef, exps)`` — a nonnegative coefficient and an
    exponent vector over the constraints, giving ``coef · ∏ ℓ_i^{exps_i}``.

    FINDER mode: return ``terms = None`` and Telperion SEARCHES for the
    certificate itself (`find_handelman_certificate`, exact, up to ``max_deg``) —
    upgrading the emitter from "you supply the products" to "you supply the
    polytope."  Either way ``certify_handelman_point`` verifies ``p = Σ`` exactly
    with all coefficients nonnegative, and refuses otherwise.
    """
    if not tuple(symbols):
        raise ValueError("Handelman families require at least one symbol")
    consts = dict(constants or {})
    consts.setdefault("handelman_max_deg", max_deg)
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("handelman", spec),
        constants=consts,
    )

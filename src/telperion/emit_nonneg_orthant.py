"""Nonneg-orthant positivity certificates: `p(v) > 0` for `v ≥ 0` when `p` has
all-nonnegative coefficients and a strictly positive constant term.

This is the reusable Telperion capability distilled from the Kelmans two-hub /
assisted-merge bricks (`proof/formalization/R3Cert/R47R7Kelmans*Cert.lean`), where a
Positivstellensatz gap numerator, after a `pA = 1+x` style shift onto the nonnegative
orthant, comes out as a polynomial whose coefficients are ALL nonnegative and whose
constant term is positive.  Such a polynomial is trivially strictly positive on the
orthant (positive constant + a sum of nonnegative monomials), and the Lean discharge is
a `nlinarith` fed exactly the monomial-nonnegativity facts.

The one non-trivial piece is generating, for each monomial `∏ vᵢ^{eᵢ}`, a Lean proof
term of `0 ≤ ∏ vᵢ^{eᵢ}` from the per-variable hypotheses `hᵢ : 0 ≤ vᵢ` — a left-folded
`mul_nonneg` chain over the flattened factor list.  That generator works for any arity
and any monomial, so this emitter is not tied to the two/three-variable Kelmans shape.

UNTRUSTED, like every Telperion emitter: a wrong certificate is a Lean COMPILE FAILURE,
never a false theorem.  `nonneg_orthant_cert` raises locally if the hypothesis
(all-nonneg coeffs + positive constant) does not hold, so a mis-shaped input fails at
emit time rather than shipping broken Lean.  conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

__all__ = ["nonneg_orthant_cert", "monomial_nonneg_hint", "poly_lean_terms"]


def monomial_nonneg_hint(exps, hyp_names) -> str | None:
    """Lean proof term of `0 ≤ ∏ vᵢ^{exps[i]}`, from `hyp_names[i] : 0 ≤ vᵢ`.

    Returns ``None`` for the empty (constant) monomial.  For a single factor it is the
    bare hypothesis; otherwise a left-folded ``mul_nonneg`` chain over the factor list
    (each factor a variable repeated by its exponent), matching the hand-written Kelmans
    hints (`mul_nonneg (mul_nonneg hx hx) hy` for `x²y`).
    """
    factors: list[str] = []
    for h, e in zip(hyp_names, exps):
        factors.extend([h] * int(e))
    if not factors:
        return None
    acc = factors[0]
    for f in factors[1:]:
        acc = f"mul_nonneg {_paren(acc)} {f}"
    return acc


def _paren(term: str) -> str:
    return term if " " not in term else f"({term})"


def poly_lean_terms(poly: sp.Poly, var_names) -> str:
    """Render an integer-coefficient polynomial as ``c*v1*v1*v2 + ... + c0`` (products,
    not powers), highest total degree first — the exact style of the Kelmans cert files
    so a round-trip reproduces them byte-for-byte.
    """
    terms = []
    for exps, coef in sorted(poly.terms(), key=lambda t: (-sum(t[0]), t[0])):
        c = int(coef)
        if all(e == 0 for e in exps):
            terms.append(f"{c}")
            continue
        mono = "*".join(
            name for name, e in zip(var_names, exps) for _ in range(int(e))
        )
        terms.append(f"{c}*{mono}")
    return " + ".join(terms)


def nonneg_orthant_cert(
    name: str,
    poly: sp.Expr,
    syms,
    *,
    hyp_names=None,
    doc: str | None = None,
) -> str:
    """Emit a Lean theorem `0 < poly` over `ℝ`, for `syms ≥ 0`, discharged by `nlinarith`.

    ``poly`` must expand to an integer-coefficient polynomial in ``syms`` with all
    coefficients nonnegative and a strictly positive constant term (verified here; a
    violation raises ``ValueError`` so mis-shaped inputs fail at emit time).  ``hyp_names``
    default to ``h<var>`` for each symbol.  The proof feeds ``nlinarith`` the per-variable
    hypotheses plus one ``mul_nonneg`` hint per distinct monomial of degree ≥ 1.
    """
    syms = list(syms)
    var_names = [str(s) for s in syms]
    if hyp_names is None:
        hyp_names = [f"h{n}" for n in var_names]
    p = sp.Poly(sp.expand(poly), *syms)
    if any(sp.Rational(c).q != 1 for c in p.coeffs()):
        raise ValueError(f"{name}: non-integer coefficients; clear denominators first")
    if any(int(c) < 0 for c in p.coeffs()):
        raise ValueError(f"{name}: polynomial has a negative coefficient — not nonneg-orthant")
    const = p.eval({s: 0 for s in syms})
    if int(const) <= 0:
        raise ValueError(f"{name}: constant term {const} is not strictly positive")

    hints: list[str] = list(hyp_names)
    seen = set(hyp_names)
    for exps, _ in sorted(p.terms(), key=lambda t: (sum(t[0]), t[0])):
        if sum(exps) <= 1:
            continue
        h = monomial_nonneg_hint(exps, hyp_names)
        if h and h not in seen:
            seen.add(h)
            hints.append(h)

    binders = " ".join(f"({n} : ℝ)" for n in var_names)
    hyps = " ".join(f"({hn} : 0 ≤ {vn})" for hn, vn in zip(hyp_names, var_names))
    body = poly_lean_terms(p, var_names)
    hint_str = ", ".join(hints)
    docblock = f"/-- {doc} -/\n" if doc else ""
    return (
        f"{docblock}"
        f"theorem {name} {binders} {hyps} :\n"
        f"    (0:ℝ) < {body} := by\n"
        f"  nlinarith [{hint_str}]"
    )

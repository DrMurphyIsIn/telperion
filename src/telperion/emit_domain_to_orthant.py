"""Constrained-domain positivity via an affine map to the nonnegative orthant.

Many positivity goals hold on a SIMPLICIAL CONE rather than the raw orthant: e.g. the
Kelmans two-hub cert needs `pA, pB ≥ 1`, and the assisted-merge cert needs
`pA ≥ pB ≥ 1`.  The standard move (done by hand in `R47R7Kelmans*Cert.lean`) is to
introduce slack variables — `pA = 1 + x`, `pB = pA + s` — turning the constraint set into
`x, s ≥ 0`, at which point the shifted polynomial is a nonneg-orthant certificate
(`emit_nonneg_orthant`).

This module automates that reparametrization.  Given a target polynomial and a chain of
affine lower-bound constraints `varᵢ ≥ lowerᵢ` (where each `lowerᵢ` depends only on a
constant or earlier variables — a simplicial cone), it:

  * introduces slacks `tᵢ = varᵢ − lowerᵢ ≥ 0` and rewrites the polynomial in the slacks,
  * verifies the shifted polynomial is nonneg-orthant-shaped (all-nonneg coefficients,
    positive constant) — raising locally otherwise, so a domain that does NOT actually
    force positivity fails at emit time rather than shipping broken Lean,
  * emits the Lean theorem stated in the ORIGINAL variables with the constraint
    hypotheses, discharged by `nlinarith` fed the slack-nonnegativities
    (`sub_nonneg.mpr hᵢ : 0 ≤ varᵢ − lowerᵢ`) and one `mul_nonneg` product per slack
    monomial of degree ≥ 1.

Because the theorem is stated in the original variables, it drops straight into a proof
that has `1 ≤ pA`, `pA ≤ pB` etc. in context — no manual substitution at the call site.
UNTRUSTED like every emitter: wrong cert = local raise or Lean compile failure, never a
false theorem.  conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from .emit_nonneg_orthant import monomial_nonneg_hint

__all__ = ["domain_to_orthant_cert", "build_slack_substitution"]


def build_slack_substitution(constraints):
    """From `[(lower, var), ...]` (each `var ≥ lower`, simplicial), return
    `(slack_syms, subs, slack_exprs)`:

      * ``slack_syms[i]`` — a fresh nonnegative symbol `t{i}` for `varᵢ − lowerᵢ`,
      * ``subs`` — a dict mapping each ``var`` to ``lower + t`` with EARLIER vars already
        resolved to their slack form (so the whole cone unfolds to the orthant),
      * ``slack_exprs[i]`` — the slack ``varᵢ − lowerᵢ`` in the ORIGINAL variables.
    """
    slack_syms, subs, slack_exprs = [], {}, []
    for i, (lower, var) in enumerate(constraints):
        t = sp.Symbol(f"t{i}", nonnegative=True)
        lower_resolved = sp.sympify(lower).xreplace(subs)
        subs[var] = lower_resolved + t
        slack_syms.append(t)
        slack_exprs.append(sp.expand(var - sp.sympify(lower)))
    return slack_syms, subs, slack_exprs


def domain_to_orthant_cert(
    name: str,
    poly: sp.Expr,
    constraints,
    *,
    hyp_names=None,
    doc: str | None = None,
) -> str:
    """Emit a Lean theorem `0 < poly` on the simplicial cone `constraints`, over `ℝ`.

    ``constraints`` is a list of ``(lower, var)`` meaning ``var ≥ lower``, ordered so each
    ``lower`` uses only constants or earlier ``var``s.  ``poly`` must, after the slack
    substitution, be an integer-coefficient polynomial with all-nonnegative coefficients
    and a positive constant term (verified here).  ``hyp_names`` default to ``h<var>``.
    """
    lowers = [sp.sympify(l) for l, _ in constraints]
    orig_vars = [v for _, v in constraints]
    var_names = [str(v) for v in orig_vars]
    if hyp_names is None:
        hyp_names = [f"h{n}" for n in var_names]

    slack_syms, subs, slack_exprs = build_slack_substitution(constraints)
    shifted = sp.expand(sp.sympify(poly).xreplace(subs))
    ps = sp.Poly(shifted, *slack_syms)

    # Guard: the shifted polynomial must be a genuine nonneg-orthant certificate.
    if any(sp.Rational(c).q != 1 for c in ps.coeffs()):
        raise ValueError(f"{name}: non-integer coefficients after shift; clear denominators first")
    if any(int(c) < 0 for c in ps.coeffs()):
        raise ValueError(
            f"{name}: shifted polynomial has a negative coefficient — the domain does not force positivity"
        )
    const = ps.eval({t: 0 for t in slack_syms})
    if int(const) <= 0:
        raise ValueError(f"{name}: constant term {const} after shift is not strictly positive")

    # slack-nonneg proof terms in the ORIGINAL variables: `0 ≤ var - lower`.
    slack_proofs = [f"sub_nonneg.mpr {hn}" for hn in hyp_names]
    # For a bare lower bound `0 ≤ var` (lower == 0) the slack IS the variable; use the hyp
    # directly if it already proves `0 ≤ var` (kept general via sub_nonneg on `0 ≤ var`).

    hints: list[str] = list(slack_proofs)
    seen = set(slack_proofs)
    for exps, _ in sorted(ps.terms(), key=lambda e: (sum(e[0]), e[0])):
        if sum(exps) <= 1:
            continue
        h = monomial_nonneg_hint(exps, [f"({sp_})" for sp_ in slack_proofs])
        if h and h not in seen:
            seen.add(h)
            hints.append(h)

    binders = " ".join(f"({n} : ℝ)" for n in var_names)
    hyps = " ".join(
        f"({hn} : {sp.printing.str.sstr(lo)} ≤ {vn})"
        for hn, lo, vn in zip(hyp_names, lowers, var_names)
    )
    body = _poly_original_vars(poly, orig_vars)
    hint_str = ", ".join(hints)
    docblock = f"/-- {doc} -/\n" if doc else ""
    return (
        f"{docblock}"
        f"theorem {name} {binders} {hyps} :\n"
        f"    (0:ℝ) < {body} := by\n"
        f"  nlinarith [{hint_str}]"
    )


def _poly_original_vars(poly: sp.Expr, orig_vars) -> str:
    """Render the target polynomial in the ORIGINAL variables as ``c*a*a*b + ... + c0``
    (products, not powers), highest total degree first."""
    names = [str(v) for v in orig_vars]
    p = sp.Poly(sp.expand(poly), *orig_vars)
    terms = []
    for exps, coef in sorted(p.terms(), key=lambda t: (-sum(t[0]), t[0])):
        c = sp.Rational(coef)
        cs = str(c.p) if c.q == 1 else f"({c.p}/{c.q} : ℝ)"
        if all(e == 0 for e in exps):
            terms.append(cs)
            continue
        mono = "*".join(nm for nm, e in zip(names, exps) for _ in range(int(e)))
        # drop a unit coefficient (`1*ab` -> `ab`, `-1*ab` -> `-ab`)
        if c == 1:
            terms.append(mono)
        elif c == -1:
            terms.append(f"-{mono}")
        else:
            terms.append(f"{cs}*{mono}")
    return " + ".join(terms)

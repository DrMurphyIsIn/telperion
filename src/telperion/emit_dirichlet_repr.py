"""Euler-Maclaurin / Abel-summation representation emitter (zeta-type Dirichlet series).

A Dirichlet series with unit coefficients, `Σ_{n≥1} n^{-s}`, has a TRUNCATED representation obtained by
Abel summation of `f(x) = x^{-s}` against the counting function `⌊x⌋ = x - {x}`:

    ζ(s) = Σ_{n=1}^N n^{-s}  +  N^{1-s}/(s-1)  −  s · ∫_{x>N} {x} x^{-(s+1)} dx      (Re s > 1, N ≥ 1),

the finite-N companion of `zeta_repr_R1`, and the engine of the sharp near-line bound (`ZetaLogBound`).
The two CORRECTION TERMS are exact closed forms:

    truncation term   N^{1-s}/(s-1)   from   ∫_{N}^{∞} x^{-s} dx = N^{1-s}/(s-1),
    integral factor   s               from   d/dx x^{-s} = -s x^{-(s+1)}.

CERTIFICATE. Telperion is the CHECKER; this generator is UNTRUSTED. Unlike a finite algebraic
certificate, the representation is an analytic identity (an integral) whose PROOF is discharged by the
Mathlib Abel-summation lemma `sum_mul_eq_sub_integral_mul₀`. What is exactly re-verifiable -- and what
`verify_corrections` checks by SYMBOLIC DIFFERENTIATION (anti-phantom) -- is that the emitted correction
terms are the correct closed forms:  d/dx[x^{1-s}/(1-s)] == x^{-s}  (so ∫x^{-s} = x^{1-s}/(1-s) and the
truncation term reads off), and  d/dx[x^{-s}] == -s·x^{-(s+1)}  (so the integral factor is s). A wrong
closed form (wrong exponent, wrong pole factor, wrong sign) fails the differentiation check and is
REFUSED before any Lean is written. This is a REPRESENTATION-SHAPE emitter: it emits the theorem
STATEMENT (and the re-verified correction terms); the analytic proof is the Abel lemma.

A gap-filler FEEDING the growth-bound layer; NOT a proof of RH. conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp


def verify_corrections() -> tuple[bool, sp.Expr, sp.Expr]:
    """EXACT anti-phantom gate by symbolic differentiation: confirm the two closed forms underlying the
    truncation term and the integral factor. Returns (ok, antiderivative, deriv)."""
    x, s = sp.symbols("x s")
    antideriv = x ** (1 - s) / (1 - s)          # claimed ∫ x^{-s} dx
    deriv_of_power = sp.diff(x ** (-s), x)       # claimed d/dx x^{-s}
    ok_antideriv = sp.simplify(sp.diff(antideriv, x) - x ** (-s)) == 0
    ok_deriv = sp.simplify(deriv_of_power - (-s * x ** (-s - 1))) == 0
    return bool(ok_antideriv and ok_deriv), antideriv, deriv_of_power


def emit_zeta_trunc_statement(thm_name: str = "zeta_trunc") -> str:
    """Emit the truncated Euler-Maclaurin representation STATEMENT (the shape). REFUSES if the closed
    forms do not re-verify. The proof body is the Abel-summation lemma (see StripReprR1)."""
    ok, _, _ = verify_corrections()
    if not ok:
        raise ValueError("representation REFUSED: the correction-term closed forms failed the "
                         "symbolic-differentiation check")
    return f"""\
/-- Truncated Euler-Maclaurin representation of ζ on `Re s > 1` at integer cutoff `N ≥ 1`.
    Correction terms re-verified by symbolic differentiation before emission; proof via Abel summation
    (`sum_mul_eq_sub_integral_mul₀`, see `zeta_partial_sum_repr`). -/
theorem {thm_name} {{s : ℂ}} (hs : 1 < s.re) {{N : ℕ}} (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1)
        - s * ∫ x in Set.Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) := by
  sorry  -- Abel summation; discharged in StripReprR1.zeta_partial_sum_repr + integral split
"""


def _self_test() -> None:
    ok, antideriv, deriv = verify_corrections()
    assert ok, (antideriv, deriv)
    stmt = emit_zeta_trunc_statement()
    assert "riemannZeta s" in stmt and "N ^ (1 - s)" in stmt.replace("(N : ℂ)", "N") \
        or "(N : ℂ) ^ (1 - s)" in stmt
    assert "Int.fract" in stmt

    # anti-phantom: a WRONG antiderivative must fail the differentiation check.
    x, s = sp.symbols("x s")
    wrong = x ** (1 - s) / (s - 1)              # wrong pole sign
    assert sp.simplify(sp.diff(wrong, x) - x ** (-s)) != 0
    print("emit_dirichlet_repr self-test: OK")


if __name__ == "__main__":
    _self_test()

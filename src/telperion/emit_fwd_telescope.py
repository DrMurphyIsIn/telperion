"""Forward-difference telescoping emitter — the W2 prover, mechanizing the
SumEqProd.lean template (2026-08-20, knapsack_sos arc).

For a hypergeometric-type sequence defined by the first-order recurrence

    f(0) = 1,      f(q+1) = f(q) * A(q) / (P - q)        (P a parameter expr),

the iterated forward differences admit the closed form

    Δ^[j] f (q) = (-1)^j * ∏_{u<j} N(u) * f(q) / ∏_{u<j} (P - q - u),

PROVIDED the conjectured numerator factor N satisfies the CONTIGUOUS
IDENTITY (the one-step telescoping, with j symbolic):

    A(q) - (P - q - j) + N(j) = 0.

That single polynomial identity is the whole certificate: Telperion verifies
it exactly in sympy (a wrong N is REFUSED) and then emits the full Lean
induction skeleton proven on the knapsack instance — pnum/pden product
definitions, positivity, the pden shift law, and the closed-form theorem
via mathlib's `fwdDiff` — with A, N, P substituted.  Every proof step is
shape-generic: `field_simp; ring` closes exactly because the contiguous
identity is a polynomial identity.

This is the "holonomic positivity" W2 skill in its first-order incarnation:
the certificate is the contiguous relation, the Lean is the telescoping
induction.  (The alternating-sum/Newton-expansion assembly connecting
Δ^[k] f (k) to binomial sums lives in mathlib's fwdDiff_iter_eq_sum_shift
and the downstream file — see telperion/examples/g1_floors/lean/SumEqProd.lean.)
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def certify_fwd_telescope_point(family, pt, name):
    """Verify the contiguous identity A(q) - (P - q - j) + N(j) = 0 exactly."""
    spec = family.special[1](pt)
    n = tuple(family.symbols)[0]
    q, u, j = sp.symbols("q u j")
    A = sp.sympify(spec["A"])
    P = sp.sympify(spec["P"])
    N = sp.sympify(spec["N"])
    bad = (A.free_symbols - {n, q}) | (P.free_symbols - {n}) | (N.free_symbols - {n, u})
    if bad:
        raise ValueError(
            f"fwd_telescope instance '{name}' REFUSED: unexpected symbols {bad} "
            "(A may use (n, q); P only n; N only (n, u))")
    contiguous = sp.simplify(A - (P - q - j) + N.subs(u, j))
    if contiguous != 0:
        raise ValueError(
            f"fwd_telescope instance '{name}' REFUSED: contiguous identity "
            f"A(q) - (P - q - j) + N(j) = 0 fails (residual {contiguous}) — "
            "the conjectured closed form does not telescope")
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(A, P, N),
    )
    return inst, 1


_TEMPLATE = '''-- {name}: forward-difference closed form for the recurrence
-- f(q+1) = f(q) * ({A_str}) / ({P_str} - q); certificate = the contiguous
-- identity A(q) - (P - q - j) + N(j) = 0, verified exactly at certification.

def {name}_f (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | q + 1 => {name}_f n q * ({A_str}) / ({P_str} - q)

def {name}_pnum (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | u + 1 => {name}_pnum n u * ({N_u_str})

def {name}_pden (n : ℚ) (q : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => {name}_pden n q j * ({P_str} - q - j)

theorem {name}_pden_pos (n : ℚ) (q j : ℕ) (h : (q : ℚ) + j < {P_str} + 1) :
    0 < {name}_pden n q j := by
  induction j with
  | zero => norm_num [{name}_pden]
  | succ j ih =>
    have h' : (q : ℚ) + j < {P_str} + 1 := by push_cast at h ⊢; linarith
    have hf : (0 : ℚ) < {P_str} - q - j := by push_cast at h; linarith
    rw [{name}_pden]
    exact mul_pos (ih h') hf

theorem {name}_pden_shift (n : ℚ) (q j : ℕ) :
    {name}_pden n q (j + 1) = ({P_str} - q) * {name}_pden n (q + 1) j := by
  induction j with
  | zero => norm_num [{name}_pden]
  | succ j ih =>
    conv_lhs => rw [{name}_pden]
    rw [ih]
    conv_rhs => rw [{name}_pden]
    push_cast
    ring

/-- The W2 payoff: closed form for the iterated forward difference. -/
theorem {name}_fwdDiff_iter (n : ℚ) (j : ℕ) :
    ∀ q : ℕ, (q : ℚ) + j < {P_str} →
      (fwdDiff 1)^[j] ({name}_f n) q
        = (-1) ^ j * {name}_pnum n j * {name}_f n q / {name}_pden n q j := by
  induction j with
  | zero =>
    intro q _
    norm_num [{name}_pnum, {name}_pden]
  | succ j ih =>
    intro q hq
    have hq1 : ((q + 1 : ℕ) : ℚ) + j < {P_str} := by push_cast at hq ⊢; linarith
    have hq0 : (q : ℚ) + j < {P_str} := by push_cast at hq ⊢; linarith
    have hnq : (0 : ℚ) < {P_str} - q := by
      have : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
      push_cast at hq; linarith
    have hnqj : (0 : ℚ) < {P_str} - q - j := by push_cast at hq; linarith
    have hB : (0 : ℚ) < {name}_pden n q j :=
      {name}_pden_pos n q j (by push_cast at hq ⊢; linarith)
    have hA : (0 : ℚ) < {name}_pden n (q + 1) j :=
      {name}_pden_pos n (q + 1) j (by push_cast at hq ⊢; linarith)
    have hd : {name}_pden n q (j + 1) = {name}_pden n q j * ({P_str} - q - j) := by
      rw [{name}_pden]
    have hArel : {name}_pden n (q + 1) j
        = {name}_pden n q j * ({P_str} - q - j) / ({P_str} - q) := by
      rw [eq_div_iff (ne_of_gt hnq)]
      linear_combination hd - {name}_pden_shift n q j
    rw [Function.iterate_succ_apply']
    have hstep : fwdDiff 1 ((fwdDiff 1)^[j] ({name}_f n)) q
        = (fwdDiff 1)^[j] ({name}_f n) (q + 1)
          - (fwdDiff 1)^[j] ({name}_f n) q := rfl
    rw [hstep, ih (q + 1) hq1, ih q hq0]
    have hf1 : {name}_f n (q + 1)
        = {name}_f n q * ({A_str}) / ({P_str} - q) := by rw [{name}_f]
    have hpn : {name}_pnum n (j + 1) = {name}_pnum n j * ({N_j_str}) := by
      rw [{name}_pnum]
    rw [hf1, hpn, hd, hArel, pow_succ]
    field_simp
    ring
'''


@dataclass
class FwdTelescopeEmitter(Emitter):
    """Emit the fwdDiff telescoping induction with A, N, P substituted."""

    def __post_init__(self):
        self.kind = "fwd_telescope"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        n = tuple(fam.family.symbols)[0]
        q, u, j = sp.symbols("q u j")
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            A, P, N = inst.payload  # type: ignore[misc]
            lines.append(_TEMPLATE.format(
                name=inst.lean_name,
                A_str=expr_lean(A, (n, q)),
                P_str=expr_lean(P, (n,)),
                N_u_str=expr_lean(N, (n, u)),
                N_j_str=expr_lean(N.subs(u, j), (n, j)),
            ))
            n_thm += 4
        return "\n".join(lines), n_thm


def fwd_telescope_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a fwd-telescope family (kind='fwd_telescope').

    spec: ``pt -> {"A": expr(n, q), "P": expr(n), "N": expr(n, u)}`` for the
    recurrence f(q+1) = f(q)·A/(P−q) and the conjectured pnum factor N.
    """
    n = sp.symbols("n")
    return InequalityFamily(
        name=name,
        symbols=(n,),
        grid=grid,
        lean_name=lean_name,
        special=("fwd_telescope", spec),
        constants=constants or {},
    )

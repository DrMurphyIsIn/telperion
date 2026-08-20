/- telperion 0.1.6 | family WZ | input-hash 32248143b76885dd
   1 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace WZ

namespace Telperion

/-- WZ row-sum invariant.  If the WZ equation
    `Fn1 k − Fn k = G (k+1) − G k` holds for every `k` (with `Fn1`, `Fn` the
    summand rows at `n+1` and `n`, and `G` the WZ mate at row `n`), and `G`
    takes equal values at the two ends of the range `[0, N]`, then the finite
    row-sum is unchanged from `n` to `n+1`.  Iterating from the base row yields
    the closed-form identity. -/
theorem wz_row_invariant {Fn1 Fn G : ℕ → ℝ} {N : ℕ}
    (hwz : ∀ k, Fn1 k - Fn k = G (k + 1) - G k)
    (hbdry : G N = G 0) :
    (∑ k ∈ Finset.range N, Fn1 k) = ∑ k ∈ Finset.range N, Fn k := by
  have h : (∑ k ∈ Finset.range N, (Fn1 k - Fn k))
         = ∑ k ∈ Finset.range N, (G (k + 1) - G k) :=
    Finset.sum_congr rfl (fun k _ => hwz k)
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub] at h
  rw [hbdry] at h
  linarith

end Telperion

-- binom_2n: WZ certificate for  Σ_k F(n,k) = rhs(n).
-- Denominator-cleared WZ equation (verifies the mate R); pair with
-- Telperion.wz_row_invariant + the base-row value to close the sum.
theorem binom_2n_wz : ∀ n k : ℝ, (0 - 1 - n) * (2 * n - 2 * k) * (1 + k) * (2 + 2 * n - 2 * k) - (2 * k - 2 - 2 * n) * (2 * n - 2 * k) * (1 + k) * (2 + 2 * n - 2 * k) - (0 - 1 - k) * (n - k) * (2 * k - 2 - 2 * n) * (2 + 2 * n - 2 * k) + (0 - k) * (2 * k - 2 - 2 * n) * (2 * n - 2 * k) * (1 + k) = 0 := by
  intro n k
  ring

end WZ
end G1

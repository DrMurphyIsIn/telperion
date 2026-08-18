/- telperion 0.1.3 | family PadicValuation | input-hash acc54ca7e255cda3
   5 theorems, 5 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Padic

/-- Valuation-magnitude split: a p-free magnitude bound `N ≤ C * D0`
    combined with `C ≤ p^K` gives `N ≤ p^K * D0` — the bridge from an
    analytic bound to the p-adic cancellation count (`p^K` dominates once the
    cancellation count `K` is large; the tie is the residual `K` small case). -/
theorem le_pow_mul_of_le_mul {N C D0 pK : ℕ}
    (hmag : N ≤ C * D0) (hpow : C ≤ pK) : N ≤ pK * D0 := by
  calc N ≤ C * D0 := hmag
    _ ≤ pK * D0 := Nat.mul_le_mul_right _ hpow

/-- Telescoping of the p-adic valuation over a product (Mathlib
    `padicValRat.mul`): the valuation of a product is the sum of the
    valuations — the node-by-node accounting of the cancellation count `K`.
    Stated concretely for three factors (the general n-fold form is this by
    induction / `Finset.prod`); this is the primitive a tree certificate
    chains over its nodes. -/
theorem padicValRat_mul3 {p : ℕ} [Fact p.Prime] {a b c : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    padicValRat p (a * b * c)
      = padicValRat p a + padicValRat p b + padicValRat p c := by
  rw [padicValRat.mul (mul_ne_zero ha hb) hc, padicValRat.mul ha hb]

theorem v23_root_num : (1 ∣ 64) ∧ ¬ (23 ∣ 64) := by norm_num
theorem v23_root_den : (23 ∣ 621) ∧ ¬ (529 ∣ 621) := by norm_num
theorem v23_child_num : (1 ∣ 86959512306484890624) ∧ ¬ (23 ∣ 86959512306484890624) := by norm_num
theorem v23_child_den : (1801152661463 ∣ 87946907297998046875) ∧ ¬ (41426511213649 ∣ 87946907297998046875) := by norm_num
theorem v23_tree_denominator : (74615470927590710561908487 ∣ 177897145575501228718539445400238037109375) ∧ ¬ (1716155831334586342923895201 ∣ 177897145575501228718539445400238037109375) := by norm_num

end Padic
end G1

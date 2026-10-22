/- telperion 0.1.6 | family RangeCompletenessDecide | input-hash 05b88074bfa54d7f
   10 theorems, 4251 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RangeCompletenessDecide

/-- sqf_lt_200: the explicit list L. -/
def sqf_lt_200_list : List ℕ := [5, 6, 10, 13, 14, 15, 17, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37, 38, 39, 41, 42, 46, 47, 51, 53, 55, 57, 58, 59, 61, 62, 65, 66, 69, 70, 71, 73, 74, 77, 78, 79, 82, 83, 85, 86, 87, 89, 91, 93, 94, 95, 97, 101, 102, 103, 105, 106, 107, 109, 110, 111, 113, 114, 115, 118, 119, 122, 123, 127, 129, 130, 131, 133, 134, 137, 138, 139, 141, 142, 143, 145, 146, 149, 151, 154, 155, 157, 158, 159, 161, 165, 166, 167, 170, 173, 174, 177, 178, 179, 181, 182, 183, 185, 186, 187, 190, 191, 193, 194, 195, 197, 199]

/-- sqf_lt_200: the excluded elements. -/
def sqf_lt_200_excl : List ℕ := [1, 2, 3, 7, 11, 19, 43, 67, 163]

-- sqf_lt_200: coverage of the guarded range by the list, exact-evaluated in Python
-- pre-emission through the same AST; kernel `decide` is the final gate.
set_option maxRecDepth 8192 in
theorem sqf_lt_200 : ∀ m ∈ Finset.range 200, (∀ k ∈ Finset.Icc 2 15, ¬ (k * k) ∣ m) → m ∉ sqf_lt_200_excl → m ∈ sqf_lt_200_list := by
  decide +kernel

/-- Bridge: Mathlib's `Squarefree` implies the kernel-friendly surrogate `SqfBelow 15` (sound for every bound K). -/
theorem sqf_lt_200_sqfBelow_of_squarefree {m : ℕ} (hm : Squarefree m) :
    ∀ k ∈ Finset.Icc 2 15, ¬ (k * k) ∣ m := by
  intro k hk h
  have := Nat.isUnit_iff.mp (hm k h)
  rw [Finset.mem_Icc] at hk
  omega

/-- sqf_lt_200: the consumer-facing theorem about `Squarefree m`, from the kernel coverage through the bridge. -/
theorem sqf_lt_200_of_squarefree : ∀ m < 200, Squarefree m → m ∉ sqf_lt_200_excl → m ∈ sqf_lt_200_list :=
  fun m hm hsq hg1 => sqf_lt_200 m (Finset.mem_range.mpr hm) (sqf_lt_200_sqfBelow_of_squarefree hsq) hg1

theorem sqf_lt_200_length : sqf_lt_200_list.length = 113 := by
  decide +kernel

theorem sqf_lt_200_nodup : sqf_lt_200_list.Nodup := by
  decide +kernel

-- sqf_lt_200: soundness, every list element is in the guarded range (with the
-- coverage theorem: the list is EXACTLY the guarded set).
set_option maxRecDepth 8192 in
theorem sqf_lt_200_sound : ∀ m ∈ sqf_lt_200_list, m < 200 ∧ ((∀ k ∈ Finset.Icc 2 15, ¬ (k * k) ∣ m) ∧ m ∉ sqf_lt_200_excl) := by
  decide +kernel

/-- sqf_3mod4_lt_60: the explicit list L. -/
def sqf_3mod4_lt_60_list : List ℕ := [3, 7, 11, 15, 19, 23, 31, 35, 39, 43, 47, 51, 55, 59]

-- sqf_3mod4_lt_60: coverage of the guarded range by the list, exact-evaluated in Python
-- pre-emission through the same AST; kernel `decide` is the final gate.
set_option maxRecDepth 8192 in
theorem sqf_3mod4_lt_60 : ∀ m ∈ Finset.range 60, (∀ k ∈ Finset.Icc 2 8, ¬ (k * k) ∣ m) → (m % 4) = 3 → m ∈ sqf_3mod4_lt_60_list := by
  decide +kernel

/-- Bridge: Mathlib's `Squarefree` implies the kernel-friendly surrogate `SqfBelow 8` (sound for every bound K). -/
theorem sqf_3mod4_lt_60_sqfBelow_of_squarefree {m : ℕ} (hm : Squarefree m) :
    ∀ k ∈ Finset.Icc 2 8, ¬ (k * k) ∣ m := by
  intro k hk h
  have := Nat.isUnit_iff.mp (hm k h)
  rw [Finset.mem_Icc] at hk
  omega

/-- sqf_3mod4_lt_60: the consumer-facing theorem about `Squarefree m`, from the kernel coverage through the bridge. -/
theorem sqf_3mod4_lt_60_of_squarefree : ∀ m < 60, Squarefree m → (m % 4) = 3 → m ∈ sqf_3mod4_lt_60_list :=
  fun m hm hsq hg1 => sqf_3mod4_lt_60 m (Finset.mem_range.mpr hm) (sqf_3mod4_lt_60_sqfBelow_of_squarefree hsq) hg1

theorem sqf_3mod4_lt_60_length : sqf_3mod4_lt_60_list.length = 14 := by
  decide +kernel

end RangeCompletenessDecide

/- telperion 0.1.6 | family GramInertia | input-hash 6f49eaa3ebc99ebb
   4 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import RHInertia

namespace GramInertia

open Matrix

-- inertia_pair_block_2: certified inertia of EVERY real symmetric matrix in the rational box
-- lo ≤ G ≤ hi (n = 2, half-width w = 1/10).  Signature (p, q) = (1, 1).
-- Witness bases have unit absolute-sum columns; the compressed midpoint forms are
-- diagonal with margins delta_X = 1 > w*S_X = 1/10 and
-- delta_Y = 2 > w*S_Y = 1/10.  Sylvester's law (RHLinalg) does the rest.
-- A finite linear-algebra certificate; says nothing about zeta.  conjecture1_proved = False.
set_option maxHeartbeats 1000000 in
theorem inertia_pair_block_2 (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsHermitian)
    (hlo : ∀ i j, (!![(9 / 10), (-(1 / 10)); (-(1 / 10)), (-(21 / 10))] : Matrix (Fin 2) (Fin 2) ℝ) i j ≤ G i j)
    (hhi : ∀ i j, G i j ≤ (!![(11 / 10), (1 / 10); (1 / 10), (-(19 / 10))] : Matrix (Fin 2) (Fin 2) ℝ) i j) :
    RHLinalg.posIndex hG = 1 ∧ RHInertia.defect hG = 1 := by
  have lo_0_0 : ((9 / 10) : ℝ) ≤ G 0 0 := by
    inertia_entries_using hlo 0 0
  have lo_0_1 : ((-(1 / 10)) : ℝ) ≤ G 0 1 := by
    inertia_entries_using hlo 0 1
  have lo_1_0 : ((-(1 / 10)) : ℝ) ≤ G 1 0 := by
    inertia_entries_using hlo 1 0
  have lo_1_1 : ((-(21 / 10)) : ℝ) ≤ G 1 1 := by
    inertia_entries_using hlo 1 1
  have hi_0_0 : G 0 0 ≤ ((11 / 10) : ℝ) := by
    inertia_entries_using hhi 0 0
  have hi_0_1 : G 0 1 ≤ ((1 / 10) : ℝ) := by
    inertia_entries_using hhi 0 1
  have hi_1_0 : G 1 0 ≤ ((1 / 10) : ℝ) := by
    inertia_entries_using hhi 1 0
  have hi_1_1 : G 1 1 ≤ ((-(19 / 10)) : ℝ) := by
    inertia_entries_using hhi 1 1
  have hX : ∀ v : Fin 1 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ * G *
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval G (!![1, 0; 0, (-2)]) (!![1; 0]) (!![1]) ![1]
      ((1 / 10)) (1) 1
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0)]
  have hY : ∀ v : Fin 1 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ * (-G) *
        (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval (-G) (!![(-1), 0; 0, 2]) (!![0; 1]) (!![2]) ![1]
      ((1 / 10)) (2) 1
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0)]
  exact RHInertia.inertia_eq_of_witnesses hG _ _ (by norm_num) hX hY

-- inertia_coupled_3: certified inertia of EVERY real symmetric matrix in the rational box
-- lo ≤ G ≤ hi (n = 3, half-width w = 1/20).  Signature (p, q) = (2, 1).
-- Witness bases have unit absolute-sum columns; the compressed midpoint forms are
-- diagonal with margins delta_X = 2/3 > w*S_X = 1/10 and
-- delta_Y = 3 > w*S_Y = 1/20.  Sylvester's law (RHLinalg) does the rest.
-- A finite linear-algebra certificate; says nothing about zeta.  conjecture1_proved = False.
set_option maxHeartbeats 1000000 in
theorem inertia_coupled_3 (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsHermitian)
    (hlo : ∀ i j, (!![(39 / 20), (19 / 20), (-(1 / 20)); (19 / 20), (39 / 20), (-(1 / 20)); (-(1 / 20)), (-(1 / 20)), (-(61 / 20))] : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ G i j)
    (hhi : ∀ i j, G i j ≤ (!![(41 / 20), (21 / 20), (1 / 20); (21 / 20), (41 / 20), (1 / 20); (1 / 20), (1 / 20), (-(59 / 20))] : Matrix (Fin 3) (Fin 3) ℝ) i j) :
    RHLinalg.posIndex hG = 2 ∧ RHInertia.defect hG = 1 := by
  have lo_0_0 : ((39 / 20) : ℝ) ≤ G 0 0 := by
    inertia_entries_using hlo 0 0
  have lo_0_1 : ((19 / 20) : ℝ) ≤ G 0 1 := by
    inertia_entries_using hlo 0 1
  have lo_0_2 : ((-(1 / 20)) : ℝ) ≤ G 0 2 := by
    inertia_entries_using hlo 0 2
  have lo_1_0 : ((19 / 20) : ℝ) ≤ G 1 0 := by
    inertia_entries_using hlo 1 0
  have lo_1_1 : ((39 / 20) : ℝ) ≤ G 1 1 := by
    inertia_entries_using hlo 1 1
  have lo_1_2 : ((-(1 / 20)) : ℝ) ≤ G 1 2 := by
    inertia_entries_using hlo 1 2
  have lo_2_0 : ((-(1 / 20)) : ℝ) ≤ G 2 0 := by
    inertia_entries_using hlo 2 0
  have lo_2_1 : ((-(1 / 20)) : ℝ) ≤ G 2 1 := by
    inertia_entries_using hlo 2 1
  have lo_2_2 : ((-(61 / 20)) : ℝ) ≤ G 2 2 := by
    inertia_entries_using hlo 2 2
  have hi_0_0 : G 0 0 ≤ ((41 / 20) : ℝ) := by
    inertia_entries_using hhi 0 0
  have hi_0_1 : G 0 1 ≤ ((21 / 20) : ℝ) := by
    inertia_entries_using hhi 0 1
  have hi_0_2 : G 0 2 ≤ ((1 / 20) : ℝ) := by
    inertia_entries_using hhi 0 2
  have hi_1_0 : G 1 0 ≤ ((21 / 20) : ℝ) := by
    inertia_entries_using hhi 1 0
  have hi_1_1 : G 1 1 ≤ ((41 / 20) : ℝ) := by
    inertia_entries_using hhi 1 1
  have hi_1_2 : G 1 2 ≤ ((1 / 20) : ℝ) := by
    inertia_entries_using hhi 1 2
  have hi_2_0 : G 2 0 ≤ ((1 / 20) : ℝ) := by
    inertia_entries_using hhi 2 0
  have hi_2_1 : G 2 1 ≤ ((1 / 20) : ℝ) := by
    inertia_entries_using hhi 2 1
  have hi_2_2 : G 2 2 ≤ ((-(59 / 20)) : ℝ) := by
    inertia_entries_using hhi 2 2
  have hX : ∀ v : Fin 2 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![1, (-(1 / 3)); 0, (2 / 3); 0, 0] : Matrix (Fin 3) (Fin 2) ℝ)ᴴ * G *
        (!![1, (-(1 / 3)); 0, (2 / 3); 0, 0] : Matrix (Fin 3) (Fin 2) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval G (!![2, 1, 0; 1, 2, 0; 0, 0, (-3)]) (!![1, (-(1 / 3)); 0, (2 / 3); 0, 0]) (!![2, 0; 0, (2 / 3)]) ![1, 1]
      ((1 / 20)) ((2 / 3)) 2
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_2, hi_0_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_2, hi_1_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_0, hi_2_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_1, hi_2_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_2, hi_2_2]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hY : ∀ v : Fin 1 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ)ᴴ * (-G) *
        (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval (-G) (!![(-2), (-1), 0; (-1), (-2), 0; 0, 0, 3]) (!![0; 0; 1]) (!![3]) ![1]
      ((1 / 20)) (3) 1
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_2, hi_0_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_2, hi_1_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_0, hi_2_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_1, hi_2_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_2, hi_2_2]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0)]
  exact RHInertia.inertia_eq_of_witnesses hG _ _ (by norm_num) hX hY

-- inertia_offline_pairs_4: certified inertia of EVERY real symmetric matrix in the rational box
-- lo ≤ G ≤ hi (n = 4, half-width w = 1/60).  Signature (p, q) = (2, 2).
-- Witness bases have unit absolute-sum columns; the compressed midpoint forms are
-- diagonal with margins delta_X = 3/2 > w*S_X = 1/30 and
-- delta_Y = 2/3 > w*S_Y = 1/30.  Sylvester's law (RHLinalg) does the rest.
-- A finite linear-algebra certificate; says nothing about zeta.  conjecture1_proved = False.
set_option maxHeartbeats 1000000 in
theorem inertia_offline_pairs_4 (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : G.IsHermitian)
    (hlo : ∀ i j, (!![(179 / 60), (59 / 60), (-(1 / 60)), (-(1 / 60)); (59 / 60), (179 / 60), (-(1 / 60)), (-(1 / 60)); (-(1 / 60)), (-(1 / 60)), (-(121 / 60)), (59 / 60); (-(1 / 60)), (-(1 / 60)), (59 / 60), (-(121 / 60))] : Matrix (Fin 4) (Fin 4) ℝ) i j ≤ G i j)
    (hhi : ∀ i j, G i j ≤ (!![(181 / 60), (61 / 60), (1 / 60), (1 / 60); (61 / 60), (181 / 60), (1 / 60), (1 / 60); (1 / 60), (1 / 60), (-(119 / 60)), (61 / 60); (1 / 60), (1 / 60), (61 / 60), (-(119 / 60))] : Matrix (Fin 4) (Fin 4) ℝ) i j) :
    RHLinalg.posIndex hG = 2 ∧ RHInertia.defect hG = 2 := by
  have lo_0_0 : ((179 / 60) : ℝ) ≤ G 0 0 := by
    inertia_entries_using hlo 0 0
  have lo_0_1 : ((59 / 60) : ℝ) ≤ G 0 1 := by
    inertia_entries_using hlo 0 1
  have lo_0_2 : ((-(1 / 60)) : ℝ) ≤ G 0 2 := by
    inertia_entries_using hlo 0 2
  have lo_0_3 : ((-(1 / 60)) : ℝ) ≤ G 0 3 := by
    inertia_entries_using hlo 0 3
  have lo_1_0 : ((59 / 60) : ℝ) ≤ G 1 0 := by
    inertia_entries_using hlo 1 0
  have lo_1_1 : ((179 / 60) : ℝ) ≤ G 1 1 := by
    inertia_entries_using hlo 1 1
  have lo_1_2 : ((-(1 / 60)) : ℝ) ≤ G 1 2 := by
    inertia_entries_using hlo 1 2
  have lo_1_3 : ((-(1 / 60)) : ℝ) ≤ G 1 3 := by
    inertia_entries_using hlo 1 3
  have lo_2_0 : ((-(1 / 60)) : ℝ) ≤ G 2 0 := by
    inertia_entries_using hlo 2 0
  have lo_2_1 : ((-(1 / 60)) : ℝ) ≤ G 2 1 := by
    inertia_entries_using hlo 2 1
  have lo_2_2 : ((-(121 / 60)) : ℝ) ≤ G 2 2 := by
    inertia_entries_using hlo 2 2
  have lo_2_3 : ((59 / 60) : ℝ) ≤ G 2 3 := by
    inertia_entries_using hlo 2 3
  have lo_3_0 : ((-(1 / 60)) : ℝ) ≤ G 3 0 := by
    inertia_entries_using hlo 3 0
  have lo_3_1 : ((-(1 / 60)) : ℝ) ≤ G 3 1 := by
    inertia_entries_using hlo 3 1
  have lo_3_2 : ((59 / 60) : ℝ) ≤ G 3 2 := by
    inertia_entries_using hlo 3 2
  have lo_3_3 : ((-(121 / 60)) : ℝ) ≤ G 3 3 := by
    inertia_entries_using hlo 3 3
  have hi_0_0 : G 0 0 ≤ ((181 / 60) : ℝ) := by
    inertia_entries_using hhi 0 0
  have hi_0_1 : G 0 1 ≤ ((61 / 60) : ℝ) := by
    inertia_entries_using hhi 0 1
  have hi_0_2 : G 0 2 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 0 2
  have hi_0_3 : G 0 3 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 0 3
  have hi_1_0 : G 1 0 ≤ ((61 / 60) : ℝ) := by
    inertia_entries_using hhi 1 0
  have hi_1_1 : G 1 1 ≤ ((181 / 60) : ℝ) := by
    inertia_entries_using hhi 1 1
  have hi_1_2 : G 1 2 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 1 2
  have hi_1_3 : G 1 3 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 1 3
  have hi_2_0 : G 2 0 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 2 0
  have hi_2_1 : G 2 1 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 2 1
  have hi_2_2 : G 2 2 ≤ ((-(119 / 60)) : ℝ) := by
    inertia_entries_using hhi 2 2
  have hi_2_3 : G 2 3 ≤ ((61 / 60) : ℝ) := by
    inertia_entries_using hhi 2 3
  have hi_3_0 : G 3 0 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 3 0
  have hi_3_1 : G 3 1 ≤ ((1 / 60) : ℝ) := by
    inertia_entries_using hhi 3 1
  have hi_3_2 : G 3 2 ≤ ((61 / 60) : ℝ) := by
    inertia_entries_using hhi 3 2
  have hi_3_3 : G 3 3 ≤ ((-(119 / 60)) : ℝ) := by
    inertia_entries_using hhi 3 3
  have hX : ∀ v : Fin 2 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![1, (-(1 / 4)); 0, (3 / 4); 0, 0; 0, 0] : Matrix (Fin 4) (Fin 2) ℝ)ᴴ * G *
        (!![1, (-(1 / 4)); 0, (3 / 4); 0, 0; 0, 0] : Matrix (Fin 4) (Fin 2) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval G (!![3, 1, 0, 0; 1, 3, 0, 0; 0, 0, (-2), 1; 0, 0, 1, (-2)]) (!![1, (-(1 / 4)); 0, (3 / 4); 0, 0; 0, 0]) (!![3, 0; 0, (3 / 2)]) ![1, 1]
      ((1 / 60)) ((3 / 2)) 2
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_2, hi_0_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_3, hi_0_3]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_2, hi_1_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_3, hi_1_3]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_0, hi_2_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_1, hi_2_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_2, hi_2_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_3, hi_2_3]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_0, hi_3_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_1, hi_3_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_2, hi_3_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_3, hi_3_3]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hY : ∀ v : Fin 2 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![0, 0; 0, 0; 1, (1 / 3); 0, (2 / 3)] : Matrix (Fin 4) (Fin 2) ℝ)ᴴ * (-G) *
        (!![0, 0; 0, 0; 1, (1 / 3); 0, (2 / 3)] : Matrix (Fin 4) (Fin 2) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval (-G) (!![(-3), (-1), 0, 0; (-1), (-3), 0, 0; 0, 0, 2, (-1); 0, 0, (-1), 2]) (!![0, 0; 0, 0; 1, (1 / 3); 0, (2 / 3)]) (!![2, 0; 0, (2 / 3)]) ![1, 1]
      ((1 / 60)) ((2 / 3)) 2
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_2, hi_0_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_3, hi_0_3]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_2, hi_1_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_3, hi_1_3]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_0, hi_2_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_1, hi_2_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_2, hi_2_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_3, hi_2_3]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_0, hi_3_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_1, hi_3_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_2, hi_3_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_3_3, hi_3_3]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact RHInertia.inertia_eq_of_witnesses hG _ _ (by norm_num) hX hY

-- inertia_fractional_3: certified inertia of EVERY real symmetric matrix in the rational box
-- lo ≤ G ≤ hi (n = 3, half-width w = 1/100).  Signature (p, q) = (1, 2).
-- Witness bases have unit absolute-sum columns; the compressed midpoint forms are
-- diagonal with margins delta_X = 1/2 > w*S_X = 1/100 and
-- delta_Y = 35/54 > w*S_Y = 1/50.  Sylvester's law (RHLinalg) does the rest.
-- A finite linear-algebra certificate; says nothing about zeta.  conjecture1_proved = False.
set_option maxHeartbeats 1000000 in
theorem inertia_fractional_3 (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsHermitian)
    (hlo : ∀ i j, (!![(49 / 100), (6 / 25), (-(1 / 100)); (6 / 25), (-(403 / 300)), (-(1 / 100)); (-(1 / 100)), (-(1 / 100)), (-(253 / 300))] : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ G i j)
    (hhi : ∀ i j, G i j ≤ (!![(51 / 100), (13 / 50), (1 / 100); (13 / 50), (-(397 / 300)), (1 / 100); (1 / 100), (1 / 100), (-(247 / 300))] : Matrix (Fin 3) (Fin 3) ℝ) i j) :
    RHLinalg.posIndex hG = 1 ∧ RHInertia.defect hG = 2 := by
  have lo_0_0 : ((49 / 100) : ℝ) ≤ G 0 0 := by
    inertia_entries_using hlo 0 0
  have lo_0_1 : ((6 / 25) : ℝ) ≤ G 0 1 := by
    inertia_entries_using hlo 0 1
  have lo_0_2 : ((-(1 / 100)) : ℝ) ≤ G 0 2 := by
    inertia_entries_using hlo 0 2
  have lo_1_0 : ((6 / 25) : ℝ) ≤ G 1 0 := by
    inertia_entries_using hlo 1 0
  have lo_1_1 : ((-(403 / 300)) : ℝ) ≤ G 1 1 := by
    inertia_entries_using hlo 1 1
  have lo_1_2 : ((-(1 / 100)) : ℝ) ≤ G 1 2 := by
    inertia_entries_using hlo 1 2
  have lo_2_0 : ((-(1 / 100)) : ℝ) ≤ G 2 0 := by
    inertia_entries_using hlo 2 0
  have lo_2_1 : ((-(1 / 100)) : ℝ) ≤ G 2 1 := by
    inertia_entries_using hlo 2 1
  have lo_2_2 : ((-(253 / 300)) : ℝ) ≤ G 2 2 := by
    inertia_entries_using hlo 2 2
  have hi_0_0 : G 0 0 ≤ ((51 / 100) : ℝ) := by
    inertia_entries_using hhi 0 0
  have hi_0_1 : G 0 1 ≤ ((13 / 50) : ℝ) := by
    inertia_entries_using hhi 0 1
  have hi_0_2 : G 0 2 ≤ ((1 / 100) : ℝ) := by
    inertia_entries_using hhi 0 2
  have hi_1_0 : G 1 0 ≤ ((13 / 50) : ℝ) := by
    inertia_entries_using hhi 1 0
  have hi_1_1 : G 1 1 ≤ ((-(397 / 300)) : ℝ) := by
    inertia_entries_using hhi 1 1
  have hi_1_2 : G 1 2 ≤ ((1 / 100) : ℝ) := by
    inertia_entries_using hhi 1 2
  have hi_2_0 : G 2 0 ≤ ((1 / 100) : ℝ) := by
    inertia_entries_using hhi 2 0
  have hi_2_1 : G 2 1 ≤ ((1 / 100) : ℝ) := by
    inertia_entries_using hhi 2 1
  have hi_2_2 : G 2 2 ≤ ((-(247 / 300)) : ℝ) := by
    inertia_entries_using hhi 2 2
  have hX : ∀ v : Fin 1 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℝ)ᴴ * G *
        (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval G (!![(1 / 2), (1 / 4), 0; (1 / 4), (-(4 / 3)), 0; 0, 0, (-(5 / 6))]) (!![1; 0; 0]) (!![(1 / 2)]) ![1]
      ((1 / 100)) ((1 / 2)) 1
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_2, hi_0_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_2, hi_1_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_0, hi_2_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_1, hi_2_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_2, hi_2_2]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0)]
  have hY : ∀ v : Fin 2 → ℝ, v ≠ 0 →
      0 < RHLinalg.hermForm ((!![(-(1 / 3)), 0; (2 / 3), 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)ᴴ * (-G) *
        (!![(-(1 / 3)), 0; (2 / 3), 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)) v := by
    refine RHInertia.compress_posDef_of_interval (-G) (!![(-(1 / 2)), (-(1 / 4)), 0; (-(1 / 4)), (4 / 3), 0; 0, 0, (5 / 6)]) (!![(-(1 / 3)), 0; (2 / 3), 0; 0, 1]) (!![(35 / 54), 0; 0, (5 / 6)]) ![1, 1]
      ((1 / 100)) ((35 / 54)) 2
      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)
    · intro i j
      fin_cases i <;> fin_cases j
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_0, hi_0_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_1, hi_0_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_0_2, hi_0_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_0, hi_1_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_1, hi_1_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_1_2, hi_1_2]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_0, hi_2_0]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_1, hi_2_1]
      · inertia_entries
        rw [abs_le]
        constructor <;> linarith only [lo_2_2, hi_2_2]
    · intro k
      fin_cases k <;> inertia_entries_sum <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num
    · intro v
      inertia_entries_sum <;> norm_num <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact RHInertia.inertia_eq_of_witnesses hG _ _ (by norm_num) hX hY

end GramInertia

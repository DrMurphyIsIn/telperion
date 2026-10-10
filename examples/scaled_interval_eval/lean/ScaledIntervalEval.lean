/- telperion 0.1.6 | family ScaledIntervalEval | input-hash cf6b08b75e3236fc
   136 theorems, 77 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import ScaledInterval

namespace ScaledIntervalEval

open ScaledInterval

-- sie_exp_third: scaled_interval_eval at scale S = 10000000000000000000000000000000000000000 (6 nodes).  Every box is recomputed by the kernel (decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.
def sie_exp_third_S : ℤ := 10000000000000000000000000000000000000000
theorem sie_exp_third_hS : (0 : ℤ) < sie_exp_third_S := by decide +kernel
def sie_exp_third_b0 : RI := ⟨2222222222222222222222222222222222222222, 2222222222222222222222222222222222222223⟩
noncomputable def sie_exp_third_v0 : ℝ := ((2 : ℝ) / 9)
theorem sie_exp_third_b0_calc : RI.subset (RI.ofFrac sie_exp_third_S 2 9) sie_exp_third_b0 = true := by decide +kernel
theorem sie_exp_third_b0_mem : RI.Mem sie_exp_third_S sie_exp_third_b0 sie_exp_third_v0 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_third_hS (by norm_num) (by norm_num [sie_exp_third_v0])) sie_exp_third_b0_calc
def sie_exp_third_b1 : RI := ⟨1428571428571428571428571428571428571428, 1428571428571428571428571428571428571429⟩
noncomputable def sie_exp_third_v1 : ℝ := ((1 : ℝ) / 7)
theorem sie_exp_third_b1_calc : RI.subset (RI.ofFrac sie_exp_third_S 1 7) sie_exp_third_b1 = true := by decide +kernel
theorem sie_exp_third_b1_mem : RI.Mem sie_exp_third_S sie_exp_third_b1 sie_exp_third_v1 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_third_hS (by norm_num) (by norm_num [sie_exp_third_v1])) sie_exp_third_b1_calc
def sie_exp_third_b2 : RI := ⟨3333333333333333333333333333333333333333, 3333333333333333333333333333333333333334⟩
noncomputable def sie_exp_third_v2 : ℝ := ((1 : ℝ) / 3)
theorem sie_exp_third_b2_calc : RI.subset (RI.ofFrac sie_exp_third_S 1 3) sie_exp_third_b2 = true := by decide +kernel
theorem sie_exp_third_b2_mem : RI.Mem sie_exp_third_S sie_exp_third_b2 sie_exp_third_v2 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_third_hS (by norm_num) (by norm_num [sie_exp_third_v2])) sie_exp_third_b2_calc
def sie_exp_third_b3 : RI := ⟨13956124250860895286281253196025868375962, 13956124250860895286281253196025868376006⟩
theorem sie_exp_third_b3_small : RI.expSmallOK sie_exp_third_S sie_exp_third_b2 0 = true := by decide +kernel
theorem sie_exp_third_b3_rem : RI.expRemOK sie_exp_third_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_third_v3 : ℝ := Real.exp sie_exp_third_v2
theorem sie_exp_third_b3_calc : RI.subset (RI.expR sie_exp_third_S sie_exp_third_b2 0 34 1) sie_exp_third_b3 = true := by decide +kernel
theorem sie_exp_third_b3_mem : RI.Mem sie_exp_third_S sie_exp_third_b3 sie_exp_third_v3 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_third_hS sie_exp_third_b2_mem sie_exp_third_b3_small sie_exp_third_b3_rem) sie_exp_third_b3_calc
def sie_exp_third_b4 : RI := ⟨1993732035837270755183036170860838339422, 1993732035837270755183036170860838339431⟩
noncomputable def sie_exp_third_v4 : ℝ := sie_exp_third_v1 * sie_exp_third_v3
theorem sie_exp_third_b4_calc : RI.subset (RI.mul sie_exp_third_S sie_exp_third_b1 sie_exp_third_b3) sie_exp_third_b4 = true := by decide +kernel
theorem sie_exp_third_b4_mem : RI.Mem sie_exp_third_S sie_exp_third_b4 sie_exp_third_v4 :=
  RI.mem_of_subset (RI.mem_mul sie_exp_third_hS sie_exp_third_b1_mem sie_exp_third_b3_mem) sie_exp_third_b4_calc
def sie_exp_third_b5 : RI := ⟨4215954258059492977405258393083060561644, 4215954258059492977405258393083060561654⟩
noncomputable def sie_exp_third_v5 : ℝ := sie_exp_third_v0 + sie_exp_third_v4
theorem sie_exp_third_b5_calc : RI.subset (RI.add sie_exp_third_b0 sie_exp_third_b4) sie_exp_third_b5 = true := by decide +kernel
theorem sie_exp_third_b5_mem : RI.Mem sie_exp_third_S sie_exp_third_b5 sie_exp_third_v5 :=
  RI.mem_of_subset (RI.mem_add sie_exp_third_b0_mem sie_exp_third_b4_mem) sie_exp_third_b5_calc
theorem sie_exp_third_lo_calc : RI.lowerOK sie_exp_third_S sie_exp_third_b5 1053988564514873244351314598270765140411 2500000000000000000000000000000000000000 = true := by decide +kernel
theorem sie_exp_third_hi_calc : RI.upperOK sie_exp_third_S sie_exp_third_b5 2107977129029746488702629196541530280827 5000000000000000000000000000000000000000 = true := by decide +kernel
/-- `sie_exp_third`: the kernel-checked enclosure (exact-evaluated pre-emission). -/
theorem sie_exp_third : ((1053988564514873244351314598270765140411 : ℝ) / 2500000000000000000000000000000000000000) ≤ (((2 : ℝ) / 9) + (((1 : ℝ) / 7) * (Real.exp ((1 : ℝ) / 3)))) ∧ (((2 : ℝ) / 9) + (((1 : ℝ) / 7) * (Real.exp ((1 : ℝ) / 3)))) ≤ ((2107977129029746488702629196541530280827 : ℝ) / 5000000000000000000000000000000000000000) := by
  have h : RI.Mem sie_exp_third_S sie_exp_third_b5 (((2 : ℝ) / 9) + (((1 : ℝ) / 7) * (Real.exp ((1 : ℝ) / 3)))) := sie_exp_third_b5_mem
  exact ⟨RI.le_of_mem sie_exp_third_hS h (by norm_num) (by norm_num) sie_exp_third_lo_calc,
    RI.ge_of_mem sie_exp_third_hS h (by norm_num) (by norm_num) sie_exp_third_hi_calc⟩
example : ((1053988564514873244351314598270765140411 : ℝ) / 2500000000000000000000000000000000000000) ≤ (((2 : ℝ) / 9) + (((1 : ℝ) / 7) * (Real.exp ((1 : ℝ) / 3)))) ∧ (((2 : ℝ) / 9) + (((1 : ℝ) / 7) * (Real.exp ((1 : ℝ) / 3)))) ≤ ((2107977129029746488702629196541530280827 : ℝ) / 5000000000000000000000000000000000000000) := sie_exp_third

-- sie_cubic: scaled_interval_eval at scale S = 10000000000000000000000000000000000000000 (8 nodes).  Every box is recomputed by the kernel (decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.
def sie_cubic_S : ℤ := 10000000000000000000000000000000000000000
theorem sie_cubic_hS : (0 : ℤ) < sie_cubic_S := by decide +kernel
def sie_cubic_b0 : RI := ⟨3333333333333333333333333333333333333333, 3333333333333333333333333333333333333334⟩
noncomputable def sie_cubic_v0 : ℝ := ((1 : ℝ) / 3)
theorem sie_cubic_b0_calc : RI.subset (RI.ofFrac sie_cubic_S 1 3) sie_cubic_b0 = true := by decide +kernel
theorem sie_cubic_b0_mem : RI.Mem sie_cubic_S sie_cubic_b0 sie_cubic_v0 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_cubic_hS (by norm_num) (by norm_num [sie_cubic_v0])) sie_cubic_b0_calc
def sie_cubic_b1 : RI := ⟨3333333333333333333333333333333333333333, 5000000000000000000000000000000000000001⟩
noncomputable def sie_cubic_v1 (x : ℝ) : ℝ := x
theorem sie_cubic_b1_calc : RI.subset (RI.ofRange sie_cubic_S 1 3 1 2) sie_cubic_b1 = true := by decide +kernel
theorem sie_cubic_b1_mem (x : ℝ) (h_x_lo : ((1 : ℝ) / 3) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_cubic_S sie_cubic_b1 (sie_cubic_v1 x) :=
  RI.mem_of_subset (RI.mem_ofRange sie_cubic_hS (by norm_num) (by norm_num) (by norm_num) (by norm_num) h_x_lo h_x_hi) sie_cubic_b1_calc
def sie_cubic_b2 : RI := ⟨1111111111111111111111111111111111111110, 2500000000000000000000000000000000000002⟩
noncomputable def sie_cubic_v2 (x : ℝ) : ℝ := (sie_cubic_v1 x) * (sie_cubic_v1 x)
theorem sie_cubic_b2_calc : RI.subset (RI.mul sie_cubic_S sie_cubic_b1 sie_cubic_b1) sie_cubic_b2 = true := by decide +kernel
theorem sie_cubic_b2_mem (x : ℝ) (h_x_lo : ((1 : ℝ) / 3) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_cubic_S sie_cubic_b2 (sie_cubic_v2 x) :=
  RI.mem_of_subset (RI.mem_mul sie_cubic_hS (sie_cubic_b1_mem x h_x_lo h_x_hi) (sie_cubic_b1_mem x h_x_lo h_x_hi)) sie_cubic_b2_calc
def sie_cubic_b3 : RI := ⟨370370370370370370370370370370370370369, 1250000000000000000000000000000000000002⟩
noncomputable def sie_cubic_v3 (x : ℝ) : ℝ := (sie_cubic_v2 x) * (sie_cubic_v1 x)
theorem sie_cubic_b3_calc : RI.subset (RI.mul sie_cubic_S sie_cubic_b2 sie_cubic_b1) sie_cubic_b3 = true := by decide +kernel
theorem sie_cubic_b3_mem (x : ℝ) (h_x_lo : ((1 : ℝ) / 3) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_cubic_S sie_cubic_b3 (sie_cubic_v3 x) :=
  RI.mem_of_subset (RI.mem_mul sie_cubic_hS (sie_cubic_b2_mem x h_x_lo h_x_hi) (sie_cubic_b1_mem x h_x_lo h_x_hi)) sie_cubic_b3_calc
def sie_cubic_b4 : RI := ⟨3703703703703703703703703703703703703702, 4583333333333333333333333333333333333336⟩
noncomputable def sie_cubic_v4 (x : ℝ) : ℝ := sie_cubic_v0 + (sie_cubic_v3 x)
theorem sie_cubic_b4_calc : RI.subset (RI.add sie_cubic_b0 sie_cubic_b3) sie_cubic_b4 = true := by decide +kernel
theorem sie_cubic_b4_mem (x : ℝ) (h_x_lo : ((1 : ℝ) / 3) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_cubic_S sie_cubic_b4 (sie_cubic_v4 x) :=
  RI.mem_of_subset (RI.mem_add sie_cubic_b0_mem (sie_cubic_b3_mem x h_x_lo h_x_hi)) sie_cubic_b4_calc
def sie_cubic_b5 : RI := ⟨20000000000000000000000000000000000000000, 20000000000000000000000000000000000000001⟩
noncomputable def sie_cubic_v5 : ℝ := (2 : ℝ)
theorem sie_cubic_b5_calc : RI.subset (RI.ofFrac sie_cubic_S 2 1) sie_cubic_b5 = true := by decide +kernel
theorem sie_cubic_b5_mem : RI.Mem sie_cubic_S sie_cubic_b5 sie_cubic_v5 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_cubic_hS (by norm_num) (by norm_num [sie_cubic_v5])) sie_cubic_b5_calc
def sie_cubic_b6 : RI := ⟨6666666666666666666666666666666666666666, 10000000000000000000000000000000000000003⟩
noncomputable def sie_cubic_v6 (x : ℝ) : ℝ := sie_cubic_v5 * (sie_cubic_v1 x)
theorem sie_cubic_b6_calc : RI.subset (RI.mul sie_cubic_S sie_cubic_b5 sie_cubic_b1) sie_cubic_b6 = true := by decide +kernel
theorem sie_cubic_b6_mem (x : ℝ) (h_x_lo : ((1 : ℝ) / 3) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_cubic_S sie_cubic_b6 (sie_cubic_v6 x) :=
  RI.mem_of_subset (RI.mem_mul sie_cubic_hS sie_cubic_b5_mem (sie_cubic_b1_mem x h_x_lo h_x_hi)) sie_cubic_b6_calc
def sie_cubic_b7 : RI := ⟨(-6296296296296296296296296296296296296301), (-2083333333333333333333333333333333333330)⟩
noncomputable def sie_cubic_v7 (x : ℝ) : ℝ := (sie_cubic_v4 x) - (sie_cubic_v6 x)
theorem sie_cubic_b7_calc : RI.subset (RI.sub sie_cubic_b4 sie_cubic_b6) sie_cubic_b7 = true := by decide +kernel
theorem sie_cubic_b7_mem (x : ℝ) (h_x_lo : ((1 : ℝ) / 3) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_cubic_S sie_cubic_b7 (sie_cubic_v7 x) :=
  RI.mem_of_subset (RI.mem_sub (sie_cubic_b4_mem x h_x_lo h_x_hi) (sie_cubic_b6_mem x h_x_lo h_x_hi)) sie_cubic_b7_calc
theorem sie_cubic_lo_calc : RI.lowerOK sie_cubic_S sie_cubic_b7 (-6296296296296296296296296296296296296301) 10000000000000000000000000000000000000000 = true := by decide +kernel
theorem sie_cubic_hi_calc : RI.upperOK sie_cubic_S sie_cubic_b7 (-208333333333333333333333333333333333333) 1000000000000000000000000000000000000000 = true := by decide +kernel
/-- `sie_cubic`: the kernel-checked enclosure (exact-evaluated pre-emission). -/
theorem sie_cubic : ∀ x : ℝ, ((1 : ℝ) / 3) ≤ x → x ≤ ((1 : ℝ) / 2) → ((-6296296296296296296296296296296296296301 : ℝ) / 10000000000000000000000000000000000000000) ≤ ((((1 : ℝ) / 3) + ((x * x) * x)) - ((2 : ℝ) * x)) ∧ ((((1 : ℝ) / 3) + ((x * x) * x)) - ((2 : ℝ) * x)) ≤ ((-208333333333333333333333333333333333333 : ℝ) / 1000000000000000000000000000000000000000) := by
  intro x h_x_lo h_x_hi
  have h : RI.Mem sie_cubic_S sie_cubic_b7 ((((1 : ℝ) / 3) + ((x * x) * x)) - ((2 : ℝ) * x)) := (sie_cubic_b7_mem x h_x_lo h_x_hi)
  exact ⟨RI.le_of_mem sie_cubic_hS h (by norm_num) (by norm_num) sie_cubic_lo_calc,
    RI.ge_of_mem sie_cubic_hS h (by norm_num) (by norm_num) sie_cubic_hi_calc⟩
example : ∀ x : ℝ, ((1 : ℝ) / 3) ≤ x → x ≤ ((1 : ℝ) / 2) → ((-6296296296296296296296296296296296296301 : ℝ) / 10000000000000000000000000000000000000000) ≤ ((((1 : ℝ) / 3) + ((x * x) * x)) - ((2 : ℝ) * x)) ∧ ((((1 : ℝ) / 3) + ((x * x) * x)) - ((2 : ℝ) * x)) ≤ ((-208333333333333333333333333333333333333 : ℝ) / 1000000000000000000000000000000000000000) := sie_cubic

-- sie_sinh_reduced: scaled_interval_eval at scale S = 10000000000000000000000000000000000000000 (6 nodes).  Every box is recomputed by the kernel (decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.
def sie_sinh_reduced_S : ℤ := 10000000000000000000000000000000000000000
theorem sie_sinh_reduced_hS : (0 : ℤ) < sie_sinh_reduced_S := by decide +kernel
def sie_sinh_reduced_b0 : RI := ⟨(-25000000000000000000000000000000000000000), (-24999999999999999999999999999999999999999)⟩
noncomputable def sie_sinh_reduced_v0 : ℝ := ((-5 : ℝ) / 2)
theorem sie_sinh_reduced_b0_calc : RI.subset (RI.ofFrac sie_sinh_reduced_S (-5) 2) sie_sinh_reduced_b0 = true := by decide +kernel
theorem sie_sinh_reduced_b0_mem : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b0 sie_sinh_reduced_v0 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_sinh_reduced_hS (by norm_num) (by norm_num [sie_sinh_reduced_v0])) sie_sinh_reduced_b0_calc
def sie_sinh_reduced_b1 : RI := ⟨820849986238987951695286744671598078365, 820849986238987951695286744671598078395⟩
theorem sie_sinh_reduced_b1_small : RI.expSmallOK sie_sinh_reduced_S sie_sinh_reduced_b0 2 = true := by decide +kernel
theorem sie_sinh_reduced_b1_rem : RI.expRemOK sie_sinh_reduced_S 34 1 = true := by decide +kernel
noncomputable def sie_sinh_reduced_v1 : ℝ := Real.exp sie_sinh_reduced_v0
theorem sie_sinh_reduced_b1_calc : RI.subset (RI.expR sie_sinh_reduced_S sie_sinh_reduced_b0 2 34 1) sie_sinh_reduced_b1 = true := by decide +kernel
theorem sie_sinh_reduced_b1_mem : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b1 sie_sinh_reduced_v1 :=
  RI.mem_of_subset (RI.mem_expR sie_sinh_reduced_hS sie_sinh_reduced_b0_mem sie_sinh_reduced_b1_small sie_sinh_reduced_b1_rem) sie_sinh_reduced_b1_calc
def sie_sinh_reduced_b2 : RI := ⟨(-820849986238987951695286744671598078395), (-820849986238987951695286744671598078365)⟩
noncomputable def sie_sinh_reduced_v2 : ℝ := -sie_sinh_reduced_v1
theorem sie_sinh_reduced_b2_calc : RI.subset (RI.neg sie_sinh_reduced_b1) sie_sinh_reduced_b2 = true := by decide +kernel
theorem sie_sinh_reduced_b2_mem : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b2 sie_sinh_reduced_v2 :=
  RI.mem_of_subset (RI.mem_neg sie_sinh_reduced_b1_mem) sie_sinh_reduced_b2_calc
def sie_sinh_reduced_b3 : RI := ⟨25000000000000000000000000000000000000000, 25000000000000000000000000000000000000001⟩
noncomputable def sie_sinh_reduced_v3 : ℝ := ((5 : ℝ) / 2)
theorem sie_sinh_reduced_b3_calc : RI.subset (RI.ofFrac sie_sinh_reduced_S 5 2) sie_sinh_reduced_b3 = true := by decide +kernel
theorem sie_sinh_reduced_b3_mem : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b3 sie_sinh_reduced_v3 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_sinh_reduced_hS (by norm_num) (by norm_num [sie_sinh_reduced_v3])) sie_sinh_reduced_b3_calc
def sie_sinh_reduced_b4 : RI := ⟨121824939607034734380701759511679661831336, 121824939607034734380701759511679661832545⟩
theorem sie_sinh_reduced_b4_small : RI.expSmallOK sie_sinh_reduced_S sie_sinh_reduced_b3 2 = true := by decide +kernel
theorem sie_sinh_reduced_b4_rem : RI.expRemOK sie_sinh_reduced_S 34 1 = true := by decide +kernel
noncomputable def sie_sinh_reduced_v4 : ℝ := Real.exp sie_sinh_reduced_v3
theorem sie_sinh_reduced_b4_calc : RI.subset (RI.expR sie_sinh_reduced_S sie_sinh_reduced_b3 2 34 1) sie_sinh_reduced_b4 = true := by decide +kernel
theorem sie_sinh_reduced_b4_mem : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b4 sie_sinh_reduced_v4 :=
  RI.mem_of_subset (RI.mem_expR sie_sinh_reduced_hS sie_sinh_reduced_b3_mem sie_sinh_reduced_b4_small sie_sinh_reduced_b4_rem) sie_sinh_reduced_b4_calc
def sie_sinh_reduced_b5 : RI := ⟨121004089620795746429006472767008063752941, 121004089620795746429006472767008063754180⟩
noncomputable def sie_sinh_reduced_v5 : ℝ := sie_sinh_reduced_v2 + sie_sinh_reduced_v4
theorem sie_sinh_reduced_b5_calc : RI.subset (RI.add sie_sinh_reduced_b2 sie_sinh_reduced_b4) sie_sinh_reduced_b5 = true := by decide +kernel
theorem sie_sinh_reduced_b5_mem : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b5 sie_sinh_reduced_v5 :=
  RI.mem_of_subset (RI.mem_add sie_sinh_reduced_b2_mem sie_sinh_reduced_b4_mem) sie_sinh_reduced_b5_calc
theorem sie_sinh_reduced_lo_calc : RI.lowerOK sie_sinh_reduced_S sie_sinh_reduced_b5 121004089620795746429006472767008063752941 10000000000000000000000000000000000000000 = true := by decide +kernel
theorem sie_sinh_reduced_hi_calc : RI.upperOK sie_sinh_reduced_S sie_sinh_reduced_b5 6050204481039787321450323638350403187709 500000000000000000000000000000000000000 = true := by decide +kernel
/-- `sie_sinh_reduced`: the kernel-checked enclosure (exact-evaluated pre-emission). -/
theorem sie_sinh_reduced : ((121004089620795746429006472767008063752941 : ℝ) / 10000000000000000000000000000000000000000) ≤ ((-(Real.exp ((-5 : ℝ) / 2))) + (Real.exp ((5 : ℝ) / 2))) ∧ ((-(Real.exp ((-5 : ℝ) / 2))) + (Real.exp ((5 : ℝ) / 2))) ≤ ((6050204481039787321450323638350403187709 : ℝ) / 500000000000000000000000000000000000000) := by
  have h : RI.Mem sie_sinh_reduced_S sie_sinh_reduced_b5 ((-(Real.exp ((-5 : ℝ) / 2))) + (Real.exp ((5 : ℝ) / 2))) := sie_sinh_reduced_b5_mem
  exact ⟨RI.le_of_mem sie_sinh_reduced_hS h (by norm_num) (by norm_num) sie_sinh_reduced_lo_calc,
    RI.ge_of_mem sie_sinh_reduced_hS h (by norm_num) (by norm_num) sie_sinh_reduced_hi_calc⟩
example : ((121004089620795746429006472767008063752941 : ℝ) / 10000000000000000000000000000000000000000) ≤ ((-(Real.exp ((-5 : ℝ) / 2))) + (Real.exp ((5 : ℝ) / 2))) ∧ ((-(Real.exp ((-5 : ℝ) / 2))) + (Real.exp ((5 : ℝ) / 2))) ≤ ((6050204481039787321450323638350403187709 : ℝ) / 500000000000000000000000000000000000000) := sie_sinh_reduced

-- sie_exp_series: scaled_interval_eval at scale S = 10000000000000000000000000000000000000000 (31 nodes).  Every box is recomputed by the kernel (decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.
def sie_exp_series_S : ℤ := 10000000000000000000000000000000000000000
theorem sie_exp_series_hS : (0 : ℤ) < sie_exp_series_S := by decide +kernel
def sie_exp_series_b0 : RI := ⟨10000000000000000000000000000000000000000, 10000000000000000000000000000000000000001⟩
noncomputable def sie_exp_series_v0 : ℝ := (1 : ℝ)
theorem sie_exp_series_b0_calc : RI.subset (RI.ofFrac sie_exp_series_S 1 1) sie_exp_series_b0 = true := by decide +kernel
theorem sie_exp_series_b0_mem : RI.Mem sie_exp_series_S sie_exp_series_b0 sie_exp_series_v0 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v0])) sie_exp_series_b0_calc
def sie_exp_series_b1 : RI := ⟨0, 5000000000000000000000000000000000000001⟩
noncomputable def sie_exp_series_v1 (x : ℝ) : ℝ := x
theorem sie_exp_series_b1_calc : RI.subset (RI.ofRange sie_exp_series_S 0 1 1 2) sie_exp_series_b1 = true := by decide +kernel
theorem sie_exp_series_b1_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b1 (sie_exp_series_v1 x) :=
  RI.mem_of_subset (RI.mem_ofRange sie_exp_series_hS (by norm_num) (by norm_num) (by norm_num) (by norm_num) h_x_lo h_x_hi) sie_exp_series_b1_calc
def sie_exp_series_b2 : RI := ⟨(-2500000000000000000000000000000000000000), (-2499999999999999999999999999999999999999)⟩
noncomputable def sie_exp_series_v2 : ℝ := ((-1 : ℝ) / 4)
theorem sie_exp_series_b2_calc : RI.subset (RI.ofFrac sie_exp_series_S (-1) 4) sie_exp_series_b2 = true := by decide +kernel
theorem sie_exp_series_b2_mem : RI.Mem sie_exp_series_S sie_exp_series_b2 sie_exp_series_v2 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v2])) sie_exp_series_b2_calc
def sie_exp_series_b3 : RI := ⟨7788007830714048682451702669783206472946, 7788007830714048682451702669783206472998⟩
theorem sie_exp_series_b3_small : RI.expSmallOK sie_exp_series_S sie_exp_series_b2 0 = true := by decide +kernel
theorem sie_exp_series_b3_rem : RI.expRemOK sie_exp_series_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_series_v3 : ℝ := Real.exp sie_exp_series_v2
theorem sie_exp_series_b3_calc : RI.subset (RI.expR sie_exp_series_S sie_exp_series_b2 0 34 1) sie_exp_series_b3 = true := by decide +kernel
theorem sie_exp_series_b3_mem : RI.Mem sie_exp_series_S sie_exp_series_b3 sie_exp_series_v3 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_series_hS sie_exp_series_b2_mem sie_exp_series_b3_small sie_exp_series_b3_rem) sie_exp_series_b3_calc
def sie_exp_series_b4 : RI := ⟨0, 3894003915357024341225851334891603236500⟩
noncomputable def sie_exp_series_v4 (x : ℝ) : ℝ := (sie_exp_series_v1 x) * sie_exp_series_v3
theorem sie_exp_series_b4_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b1 sie_exp_series_b3) sie_exp_series_b4 = true := by decide +kernel
theorem sie_exp_series_b4_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b4 (sie_exp_series_v4 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b1_mem x h_x_lo h_x_hi) sie_exp_series_b3_mem) sie_exp_series_b4_calc
def sie_exp_series_b5 : RI := ⟨10000000000000000000000000000000000000000, 13894003915357024341225851334891603236501⟩
noncomputable def sie_exp_series_v5 (x : ℝ) : ℝ := sie_exp_series_v0 + (sie_exp_series_v4 x)
theorem sie_exp_series_b5_calc : RI.subset (RI.add sie_exp_series_b0 sie_exp_series_b4) sie_exp_series_b5 = true := by decide +kernel
theorem sie_exp_series_b5_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b5 (sie_exp_series_v5 x) :=
  RI.mem_of_subset (RI.mem_add sie_exp_series_b0_mem (sie_exp_series_b4_mem x h_x_lo h_x_hi)) sie_exp_series_b5_calc
def sie_exp_series_b6 : RI := ⟨0, 2500000000000000000000000000000000000002⟩
noncomputable def sie_exp_series_v6 (x : ℝ) : ℝ := (sie_exp_series_v1 x) * (sie_exp_series_v1 x)
theorem sie_exp_series_b6_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b1 sie_exp_series_b1) sie_exp_series_b6 = true := by decide +kernel
theorem sie_exp_series_b6_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b6 (sie_exp_series_v6 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b1_mem x h_x_lo h_x_hi) (sie_exp_series_b1_mem x h_x_lo h_x_hi)) sie_exp_series_b6_calc
def sie_exp_series_b7 : RI := ⟨(-5000000000000000000000000000000000000000), (-4999999999999999999999999999999999999999)⟩
noncomputable def sie_exp_series_v7 : ℝ := ((-1 : ℝ) / 2)
theorem sie_exp_series_b7_calc : RI.subset (RI.ofFrac sie_exp_series_S (-1) 2) sie_exp_series_b7 = true := by decide +kernel
theorem sie_exp_series_b7_mem : RI.Mem sie_exp_series_S sie_exp_series_b7 sie_exp_series_v7 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v7])) sie_exp_series_b7_calc
def sie_exp_series_b8 : RI := ⟨6065306597126334236037995349911804534397, 6065306597126334236037995349911804534448⟩
theorem sie_exp_series_b8_small : RI.expSmallOK sie_exp_series_S sie_exp_series_b7 0 = true := by decide +kernel
theorem sie_exp_series_b8_rem : RI.expRemOK sie_exp_series_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_series_v8 : ℝ := Real.exp sie_exp_series_v7
theorem sie_exp_series_b8_calc : RI.subset (RI.expR sie_exp_series_S sie_exp_series_b7 0 34 1) sie_exp_series_b8 = true := by decide +kernel
theorem sie_exp_series_b8_mem : RI.Mem sie_exp_series_S sie_exp_series_b8 sie_exp_series_v8 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_series_hS sie_exp_series_b7_mem sie_exp_series_b8_small sie_exp_series_b8_rem) sie_exp_series_b8_calc
def sie_exp_series_b9 : RI := ⟨0, 1516326649281583559009498837477951133614⟩
noncomputable def sie_exp_series_v9 (x : ℝ) : ℝ := (sie_exp_series_v6 x) * sie_exp_series_v8
theorem sie_exp_series_b9_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b6 sie_exp_series_b8) sie_exp_series_b9 = true := by decide +kernel
theorem sie_exp_series_b9_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b9 (sie_exp_series_v9 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b6_mem x h_x_lo h_x_hi) sie_exp_series_b8_mem) sie_exp_series_b9_calc
def sie_exp_series_b10 : RI := ⟨10000000000000000000000000000000000000000, 15410330564638607900235350172369554370115⟩
noncomputable def sie_exp_series_v10 (x : ℝ) : ℝ := (sie_exp_series_v5 x) + (sie_exp_series_v9 x)
theorem sie_exp_series_b10_calc : RI.subset (RI.add sie_exp_series_b5 sie_exp_series_b9) sie_exp_series_b10 = true := by decide +kernel
theorem sie_exp_series_b10_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b10 (sie_exp_series_v10 x) :=
  RI.mem_of_subset (RI.mem_add (sie_exp_series_b5_mem x h_x_lo h_x_hi) (sie_exp_series_b9_mem x h_x_lo h_x_hi)) sie_exp_series_b10_calc
def sie_exp_series_b11 : RI := ⟨0, 1250000000000000000000000000000000000002⟩
noncomputable def sie_exp_series_v11 (x : ℝ) : ℝ := (sie_exp_series_v6 x) * (sie_exp_series_v1 x)
theorem sie_exp_series_b11_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b6 sie_exp_series_b1) sie_exp_series_b11 = true := by decide +kernel
theorem sie_exp_series_b11_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b11 (sie_exp_series_v11 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b6_mem x h_x_lo h_x_hi) (sie_exp_series_b1_mem x h_x_lo h_x_hi)) sie_exp_series_b11_calc
def sie_exp_series_b12 : RI := ⟨(-7500000000000000000000000000000000000000), (-7499999999999999999999999999999999999999)⟩
noncomputable def sie_exp_series_v12 : ℝ := ((-3 : ℝ) / 4)
theorem sie_exp_series_b12_calc : RI.subset (RI.ofFrac sie_exp_series_S (-3) 4) sie_exp_series_b12 = true := by decide +kernel
theorem sie_exp_series_b12_mem : RI.Mem sie_exp_series_S sie_exp_series_b12 sie_exp_series_v12 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v12])) sie_exp_series_b12_calc
def sie_exp_series_b13 : RI := ⟨4723665527410147071380465509432679129678, 4723665527410147071380465509432679129729⟩
theorem sie_exp_series_b13_small : RI.expSmallOK sie_exp_series_S sie_exp_series_b12 0 = true := by decide +kernel
theorem sie_exp_series_b13_rem : RI.expRemOK sie_exp_series_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_series_v13 : ℝ := Real.exp sie_exp_series_v12
theorem sie_exp_series_b13_calc : RI.subset (RI.expR sie_exp_series_S sie_exp_series_b12 0 34 1) sie_exp_series_b13 = true := by decide +kernel
theorem sie_exp_series_b13_mem : RI.Mem sie_exp_series_S sie_exp_series_b13 sie_exp_series_v13 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_series_hS sie_exp_series_b12_mem sie_exp_series_b13_small sie_exp_series_b13_rem) sie_exp_series_b13_calc
def sie_exp_series_b14 : RI := ⟨0, 590458190926268383922558188679084891218⟩
noncomputable def sie_exp_series_v14 (x : ℝ) : ℝ := (sie_exp_series_v11 x) * sie_exp_series_v13
theorem sie_exp_series_b14_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b11 sie_exp_series_b13) sie_exp_series_b14 = true := by decide +kernel
theorem sie_exp_series_b14_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b14 (sie_exp_series_v14 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b11_mem x h_x_lo h_x_hi) sie_exp_series_b13_mem) sie_exp_series_b14_calc
def sie_exp_series_b15 : RI := ⟨10000000000000000000000000000000000000000, 16000788755564876284157908361048639261333⟩
noncomputable def sie_exp_series_v15 (x : ℝ) : ℝ := (sie_exp_series_v10 x) + (sie_exp_series_v14 x)
theorem sie_exp_series_b15_calc : RI.subset (RI.add sie_exp_series_b10 sie_exp_series_b14) sie_exp_series_b15 = true := by decide +kernel
theorem sie_exp_series_b15_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b15 (sie_exp_series_v15 x) :=
  RI.mem_of_subset (RI.mem_add (sie_exp_series_b10_mem x h_x_lo h_x_hi) (sie_exp_series_b14_mem x h_x_lo h_x_hi)) sie_exp_series_b15_calc
def sie_exp_series_b16 : RI := ⟨0, 625000000000000000000000000000000000002⟩
noncomputable def sie_exp_series_v16 (x : ℝ) : ℝ := (sie_exp_series_v11 x) * (sie_exp_series_v1 x)
theorem sie_exp_series_b16_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b11 sie_exp_series_b1) sie_exp_series_b16 = true := by decide +kernel
theorem sie_exp_series_b16_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b16 (sie_exp_series_v16 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b11_mem x h_x_lo h_x_hi) (sie_exp_series_b1_mem x h_x_lo h_x_hi)) sie_exp_series_b16_calc
def sie_exp_series_b17 : RI := ⟨(-10000000000000000000000000000000000000000), (-9999999999999999999999999999999999999999)⟩
noncomputable def sie_exp_series_v17 : ℝ := (-1 : ℝ)
theorem sie_exp_series_b17_calc : RI.subset (RI.ofFrac sie_exp_series_S (-1) 1) sie_exp_series_b17 = true := by decide +kernel
theorem sie_exp_series_b17_mem : RI.Mem sie_exp_series_S sie_exp_series_b17 sie_exp_series_v17 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v17])) sie_exp_series_b17_calc
def sie_exp_series_b18 : RI := ⟨3678794411714423215955237701614608674436, 3678794411714423215955237701614608674489⟩
theorem sie_exp_series_b18_small : RI.expSmallOK sie_exp_series_S sie_exp_series_b17 0 = true := by decide +kernel
theorem sie_exp_series_b18_rem : RI.expRemOK sie_exp_series_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_series_v18 : ℝ := Real.exp sie_exp_series_v17
theorem sie_exp_series_b18_calc : RI.subset (RI.expR sie_exp_series_S sie_exp_series_b17 0 34 1) sie_exp_series_b18 = true := by decide +kernel
theorem sie_exp_series_b18_mem : RI.Mem sie_exp_series_S sie_exp_series_b18 sie_exp_series_v18 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_series_hS sie_exp_series_b17_mem sie_exp_series_b18_small sie_exp_series_b18_rem) sie_exp_series_b18_calc
def sie_exp_series_b19 : RI := ⟨0, 229924650732151450997202356350913042157⟩
noncomputable def sie_exp_series_v19 (x : ℝ) : ℝ := (sie_exp_series_v16 x) * sie_exp_series_v18
theorem sie_exp_series_b19_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b16 sie_exp_series_b18) sie_exp_series_b19 = true := by decide +kernel
theorem sie_exp_series_b19_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b19 (sie_exp_series_v19 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b16_mem x h_x_lo h_x_hi) sie_exp_series_b18_mem) sie_exp_series_b19_calc
def sie_exp_series_b20 : RI := ⟨10000000000000000000000000000000000000000, 16230713406297027735155110717399552303490⟩
noncomputable def sie_exp_series_v20 (x : ℝ) : ℝ := (sie_exp_series_v15 x) + (sie_exp_series_v19 x)
theorem sie_exp_series_b20_calc : RI.subset (RI.add sie_exp_series_b15 sie_exp_series_b19) sie_exp_series_b20 = true := by decide +kernel
theorem sie_exp_series_b20_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b20 (sie_exp_series_v20 x) :=
  RI.mem_of_subset (RI.mem_add (sie_exp_series_b15_mem x h_x_lo h_x_hi) (sie_exp_series_b19_mem x h_x_lo h_x_hi)) sie_exp_series_b20_calc
def sie_exp_series_b21 : RI := ⟨0, 312500000000000000000000000000000000002⟩
noncomputable def sie_exp_series_v21 (x : ℝ) : ℝ := (sie_exp_series_v16 x) * (sie_exp_series_v1 x)
theorem sie_exp_series_b21_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b16 sie_exp_series_b1) sie_exp_series_b21 = true := by decide +kernel
theorem sie_exp_series_b21_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b21 (sie_exp_series_v21 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b16_mem x h_x_lo h_x_hi) (sie_exp_series_b1_mem x h_x_lo h_x_hi)) sie_exp_series_b21_calc
def sie_exp_series_b22 : RI := ⟨(-12500000000000000000000000000000000000000), (-12499999999999999999999999999999999999999)⟩
noncomputable def sie_exp_series_v22 : ℝ := ((-5 : ℝ) / 4)
theorem sie_exp_series_b22_calc : RI.subset (RI.ofFrac sie_exp_series_S (-5) 4) sie_exp_series_b22 = true := by decide +kernel
theorem sie_exp_series_b22_mem : RI.Mem sie_exp_series_S sie_exp_series_b22 sie_exp_series_v22 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v22])) sie_exp_series_b22_calc
def sie_exp_series_b23 : RI := ⟨2865047968601901003248854266478376027909, 2865047968601901003248854266478376027960⟩
theorem sie_exp_series_b23_small : RI.expSmallOK sie_exp_series_S sie_exp_series_b22 1 = true := by decide +kernel
theorem sie_exp_series_b23_rem : RI.expRemOK sie_exp_series_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_series_v23 : ℝ := Real.exp sie_exp_series_v22
theorem sie_exp_series_b23_calc : RI.subset (RI.expR sie_exp_series_S sie_exp_series_b22 1 34 1) sie_exp_series_b23 = true := by decide +kernel
theorem sie_exp_series_b23_mem : RI.Mem sie_exp_series_S sie_exp_series_b23 sie_exp_series_v23 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_series_hS sie_exp_series_b22_mem sie_exp_series_b23_small sie_exp_series_b23_rem) sie_exp_series_b23_calc
def sie_exp_series_b24 : RI := ⟨0, 89532749018809406351526695827449250875⟩
noncomputable def sie_exp_series_v24 (x : ℝ) : ℝ := (sie_exp_series_v21 x) * sie_exp_series_v23
theorem sie_exp_series_b24_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b21 sie_exp_series_b23) sie_exp_series_b24 = true := by decide +kernel
theorem sie_exp_series_b24_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b24 (sie_exp_series_v24 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b21_mem x h_x_lo h_x_hi) sie_exp_series_b23_mem) sie_exp_series_b24_calc
def sie_exp_series_b25 : RI := ⟨10000000000000000000000000000000000000000, 16320246155315837141506637413227001554365⟩
noncomputable def sie_exp_series_v25 (x : ℝ) : ℝ := (sie_exp_series_v20 x) + (sie_exp_series_v24 x)
theorem sie_exp_series_b25_calc : RI.subset (RI.add sie_exp_series_b20 sie_exp_series_b24) sie_exp_series_b25 = true := by decide +kernel
theorem sie_exp_series_b25_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b25 (sie_exp_series_v25 x) :=
  RI.mem_of_subset (RI.mem_add (sie_exp_series_b20_mem x h_x_lo h_x_hi) (sie_exp_series_b24_mem x h_x_lo h_x_hi)) sie_exp_series_b25_calc
def sie_exp_series_b26 : RI := ⟨0, 156250000000000000000000000000000000002⟩
noncomputable def sie_exp_series_v26 (x : ℝ) : ℝ := (sie_exp_series_v21 x) * (sie_exp_series_v1 x)
theorem sie_exp_series_b26_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b21 sie_exp_series_b1) sie_exp_series_b26 = true := by decide +kernel
theorem sie_exp_series_b26_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b26 (sie_exp_series_v26 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b21_mem x h_x_lo h_x_hi) (sie_exp_series_b1_mem x h_x_lo h_x_hi)) sie_exp_series_b26_calc
def sie_exp_series_b27 : RI := ⟨(-15000000000000000000000000000000000000000), (-14999999999999999999999999999999999999999)⟩
noncomputable def sie_exp_series_v27 : ℝ := ((-3 : ℝ) / 2)
theorem sie_exp_series_b27_calc : RI.subset (RI.ofFrac sie_exp_series_S (-3) 2) sie_exp_series_b27 = true := by decide +kernel
theorem sie_exp_series_b27_mem : RI.Mem sie_exp_series_S sie_exp_series_b27 sie_exp_series_v27 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_series_hS (by norm_num) (by norm_num [sie_exp_series_v27])) sie_exp_series_b27_calc
def sie_exp_series_b28 : RI := ⟨2231301601484298289332804707640125213399, 2231301601484298289332804707640125213446⟩
theorem sie_exp_series_b28_small : RI.expSmallOK sie_exp_series_S sie_exp_series_b27 1 = true := by decide +kernel
theorem sie_exp_series_b28_rem : RI.expRemOK sie_exp_series_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_series_v28 : ℝ := Real.exp sie_exp_series_v27
theorem sie_exp_series_b28_calc : RI.subset (RI.expR sie_exp_series_S sie_exp_series_b27 1 34 1) sie_exp_series_b28 = true := by decide +kernel
theorem sie_exp_series_b28_mem : RI.Mem sie_exp_series_S sie_exp_series_b28 sie_exp_series_v28 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_series_hS sie_exp_series_b27_mem sie_exp_series_b28_small sie_exp_series_b28_rem) sie_exp_series_b28_calc
def sie_exp_series_b29 : RI := ⟨0, 34864087523192160770825073556876956461⟩
noncomputable def sie_exp_series_v29 (x : ℝ) : ℝ := (sie_exp_series_v26 x) * sie_exp_series_v28
theorem sie_exp_series_b29_calc : RI.subset (RI.mul sie_exp_series_S sie_exp_series_b26 sie_exp_series_b28) sie_exp_series_b29 = true := by decide +kernel
theorem sie_exp_series_b29_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b29 (sie_exp_series_v29 x) :=
  RI.mem_of_subset (RI.mem_mul sie_exp_series_hS (sie_exp_series_b26_mem x h_x_lo h_x_hi) sie_exp_series_b28_mem) sie_exp_series_b29_calc
def sie_exp_series_b30 : RI := ⟨10000000000000000000000000000000000000000, 16355110242839029302277462486783878510826⟩
noncomputable def sie_exp_series_v30 (x : ℝ) : ℝ := (sie_exp_series_v25 x) + (sie_exp_series_v29 x)
theorem sie_exp_series_b30_calc : RI.subset (RI.add sie_exp_series_b25 sie_exp_series_b29) sie_exp_series_b30 = true := by decide +kernel
theorem sie_exp_series_b30_mem (x : ℝ) (h_x_lo : (0 : ℝ) ≤ x) (h_x_hi : x ≤ ((1 : ℝ) / 2)) : RI.Mem sie_exp_series_S sie_exp_series_b30 (sie_exp_series_v30 x) :=
  RI.mem_of_subset (RI.mem_add (sie_exp_series_b25_mem x h_x_lo h_x_hi) (sie_exp_series_b29_mem x h_x_lo h_x_hi)) sie_exp_series_b30_calc
theorem sie_exp_series_lo_calc : RI.lowerOK sie_exp_series_S sie_exp_series_b30 1 1 = true := by decide +kernel
theorem sie_exp_series_hi_calc : RI.upperOK sie_exp_series_S sie_exp_series_b30 8177555121419514651138731243391939255413 5000000000000000000000000000000000000000 = true := by decide +kernel
/-- `sie_exp_series`: the kernel-checked enclosure (exact-evaluated pre-emission). -/
theorem sie_exp_series : ∀ x : ℝ, (0 : ℝ) ≤ x → x ≤ ((1 : ℝ) / 2) → (1 : ℝ) ≤ (((((((1 : ℝ) + (x * (Real.exp ((-1 : ℝ) / 4)))) + ((x * x) * (Real.exp ((-1 : ℝ) / 2)))) + (((x * x) * x) * (Real.exp ((-3 : ℝ) / 4)))) + ((((x * x) * x) * x) * (Real.exp (-1 : ℝ)))) + (((((x * x) * x) * x) * x) * (Real.exp ((-5 : ℝ) / 4)))) + ((((((x * x) * x) * x) * x) * x) * (Real.exp ((-3 : ℝ) / 2)))) ∧ (((((((1 : ℝ) + (x * (Real.exp ((-1 : ℝ) / 4)))) + ((x * x) * (Real.exp ((-1 : ℝ) / 2)))) + (((x * x) * x) * (Real.exp ((-3 : ℝ) / 4)))) + ((((x * x) * x) * x) * (Real.exp (-1 : ℝ)))) + (((((x * x) * x) * x) * x) * (Real.exp ((-5 : ℝ) / 4)))) + ((((((x * x) * x) * x) * x) * x) * (Real.exp ((-3 : ℝ) / 2)))) ≤ ((8177555121419514651138731243391939255413 : ℝ) / 5000000000000000000000000000000000000000) := by
  intro x h_x_lo h_x_hi
  have h : RI.Mem sie_exp_series_S sie_exp_series_b30 (((((((1 : ℝ) + (x * (Real.exp ((-1 : ℝ) / 4)))) + ((x * x) * (Real.exp ((-1 : ℝ) / 2)))) + (((x * x) * x) * (Real.exp ((-3 : ℝ) / 4)))) + ((((x * x) * x) * x) * (Real.exp (-1 : ℝ)))) + (((((x * x) * x) * x) * x) * (Real.exp ((-5 : ℝ) / 4)))) + ((((((x * x) * x) * x) * x) * x) * (Real.exp ((-3 : ℝ) / 2)))) := (sie_exp_series_b30_mem x h_x_lo h_x_hi)
  exact ⟨RI.le_of_mem sie_exp_series_hS h (by norm_num) (by norm_num) sie_exp_series_lo_calc,
    RI.ge_of_mem sie_exp_series_hS h (by norm_num) (by norm_num) sie_exp_series_hi_calc⟩
example : ∀ x : ℝ, (0 : ℝ) ≤ x → x ≤ ((1 : ℝ) / 2) → (1 : ℝ) ≤ (((((((1 : ℝ) + (x * (Real.exp ((-1 : ℝ) / 4)))) + ((x * x) * (Real.exp ((-1 : ℝ) / 2)))) + (((x * x) * x) * (Real.exp ((-3 : ℝ) / 4)))) + ((((x * x) * x) * x) * (Real.exp (-1 : ℝ)))) + (((((x * x) * x) * x) * x) * (Real.exp ((-5 : ℝ) / 4)))) + ((((((x * x) * x) * x) * x) * x) * (Real.exp ((-3 : ℝ) / 2)))) ∧ (((((((1 : ℝ) + (x * (Real.exp ((-1 : ℝ) / 4)))) + ((x * x) * (Real.exp ((-1 : ℝ) / 2)))) + (((x * x) * x) * (Real.exp ((-3 : ℝ) / 4)))) + ((((x * x) * x) * x) * (Real.exp (-1 : ℝ)))) + (((((x * x) * x) * x) * x) * (Real.exp ((-5 : ℝ) / 4)))) + ((((((x * x) * x) * x) * x) * x) * (Real.exp ((-3 : ℝ) / 2)))) ≤ ((8177555121419514651138731243391939255413 : ℝ) / 5000000000000000000000000000000000000000) := sie_exp_series

end ScaledIntervalEval

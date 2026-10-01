/- telperion 0.1.6 | family RationalIdentityExt | input-hash 3bb5c4734af48c6a
   31 theorems, 53 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RationalIdentityExt

-- partial_fraction_two_linear: rational identity on a box (multivariate extension, 2026-10-01): -1 < x
-- (2 denominator atoms certified positive there).
theorem partial_fraction_two_linear : ∀ x : ℚ, (-1 : ℚ) < x →
    ((1) / ((1 + x) * (2 + x))) = ((1 / (1 + x)) + (((-1)) / ((2 + x)))) := by
  intro x hx
  have hD0 : ((1 + x) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hD1 : ((2 + x) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

-- partial_fraction_quadratic_factor: rational identity on a box (multivariate extension, 2026-10-01): 0 < x
-- (2 denominator atoms certified positive there).
theorem partial_fraction_quadratic_factor : ∀ x : ℚ, (0 : ℚ) < x →
    ((1) / (x * (1 + x ^ 2))) = ((1 / x) + (((-1) * x) / ((1 + x ^ 2)))) := by
  intro x hx
  have hD0 : (x : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hD1 : ((1 + x ^ 2) : ℚ) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

-- partial_fraction_two_variable: rational identity on a box (multivariate extension, 2026-10-01): 0 < x, 0 < y
-- (3 denominator atoms certified positive there).
theorem partial_fraction_two_variable : ∀ x y : ℚ, (0 : ℚ) < x → (0 : ℚ) < y →
    ((1) / ((x + y) * (x + (2 * y)))) = ((((1 / (x + y)) + (((-1)) / ((x + (2 * y)))))) / (y)) := by
  intro x y hx hy
  have hD0 : ((x + y) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hD1 : ((x + (2 * y)) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hD2 : (y : ℚ) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

-- harmonic_pair_two_variable: rational identity on a box (multivariate extension, 2026-10-01): 0 < x, 0 < y
-- (3 denominator atoms certified positive there).
theorem harmonic_pair_two_variable : ∀ x y : ℚ, (0 : ℚ) < x → (0 : ℚ) < y →
    (((1) / (x * (x + y))) + ((1) / (y * (x + y)))) = ((1) / (x * y)) := by
  intro x y hx hy
  have hD0 : (x : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hD1 : ((x + y) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hD2 : (y : ℚ) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The real root `(-b + √d)/2` of t**2 - t - 1 (d = 5). -/
theorem minpoly_root_1_m1_m1 : ((-1 : ℝ) + (-1 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2) = 0 := by
  have hs : Real.sqrt (5 : ℝ) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * hs

-- phi_square: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem phi_square : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 2) = ((1 : ℝ) + t) := by
  intro t h
  linear_combination ((1 : ℝ)) * h

/-- `phi_square` at the real root `(-b + √d)/2`. -/
theorem phi_square_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2) = ((1 : ℝ) + (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  phi_square _ minpoly_root_1_m1_m1

-- sqrt5_from_root: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem sqrt5_from_root : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    ((1 : ℝ) + (-4 : ℝ) * t + (4 : ℝ) * t ^ 2) = ((5 : ℝ)) := by
  intro t h
  linear_combination ((4 : ℝ)) * h

/-- `sqrt5_from_root` at the real root `(-b + √d)/2`. -/
theorem sqrt5_from_root_at_root :
    ((1 : ℝ) + (-4 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (4 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2) = ((5 : ℝ)) :=
  sqrt5_from_root _ minpoly_root_1_m1_m1

-- fibonacci_power_3: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem fibonacci_power_3 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 3) = ((1 : ℝ) + (2 : ℝ) * t) := by
  intro t h
  linear_combination ((1 : ℝ) + t) * h

/-- `fibonacci_power_3` at the real root `(-b + √d)/2`. -/
theorem fibonacci_power_3_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 3) = ((1 : ℝ) + (2 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  fibonacci_power_3 _ minpoly_root_1_m1_m1

-- fibonacci_power_4: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem fibonacci_power_4 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 4) = ((2 : ℝ) + (3 : ℝ) * t) := by
  intro t h
  linear_combination ((2 : ℝ) + t + t ^ 2) * h

/-- `fibonacci_power_4` at the real root `(-b + √d)/2`. -/
theorem fibonacci_power_4_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 4) = ((2 : ℝ) + (3 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  fibonacci_power_4 _ minpoly_root_1_m1_m1

-- fibonacci_power_5: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem fibonacci_power_5 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 5) = ((3 : ℝ) + (5 : ℝ) * t) := by
  intro t h
  linear_combination ((3 : ℝ) + (2 : ℝ) * t + t ^ 2 + t ^ 3) * h

/-- `fibonacci_power_5` at the real root `(-b + √d)/2`. -/
theorem fibonacci_power_5_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 5) = ((3 : ℝ) + (5 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  fibonacci_power_5 _ minpoly_root_1_m1_m1

-- fibonacci_power_6: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem fibonacci_power_6 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 6) = ((5 : ℝ) + (8 : ℝ) * t) := by
  intro t h
  linear_combination ((5 : ℝ) + (3 : ℝ) * t + (2 : ℝ) * t ^ 2 + t ^ 3 + t ^ 4) * h

/-- `fibonacci_power_6` at the real root `(-b + √d)/2`. -/
theorem fibonacci_power_6_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 6) = ((5 : ℝ) + (8 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  fibonacci_power_6 _ minpoly_root_1_m1_m1

-- fibonacci_power_7: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem fibonacci_power_7 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 7) = ((8 : ℝ) + (13 : ℝ) * t) := by
  intro t h
  linear_combination ((8 : ℝ) + (5 : ℝ) * t + (3 : ℝ) * t ^ 2 + (2 : ℝ) * t ^ 3 + t ^ 4 + t ^ 5) * h

/-- `fibonacci_power_7` at the real root `(-b + √d)/2`. -/
theorem fibonacci_power_7_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 7) = ((8 : ℝ) + (13 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  fibonacci_power_7 _ minpoly_root_1_m1_m1

-- fibonacci_power_8: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem fibonacci_power_8 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    (t ^ 8) = ((13 : ℝ) + (21 : ℝ) * t) := by
  intro t h
  linear_combination ((13 : ℝ) + (8 : ℝ) * t + (5 : ℝ) * t ^ 2 + (3 : ℝ) * t ^ 3 + (2 : ℝ) * t ^ 4 + t ^ 5 + t ^ 6) * h

/-- `fibonacci_power_8` at the real root `(-b + √d)/2`. -/
theorem fibonacci_power_8_at_root :
    ((((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 8) = ((13 : ℝ) + (21 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2)) :=
  fibonacci_power_8 _ minpoly_root_1_m1_m1

-- lucas_sum_2: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem lucas_sum_2 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    ((1 : ℝ) + (-2 : ℝ) * t + (2 : ℝ) * t ^ 2) = ((3 : ℝ)) := by
  intro t h
  linear_combination ((2 : ℝ)) * h

/-- `lucas_sum_2` at the real root `(-b + √d)/2`. -/
theorem lucas_sum_2_at_root :
    ((1 : ℝ) + (-2 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (2 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2) = ((3 : ℝ)) :=
  lucas_sum_2 _ minpoly_root_1_m1_m1

-- lucas_sum_3: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem lucas_sum_3 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    ((1 : ℝ) + (-3 : ℝ) * t + (3 : ℝ) * t ^ 2) = ((4 : ℝ)) := by
  intro t h
  linear_combination ((3 : ℝ)) * h

/-- `lucas_sum_3` at the real root `(-b + √d)/2`. -/
theorem lucas_sum_3_at_root :
    ((1 : ℝ) + (-3 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (3 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2) = ((4 : ℝ)) :=
  lucas_sum_3 _ minpoly_root_1_m1_m1

-- lucas_sum_4: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem lucas_sum_4 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    ((1 : ℝ) + (-4 : ℝ) * t + (6 : ℝ) * t ^ 2 + (-4 : ℝ) * t ^ 3 + (2 : ℝ) * t ^ 4) = ((7 : ℝ)) := by
  intro t h
  linear_combination ((6 : ℝ) + (-2 : ℝ) * t + (2 : ℝ) * t ^ 2) * h

/-- `lucas_sum_4` at the real root `(-b + √d)/2`. -/
theorem lucas_sum_4_at_root :
    ((1 : ℝ) + (-4 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (6 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2 + (-4 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 3 + (2 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 4) = ((7 : ℝ)) :=
  lucas_sum_4 _ minpoly_root_1_m1_m1

-- lucas_sum_5: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem lucas_sum_5 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    ((1 : ℝ) + (-5 : ℝ) * t + (10 : ℝ) * t ^ 2 + (-10 : ℝ) * t ^ 3 + (5 : ℝ) * t ^ 4) = ((11 : ℝ)) := by
  intro t h
  linear_combination ((10 : ℝ) + (-5 : ℝ) * t + (5 : ℝ) * t ^ 2) * h

/-- `lucas_sum_5` at the real root `(-b + √d)/2`. -/
theorem lucas_sum_5_at_root :
    ((1 : ℝ) + (-5 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (10 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2 + (-10 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 3 + (5 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 4) = ((11 : ℝ)) :=
  lucas_sum_5 _ minpoly_root_1_m1_m1

-- lucas_sum_6: identity modulo the minimal polynomial t**2 - t - 1 (extension, 2026-10-01):
-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.
theorem lucas_sum_6 : ∀ t : ℝ, ((-1 : ℝ) + (-1 : ℝ) * t + t ^ 2) = 0 →
    ((1 : ℝ) + (-6 : ℝ) * t + (15 : ℝ) * t ^ 2 + (-20 : ℝ) * t ^ 3 + (15 : ℝ) * t ^ 4 + (-6 : ℝ) * t ^ 5 + (2 : ℝ) * t ^ 6) = ((18 : ℝ)) := by
  intro t h
  linear_combination ((17 : ℝ) + (-11 : ℝ) * t + (13 : ℝ) * t ^ 2 + (-4 : ℝ) * t ^ 3 + (2 : ℝ) * t ^ 4) * h

/-- `lucas_sum_6` at the real root `(-b + √d)/2`. -/
theorem lucas_sum_6_at_root :
    ((1 : ℝ) + (-6 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) + (15 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 2 + (-20 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 3 + (15 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 4 + (-6 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 5 + (2 : ℝ) * (((1 : ℝ) + Real.sqrt (5 : ℝ)) / 2) ^ 6) = ((18 : ℝ)) :=
  lucas_sum_6 _ minpoly_root_1_m1_m1

end RationalIdentityExt

/- Comparator challenge module for `BernoulliChallenge` -- INDEPENDENT statement
   authority for the Telperion-emitted solution.  Signatures are the
   emitted theorems' types (Comparator asserts the solution proves
   exactly these); the proofs here are independent of Telperion's
   certificate.  Replace with hand-authored statements to guard against
   certificate drift.  -/

import Mathlib

namespace BernoulliInequality

theorem bernoulli_k2 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x ^ 2 := by
  positivity

theorem bernoulli_k3 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 3 * x ^ 2 + x ^ 3 := by
  positivity

theorem bernoulli_k4 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 6 * x ^ 2 + 4 * x ^ 3 + x ^ 4 := by
  positivity

theorem bernoulli_k5 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 10 * x ^ 2 + 10 * x ^ 3 + 5 * x ^ 4 + x ^ 5 := by
  positivity

theorem bernoulli_k6 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 15 * x ^ 2 + 20 * x ^ 3 + 15 * x ^ 4 + 6 * x ^ 5 + x ^ 6 := by
  positivity

end BernoulliInequality

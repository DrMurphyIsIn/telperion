import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
Target theorems for the closure-audit example (hand-written; the audit scripts next to this
library are generated).  Small on purpose: the point is the audit, not the mathematics.
-/

namespace ClosureAuditExample

theorem prime_101 : Nat.Prime 101 := by norm_num

theorem two_le_of_prime (p : ℕ) (hp : Nat.Prime p) : 2 ≤ p := hp.two_le

theorem sum_le (a b : ℕ) (h : a ≤ b) : a + a ≤ b + b := Nat.add_le_add h h

def smallPrimes : List ℕ := [2, 3, 5, 7]

theorem smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by decide

end ClosureAuditExample

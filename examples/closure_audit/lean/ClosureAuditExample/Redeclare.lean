import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
NEGATIVE CONTROL for the closure audit, second kind: a module that RE-DECLARES a target's
name with a different proof.  It does not import `Example.lean`; Lean imports the two side by
side without complaint.  `env.find?` then returns one of the two proofs while `collectAxioms`
reports the axioms the OTHER module recorded at compile time, so `#print axioms` can say the
clean three while the closure holds a `native_decide` axiom.  An independent reviewer
demonstrated this on the CN-1 theorem; the audit of `prime_101` with this module imported must
FAIL with "inconsistent environment".  This is the scenario the design note's "never
re-declare a target name" rule is about.
-/

namespace ClosureAuditExample

theorem prime_101 : Nat.Prime 101 := by native_decide

end ClosureAuditExample

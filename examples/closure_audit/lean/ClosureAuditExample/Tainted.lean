import ClosureAuditExample.Example

/-!
NEGATIVE CONTROL for the closure audit.  Everything here is deliberately unsound or
unchecked: a false axiom (1001 = 7 * 11 * 13), a `sorry` (1003 = 17 * 59) and a
`native_decide` (which adds `Lean.ofReduceBool` to the axioms).  The audit of these targets
must FAIL; the audit of `ClosureAuditExample.Example` must show none of this in its closure
even though this module is imported into the same environment.
-/

namespace ClosureAuditExample.NegControl

axiom fake_fact : Nat.Prime 1001

theorem via_axiom : ∃ p, 1000 < p ∧ Nat.Prime p := ⟨1001, by norm_num, fake_fact⟩

theorem via_sorry : Nat.Prime 1003 := by sorry

theorem via_native : Nat.Prime 101 := by native_decide

end ClosureAuditExample.NegControl

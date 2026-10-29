/-
Axiom guard for the RHLinalg prelude (ported from anthropics/zeta-23-lean, §3 of
arXiv:2608.13637).  CI runs `lake env lean AxiomGuardRHLinalg.lean` and asserts every
`#print axioms` line below is exactly `[propext, Classical.choice, Quot.sound]` — Lean's
three standard axioms — with no `sorryAx` and no project-specific axiom.  This is the same
enforced-honesty discipline used across the Arda formalization; a regression here fails CI.

These nine anchors are the lemmas the `hermitian_moment` Telperion emitter family (and future
Weil-positivity / Track-3 work) cites by name.  NOTE: this file only type-checks once the port
compiles under the pinned Mathlib v4.32.0 (see PORT_NOTES.md for the v4.33→v4.32 drift checklist);
until CI confirms, the port is transcribed-but-unverified.
-/
import RHLinalg

open RHLinalg

#print axioms posIndex_conj_le
#print axioms posIndex_add_le
#print axioms rank_trace_ineq
#print axioms rank_trace_ineq_two
#print axioms finrank_le_posIndex_of_posDefOn
#print axioms posDefOn_range_hermPosPart
#print axioms vonNeumann_trace_ineq
#print axioms weyl_posIndexAbove_le
#print axioms cauchySchwarz_count

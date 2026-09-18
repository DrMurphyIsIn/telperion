/-
Axiom guard for the interval-Gram-inertia island.

Run AFTER `lake build` (CI does): it prints the axiom dependencies of the four RHInertia bridge
lemmas and of every emitted per-box inertia certificate.  A clean run shows nothing beyond
mathlib's three axioms `[propext, Classical.choice, Quot.sound]`; CI additionally fails the job if
`sorryAx` appears anywhere in the output.

This file is HAND-WRITTEN (it is not emitted, so it is not part of the generate.py drift check) and
deliberately lists the capstones by name: adding a certificate without adding its guard line is a
visible omission in the diff.

conjecture1_proved = False -- these are finite linear-algebra certificates about explicit rational
interval boxes; none of them says anything about zeta.
-/
import GramInertia

-- The general interval-to-inertia bridge (no instance data).
#print axioms RHInertia.posIndex_add_posIndex_neg_le
#print axioms RHInertia.card_le_posIndex_of_compress_posDef
#print axioms RHInertia.compress_posDef_of_interval
#print axioms RHInertia.inertia_eq_of_witnesses

-- The emitted per-box certificates.
#print axioms GramInertia.inertia_pair_block_2
#print axioms GramInertia.inertia_coupled_3
#print axioms GramInertia.inertia_offline_pairs_4
#print axioms GramInertia.inertia_fractional_3

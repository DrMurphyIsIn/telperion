/-
Axiom guard for the scaled-interval-eval island.

Run AFTER `lake build` (CI does): it prints the axiom dependencies of the ScaledInterval
soundness lemmas and of every emitted enclosure.  A clean run shows nothing beyond mathlib's
three axioms `[propext, Classical.choice, Quot.sound]`; CI additionally fails the job if
`sorryAx` (or `Lean.ofReduceBool`, the native_decide axiom) appears anywhere in the output.

This file is HAND-WRITTEN (it is not emitted, so it is not part of the generate.py drift check)
and lists the capstones by name: adding an instance without adding its guard line is a visible
omission in the diff.

conjecture1_proved = False -- enclosures of explicit elementary expressions; nothing here
concerns zeta.
-/
import ScaledIntervalEval

-- The once-proved soundness lemmas (no instance data).
#print axioms ScaledInterval.RI.mem_ofRange
#print axioms ScaledInterval.RI.mem_mul
#print axioms ScaledInterval.RI.mem_expR
#print axioms ScaledInterval.RI.mem_of_subset
#print axioms ScaledInterval.RI.le_of_mem
#print axioms ScaledInterval.RI.ge_of_mem

-- The emitted enclosures.
#print axioms ScaledIntervalEval.sie_exp_third
#print axioms ScaledIntervalEval.sie_cubic
#print axioms ScaledIntervalEval.sie_sinh_reduced
#print axioms ScaledIntervalEval.sie_exp_series

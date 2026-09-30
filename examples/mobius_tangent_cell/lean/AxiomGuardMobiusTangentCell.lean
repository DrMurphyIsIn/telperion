import MobiusTangentCell

/-! Axiom guard for the mobius_tangent_cell dogfood: the union and sides theorems of every
instance depend on the standard axioms only (no `sorry`, no `native_decide`, no new axiom).
A drift in the printed axiom list fails `lake build`.  conjecture1_proved = False. -/

/-- info: 'MobiusTangentCell.pade_log1p_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.pade_log1p_sides

/-- info: 'MobiusTangentCell.logmean_lower_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.logmean_lower_sides

/-- info: 'MobiusTangentCell.concave_mobius_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.concave_mobius_sides

/-- info: 'MobiusTangentCell.pade_log1p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.pade_log1p

/-- info: 'MobiusTangentCell.logmean_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.logmean_lower

/-- info: 'MobiusTangentCell.concave_mobius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.concave_mobius

/-- info: 'MobiusTangentCell.no_mobius_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.no_mobius_sides

/-- info: 'MobiusTangentCell.zhu_band0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.zhu_band0

/-- info: 'MobiusTangentCell.zhu_band0_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MobiusTangentCell.zhu_band0_sides

"""Generate the gap_budget_multiplicity dogfood: certify -> emit -> append cross-checks -> write.

    python examples/gap_budget_multiplicity/generate.py           # write lean/GapBudgetMultiplicity.lean
    python examples/gap_budget_multiplicity/generate.py --check   # drift check (no write)
    cd examples/gap_budget_multiplicity/lean && lake build        # compile (Lean v4.32.0 + Mathlib)

A CLASSICAL instance (not the Brualdi-Goldwasser problem): maximise the product of positive
integer parts with a fixed sum N.  Taking logs, Phi(m) = sum_{k in m} log k under sum k = N; the
price tau = (log 3) / 3 is the best value per unit of log(k)/k over the integers, so the per-part
gap gamma(k) = k (log 3)/3 - log k is >= 0 with equality only at k = 3.  For each residue of N
mod 3 the classical optimum is the benchmark (3's; 3's and one 2; 3's and one 4), theta = C - B
is param-free, and the budget yields, uniformly in t:

  * N = 3t      : theta = 0 -- no 1s, 2s or 4s, every part < 5 (all parts are 3);
  * N = 3t + 2  : theta = gamma(2) -- no 1s or 4s, at most one 2, every part < 5;
  * N = 3t + 4  : theta = gamma(4) = 2 gamma(2) -- no 1s, at most two 2s, at most one 4, every
                  part < 5, and (count 2, count 4) in {(0,0), (0,1), (1,0), (2,0)}.

The tail k >= 5 is certified by the log tangent at 5 (gamma is convex, slope log3/3 - 1/5 > 0).
Log constants come from enclosure_tree (Real.log_two_gt_d9, the Taylor estimate at 3/2, the
Real.log_mul fold for 3 = 2 * 3/2 and 4 = 2 * 2).

A second, SMALL instance exercises the concave step: ten items from sizes 1..6, value
sum -k^2/9 + 12 log(mean k); the optimum 2^8 3^2 is the benchmark.  Tangent at x0 = 11/5 (the
benchmark mean): theta = 2/99 -- no 1s, 4s, 5s, 6s and at most two 3s.  Tangent at x0 = 2: a
looser theta = 14/9 + 12 log(10/11) (via enclosures of log 2, log 11/5) and a decided knapsack
over the counts of 1, 2, 4.

Appended by this generator (not emitter output): a CROSS-CHECK stating the N = 3t + 4 result
in its classical product form (m.sum = 3t + 4, 4 * 3^t <= m.prod), proved by feeding the
emitted theorem; and #print axioms lines.

conjecture1_proved = False -- elementary inequalities about a classical toy problem; nothing
here bears on RH or on the Laplacian-ratio problem.
"""
import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_gap_budget_multiplicity import (  # noqa: E402
    K,
    GapBudgetMultiplicityEmitter,
    gap_budget_multiplicity_family,
    gb_log,
    gb_logk,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

T = sp.Symbol("t")
_PRODUCT = dict(atoms=(1, None), tail_start=5, w=gb_logk(), ell=K, tau=gb_log(3) / 3,
                params=(T,))
_CONCAVE = dict(atoms=(1, 6), w=-K ** 2 / 9, ell=1, M=10, bench=((2, 8), (3, 2)))

SPECS = {
    "maxprod_mod0": dict(_PRODUCT, M=3 * T, bench=((3, T),)),
    "maxprod_mod2": dict(_PRODUCT, M=3 * T + 2, bench=((2, 1), (3, T))),
    "maxprod_mod1": dict(_PRODUCT, M=3 * T + 4, bench=((3, T), (4, 1))),
    "concave_sharp": dict(_CONCAVE, tau=sp.Rational(64, 99),
                          concave=("log", 12, sp.Rational(11, 5), K)),
    "concave_knapsack": dict(_CONCAVE, tau=sp.Rational(4, 5), concave=("log", 12, 2, K)),
}
NAMES = tuple(SPECS)

_OUT = Path(__file__).resolve().parent / "lean" / "GapBudgetMultiplicity.lean"

_CROSS_CHECK = """
/-! ### Cross-check (appended by generate.py, not emitter output)

The `N = 3t + 4` pruning in its classical PRODUCT form: a multiset of positive parts with sum
`3t + 4` and product at least `4 * 3^t` (the classical optimum) has no 1s, at most two 2s, at most
one 4, no part >= 5, and the (2s, 4s) counts in the decided list.  Proved by feeding the emitted
`maxprod_mod1` (so the emitted statement is the one the kernel checks against this one). -/
theorem maxprod_mod1_classical (t : ℕ) (m : Multiset ℕ) (hA : ∀ k ∈ m, 1 ≤ k)
    (hsum : m.sum = 3 * t + 4) (hprod : 4 * 3 ^ t ≤ m.prod) :
    m.count 1 = 0 ∧ m.count 2 ≤ 2 ∧ m.count 4 ≤ 1 ∧ (∀ k ∈ m, k < 5) ∧
      [m.count 2, m.count 4] ∈ [[0, 0], [0, 1], [1, 0], [2, 0]] := by
  have hne : ∀ x ∈ m.map (fun k : ℕ => (k : ℝ)), x ≠ 0 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp hx
    have : (1 : ℝ) ≤ k := by exact_mod_cast hA k hk
    positivity
  apply maxprod_mod1 t m hA
  · have h := congrArg (fun n : ℕ => (n : ℝ)) hsum
    simp only [Nat.cast_multiset_sum] at h
    simp only [maxprod_mod1_ell]
    rw [h]
    push_cast
    ring
  · have hw : (m.map maxprod_mod1_w).sum = Real.log ((m.map (fun k : ℕ => (k : ℝ))).prod) := by
      rw [Real.log_multiset_prod hne, Multiset.map_map]
      rfl
    have hp : ((4 * 3 ^ t : ℕ) : ℝ) ≤ ((m.prod : ℕ) : ℝ) := by exact_mod_cast hprod
    rw [Nat.cast_multiset_prod] at hp
    have hl := Real.log_le_log (by positivity) hp
    have h43 : Real.log ((4 * 3 ^ t : ℕ) : ℝ) = Real.log 4 + t * Real.log 3 := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rw [hw]
    linarith
"""


def _axioms() -> str:
    names = ["gapBudget_log_tangent", "gapBudget_of_sep", "gapBudget_of_concave",
             "gapBudget_count_mul_le", "gapBudget_nat_cap", "gapBudget_knapsack"]
    for nm in NAMES:
        names += [nm, f"{nm}_bench"]
    names += ["maxprod_mod1_tail", "maxprod_mod1_classical"]
    return "\n" + "\n".join(f"#print axioms GapBudgetMultiplicity.{n}" for n in names) + "\n"


def build() -> str:
    fam = gap_budget_multiplicity_family(
        "GapBudgetMultiplicity",
        GridSpec([("case", list(range(len(NAMES))))]),
        lambda pt: NAMES[pt["case"]],
        spec=lambda pt: SPECS[NAMES[pt["case"]]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("GapBudgetMultiplicity",)),
        [GapBudgetMultiplicityEmitter()],
        ValidationReport(checks=(("gap_budget_multiplicity", True),)),
    )
    text = next(iter(report.files.values()))
    tail = "\nend GapBudgetMultiplicity\n"
    assert text.endswith(tail)
    return text[: -len(tail)] + _CROSS_CHECK + tail + _axioms()


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: GapBudgetMultiplicity.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))

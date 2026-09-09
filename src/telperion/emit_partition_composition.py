"""GevreyPartitionComposition emitter — the Faà di Bruno factorial-square
partition bound, ported verbatim from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``,
``Euler/GevreyCompositionPartitions.lean``, Apache-2.0; 144 lines,
self-contained over Mathlib's ``OrderedFinpartition``).

The combinatorial-species engine behind Gevrey composition stability: the
factorial-square weighted sum over ALL ordered finpartitions of ``n``,

    partitionSum n x := Σ_{c : OrderedFinpartition n} x^len(c)·(len(c)!·∏ᵢ sizeᵢ!)²,

has ONE fixed exponential radius uniformly in the order:

    partitionSum n x  ≤  (x+2)ⁿ·(n!)²        (x ≥ 0).

The proof recurses over Mathlib's ``OrderedFinpartition.extendEquiv``
(extending a partition either creates a singleton — ``extendLeft`` — or grows
one part — ``extendMiddle``), with the per-step weight growth bounded by
``(n+1)²·(x+2)`` via the simplex second moment.  This is the composition
companion of ``gevrey_majorant`` (which covers shift/convolution/recurrence but
not composition-over-partitions).

HONESTY SEAM: the application to actual Faà di Bruno derivative norms
(``norm_taylorComp_le``) is analysis-side PRELUDE, not emitted; the kernel
certifies the combinatorial sum bound only.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

PARTITION_COMPOSITION_PRELUDE = r"""
-- Faà di Bruno factorial-square partition bound, ported verbatim from OpenAI's
-- Euler blowup formalization (github.com/openai/NavierStokesAndEuler,
-- Euler/GevreyCompositionPartitions.lean; Apache-2.0).
open scoped BigOperators

section PartitionComposition
variable {n : ℕ}

lemma sum_partSize (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr c.equivSigma

lemma sum_partSize_real (c : OrderedFinpartition n) :
    ∑ i, (c.partSize i : ℝ) = n := by
  exact_mod_cast sum_partSize c

lemma sum_partSize_succ_sq_le (c : OrderedFinpartition n) :
    ∑ i, ((c.partSize i : ℝ) + 1)^2 ≤ 2 * ((n : ℝ) + 1)^2 := by
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  calc
    _ ≤ ∑ i, ((n : ℝ) + 1) * ((c.partSize i : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (c.partSize i : ℝ) ≤ n := by exact_mod_cast c.partSize_le i
      nlinarith [mul_nonneg (sub_nonneg.mpr hi)
        (show 0 ≤ (c.partSize i : ℝ) + 1 by positivity)]
    _ = ((n : ℝ) + 1) * ((n : ℝ) + c.length) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_partSize_real]
      simp
    _ ≤ _ := by nlinarith

noncomputable def factorialProduct (c : OrderedFinpartition n) : ℝ :=
  ∏ i, ((c.partSize i).factorial : ℝ)

noncomputable def partitionWeight (x : ℝ) (c : OrderedFinpartition n) : ℝ :=
  x^c.length * ((c.length.factorial : ℝ) * factorialProduct c)^2

noncomputable def partitionSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, partitionWeight x c

lemma partitionWeight_nonneg (x : ℝ) (hx : 0 ≤ x) (c : OrderedFinpartition n) :
    0 ≤ partitionWeight x c := by
  unfold partitionWeight
  positivity

lemma factorialProduct_extendLeft (c : OrderedFinpartition n) :
    factorialProduct c.extendLeft = factorialProduct c := by
  change (∏ i : Fin (c.length+1),
    (Nat.factorial (Fin.cons (α := fun _ => ℕ) 1 c.partSize i) : ℝ)) =
    ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)
  rw [Fin.prod_univ_succ]
  simp

lemma factorialProduct_extendMiddle (c : OrderedFinpartition n) (i : Fin c.length) :
    factorialProduct (c.extendMiddle i) =
      ((c.partSize i : ℝ) + 1) * factorialProduct c := by
  change (∏ j : Fin c.length,
    ((Function.update c.partSize i (c.partSize i+1) j).factorial : ℝ)) =
      ((c.partSize i : ℝ) + 1) * ∏ j : Fin c.length, ((c.partSize j).factorial : ℝ)
  have he : (fun j : Fin c.length =>
      ((Function.update c.partSize i (c.partSize i+1) j).factorial : ℝ)) =
      fun j => (if j = i then (c.partSize i : ℝ) + 1 else 1) *
        ((c.partSize j).factorial : ℝ) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [Nat.factorial_succ]
    · simp [h]
  rw [he, Finset.prod_mul_distrib]
  simp

lemma partitionWeight_extendLeft (x : ℝ) (c : OrderedFinpartition n) :
    partitionWeight x c.extendLeft =
      (x * ((c.length : ℝ) + 1)^2) * partitionWeight x c := by
  simp only [partitionWeight, OrderedFinpartition.extendLeft_length,
    factorialProduct_extendLeft, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  ring

lemma partitionWeight_extendMiddle (x : ℝ) (c : OrderedFinpartition n) (i : Fin c.length) :
    partitionWeight x (c.extendMiddle i) =
      ((c.partSize i : ℝ) + 1)^2 * partitionWeight x c := by
  simp only [partitionWeight, OrderedFinpartition.extendMiddle_length,
    factorialProduct_extendMiddle]
  ring

lemma partitionSum_succ (n : ℕ) (x : ℝ) :
    partitionSum (n+1) x =
      ∑ c : OrderedFinpartition n,
        (x * ((c.length : ℝ) + 1)^2 + ∑ i, ((c.partSize i : ℝ) + 1)^2) *
          partitionWeight x c := by
  unfold partitionSum
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  simp only [Fintype.sum_sigma, Fintype.sum_option, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    partitionWeight_extendLeft, partitionWeight_extendMiddle, ← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma partitionSum_succ_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum (n+1) x ≤ ((n : ℝ) + 1)^2 * (x+2) * partitionSum n x := by
  rw [partitionSum_succ, partitionSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  have hs : ((c.length : ℝ) + 1)^2 ≤ ((n : ℝ) + 1)^2 := by gcongr
  apply mul_le_mul_of_nonneg_right _ (partitionWeight_nonneg x hx c)
  calc
    _ ≤ x * ((n : ℝ) + 1)^2 + 2 * ((n : ℝ) + 1)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hs hx) (sum_partSize_succ_sq_le c)
    _ = _ := by ring

/-- The entire factorial-square Faà di Bruno partition sum has one fixed
exponential radius, independent of the differentiation order. -/
theorem partitionSum_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum n x ≤ (x+2)^n * (n.factorial : ℝ)^2 := by
  induction n with
  | zero =>
    simp [partitionSum, partitionWeight, factorialProduct,
      OrderedFinpartition.default_eq]
  | succ n ih =>
    calc
      _ ≤ ((n : ℝ) + 1)^2 * (x+2) * partitionSum n x :=
        partitionSum_succ_le n x hx
      _ ≤ ((n : ℝ) + 1)^2 * (x+2) * ((x+2)^n * (n.factorial : ℝ)^2) := by
        gcongr
      _ = _ := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

end PartitionComposition
""".strip("\n")


@dataclass(frozen=True)
class PartitionCompositionCert:
    mode: str = "calculus"


def partition_composition_certificate() -> PartitionCompositionCert:
    return PartitionCompositionCert()


def certify_partition_composition_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic calculus); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=partition_composition_certificate())
    return inst, 1


@dataclass
class PartitionCompositionEmitter(Emitter):
    """Emit the fixed Faà di Bruno partition-sum calculus (once per file)."""

    def __post_init__(self):
        self.kind = "partition_composition"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return PARTITION_COMPOSITION_PRELUDE + "\n", 12


def partition_composition_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``partition_composition`` (fully generic calculus; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("partition_composition", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )

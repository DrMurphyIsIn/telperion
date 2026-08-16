"""p-adic valuation certificates — Telperion's arithmetic vocabulary.

The rational-Polya machinery proves `0 <= P(x)` for polynomials; it has no way
to talk about DIVISIBILITY or p-adic valuation.  But some inequalities are
arithmetic, not analytic: the Brualdi-Goldwasser crux is `N <= D` where
`Phi^11 = N/D` and the whole difficulty is the interplay of `K = v_p(D)` (the
p-cancellation count) with the p-free ratio `N/D0` (`D = p^K * D0`).  A single
prime `p = 23` runs the show: `621 = 3^3 * 23` injects `23^(1+2c)` per node,
and the tie is where those cancel completely (`K = 0`).

This module gives exact valuation arithmetic (the untrusted engine) plus Lean
emission of the two primitives such proofs need:

  * VALUATION FACTS `v_p(n) = k`, certified as `p^k | n and not p^(k+1) | n`
    (decidable divisibility — no reliance on `padicValNat` reduction);
  * the VALUATION-MAGNITUDE SPLIT, the reasoning step `N <= p^K * D0` from a
    p-free magnitude bound `N <= C * D0` and `C <= p^K` (`p^K` dominates once K
    is large — the "trivial away from the tie" phenomenon), emitted as a
    reusable prelude lemma over the naturals.

Everything is exact; the Lean kernel is the arbiter.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


def padic_val(n: int, p: int) -> int:
    """v_p(n) for a nonzero integer (v_p(0) is undefined -> raises)."""
    if n == 0:
        raise ValueError("v_p(0) is undefined")
    n, k = abs(n), 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def padic_decompose(n: int, p: int) -> tuple[int, int]:
    """n = p^k * n0 with p not dividing n0; returns (k, n0).  Sign kept on n0."""
    if n == 0:
        raise ValueError("cannot decompose 0")
    s = 1 if n > 0 else -1
    k = padic_val(n, p)
    return k, s * (abs(n) // p**k)


def padic_val_frac(x: Fraction, p: int) -> int:
    """v_p(a/b) = v_p(a) - v_p(b) (0 has no valuation)."""
    if x == 0:
        raise ValueError("v_p(0) is undefined")
    num = padic_val(x.numerator, p) if x.numerator % p == 0 else 0
    den = padic_val(x.denominator, p) if x.denominator % p == 0 else 0
    return num - den


@dataclass(frozen=True)
class ValuationFact:
    """The certified statement `v_p(n) = k`, in decidable-divisibility form:
    `p^k | n and not (p^(k+1) | n)`.  `check()` re-derives k from n by the exact
    engine (the dual to the Lean proof)."""

    name: str
    n: int
    p: int
    k: int

    def check(self) -> bool:
        return self.n != 0 and padic_val(self.n, self.p) == self.k

    def lean(self, tactic: str = "decide") -> str:
        pk = self.p ** self.k
        pk1 = self.p ** (self.k + 1)
        # `p^k | n and not p^(k+1) | n` pins v_p(n) = k exactly.
        return (
            f"theorem {self.name} : "
            f"({pk} ∣ {self.n}) ∧ ¬ ({pk1} ∣ {self.n}) := by {tactic}\n"
        )


def valuation_facts_lean(facts, tactic: str = "decide") -> str:
    body = "".join(f.lean(tactic) for f in facts)
    return body


# The valuation-magnitude split, as a reusable Lean prelude lemma over ℕ.
# This is the crux's shape: N <= p^K * D0 whenever N <= C * D0 (a p-free
# magnitude bound) and C <= p^K (the p-power dominates).  Trivial to prove, but
# it is the load-bearing bridge between the analytic magnitude bound and the
# arithmetic cancellation count -- the thing the rational machinery could never
# state.
SPLIT_LEMMA = """/-- Valuation-magnitude split: a p-free magnitude bound `N ≤ C * D0`
    combined with `C ≤ p^K` gives `N ≤ p^K * D0` — the bridge from an
    analytic bound to the p-adic cancellation count (`p^K` dominates once the
    cancellation count `K` is large; the tie is the residual `K` small case). -/
theorem le_pow_mul_of_le_mul {N C D0 pK : ℕ}
    (hmag : N ≤ C * D0) (hpow : C ≤ pK) : N ≤ pK * D0 := by
  calc N ≤ C * D0 := hmag
    _ ≤ pK * D0 := Nat.mul_le_mul_right _ hpow
"""

# The telescoping primitive, backed by Mathlib's multiplicativity of the p-adic
# valuation (`padicValRat.mul`): the valuation of a product is the sum of the
# valuations.  This is what lets `K = v_p(D)` be accounted node-by-node over the
# tree product `Phi^11 = prod_v factor_v` — the arithmetic telescoping that the
# rational-Polya machinery cannot express.  Emitted as a prelude the tree
# certificate cites; the leaves are the per-node `ValuationFact`s.
TELESCOPE_LEMMA = """/-- Telescoping of the p-adic valuation over a product (Mathlib
    `padicValRat.mul`): the valuation of a product is the sum of the
    valuations — the node-by-node accounting of the cancellation count `K`.
    Stated concretely for three factors (the general n-fold form is this by
    induction / `Finset.prod`); this is the primitive a tree certificate
    chains over its nodes. -/
theorem padicValRat_mul3 {p : ℕ} [Fact p.Prime] {a b c : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    padicValRat p (a * b * c)
      = padicValRat p a + padicValRat p b + padicValRat p c := by
  rw [padicValRat.mul (mul_ne_zero ha hb) hc, padicValRat.mul ha hb]
"""

# The adelic reframing (the product-formula view the Padic API makes precise):
# for a positive rational q = N/D, the archimedean bound |q| <= 1 is EQUIVALENT
# to a valuation balance over primes, because |q|_infty * prod_p ‖q‖_p = 1
# (product formula) with ‖q‖_p = p^{-v_p(q)}.  Concretely N <= D iff
#     sum_p (v_p(D) - v_p(N)) * log p  >=  0,
# and the p = 23 term contributes K * log 23 (large away from the tie, zero at
# it).  Telperion cannot yet emit this as one certificate, but it names the
# object: a per-prime valuation-balance ledger whose dominant column is 23.
ADELIC_NOTE = "N ≤ D  ⇔  Σ_p (v_p(D) − v_p(N))·log p ≥ 0  (23-column = K·log 23)"


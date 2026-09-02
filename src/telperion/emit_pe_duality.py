"""Pseudo-expectation / SoS-duality emitter — "no degree-d SoS refutation exists".

The strongest sweep-2 candidate: a *feasibility* certificate for the degree-`d`
moment relaxation of a polynomial constraint system ``{gᵢ = 0}``, presented in
REFUTATION-BLOCKING (duality) form.  A pseudo-expectation functional

    E : (MvPolynomial (Fin N) ℚ) →ₗ[ℚ] ℚ

with three properties

    (i)   E 1 = 1                                        (normalization)
    (ii)  E (s²) ≥ 0   for   deg s ≤ d                   (moment-matrix PSD)
    (iii) E (p · gᵢ) = 0                                 (ideal / constraint kill)

makes every low-degree SoS refutation ``−1 = Σ sⱼ² + Σ pᵢ·gᵢ`` impossible:
applying ``E`` to that identity yields ``−1 = (≥ 0) + 0``, a contradiction.  So
``IsEmpty (SOSRefutation g d dc)`` — no degree-`d` Positivstellensatz refutation
of the system exists (a moment-relaxation lower bound, in duality form).

This FIRST-CLASSES the ad-hoc ``examples/knapsack_sos/gen_xor3_duality.py``
regex-substitution generator into a proper Telperion emitter, and models the
emitted Lean FAITHFULLY on the kernel-green proofs already in the repo —
``examples/g1_floors/lean/Duality.lean`` (``no_refutation``, ``pe``,
``pe_bool_kill``) and ``examples/g1_floors/lean/Xor3Duality.lean``
(``oddSet_add``, ``pe3_bool_kill``).  The abstract duality ``no_refutation`` and
the multilinear kill are reproduced verbatim (same lemma names, same tactics),
so the Lean kernel re-checks every emitted instance from scratch.

TWO BOOLEAN SEMANTICS (the "multilinear kill" sub-mode, folded in per spec):

  * ``mode="bool"`` (0/1 variables): the ideal generator is ``Xᵢ² − Xᵢ``.  The
    support-weighted functional ``pe`` (weight sees only WHICH variables occur,
    a la ``Duality.pe``) kills it UNCONDITIONALLY because
    ``support(α + 2eᵢ) = support(α + eᵢ)`` — the ``pe_bool_kill`` lemma.

  * ``mode="parity"`` (±1 variables): the ideal generator is ``Xᵢ² − 1``.  The
    parity-weighted functional ``pePar`` (weight sees only the odd-exponent set,
    a la ``Xor3Duality.pe3``) kills it UNCONDITIONALLY because adding 2 to an
    exponent never changes parity — the ``pePar_bool_kill`` lemma (built on the
    ``oddSet_add`` Δ-homomorphism / ``oddSet_add_two`` parity-mask lemmas).

THE PSD LEAF ``E(s²) ≥ 0`` IS SUPPLIED AS A HYPOTHESIS to the emitted master
theorem (``hsq``).  This is deliberate and keeps the emitter DETERMINISTIC and
SELF-CONTAINED (``import Mathlib`` only): the moment-matrix PSD fact is the one
genuinely instance-specific, SDP-flavored leaf (in the full pipeline it is the
kernel-checked ``petersen_moment_psd`` / knapsack block-decomposition); here it
is named and threaded, exactly as ``Duality.knapsack_no_refutation`` threads its
own ``hsq``.  Everything else — the abstract obstruction and both multilinear
kills — is proved outright, so the emitted ``*_no_refutation`` theorem is a
faithful CONDITIONAL master identical in structure to the proven originals.

EMITTED LEAN (per family, one self-contained file):

    structure SOSRefutation …                    -- copied verbatim
    theorem no_refutation …                       -- copied verbatim (4-line proof)
    -- per instance (name N mode):
    noncomputable def pe_<name> …                 -- the functional
    theorem pe_<name>_one …                       -- E 1 = 1
    theorem <name>_bool_kill …                    -- the multilinear ideal kill
    noncomputable def <name>System …             -- the constraint system
    theorem <name>_no_refutation … (hsq …) …      -- CONDITIONAL master

ANTI-PHANTOM (negative control): ``pe_duality_certificate`` sympy-checks the
defining functional properties on the supplied moment data — ``E 1 = 1``, that
each ideal generator's multilinear kill is identically zero on a spanning set of
monomials (the exponent-bump-of-2 invariance), and (when moment data is given)
that the supplied square-moment values are ``≥ 0``.  It RAISES ``ValueError`` on
a bad functional: a weight set with ``E 1 ≠ 1``, a kill that fails to vanish, a
negative supplied square-moment, or an out-of-range mode/degree.

HONEST SCOPE: this certifies ONLY the degree-`d` moment-relaxation feasibility
(no degree-`d` SoS refutation exists), CONDITIONAL on the named PSD leaf.  It is
not a proof of satisfiability of the system, nor does it close any downstream
obligation.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_pe_duality.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# ---------------------------------------------------------------- weights
def _bool_weight(k: int) -> Fraction:
    """Support-cardinality weight for the 0/1 (``bool``) functional: an
    admissible weight seeing only |support|.  ``f(k) = 1/k!`` (any weight with
    ``f(0) = 1`` works for E 1 = 1; the *kill* is weight-independent because it
    depends only on ``support`` being 2-exponent-bump-invariant)."""
    fac = 1
    for i in range(2, k + 1):
        fac *= i
    return Fraction(1, fac)


def _parity_weight(oddset: frozenset[int]) -> Fraction:
    """Parity-mask weight for the ±1 (``parity``) functional: an admissible
    weight seeing only the odd-exponent set.  Here the indicator of the empty
    parity set (``w = 1`` iff every variable occurs to even degree), so
    ``E 1 = 1`` and the kill (parity-invariant under +2 bumps) vanishes."""
    return Fraction(1) if len(oddset) == 0 else Fraction(0)


@dataclass(frozen=True)
class PeDualityCertificate:
    """A verified pseudo-expectation / SoS-duality (no-refutation) certificate.

    Fields
    ------
    name : str
        Lean-safe base name for this instance's definitions/theorems.
    n_vars : int
        Number of variables ``N`` (the polynomial ring is ``MvPolynomial (Fin N) ℚ``).
    degree : int
        SoS degree bound ``d`` (squares of degree ≤ d; cofactors ≤ 2d).
    mode : str
        ``"bool"`` (0/1, ideal gen ``Xᵢ² − Xᵢ``) or ``"parity"`` (±1, gen ``Xᵢ² − 1``).
    """

    name: str
    n_vars: int
    degree: int
    mode: str


def pe_duality_certificate(
    name: str,
    n_vars: int,
    degree: int,
    *,
    mode: str = "bool",
    square_moments: tuple | None = None,
) -> PeDualityCertificate:
    """Build and EXACTLY self-check a pseudo-expectation duality certificate.

    Sympy-verifies the functional's DEFINING properties on the supplied data:

      * ``E 1 = 1`` (normalization: the empty-support / empty-parity weight is 1);
      * the MULTILINEAR KILL vanishes identically — for each variable ``i`` and a
        spanning set of test exponent vectors ``α``, the functional's weight is
        invariant under bumping ``αᵢ`` by 2 (i.e.
        ``w(α + 2eᵢ) = w(α + eᵢ)`` for ``bool`` via support,
        ``w(α + 2eᵢ) = w(α)`` for ``parity`` via oddSet), which is exactly the
        algebraic fact that makes ``pe_bool_kill`` / ``pePar_bool_kill`` hold;
      * (when ``square_moments`` is given) every supplied ``E(sⱼ²)`` value is
        ``≥ 0`` — the PSD-leaf sanity check.

    RAISES ``ValueError`` (the anti-phantom negative control) on a bad functional:
    non-positive ``n_vars``/``degree``, an unknown ``mode``, ``2*degree ≥ n_vars``
    (the truncation must leave room — mirrors ``knapsack_no_refutation``'s
    ``2*d < N``), an ``E 1 ≠ 1`` weight, a kill that fails to vanish, or any
    supplied ``E(sⱼ²) < 0``.
    """
    if mode not in ("bool", "parity"):
        raise ValueError(f"REFUSED: unknown mode {mode!r} (want 'bool' or 'parity')")
    if n_vars <= 0:
        raise ValueError(f"REFUSED: n_vars = {n_vars} must be positive")
    if degree <= 0:
        raise ValueError(f"REFUSED: degree = {degree} must be positive")
    if 2 * degree >= n_vars:
        raise ValueError(
            f"REFUSED: need 2*degree < n_vars for the truncation to leave room "
            f"(got 2*{degree} = {2 * degree} >= {n_vars}); mirrors knapsack 2d < N"
        )

    N = n_vars

    # (i) normalization E 1 = 1  (the α = 0 monomial).
    if mode == "bool":
        w0 = _bool_weight(0)  # |support(0)| = 0
    else:
        w0 = _parity_weight(frozenset())  # oddSet(0) = ∅
    if w0 != Fraction(1):
        raise ValueError(
            f"REFUSED: E 1 != 1 (weight of the constant monomial is {w0}, want 1)"
        )

    # (ii) MULTILINEAR KILL vanishes identically on a spanning set of test
    #      exponent vectors.  For each variable i and each test base exponent
    #      vector `base` (0, and every single-variable e_j), check that the
    #      degree-1 and degree-2 bumps of variable i carry EQUAL functional
    #      weight, so E((X_i^2 - X_i)*monomial)=0  (bool) resp.
    #      E((X_i^2 - 1)*monomial)=0  (parity).
    def _support_card(exps: dict[int, int]) -> int:
        return sum(1 for v in exps.values() if v != 0)

    def _oddset(exps: dict[int, int]) -> frozenset[int]:
        return frozenset(i for i, v in exps.items() if v % 2 == 1)

    def _weight(exps: dict[int, int]) -> Fraction:
        if mode == "bool":
            return _bool_weight(_support_card(exps))
        return _parity_weight(_oddset(exps))

    # spanning test bases: the zero vector and each single-variable exponent.
    test_bases: list[dict[int, int]] = [dict()] + [{j: 1} for j in range(N)]
    for i in range(N):
        for base in test_bases:
            deg1 = dict(base)
            deg1[i] = deg1.get(i, 0) + 1  # base * X_i
            deg2 = dict(base)
            deg2[i] = deg2.get(i, 0) + 2  # base * X_i^2
            if mode == "bool":
                # E((X_i^2 - X_i)*mono) = w(deg2) - w(deg1) must be 0.
                if _weight(deg2) != _weight(deg1):
                    raise ValueError(
                        f"REFUSED: bool kill fails at var {i}, base {base}: "
                        f"w(deg2)={_weight(deg2)} != w(deg1)={_weight(deg1)}"
                    )
            else:
                # E((X_i^2 - 1)*mono) = w(deg2) - w(base) must be 0.
                if _weight(deg2) != _weight(base):
                    raise ValueError(
                        f"REFUSED: parity kill fails at var {i}, base {base}: "
                        f"w(deg2)={_weight(deg2)} != w(base)={_weight(base)}"
                    )

    # (iii) PSD-leaf sanity: supplied square-moments must be nonnegative.
    if square_moments is not None:
        for j, m in enumerate(square_moments):
            mv = sp.nsimplify(m)
            if not (mv >= 0):
                raise ValueError(
                    f"REFUSED: supplied square-moment E(s_{j}^2) = {m} is negative; "
                    f"PSD leaf violated"
                )

    return PeDualityCertificate(
        name=str(name), n_vars=int(N), degree=int(degree), mode=str(mode)
    )


def certify_pe_duality_point(family, pt, name):
    """Certify one pe-duality instance from ``family.special[1](pt) -> spec``.

    ``spec`` is a dict ``{"n_vars": int, "degree": int, "mode": "bool"|"parity",
    "square_moments": optional}`` (or a ``(n_vars, degree)`` / ``(n_vars, degree,
    mode)`` tuple).  Returns ``(CertifiedInstance, n_checks)`` where ``n_checks``
    counts the emitted theorems in this instance's block (normalization + kill +
    master = 3)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = pe_duality_certificate(
            name,
            spec["n_vars"],
            spec["degree"],
            mode=spec.get("mode", "bool"),
            square_moments=spec.get("square_moments"),
        )
    else:
        n_vars, degree = spec[0], spec[1]
        mode = spec[2] if len(spec) > 2 else "bool"
        cert = pe_duality_certificate(name, n_vars, degree, mode=mode)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 3  # pe_one + bool_kill + no_refutation per instance


# --------------------------------------------------------------- Lean text
# The abstract duality PREAMBLE — copied VERBATIM from the kernel-green
# examples/g1_floors/lean/Duality.lean (`SOSRefutation` + `no_refutation`),
# emitted once per file (all instances share it).
_PREAMBLE = """open MvPolynomial
open scoped symmDiff

/-- A degree-bounded Positivstellensatz refutation of `{g i = 0}`:
`-1 = Σ s_j² + Σ p_i·g_i` with square degrees ≤ ds, cofactor degrees ≤ dc.
(Copied verbatim from the kernel-green KnapsackSOS.Duality.SOSRefutation.) -/
structure SOSRefutation {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin N) ℚ) (ds : ℕ) (dc : ι → ℕ) where
  k : ℕ
  squares : Fin k → MvPolynomial (Fin N) ℚ
  sqDeg : ∀ j, (squares j).totalDegree ≤ ds
  cof : ι → MvPolynomial (Fin N) ℚ
  cofDeg : ∀ i, (cof i).totalDegree ≤ dc i
  identity : (-1 : MvPolynomial (Fin N) ℚ)
      = (∑ j, squares j ^ 2) + ∑ i, cof i * g i

/-- The abstract duality: a pseudoexpectation blocks all refutations.
(Copied verbatim from the kernel-green KnapsackSOS.Duality.no_refutation:
`map_add`/`map_sum`/`map_neg` + `Finset.sum_eq_zero` + `Finset.sum_nonneg`
+ `linarith`.) -/
theorem no_refutation {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin N) ℚ) (ds : ℕ) (dc : ι → ℕ)
    (E : MvPolynomial (Fin N) ℚ →ₗ[ℚ] ℚ)
    (hE1 : E 1 = 1)
    (hsq : ∀ s : MvPolynomial (Fin N) ℚ, s.totalDegree ≤ ds → 0 ≤ E (s ^ 2))
    (hker : ∀ i, ∀ p : MvPolynomial (Fin N) ℚ,
      p.totalDegree ≤ dc i → E (p * g i) = 0) :
    IsEmpty (SOSRefutation g ds dc) := by
  constructor
  intro R
  have h := congrArg E R.identity
  rw [map_add, map_sum, map_sum, map_neg, hE1] at h
  have hz : ∑ i, E (R.cof i * g i) = 0 :=
    Finset.sum_eq_zero fun i _ => hker i (R.cof i) (R.cofDeg i)
  have hpos : (0 : ℚ) ≤ ∑ j, E (R.squares j ^ 2) :=
    Finset.sum_nonneg fun j _ => hsq _ (R.sqDeg j)
  rw [hz] at h
  linarith

/-- Support of a shifted exponent vector: adding `single i k` (k ≠ 0) inserts
`i`.  (Copied verbatim from KnapsackSOS.Duality.support_single_add.) -/
theorem support_single_add {N : ℕ} {k : ℕ} (hk : k ≠ 0) (i : Fin N)
    (α : Fin N →₀ ℕ) :
    (Finsupp.single i k + α).support = insert i α.support := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [Finsupp.mem_support_iff, hk]
  · simp [Finsupp.mem_support_iff, hj]

/-- The odd-exponent variable set of a monomial exponent vector (±1 mode).
(Copied from Xor3Duality.oddSet, generalized in N.) -/
def oddSet {N : ℕ} (α : Fin N →₀ ℕ) : Finset (Fin N) :=
  α.support.filter (fun i => α i % 2 = 1)

theorem mem_oddSet {N : ℕ} {α : Fin N →₀ ℕ} {i : Fin N} :
    i ∈ oddSet α ↔ α i % 2 = 1 := by
  simp only [oddSet, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

/-- Parity is a symmetric-difference homomorphism: the ±1 multilinearization
law.  (Copied from Xor3Duality.oddSet_add.) -/
theorem oddSet_add {N : ℕ} (α β : Fin N →₀ ℕ) :
    oddSet (α + β) = oddSet α ∆ oddSet β := by
  ext i
  rw [Finset.mem_symmDiff]
  simp only [mem_oddSet, Finsupp.add_apply]
  omega

/-- Adding 2 to any exponent preserves the parity set.
(Copied from Xor3Duality.oddSet_add_two.) -/
theorem oddSet_add_two {N : ℕ} (i : Fin N) (α : Fin N →₀ ℕ) :
    oddSet (Finsupp.single i 2 + α) = oddSet α := by
  ext j
  simp only [mem_oddSet, Finsupp.add_apply, Finsupp.single_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]
"""


def _emit_bool_instance(cert: PeDualityCertificate) -> tuple[str, int]:
    """One 0/1 (``bool``) instance block: support-weighted functional, the
    ``Xᵢ² − Xᵢ`` unconditional kill, and the conditional master."""
    nm = cert.name
    N = cert.n_vars
    d = cert.degree
    lines = f"""/-! ### Instance `{nm}`: {N} vars, degree {d}, 0/1 (bool) semantics.
Support-weighted pseudoexpectation (weight sees only WHICH variables occur);
the boolean ideal `X i ^ 2 - X i` is killed UNCONDITIONALLY. -/

/-- Support-cardinality weight (admissible: `fw 0 = 1`). -/
noncomputable def fw_{nm} : ℕ → ℚ := fun k => (1 : ℚ) / (k.factorial : ℚ)

/-- The support-weighted pseudoexpectation as a linear functional. -/
noncomputable def pe_{nm} : MvPolynomial (Fin {N}) ℚ →ₗ[ℚ] ℚ := by
  exact (Finsupp.linearCombination ℚ
      (fun α : Fin {N} →₀ ℕ => fw_{nm} α.support.card)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ)).toLinearMap

theorem pe_{nm}_monomial (α : Fin {N} →₀ ℕ) (c : ℚ) :
    pe_{nm} (monomial α c) = c * fw_{nm} α.support.card := by
  unfold pe_{nm}
  rw [← single_eq_monomial]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem pe_{nm}_one : pe_{nm} (1 : MvPolynomial (Fin {N}) ℚ) = 1 := by
  rw [one_def, pe_{nm}_monomial]
  simp [fw_{nm}]

/-- The boolean ideal `X i ^ 2 - X i` is killed UNCONDITIONALLY (the weight sees
only supports, and `support(α + 2eᵢ) = support(α + eᵢ)`). -/
theorem {nm}_bool_kill (i : Fin {N}) (p : MvPolynomial (Fin {N}) ℚ) :
    pe_{nm} ((X i ^ 2 - X i) * p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have h2 : (X i : MvPolynomial (Fin {N}) ℚ) ^ 2 * monomial α c
        = monomial (Finsupp.single i 2 + α) c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have h1 : (X i : MvPolynomial (Fin {N}) ℚ) * monomial α c
        = monomial (Finsupp.single i 1 + α) c := by
      rw [X, monomial_mul, one_mul]
    rw [sub_mul, map_sub, h2, h1, pe_{nm}_monomial, pe_{nm}_monomial,
      support_single_add (by norm_num) i α,
      support_single_add (by norm_num) i α, sub_self]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, add_zero]

/-- The boolean constraint system: booleanity per variable. -/
noncomputable def {nm}System : Fin {N} → MvPolynomial (Fin {N}) ℚ :=
  fun i => X i ^ 2 - X i

/-- CONDITIONAL MASTER: modulo the named square-nonnegativity hypothesis (the
moment-matrix PSD fact in functional form — the SDP leaf), NO degree-{d} SoS
refutation of the boolean system exists (cofactors of degree ≤ {2 * d}).
Structurally identical to KnapsackSOS.Duality.knapsack_no_refutation. -/
theorem {nm}_no_refutation
    (hsq : ∀ s : MvPolynomial (Fin {N}) ℚ, s.totalDegree ≤ {d} →
      0 ≤ pe_{nm} (s ^ 2)) :
    IsEmpty (SOSRefutation {nm}System {d} (fun _ => {2 * d})) := by
  refine no_refutation _ {d} (fun _ => {2 * d}) pe_{nm} pe_{nm}_one hsq ?_
  intro i p _
  rw [show pe_{nm} (p * {nm}System i) = pe_{nm} ((X i ^ 2 - X i) * p) from by
    rw [mul_comm]; rfl]
  exact {nm}_bool_kill i p

#print axioms {nm}_no_refutation
"""
    return lines, 3


def _emit_parity_instance(cert: PeDualityCertificate) -> tuple[str, int]:
    """One ±1 (``parity``) instance block: parity-weighted functional, the
    ``Xᵢ² − 1`` unconditional kill, and the conditional master."""
    nm = cert.name
    N = cert.n_vars
    d = cert.degree
    lines = f"""/-! ### Instance `{nm}`: {N} vars, degree {d}, ±1 (parity) semantics.
Parity-weighted pseudoexpectation (weight sees only the odd-exponent set);
the ±1 booleanity ideal `X i ^ 2 - 1` is killed UNCONDITIONALLY. -/

/-- Parity-mask weight: indicator of the empty parity set (admissible: the
constant monomial has weight 1). -/
noncomputable def wpar_{nm} (α : Fin {N} →₀ ℕ) : ℚ :=
  if oddSet α = ∅ then 1 else 0

/-- The parity-weighted pseudoexpectation as a linear functional. -/
noncomputable def pe_{nm} : MvPolynomial (Fin {N}) ℚ →ₗ[ℚ] ℚ := by
  exact (Finsupp.linearCombination ℚ wpar_{nm}).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ)).toLinearMap

theorem pe_{nm}_monomial (α : Fin {N} →₀ ℕ) (c : ℚ) :
    pe_{nm} (monomial α c) = c * wpar_{nm} α := by
  unfold pe_{nm}
  rw [← single_eq_monomial]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem pe_{nm}_one : pe_{nm} (1 : MvPolynomial (Fin {N}) ℚ) = 1 := by
  rw [one_def, pe_{nm}_monomial]
  have h0 : oddSet (0 : Fin {N} →₀ ℕ) = ∅ := by
    ext i; simp [mem_oddSet]
  rw [wpar_{nm}, h0]
  norm_num

/-- The ±1 booleanity ideal `X i ^ 2 - 1` is killed UNCONDITIONALLY (adding 2 to
any exponent preserves the parity set).  Copied from Xor3Duality.pe3_bool_kill. -/
theorem {nm}_bool_kill (i : Fin {N}) (p : MvPolynomial (Fin {N}) ℚ) :
    pe_{nm} ((X i ^ 2 - 1) * p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have h2 : (X i : MvPolynomial (Fin {N}) ℚ) ^ 2 * monomial α c
        = monomial (Finsupp.single i 2 + α) c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [sub_mul, map_sub, h2, one_mul, pe_{nm}_monomial, pe_{nm}_monomial,
      wpar_{nm}, wpar_{nm}, oddSet_add_two, sub_self]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, add_zero]

/-- The ±1 booleanity constraint system. -/
noncomputable def {nm}System : Fin {N} → MvPolynomial (Fin {N}) ℚ :=
  fun i => X i ^ 2 - 1

/-- CONDITIONAL MASTER: modulo the named square-nonnegativity hypothesis (the
moment-matrix PSD fact in functional form — the SDP leaf), NO degree-{d} SoS
refutation of the ±1 booleanity system exists (cofactors of degree ≤ {2 * d}).
Structurally identical to Xor3Duality.petersen_no_refutation. -/
theorem {nm}_no_refutation
    (hsq : ∀ s : MvPolynomial (Fin {N}) ℚ, s.totalDegree ≤ {d} →
      0 ≤ pe_{nm} (s ^ 2)) :
    IsEmpty (SOSRefutation {nm}System {d} (fun _ => {2 * d})) := by
  refine no_refutation _ {d} (fun _ => {2 * d}) pe_{nm} pe_{nm}_one hsq ?_
  intro i p _
  rw [show pe_{nm} (p * {nm}System i) = pe_{nm} ((X i ^ 2 - 1) * p) from by
    rw [mul_comm]; rfl]
  exact {nm}_bool_kill i p

#print axioms {nm}_no_refutation
"""
    return lines, 3


@dataclass
class PseudoExpectationDualityEmitter(Emitter):
    """Emit the pseudo-expectation / SoS-duality (no-refutation) certificate: a
    self-contained Lean file with the abstract ``no_refutation`` obstruction
    (copied verbatim from the proven ``KnapsackSOS.Duality``) plus, per instance,
    a support/parity-weighted pseudoexpectation, its unconditional multilinear
    kill (``Xᵢ² − Xᵢ`` for 0/1, ``Xᵢ² − 1`` for ±1), and the conditional master
    ``*_no_refutation`` (PSD leaf ``hsq`` supplied as a hypothesis).

    Models the kernel-green ``examples/g1_floors/lean/Duality.lean`` /
    ``Xor3Duality.lean`` — same lemma names, same tactics."""

    def __post_init__(self):
        self.kind = "pe_duality"

    def emit_units(self, fam, profile: LeanProfile):
        # Single unit: the shared preamble is emitted once, so the whole family
        # renders as one file (no per-instance sharding of the preamble).
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        parts: list[str] = [_PREAMBLE]
        # Shared proven theorems in the preamble: no_refutation, support_single_add,
        # mem_oddSet, oddSet_add, oddSet_add_two (the multilinearization scaffolding).
        nthm = 5
        for inst in fam.instances:
            cert: PeDualityCertificate = inst.payload  # type: ignore[assignment]
            if cert.mode == "bool":
                body, n = _emit_bool_instance(cert)
            else:
                body, n = _emit_parity_instance(cert)
            parts.append(body)
            nthm += n
        return "\n".join(parts), nthm


def pe_duality_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a pe-duality family (kind='pe_duality').

    ``spec``: a callable ``pt -> {"n_vars": int, "degree": int, "mode":
    "bool"|"parity", "square_moments": optional}`` (or a ``(n_vars, degree[,
    mode])`` tuple).  Refuses (at certification) a non-positive dimension/degree,
    an unknown mode, ``2*degree >= n_vars``, an ``E 1 != 1`` weight, a
    non-vanishing kill, or a negative supplied square-moment."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("pe_duality", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid certs, negative controls, print emitted Lean --------
    print("=== positive: knapsack-style 0/1 system, N=5 vars, degree d=1 ===")
    cert_bool = pe_duality_certificate("knap_n5_d1", 5, 1, mode="bool")
    print(f"  cert OK: name={cert_bool.name}, N={cert_bool.n_vars}, "
          f"d={cert_bool.degree}, mode={cert_bool.mode}")

    print("\n=== positive: 3-XOR-style ±1 system, N=7 vars, degree d=2, "
          "with PSD moment data ===")
    cert_par = pe_duality_certificate(
        "xor_n7_d2", 7, 2, mode="parity", square_moments=(1, sp.Rational(3, 2), 0)
    )
    print(f"  cert OK: name={cert_par.name}, N={cert_par.n_vars}, "
          f"d={cert_par.degree}, mode={cert_par.mode}")

    print("\n=== NEGATIVE CONTROL: unknown mode (expect ValueError) ===")
    try:
        pe_duality_certificate("bad", 5, 1, mode="tropical")
        raise SystemExit("FAIL: unknown mode was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: truncation too tight, 2d >= N "
          "(expect ValueError) ===")
    try:
        pe_duality_certificate("bad", 4, 2, mode="bool")  # 2*2 = 4 >= 4
        raise SystemExit("FAIL: 2d >= N was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: negative supplied square-moment "
          "(bad PSD leaf, expect ValueError) ===")
    try:
        pe_duality_certificate("bad", 7, 2, mode="parity", square_moments=(1, -1))
        raise SystemExit("FAIL: negative square-moment was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: non-positive degree (expect ValueError) ===")
    try:
        pe_duality_certificate("bad", 5, 0, mode="bool")
        raise SystemExit("FAIL: degree 0 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (two instances: one bool, one parity) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="knap_n5_d1",
                          corners=(), payload=cert_bool),
        CertifiedInstance(point={"case": 1}, lean_name="xor_n7_d2",
                          corners=(), payload=cert_par),
    ]

    class _View:
        instances = insts

    body, nthm = PseudoExpectationDualityEmitter().emit_body(
        _View(), LeanProfile(namespace=("PeDuality",))
    )
    print(f"\n-- {nthm} theorems (shared + per-instance) --\n")
    print(body)

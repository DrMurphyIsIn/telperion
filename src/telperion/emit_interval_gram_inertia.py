"""Interval-Gram-inertia emitter -- kernel-certified inertia (posIndex, defect) of EVERY
Hermitian matrix inside a rational interval box.

THE SHAPE THAT HAD NO CERTIFICATE TYPE
--------------------------------------
Every D2 / D3 / T3 numeric instance of the Mirrormere program ends in the same sentence:
"this Arb-enclosed Hermitian matrix has negative index exactly q (or is PSD)".  The existing
emitters only touch pieces of it:

  * ``psd_form``        -- exact rational PSD of ONE explicit matrix (no interval, no negative part);
  * ``hermitian_moment``/``rank_trace_scalar`` -- scalar shadows (trace / rank counts);
  * ``rayleigh_gram``   -- ONE Rayleigh direction, not a subspace pair;
  * ``two_moment_count``-- an eigenvalue COUNT from two moments, not a signature.

None of them certifies the INERTIA of an INTERVAL matrix.  This emitter does: given rational
entrywise bounds ``lo <= G <= hi``, it certifies the exact signature ``(p, q)`` shared by every
Hermitian ``G`` in the box.

THE CERTIFICATE
---------------
Untrusted Python computes, in exact rationals:

  * the midpoint ``M = (lo + hi) / 2`` and the half-width ``w = max_ij (hi_ij - lo_ij) / 2``;
  * an exact congruence ``B^T M B = D`` (symmetric Gaussian elimination -- the same exact-rational
    LDL^T primitive ``emit_psd_form`` uses, here run to a full diagonalization with symmetric
    pivoting), giving the midpoint's Sylvester signature directly;
  * the witness bases ``X`` (the columns of ``B`` at positive pivots) and ``Y`` (at negative
    pivots), each column rescaled to absolute-sum one, so the compressed forms
    ``C_X = X^T M X`` and ``C_Y = Y^T (-M) Y`` are DIAGONAL with entries ``c_k > 0``;
  * the margins ``delta_X = min_k (C_X)_kk``, ``delta_Y = min_k (C_Y)_kk`` and the column-norm
    constants ``S_X = p``, ``S_Y = q`` (one per unit-abs-sum column).

The certificate is SOUND when ``w * S < delta`` on both sides, because for any ``G`` in the box

    |x^T (G - M) x| <= w * (sum_i |x_i|)^2 ,

and with ``x = X v`` and unit-abs-sum columns, ``(sum_i |x_i|)^2 <= S * |v|^2`` (Cauchy-Schwarz).
So the compressed form of ``G`` obeys ``v^T (X^T G X) v >= (delta - w*S) |v|^2 > 0``: the Hermitian
form of ``G`` is positive definite on a p-dimensional subspace, and ``-G``'s on a q-dimensional one.
Sylvester's law (RHLinalg ``finrank_le_posIndex_of_posDefOn``) turns those into the LOWER bounds
``p <= posIndex hG`` and ``q <= posIndex hG.neg``; the UPPER bounds come free from
``posIndex hG + posIndex hG.neg <= n`` (two forms cannot both be positive definite on intersecting
subspaces) together with ``p + q = n``.  Emitted theorem:

    theorem <name> (G : Matrix (Fin n) (Fin n) R) (hG : G.IsHermitian)
        (hlo : forall i j, lo i j <= G i j) (hhi : forall i j, G i j <= hi i j) :
        RHLinalg.posIndex hG = p AND RHInertia.defect hG = q

ISLAND PIN (the documented risk)
--------------------------------
``posIndex`` / ``PosDefOn`` / ``finrank_le_posIndex_of_posDefOn`` are NOT upstream Mathlib: they are
the ported RHLinalg block (Apache-2.0, anthropics zeta-23-lean, Lean v4.32.0) that lives on the
``hermitian_moment`` and ``zeta_zero_localization`` islands.  The emitted Lean therefore imports
``RHLinalg`` plus this module's own prelude (:func:`interval_gram_inertia_prelude_lean`), and the
emitter is island-pinned to v4.32.0.  Only the REAL-SYMMETRIC case is certified here; complex
Hermitian instances need the 2n real embedding (inertia doubles), which is NOT built -- an instance
over C is refused rather than faked.

REFUSALS (the anti-phantom face)
--------------------------------
``interval_gram_inertia_certificate`` refuses, loudly and by name:

  * a non-symmetric box (``lo`` or ``hi`` not symmetric) -- the hypothesis set could be EMPTY of
    Hermitian matrices, and the theorem would be vacuously true (the phantom);
  * ``lo_ij > hi_ij`` anywhere (an empty box -- the same phantom);
  * a SINGULAR midpoint (a zero pivot in the congruence): the box straddles a zero eigenvalue and
    has no well-defined shared signature;
  * ``p + q != n`` (the claimed signature does not fill the dimension);
  * ``p == 0`` or ``q == 0``: a definite box is ``psd_form``'s job, and ``Fin 0`` witness matrices
    have no matrix literal -- refused rather than emitted degenerately;
  * ``w * S >= delta`` on either side: the box is WIDER than the pivot margin can absorb, so the
    signature is not constant on the box (or our witnesses are too weak to show it is).  This is the
    "box straddling an eigenvalue sign" refusal, and it is what the negative control forges past.

conjecture1_proved = False -- this is a finite, kernel-checkable linear-algebra instrument, not a
step toward RH.  Nothing here says anything about zeta.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# --------------------------------------------------------------------------------------
# The certificate
# --------------------------------------------------------------------------------------


@dataclass(frozen=True)
class IntervalGramInertiaCert:
    """One interval box and its kernel-checkable inertia witness.

    ``lo`` / ``hi`` are the rational entrywise bounds (symmetric, ``lo <= hi``); ``mid`` their exact
    midpoint and ``w`` the largest half-width.  ``X`` (n x p) and ``Y`` (n x q) are the witness
    bases with unit absolute-sum columns; ``cx`` / ``cy`` are the DIAGONALS of the compressed forms
    ``X^T M X`` and ``Y^T (-M) Y`` (both strictly positive); ``delta_x`` / ``delta_y`` their minima
    and ``s_x = p`` / ``s_y = q`` the Cauchy-Schwarz column constants.  The claimed signature is
    ``(p, q)`` with ``p + q = n``.
    """

    n: int
    lo: tuple
    hi: tuple
    mid: tuple
    w: sp.Rational
    p: int
    q: int
    x_basis: tuple            # n x p, tuple of rows
    y_basis: tuple            # n x q, tuple of rows
    cx: tuple                 # length p, the positive diagonal of X^T M X
    cy: tuple                 # length q, the positive diagonal of Y^T (-M) Y
    delta_x: sp.Rational
    delta_y: sp.Rational

    @property
    def s_x(self) -> int:
        """Cauchy-Schwarz constant for X: the columns have absolute-sum one, so it is p."""
        return self.p

    @property
    def s_y(self) -> int:
        return self.q

    @property
    def margin_x(self) -> sp.Rational:
        """delta_X - w * S_X: strictly positive exactly when the box is narrow enough."""
        return sp.Rational(self.delta_x - self.w * self.s_x)

    @property
    def margin_y(self) -> sp.Rational:
        return sp.Rational(self.delta_y - self.w * self.s_y)


def _to_matrix(rows) -> sp.Matrix:
    return sp.Matrix([[sp.nsimplify(sp.Rational(v)) for v in row] for row in rows])


def _congruence_diagonalize(M: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix]:
    """Exact rational congruence ``B^T M B = D`` (D diagonal) by symmetric Gaussian elimination.

    This is ``emit_psd_form``'s completing-the-square LDL^T primitive run to a FULL diagonalization
    with symmetric pivoting, so it handles indefinite matrices (which ``psd_certificate`` refuses)
    and returns the change of basis, not just the pivots.  Raises ``ValueError`` when a trailing
    block is entirely zero (a singular midpoint: the box straddles a zero eigenvalue).
    """
    n = M.rows
    B = sp.eye(n)
    for k in range(n):
        guard = 0
        while True:
            guard += 1
            if guard > 2 * n + 4:  # pragma: no cover - structural safety net
                raise ValueError("interval_gram_inertia REFUSED: congruence failed to pivot")
            A = (B.T * M * B).applyfunc(sp.nsimplify)
            if A[k, k] != 0:
                break
            j = next((j for j in range(k + 1, n) if A[j, j] != 0), None)
            if j is not None:
                B.col_swap(k, j)
                continue
            j = next((j for j in range(k + 1, n) if A[k, j] != 0), None)
            if j is not None:
                B[:, k] = B[:, k] + B[:, j]
                continue
            if any(A[i, l] != 0 for i in range(k, n) for l in range(k, n)):
                j2 = next(i for i in range(k + 1, n)
                          if any(A[i, l] != 0 for l in range(k, n)))
                B.col_swap(k, j2)
                continue
            raise ValueError(
                "interval_gram_inertia REFUSED: the midpoint matrix is SINGULAR (a zero pivot in "
                "the exact congruence) -- the box straddles a zero eigenvalue and has no constant "
                "signature"
            )
        A = (B.T * M * B).applyfunc(sp.nsimplify)
        d = A[k, k]
        for i in range(k + 1, n):
            f = sp.nsimplify(A[i, k] / d)
            if f != 0:
                B[:, i] = B[:, i] - f * B[:, k]
    D = (B.T * M * B).applyfunc(sp.nsimplify)
    return B, D


def _normalized_column(B: sp.Matrix, idx: int) -> tuple[sp.Matrix, sp.Rational]:
    """Column ``idx`` of ``B`` rescaled to absolute-sum one; returns (column, scale)."""
    col = B[:, idx]
    s = sp.Rational(sum(abs(sp.Rational(v)) for v in col))
    if s == 0:  # pragma: no cover - B is invertible, so no column vanishes
        raise ValueError("interval_gram_inertia REFUSED: a witness column vanished")
    return (col / s).applyfunc(sp.nsimplify), s


def interval_gram_inertia_certificate(lo, hi, claimed=None) -> IntervalGramInertiaCert:
    """Build and EXACTLY self-check an interval-Gram-inertia certificate.

    ``lo`` / ``hi``: square rational matrices (sequences of rows) with ``lo <= hi`` entrywise, both
    SYMMETRIC.  ``claimed``: optional ``(p, q)`` -- when supplied it must match the computed
    signature (a mismatch is refused, never silently corrected).

    See the module docstring for the full refusal list.  Every refusal is a ``ValueError`` naming
    the reason; nothing false and nothing vacuous is ever emitted.
    """
    L, H = _to_matrix(lo), _to_matrix(hi)
    n = L.rows
    if n == 0 or L.cols != n or H.rows != n or H.cols != n:
        raise ValueError(
            f"interval_gram_inertia REFUSED: need equal non-empty square bounds, got "
            f"{L.rows}x{L.cols} and {H.rows}x{H.cols}")
    if L != L.T or H != H.T:
        raise ValueError(
            "interval_gram_inertia REFUSED: the box bounds must be SYMMETRIC -- an asymmetric box "
            "may contain NO Hermitian matrix at all, making the emitted theorem vacuously true "
            "(the phantom)")
    for i in range(n):
        for j in range(n):
            if L[i, j] > H[i, j]:
                raise ValueError(
                    f"interval_gram_inertia REFUSED: empty box at ({i},{j}): lo={L[i, j]} > "
                    f"hi={H[i, j]} -- no matrix satisfies the hypotheses (the phantom)")
    M = ((L + H) / 2).applyfunc(sp.nsimplify)
    w = sp.Rational(max(sp.Rational(H[i, j] - L[i, j]) for i in range(n) for j in range(n))) / 2
    B, D = _congruence_diagonalize(M)
    pos = [i for i in range(n) if D[i, i] > 0]
    neg = [i for i in range(n) if D[i, i] < 0]
    if len(pos) + len(neg) != n:
        raise ValueError(
            "interval_gram_inertia REFUSED: p + q != n (a zero pivot survived the congruence) -- "
            "the midpoint is singular")
    p, q = len(pos), len(neg)
    if claimed is not None and tuple(claimed) != (p, q):
        raise ValueError(
            f"interval_gram_inertia REFUSED: claimed signature {tuple(claimed)} != the exact "
            f"midpoint signature ({p}, {q})")
    if p == 0 or q == 0:
        raise ValueError(
            f"interval_gram_inertia REFUSED: definite box (p={p}, q={q}) -- a definite interval is "
            f"emit_psd_form's shape, and a Fin 0 witness basis has no Lean matrix literal")
    xcols, cx = [], []
    for i in pos:
        col, s = _normalized_column(B, i)
        xcols.append(col)
        cx.append(sp.nsimplify(sp.Rational(D[i, i]) / (s * s)))
    ycols, cy = [], []
    for i in neg:
        col, s = _normalized_column(B, i)
        ycols.append(col)
        cy.append(sp.nsimplify(-sp.Rational(D[i, i]) / (s * s)))
    X = sp.Matrix.hstack(*xcols)
    Y = sp.Matrix.hstack(*ycols)
    # exact self-checks: the compressed forms really are the claimed diagonals.
    CX = (X.T * M * X).applyfunc(sp.nsimplify)
    CY = (Y.T * (-M) * Y).applyfunc(sp.nsimplify)
    for k in range(p):
        for l in range(p):
            want = cx[k] if k == l else sp.Integer(0)
            if sp.nsimplify(CX[k, l] - want) != 0:
                raise ValueError(
                    f"interval_gram_inertia REFUSED: X^T M X is not the claimed diagonal at "
                    f"({k},{l}): {CX[k, l]} != {want}")
    for k in range(q):
        for l in range(q):
            want = cy[k] if k == l else sp.Integer(0)
            if sp.nsimplify(CY[k, l] - want) != 0:
                raise ValueError(
                    f"interval_gram_inertia REFUSED: Y^T (-M) Y is not the claimed diagonal at "
                    f"({k},{l}): {CY[k, l]} != {want}")
    for k in range(p):
        if sp.Rational(sum(abs(sp.Rational(v)) for v in X[:, k])) != 1:
            raise ValueError("interval_gram_inertia REFUSED: X column absolute-sum is not 1")
    for k in range(q):
        if sp.Rational(sum(abs(sp.Rational(v)) for v in Y[:, k])) != 1:
            raise ValueError("interval_gram_inertia REFUSED: Y column absolute-sum is not 1")
    delta_x = min(cx)
    delta_y = min(cy)
    cert = IntervalGramInertiaCert(
        n=n,
        lo=tuple(tuple(v for v in L.row(i)) for i in range(n)),
        hi=tuple(tuple(v for v in H.row(i)) for i in range(n)),
        mid=tuple(tuple(v for v in M.row(i)) for i in range(n)),
        w=sp.Rational(w), p=p, q=q,
        x_basis=tuple(tuple(v for v in X.row(i)) for i in range(n)),
        y_basis=tuple(tuple(v for v in Y.row(i)) for i in range(n)),
        cx=tuple(cx), cy=tuple(cy),
        delta_x=sp.Rational(delta_x), delta_y=sp.Rational(delta_y),
    )
    if cert.margin_x <= 0:
        raise ValueError(
            f"interval_gram_inertia REFUSED: the box is WIDER than the positive-side pivot margin "
            f"(w*S_X = {cert.w * cert.s_x} >= delta_X = {cert.delta_x}) -- the signature is not "
            f"certifiably constant on this box (it may straddle an eigenvalue sign)")
    if cert.margin_y <= 0:
        raise ValueError(
            f"interval_gram_inertia REFUSED: the box is WIDER than the negative-side pivot margin "
            f"(w*S_Y = {cert.w * cert.s_y} >= delta_Y = {cert.delta_y}) -- the signature is not "
            f"certifiably constant on this box (it may straddle an eigenvalue sign)")
    return cert


def certify_interval_gram_inertia_point(family, pt, name):
    """Certify one interval-Gram-inertia instance: ``(CertifiedInstance, 1)``.

    ``family.special[1](pt)`` returns ``(lo, hi)`` or ``(lo, hi, (p, q))``.
    """
    spec = family.special[1](pt)
    if len(spec) == 3:
        lo, hi, claimed = spec
    else:
        lo, hi = spec
        claimed = None
    cert = interval_gram_inertia_certificate(lo, hi, claimed)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# --------------------------------------------------------------------------------------
# Lean rendering
# --------------------------------------------------------------------------------------


def _mat_lean(rows) -> str:
    """A rational matrix as the Lean `!![a, b; c, d]` literal (single column -> `!![a; b]`)."""
    return "!![" + "; ".join(", ".join(rat_lean(v) for v in row) for row in rows) + "]"


def _vec_lean(vals) -> str:
    return "![" + ", ".join(rat_lean(v) for v in vals) + "]"


def _diag_lean(diag) -> str:
    n = len(diag)
    rows = [[diag[i] if i == j else sp.Integer(0) for j in range(n)] for i in range(n)]
    return _mat_lean(rows)


def _neg_rows(rows) -> tuple:
    return tuple(tuple(-sp.Rational(v) for v in row) for row in rows)


def interval_gram_inertia_prelude_lean() -> str:
    """The RHInertia prelude: the interval-to-inertia bridge over the ported RHLinalg block.

    Five general lemmas, all proof-complete and axiom-clean, none of them instance-specific:

      * ``hermForm_neg`` / ``defect`` -- the negative-index vocabulary (``defect`` is definitionally
        the ``DefectDictionary.defect`` of the zeta_zero_localization island);
      * ``posIndex_add_posIndex_neg_le`` -- ``n_+(A) + n_+(-A) <= n``, the UPPER half of Sylvester's
        law, proved from ``posIndex_eq_max_finrank_posDefOn`` and the fact that a form and its
        negative cannot both be positive definite on a shared nonzero vector;
      * ``card_le_posIndex_of_compress_posDef`` -- the LOWER half: a compressed form ``X^H A X`` that
        is positive definite exhibits a ``card p``-dimensional ``PosDefOn`` subspace (``X`` is then
        automatically injective), so ``card p <= posIndex hA``.  This is the same mechanism
        ``offline_pairs_le_defect`` uses, made generic in the witness basis;
      * ``compress_posDef_of_interval`` -- the INTERVAL step: entrywise ``|G - M| <= w`` plus a
        diagonal-dominant margin ``delta`` on the compressed midpoint form plus ``w * S < delta``
        forces the compressed form of every ``G`` in the box to be positive definite;
      * ``inertia_eq_of_witnesses`` -- the assembly: two witness bases with ``p + q = n`` pin the
        signature exactly.

    conjecture1_proved = False.
    """
    return _PRELUDE


_PRELUDE = r'''/-
RHInertia -- the interval-to-inertia bridge for Telperion's `interval_gram_inertia` emitter.

Built on the ported RHLinalg block (Apache-2.0, anthropics zeta-23-lean, Lean v4.32.0): `posIndex`,
`hermForm`, `PosDefOn`, `finrank_le_posIndex_of_posDefOn`, `posIndex_eq_max_finrank_posDefOn`.
Every lemma here is general (no instance data) and proof-complete: no placeholder
tactic appears anywhere in this file.

`defect hA := posIndex hA.neg` is definitionally the `DefectDictionary.defect` of the
zeta_zero_localization island, so certificates emitted against this prelude are consumable there.

conjecture1_proved = False -- a finite linear-algebra instrument, not a step toward RH.
-/
import RHLinalg

noncomputable section
open Matrix Finset Submodule
namespace RHInertia
open RHLinalg

/-! ### Entry-reduction tactics

A bare `simp` reduces `!![...] i j` and `![...] i` at numeral indices, but its full simp set blows
the `isDefEq` heartbeat budget on 4x4 literals.  These macros wrap the minimal `simp only` set that
does the same job in seconds; every emitted instance uses them, so the emitted Lean stays short and
the set is maintained in ONE place. -/

/-- Reduce matrix/vector literal applications at numeral indices. -/
macro "inertia_entries" : tactic =>
  `(tactic| simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply])

/-- `inertia_entries`, also expanding `Finset.univ` sums over `Fin`. -/
macro "inertia_entries_sum" : tactic =>
  `(tactic| simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply])

/-- `inertia_entries_sum`, also unfolding matrix products and transposes. -/
macro "inertia_entries_mul" : tactic =>
  `(tactic| simp only [Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply])

/-- `simpa only` with the entry-reduction set. -/
macro "inertia_entries_using " t:term : tactic =>
  `(tactic| simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply] using $t)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `hermForm (-A) x = - hermForm A x`. -/
lemma hermForm_neg (A : Matrix n n 𝕜) (x : n → 𝕜) : hermForm (-A) x = - hermForm A x := by
  unfold hermForm; simp [neg_mulVec, dotProduct_neg]

/-- The **defect** (negative index) `n₋(A) = n₊(−A)`.  Definitionally identical to
`DefectDictionary.defect`. -/
def defect {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ := posIndex hA.neg

/-- **Upper half of Sylvester's law**: a Hermitian form and its negative cannot both be positive
definite on subspaces that meet nontrivially, so `n₊(A) + n₊(−A) ≤ n`. -/
theorem posIndex_add_posIndex_neg_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    posIndex hA + posIndex hA.neg ≤ Fintype.card n := by
  obtain ⟨W, hW, hWdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  obtain ⟨V, hV, hVdim⟩ := posIndex_eq_max_finrank_posDefOn hA.neg
  have hinf : W ⊓ V = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxW, hxV⟩ := hx
    simp only [Submodule.mem_bot]
    by_contra hne
    have h1 := hW x hxW hne
    have h2 := hV x hxV hne
    rw [hermForm_neg] at h2
    linarith
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W V
  rw [hinf] at hsup
  simp only [finrank_bot, add_zero] at hsup
  have hle : Module.finrank 𝕜 (W ⊔ V : Submodule 𝕜 (n → 𝕜)) ≤ Module.finrank 𝕜 (n → 𝕜) :=
    Submodule.finrank_le _
  rw [Module.finrank_fintype_fun_eq_card] at hle
  omega

/-- **Lower half of Sylvester's law, in witness form**: if the compressed form `Xᴴ A X` is positive
definite then `X` is injective and `range X` is a `card p`-dimensional `PosDefOn` subspace, so
`card p ≤ posIndex hA`.  (The mechanism behind `offline_pairs_le_defect`, generic in `X`.) -/
theorem card_le_posIndex_of_compress_posDef {p : Type*} [Fintype p] [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (X : Matrix n p 𝕜)
    (hpos : ∀ v : p → 𝕜, v ≠ 0 → 0 < hermForm (Xᴴ * A * X) v) :
    Fintype.card p ≤ posIndex hA := by
  set L : (p → 𝕜) →ₗ[𝕜] (n → 𝕜) := X.mulVecLin with hL
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    simp only [LinearMap.mem_ker] at hv
    simp only [Submodule.mem_bot]
    by_contra hne
    have hp := hpos v hne
    rw [hermForm_conj] at hp
    have hXv : X *ᵥ v = 0 := hv
    rw [hXv] at hp
    simp [hermForm] at hp
  have hW : PosDefOn A (LinearMap.range L) := by
    rintro _ ⟨v, rfl⟩ hne
    have hv : v ≠ 0 := by rintro rfl; exact hne (by simp [hL])
    have hp := hpos v hv
    rw [hermForm_conj] at hp
    exact hp
  have hfin := finrank_le_posIndex_of_posDefOn hA hW
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at hfin

/-- The real Hermitian form, entrywise. -/
lemma hermForm_real {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    hermForm A x = ∑ i, ∑ j, x i * A i j * x j := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Column absolute-sums control the absolute-sum of `X *ᵥ v`. -/
lemma sum_abs_mulVec_le {N P : ℕ} (X : Matrix (Fin N) (Fin P) ℝ) (s : Fin P → ℝ)
    (hs : ∀ k, ∑ i, |X i k| ≤ s k) (v : Fin P → ℝ) :
    ∑ i, |(X *ᵥ v) i| ≤ ∑ k, s k * |v k| := by
  have step1 : ∀ i, |(X *ᵥ v) i| ≤ ∑ k, |X i k| * |v k| := by
    intro i
    have h : (X *ᵥ v) i = ∑ k, X i k * v k := rfl
    rw [h]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    simp [abs_mul]
  calc ∑ i, |(X *ᵥ v) i| ≤ ∑ i, ∑ k, |X i k| * |v k| := Finset.sum_le_sum (fun i _ => step1 i)
    _ = ∑ k, (∑ i, |X i k|) * |v k| := by rw [Finset.sum_comm]; simp [Finset.sum_mul]
    _ ≤ ∑ k, s k * |v k| :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hs k) (abs_nonneg _))

/-- An entrywise `w`-perturbation moves the real Hermitian form by at most `w * (∑ |u i|)²`. -/
lemma abs_hermForm_diff_le {N : ℕ} (G M : Matrix (Fin N) (Fin N) ℝ) (w : ℝ)
    (hw : ∀ i j, |G i j - M i j| ≤ w) (u : Fin N → ℝ) :
    |∑ i, ∑ j, u i * (G i j - M i j) * u j| ≤ w * (∑ i, |u i|) ^ 2 := by
  calc |∑ i, ∑ j, u i * (G i j - M i j) * u j|
      ≤ ∑ i, |∑ j, u i * (G i j - M i j) * u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |u i| * w * |u j| := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hw i j) (abs_nonneg _)) (abs_nonneg _)
    _ = w * (∑ i, |u i|) ^ 2 := by
        have h1 : ∀ i : Fin N, ∑ j, |u i| * w * |u j| = (|u i| * w) * ∑ j, |u j| := by
          intro i; rw [Finset.mul_sum]
        simp_rw [h1]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- **The interval step.**  If `G` lies entrywise within `w` of `M`, the compressed midpoint form
`C = Xᵀ M X` dominates `δ • I`, the columns of `X` have absolute-sums bounded by `s` with
`S = ∑ s k ^ 2`, and `w * S < δ`, then the compressed form of `G` is positive definite. -/
theorem compress_posDef_of_interval {N P : ℕ}
    (G M : Matrix (Fin N) (Fin N) ℝ) (X : Matrix (Fin N) (Fin P) ℝ)
    (C : Matrix (Fin P) (Fin P) ℝ) (s : Fin P → ℝ) (w δ S : ℝ)
    (hw : ∀ i j, |G i j - M i j| ≤ w) (hw0 : 0 ≤ w)
    (hs : ∀ k, ∑ i, |X i k| ≤ s k)
    (hS : S = ∑ k, (s k) ^ 2)
    (hC : C = Xᵀ * M * X)
    (hd : ∀ v : Fin P → ℝ, δ * (∑ k, (v k) ^ 2) ≤ ∑ k, ∑ l, v k * C k l * v l)
    (hslack : w * S < δ) :
    ∀ v : Fin P → ℝ, v ≠ 0 → 0 < hermForm (Xᴴ * G * X) v := by
  intro v hv
  have hXH : (Xᴴ : Matrix (Fin P) (Fin N) ℝ) = Xᵀ := Matrix.conjTranspose_eq_transpose_of_trivial X
  have key : hermForm (Xᴴ * G * X) v = hermForm G (X *ᵥ v) := hermForm_conj G X v
  have hMcomp : hermForm M (X *ᵥ v) = ∑ k, ∑ l, v k * C k l * v l := by
    rw [← hermForm_conj M X v, hC, ← hXH, hermForm_real]
  have hsplit : hermForm G (X *ᵥ v)
      = hermForm M (X *ᵥ v) + ∑ i, ∑ j, (X *ᵥ v) i * (G i j - M i j) * (X *ᵥ v) j := by
    rw [hermForm_real, hermForm_real, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hpert := abs_hermForm_diff_le G M w hw (X *ᵥ v)
  have habs : -(w * (∑ i, |(X *ᵥ v) i|) ^ 2)
      ≤ ∑ i, ∑ j, (X *ᵥ v) i * (G i j - M i j) * (X *ᵥ v) j := (abs_le.mp hpert).1
  have hsum : (∑ i, |(X *ᵥ v) i|) ≤ ∑ k, s k * |v k| := sum_abs_mulVec_le X s hs v
  have hsum0 : 0 ≤ ∑ i, |(X *ᵥ v) i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hcs : (∑ k, s k * |v k|) ^ 2 ≤ S * ∑ k, (v k) ^ 2 := by
    rw [hS]
    simpa [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s (fun k => |v k|)
  have hsq : (∑ i, |(X *ᵥ v) i|) ^ 2 ≤ S * ∑ k, (v k) ^ 2 :=
    le_trans (pow_le_pow_left₀ hsum0 hsum 2) hcs
  have hvpos : 0 < ∑ k, (v k) ^ 2 := by
    rcases Function.ne_iff.mp hv with ⟨k, hk⟩
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨k, Finset.mem_univ k, ?_⟩
    have hk' : v k ≠ 0 := hk
    positivity
  have hdelta := hd v
  rw [key, hsplit, hMcomp]
  nlinarith [mul_le_mul_of_nonneg_left hsq hw0, mul_pos (sub_pos.mpr hslack) hvpos]

/-- **The assembly.**  Witness bases of sizes `P` and `Q` with `P + Q = N` pin the signature of `G`
exactly: `posIndex hG = P` and `defect hG = Q`. -/
theorem inertia_eq_of_witnesses {N P Q : ℕ}
    {G : Matrix (Fin N) (Fin N) ℝ} (hG : G.IsHermitian)
    (X : Matrix (Fin N) (Fin P) ℝ) (Y : Matrix (Fin N) (Fin Q) ℝ)
    (hpq : P + Q = N)
    (hX : ∀ v : Fin P → ℝ, v ≠ 0 → 0 < hermForm (Xᴴ * G * X) v)
    (hY : ∀ v : Fin Q → ℝ, v ≠ 0 → 0 < hermForm (Yᴴ * (-G) * Y) v) :
    posIndex hG = P ∧ defect hG = Q := by
  have h1 := card_le_posIndex_of_compress_posDef hG X hX
  have h2 := card_le_posIndex_of_compress_posDef hG.neg Y hY
  have h3 := posIndex_add_posIndex_neg_le hG
  simp only [Fintype.card_fin] at h1 h2 h3
  constructor
  · omega
  · show posIndex hG.neg = Q
    omega

end RHInertia
'''


# --------------------------------------------------------------------------------------
# The emitter
# --------------------------------------------------------------------------------------


@dataclass
class IntervalGramInertiaEmitter(Emitter):
    """Emit the interval-inertia theorem `posIndex hG = p ∧ defect hG = q` for every Hermitian `G`
    inside a rational box, against the RHInertia prelude over the ported RHLinalg block."""

    def __post_init__(self):
        self.kind = "interval_gram_inertia"
        self.requires_prelude = (
            "RHInertia.compress_posDef_of_interval",
            "RHInertia.inertia_eq_of_witnesses",
            "RHInertia.defect",
        )

    # -- the pure-ℝ arithmetic core (the negative-control route) -------------------------
    def _emit_compress_margin(self, cert: IntervalGramInertiaCert, name: str) -> str:
        """The certificate's LOAD-BEARING arithmetic, as a standalone `import Mathlib` theorem.

        For every nonzero `v`, the compressed midpoint form (the diagonal `cx`) exceeds the
        interval slack `w * S_X`:

            0 < (∑ cx_k v_k²) − (w * S_X) * (∑ v_k²).

        True exactly when `min_k cx_k > w * S_X`, which is the certificate's soundness condition.
        Corrupt a pivot `cx_k`, the width `w`, or the constant `S_X` and the inequality becomes
        false -- `nlinarith` fails and the Lean KERNEL rejects the proof.  This is what the
        negative-control adapter forges.
        """
        p = cert.p
        vs = [f"v{k}" for k in range(p)]
        binders = " ".join(vs)
        quad = " + ".join(f"{rat_lean(cert.cx[k])} * {vs[k]} ^ 2" for k in range(p))
        norm = " + ".join(f"{vs[k]} ^ 2" for k in range(p))
        hints = ", ".join(f"sq_nonneg {v}" for v in vs)
        return (
            f"-- {name}: the arithmetic core of one interval_gram_inertia certificate.  The "
            f"compressed\n"
            f"-- midpoint form (diagonal cx = {tuple(str(c) for c in cert.cx)}) strictly dominates "
            f"the interval slack\n"
            f"-- w * S_X = {cert.w} * {cert.s_x} = {sp.Rational(cert.w * cert.s_x)} on every "
            f"nonzero direction.  Pure ℝ arithmetic;\n"
            f"-- a corrupted pivot, width, or column constant makes it FALSE and the kernel "
            f"rejects it.\n"
            f"-- conjecture1_proved = False.\n"
            f"theorem {name} ({binders} : ℝ) (hv : 0 < {norm}) :\n"
            f"    0 < ({quad}) - ({rat_lean(sp.Rational(cert.w * cert.s_x))}) * ({norm}) := by\n"
            f"  nlinarith [{hints}, hv]\n"
        )

    # -- the witness-side obligation block ----------------------------------------------
    def _emit_side(self, cert: IntervalGramInertiaCert, *, positive: bool) -> str:
        n = cert.n
        if positive:
            basis, diag, delta, dim, tag = (
                cert.x_basis, cert.cx, cert.delta_x, cert.p, "X")
            mid = cert.mid
            gterm = "G"
        else:
            basis, diag, delta, dim, tag = (
                cert.y_basis, cert.cy, cert.delta_y, cert.q, "Y")
            mid = _neg_rows(cert.mid)
            gterm = "(-G)"
        Bl = _mat_lean(basis)
        Ml = _mat_lean(mid)
        Cl = _diag_lean(diag)
        sl = _vec_lean([sp.Integer(1)] * dim)
        hints = ", ".join(f"sq_nonneg (v {k})" for k in range(dim))
        hname = "hX" if positive else "hY"
        return (
            f"  have {hname} : ∀ v : Fin {dim} → ℝ, v ≠ 0 →\n"
            f"      0 < RHLinalg.hermForm (({Bl} : Matrix (Fin {n}) (Fin {dim}) ℝ)ᴴ * {gterm} *\n"
            f"        ({Bl} : Matrix (Fin {n}) (Fin {dim}) ℝ)) v := by\n"
            f"    refine RHInertia.compress_posDef_of_interval {gterm} ({Ml}) ({Bl}) ({Cl}) "
            f"{sl}\n"
            f"      ({rat_lean(cert.w)}) ({rat_lean(delta)}) {dim}\n"
            f"      ?_ (by norm_num) ?_ (by norm_num [Fin.sum_univ_succ]) ?_ ?_ (by norm_num)\n"
            f"    · intro i j\n"
            f"      fin_cases i <;> fin_cases j\n"
            + "".join(
                f"      · inertia_entries\n"
                f"        rw [abs_le]\n"
                f"        constructor <;> linarith only [lo_{i}_{j}, hi_{i}_{j}]\n"
                for i in range(n) for j in range(n))
            +
            f"    · intro k\n"
            f"      fin_cases k <;> inertia_entries_sum <;> norm_num\n"
            f"    · ext k l\n"
            f"      fin_cases k <;> fin_cases l <;> inertia_entries_mul <;> norm_num\n"
            f"    · intro v\n"
            f"      inertia_entries_sum <;> norm_num <;> nlinarith [{hints}]\n"
        )

    def _emit_inertia(self, cert: IntervalGramInertiaCert, name: str) -> str:
        n = cert.n
        lol = _mat_lean(cert.lo)
        hil = _mat_lean(cert.hi)
        lines = [
            f"-- {name}: certified inertia of EVERY real symmetric matrix in the rational box\n"
            f"-- lo ≤ G ≤ hi (n = {n}, half-width w = {cert.w}).  Signature (p, q) = "
            f"({cert.p}, {cert.q}).\n"
            f"-- Witness bases have unit absolute-sum columns; the compressed midpoint forms are\n"
            f"-- diagonal with margins delta_X = {cert.delta_x} > w*S_X = "
            f"{sp.Rational(cert.w * cert.s_x)} and\n"
            f"-- delta_Y = {cert.delta_y} > w*S_Y = {sp.Rational(cert.w * cert.s_y)}.  "
            f"Sylvester's law (RHLinalg) does the rest.\n"
            f"-- A finite linear-algebra certificate; says nothing about zeta.  "
            f"conjecture1_proved = False.\n"
            f"set_option maxHeartbeats 1000000 in\n"
            f"theorem {name} (G : Matrix (Fin {n}) (Fin {n}) ℝ) (hG : G.IsHermitian)\n"
            f"    (hlo : ∀ i j, ({lol} : Matrix (Fin {n}) (Fin {n}) ℝ) i j ≤ G i j)\n"
            f"    (hhi : ∀ i j, G i j ≤ ({hil} : Matrix (Fin {n}) (Fin {n}) ℝ) i j) :\n"
            f"    RHLinalg.posIndex hG = {cert.p} ∧ RHInertia.defect hG = {cert.q} := by\n"
        ]
        for i in range(n):
            for j in range(n):
                lines.append(
                    f"  have lo_{i}_{j} : ({rat_lean(cert.lo[i][j])} : ℝ) ≤ G {i} {j} := by\n"
                    f"    inertia_entries_using hlo {i} {j}\n")
        for i in range(n):
            for j in range(n):
                lines.append(
                    f"  have hi_{i}_{j} : G {i} {j} ≤ ({rat_lean(cert.hi[i][j])} : ℝ) := by\n"
                    f"    inertia_entries_using hhi {i} {j}\n")
        lines.append(self._emit_side(cert, positive=True))
        lines.append(self._emit_side(cert, positive=False))
        lines.append(
            "  exact RHInertia.inertia_eq_of_witnesses hG _ _ (by norm_num) hX hY\n")
        return "".join(lines)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        out: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: IntervalGramInertiaCert = inst.payload  # type: ignore[assignment]
            out.append(self._emit_inertia(cert, inst.lean_name))
            nthm += 1
        return "\n".join(out), nthm


def interval_gram_inertia_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an interval-Gram-inertia family (kind ``interval_gram_inertia``).

    ``spec``: ``pt -> (lo, hi)`` or ``pt -> (lo, hi, (p, q))`` -- rational symmetric entrywise
    bounds and an optional claimed signature (checked, never trusted)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("interval_gram_inertia", spec),
        constants=dict(constants or {}),
    )

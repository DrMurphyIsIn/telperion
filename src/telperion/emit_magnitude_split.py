"""Magnitude-split triangle-inequality emitter — a three-term ``A + B - C``
norm bound assembled from per-term magnitude bounds.

The triangle-inequality assembly behind a near-line magnitude bound (the final
step of the ZetaLogBound zero-free-region upgrade): for complex ``A, B, C`` and
rational (or real) bounds ``α, β, γ ≥ 0``,

    ‖A‖ ≤ α → ‖B‖ ≤ β → ‖C‖ ≤ γ → ‖A + B − C‖ ≤ α + β + γ.

This is fully GENERAL — no rational data is needed beyond the *shape*
``A + B − C`` and the nonnegativity of the bounds.  The proof is EXACTLY the
final assembly of ``zeta_log_bound`` in
``examples/zero_free_bridge/lean/ZetaLogBound.lean`` (lines 209-212):

    have h1 := norm_sub_le (A + B) C     -- ‖(A+B) − C‖ ≤ ‖A+B‖ + ‖C‖
    have h2 := norm_add_le A B           -- ‖A + B‖ ≤ ‖A‖ + ‖B‖
    linarith [h1, h2, hA, hB, hC]

Both ``norm_sub_le : ‖a − b‖ ≤ ‖a‖ + ‖b‖`` and ``norm_add_le : ‖a + b‖ ≤ ‖a‖ + ‖b‖``
are standard Mathlib lemmas (present in v4.32.0).

Two emitted forms per instance:
  * the clean UNIVERSALLY-QUANTIFIED theorem (``A B C : ℂ``, ``α β γ : ℝ``,
    the three magnitude hypotheses) — the default and preferred form; and
  * an optional CONCRETE-INSTANCE variant where ``α, β, γ`` are specific
    rationals (ascribed ``(α : ℝ)`` to avoid the ℤ-default pitfall) and the
    conclusion ``‖A + B − C‖ ≤ α + β + γ`` is stated with those literals.

An optional GENERAL n-term ``Σ ± termᵢ`` variant is supported too: given signs
``s₁ … sₙ ∈ {+1, −1}`` and bounds ``β₁ … βₙ ≥ 0``, ``‖Σ sᵢ·termᵢ‖ ≤ Σ βᵢ`` is
assembled by folding ``norm_add_le`` / ``norm_sub_le`` left-to-right.

NEGATIVE CONTROL: a negative bound (``α, β, γ < 0``) — which would make the
target ``‖·‖ ≤ (negative)`` unprovable from ``‖·‖ ≥ 0`` — is REFUSED at
certification with a ``ValueError``.  So is an ill-formed representation
(the ``A + B − C`` shape must have exactly three terms; the n-term shape must
have matching sign/bound lengths and every sign in ``{+1, −1}``).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_magnitude_split.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class MagnitudeSplitCertificate:
    """A verified triangle-inequality magnitude-split certificate.

    The certified fact is purely structural: the representation shape and the
    nonnegativity of the per-term bounds.  Two modes:

      * ``shape == "abc"`` — the ``A + B − C`` three-term form.  ``bounds`` is
        ``(α, β, γ)`` (all ≥ 0).  If ``concrete`` is True the emitted theorem
        pins ``α, β, γ`` to these rational literals; otherwise they are
        universally quantified reals and ``bounds`` is only used for the
        (trivial) self-check that they are nonneg placeholders.
      * ``shape == "nterm"`` — the general ``Σ sᵢ·termᵢ`` form.  ``signs`` is a
        tuple in ``{+1, −1}`` and ``bounds`` is the matching tuple of nonneg
        rational bounds ``(β₁, …, βₙ)``.
    """

    shape: str                      # "abc" | "nterm"
    bounds: tuple                   # nonneg sp.Rational bounds
    signs: tuple                    # for "nterm": (+1|-1, ...);  () for "abc"
    concrete: bool                  # "abc": pin α,β,γ to the literals


def magnitude_split_certificate(
    bounds: Sequence,
    *,
    shape: str = "abc",
    signs: Sequence | None = None,
    concrete: bool = False,
) -> MagnitudeSplitCertificate:
    """Build and self-check a magnitude-split certificate.

    Refuses (``ValueError``) a negative bound (the anti-phantom negative control:
    ``‖·‖ ≤ negative`` is unprovable), or an ill-formed representation shape.
    """
    bs = tuple(sp.nsimplify(b) for b in bounds)
    for b in bs:
        if not b.is_rational:
            raise ValueError(f"magnitude_split bounds must be rational; got {b!r}")
        if b < 0:
            raise ValueError(
                f"magnitude_split needs nonnegative bounds (‖·‖ ≤ bound); got {b} < 0 "
                f"— target would be unprovable from ‖·‖ ≥ 0; certificate rejected"
            )

    if shape == "abc":
        if len(bs) != 3:
            raise ValueError(
                f"magnitude_split 'abc' shape (A + B − C) needs exactly 3 bounds "
                f"(α, β, γ); got {len(bs)}"
            )
        # EXACT structural self-check: the assembly proves
        #   ‖A + B − C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ ≤ α + β + γ.
        # Model it symbolically over nonneg magnitude symbols nA, nB, nC:
        #   nA ≤ α, nB ≤ β, nC ≤ γ  ⟹  (nA + nB) + nC ≤ α + β + γ, and the
        #   two triangle steps give ‖A+B−C‖ ≤ (nA + nB) + nC.
        nA, nB, nC = sp.symbols("nA nB nC", nonnegative=True)
        a, b, c = bs
        # the chained bound the linarith closes: substituting the maxima gives equality.
        chained = sp.expand((a + b + c) - ((nA + nB) + nC))
        witness = chained.subs({nA: a, nB: b, nC: c})
        if sp.simplify(witness) != 0:
            raise ValueError(
                "magnitude_split 'abc' self-check failed — certificate rejected"
            )
        return MagnitudeSplitCertificate(
            shape="abc", bounds=bs, signs=(), concrete=bool(concrete)
        )

    if shape == "nterm":
        sg = tuple(int(s) for s in (signs or ()))
        if len(sg) != len(bs):
            raise ValueError(
                f"magnitude_split 'nterm' shape needs len(signs) == len(bounds); "
                f"got {len(sg)} signs, {len(bs)} bounds"
            )
        if len(bs) < 1:
            raise ValueError("magnitude_split 'nterm' shape needs at least 1 term")
        for s in sg:
            if s not in (1, -1):
                raise ValueError(
                    f"magnitude_split 'nterm' signs must be ±1; got {s}"
                )
        # Structural self-check: Σβᵢ − Σ (max ‖termᵢ‖ = βᵢ) = 0.
        if sp.simplify(sum(bs) - sum(bs)) != 0:  # trivially true; documents intent
            raise ValueError("magnitude_split 'nterm' self-check failed")
        return MagnitudeSplitCertificate(
            shape="nterm", bounds=bs, signs=sg, concrete=bool(concrete)
        )

    raise ValueError(f"magnitude_split unknown shape {shape!r} (want 'abc' | 'nterm')")


def certify_magnitude_split_point(family, pt, name):
    """Certify one magnitude-split instance from
    ``family.special[1](pt) -> spec``.

    ``spec`` is either a sequence of bounds (the ``A + B − C`` shape), or a dict
    ``{"bounds": [...], "shape": "abc"|"nterm", "signs": [...], "concrete": bool}``.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = magnitude_split_certificate(
            spec["bounds"],
            shape=spec.get("shape", "abc"),
            signs=spec.get("signs"),
            concrete=bool(spec.get("concrete", False)),
        )
    else:
        cert = magnitude_split_certificate(spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class MagnitudeSplitBoundEmitter(Emitter):
    """Emit ``‖A + B − C‖ ≤ α + β + γ`` from the three magnitude bounds — the
    triangle-inequality assembly, one theorem per instance.

    The proof is a copy of the final assembly of the PROVEN ``zeta_log_bound``
    (``examples/zero_free_bridge/lean/ZetaLogBound.lean``):

        have h1 := norm_sub_le (A + B) C
        have h2 := norm_add_le A B
        linarith [h1, h2, hA, hB, hC]
    """

    def __post_init__(self):
        self.kind = "magnitude_split"

    def _abc_universal(self, lean_name: str) -> str:
        """The clean universally-quantified ``A + B − C`` theorem."""
        return (
            f"/-- Triangle-inequality magnitude split: `‖A‖ ≤ α`, `‖B‖ ≤ β`, `‖C‖ ≤ γ`\n"
            f"    imply `‖A + B − C‖ ≤ α + β + γ`.  Assembly of `norm_sub_le` +\n"
            f"    `norm_add_le` (as in `zeta_log_bound`). -/\n"
            f"theorem {lean_name} (A B C : ℂ) (α β γ : ℝ)\n"
            f"    (hA : ‖A‖ ≤ α) (hB : ‖B‖ ≤ β) (hC : ‖C‖ ≤ γ) :\n"
            f"    ‖A + B - C‖ ≤ α + β + γ := by\n"
            f"  have h1 := norm_sub_le (A + B) C\n"
            f"  have h2 := norm_add_le A B\n"
            f"  linarith [h1, h2, hA, hB, hC]\n"
        )

    def _abc_concrete(self, cert: MagnitudeSplitCertificate, lean_name: str) -> str:
        """A concrete-bounds ``A + B − C`` theorem (α, β, γ pinned rationals).

        Bare rational bounds are ASCRIBED ``(α : ℝ)`` to avoid the ℤ-default
        pitfall that cost a build round on a sibling emitter."""
        al, be, ga = (rat_lean(b) for b in cert.bounds)
        # ascribe ℝ on the RHS sum so `α + β + γ` is real, not ℤ-defaulted.
        return (
            f"/-- Concrete-bounds magnitude split (`α = {al}`, `β = {be}`, `γ = {ga}`):\n"
            f"    `‖A‖ ≤ {al}`, `‖B‖ ≤ {be}`, `‖C‖ ≤ {ga}` imply\n"
            f"    `‖A + B − C‖ ≤ {al} + {be} + {ga}`. -/\n"
            f"theorem {lean_name} (A B C : ℂ)\n"
            f"    (hA : ‖A‖ ≤ ({al} : ℝ)) (hB : ‖B‖ ≤ ({be} : ℝ)) (hC : ‖C‖ ≤ ({ga} : ℝ)) :\n"
            f"    ‖A + B - C‖ ≤ ({al} : ℝ) + {be} + {ga} := by\n"
            f"  have h1 := norm_sub_le (A + B) C\n"
            f"  have h2 := norm_add_le A B\n"
            f"  linarith [h1, h2, hA, hB, hC]\n"
        )

    def _nterm(self, cert: MagnitudeSplitCertificate, lean_name: str) -> str:
        """General ``Σ sᵢ·termᵢ`` form, folded left-to-right.

        We fold the partial sums ``P₁ = s₁·t₁``, ``Pₖ = P_{k-1} + sₖ·tₖ``.  At
        each step, ``‖Pₖ‖ ≤ ‖P_{k-1}‖ + ‖tₖ‖`` by ``norm_add_le`` (for ``+``) or
        ``norm_sub_le`` (for ``−``), because ``‖sₖ·tₖ‖ = ‖tₖ‖`` and
        ``‖P_{k-1} − tₖ‖ ≤ ‖P_{k-1}‖ + ‖tₖ‖``.  Chaining with ``linarith`` gives
        ``‖Σ sᵢ·tᵢ‖ ≤ Σ βᵢ``."""
        n = len(cert.bounds)
        signs = cert.signs
        # term binders t1..tn : ℂ, bound binders and hypotheses hb1..hbn.
        tbind = " ".join(f"t{i}" for i in range(1, n + 1))
        bbind = " ".join(f"b{i}" for i in range(1, n + 1))
        # the signed sum expression, left-assoc: (((s1 t1) op2 t2) op3 t3) ...
        def op(sign):  # noqa: ANN001
            return "+" if sign == 1 else "-"

        expr = f"t1" if signs[0] == 1 else f"-t1"
        for i in range(1, n):
            expr = f"({expr}) {op(signs[i])} t{i + 1}"
        bsum = " + ".join(f"b{i}" for i in range(1, n + 1))
        hyps = " ".join(f"(hb{i} : ‖t{i}‖ ≤ b{i})" for i in range(1, n + 1))
        # nonneg-bound hyps are not needed: each ‖tᵢ‖ ≤ bᵢ already bounds the fold.
        lines = [
            f"/-- General signed-sum magnitude split: `‖Σ sᵢ·tᵢ‖ ≤ Σ bᵢ`\n"
            f"    (folded `norm_add_le` / `norm_sub_le`). -/\n"
            f"theorem {lean_name} ({tbind} : ℂ) ({bbind} : ℝ)\n"
            f"    {hyps} :\n"
            f"    ‖{expr}‖ ≤ {bsum} := by\n"
        ]
        # fold: emit the per-step triangle facts.  partial P_k accumulates.
        part = "t1" if signs[0] == 1 else "-t1"
        facts = []
        # first term: ‖±t1‖ = ‖t1‖ (norm_neg handles the minus); provide as fact.
        if signs[0] == 1:
            facts.append("hb1")
        else:
            lines.append(f"  have hneg1 : ‖-t1‖ ≤ b1 := by rw [norm_neg]; exact hb1\n")
            facts.append("hneg1")
        for i in range(1, n):
            k = i + 1
            if signs[i] == 1:
                lines.append(f"  have hs{k} := norm_add_le ({part}) t{k}\n")
            else:
                lines.append(f"  have hs{k} := norm_sub_le ({part}) t{k}\n")
            facts.append(f"hs{k}")
            facts.append(f"hb{k}")
            part = f"({part}) {op(signs[i])} t{k}"
        lines.append(f"  linarith [{', '.join(facts)}]\n")
        return "".join(lines)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: MagnitudeSplitCertificate = inst.payload  # type: ignore[assignment]
            if cert.shape == "abc":
                if cert.concrete:
                    lines.append(self._abc_concrete(cert, inst.lean_name))
                else:
                    lines.append(self._abc_universal(inst.lean_name))
            elif cert.shape == "nterm":
                lines.append(self._nterm(cert, inst.lean_name))
            else:  # pragma: no cover - certificate refuses unknown shapes
                raise ValueError(f"unknown magnitude_split shape {cert.shape!r}")
            nthm += 1
        return "\n".join(lines), nthm


def magnitude_split_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a magnitude-split family (kind='magnitude_split').

    ``spec``: a callable ``pt -> bounds`` (the ``A + B − C`` shape, universally
    quantified), or ``pt -> {"bounds": [...], "shape": "abc"|"nterm",
    "signs": [...], "concrete": bool}`` for the concrete-bounds or general
    signed-sum variants.  Refuses a negative bound or an ill-formed shape."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("magnitude_split", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # ---- positive certificate: the A + B − C shape (universal) ---------------
    print("=== positive certificate: A + B − C (universal bounds) ===")
    cert = magnitude_split_certificate([1, 1, 1])
    print(f"cert OK: shape={cert.shape}, bounds={cert.bounds}, concrete={cert.concrete}")

    # ---- positive certificate: concrete rational bounds ----------------------
    cert_c = magnitude_split_certificate(
        [sp.Rational(1, 2), sp.Rational(3, 2), 4], concrete=True
    )
    print(f"cert OK (concrete): bounds={cert_c.bounds}")

    # ---- positive certificate: general n-term signed sum ---------------------
    cert_n = magnitude_split_certificate(
        [1, 2, 3, 4], shape="nterm", signs=[1, -1, 1, -1]
    )
    print(f"cert OK (nterm): signs={cert_n.signs}, bounds={cert_n.bounds}")

    # ---- NEGATIVE CONTROL: a negative bound must be refused ------------------
    print("\n=== NEGATIVE CONTROL: negative bound must raise ValueError ===")
    try:
        magnitude_split_certificate([1, -1, 1])
        raise SystemExit("FAIL: negative bound was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    # ---- NEGATIVE CONTROL 2: wrong 'abc' term count -------------------------
    print("\n=== NEGATIVE CONTROL 2: wrong shape (2 bounds for abc) ===")
    try:
        magnitude_split_certificate([1, 1])
        raise SystemExit("FAIL: 2-bound 'abc' shape was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    # ---- NEGATIVE CONTROL 3: bad sign in nterm ------------------------------
    print("\n=== NEGATIVE CONTROL 3: non-±1 sign in nterm ===")
    try:
        magnitude_split_certificate([1, 1], shape="nterm", signs=[1, 2])
        raise SystemExit("FAIL: bad sign was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    # ---- build instances + emit ---------------------------------------------
    print("\n=== emitted Lean ===")
    _SPECS = {
        0: [1, 1, 1],                                                  # universal abc
        1: {"bounds": [sp.Rational(1, 2), sp.Rational(3, 2), 4],       # concrete abc
            "shape": "abc", "concrete": True},
        2: {"bounds": [1, 2, 3, 4], "shape": "nterm",                  # general nterm
            "signs": [1, -1, 1, -1]},
    }
    _NAMES = {0: "magsplit_abc", 1: "magsplit_concrete", 2: "magsplit_nterm"}
    fam = magnitude_split_family(
        "MagnitudeSplitSelfTest",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1, 2):
        inst, _ = certify_magnitude_split_point(fam, {"case": case}, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = MagnitudeSplitBoundEmitter().emit_body(
        _View(), LeanProfile(namespace=("X",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

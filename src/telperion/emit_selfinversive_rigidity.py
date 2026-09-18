"""Self-inversive rigidity emitter — equal-modulus real-rootedness (MIRRORMERE R3, n=2).

The reverse-Dyson base-case rigidity theorem distilled from the quasicrystal island's
`TwoFreqRigidity.lean` (`twoFreq_realRooted_iff`): for a two-frequency exponential sum

    F(x) = c₁·e^{i λ₁ x} + c₂·e^{i λ₂ x},    c₁,c₂ ∈ ℂ*,   λ₁ ≠ λ₂ ∈ ℝ,

`F` is REAL-ROOTED (every zero has zero imaginary part) IF AND ONLY IF `|c₁| = |c₂|` — the reality of
the SUPPORT forced by an equal-modulus condition on the COEFFICIENTS (spectrum side).

The emitter takes Gaussian-rational coefficients `c₁ = (re₁, im₁)`, `c₂ = (re₂, im₂)` and rational
frequencies `λ₁ ≠ λ₂`.  When `|c₁|² = |c₂|²` EXACTLY (rational arithmetic: `re₁²+im₁² = re₂²+im₂²`)
it emits Lean that proves `‖c₁‖ = ‖c₂‖` (via `Complex.norm_def` + the exact rational normSq equality)
and applies `Quasicrystal.twoFreq_realRooted_iff` to conclude real-rootedness of the concrete sum.

Self-check (EXACT rational): `re₁²+im₁² = re₂²+im₂²`, both coefficients nonzero (`|cᵢ|² > 0`), and
`λ₁ ≠ λ₂`.

NEGATIVE CONTROL: `|c₁|² ≠ |c₂|²` is REFUSED to certify real-rootedness — equal modulus is exactly
the forcing condition, and unequal modulus puts every zero off the real line (on the single line
`Im x = −(1/w)·log|c₁/c₂| ≠ 0`).  Also refused: a zero coefficient, or `λ₁ = λ₂`.
conjecture1_proved = False — an unconditional finite rigidity fact, NOT a proof of RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class SelfInversiveRigidityCertificate:
    """A verified equal-modulus rigidity certificate: Gaussian-rational coefficients with
    `|c₁|² = |c₂|²` EXACTLY, distinct rational frequencies, both coefficients nonzero."""

    re1: sp.Rational
    im1: sp.Rational
    re2: sp.Rational
    im2: sp.Rational
    lam1: sp.Rational
    lam2: sp.Rational
    normsq: sp.Rational       # the common |c₁|² = |c₂|²


def selfinversive_rigidity_certificate(c1, c2, lam1, lam2) -> SelfInversiveRigidityCertificate:
    """Build and EXACTLY self-check a self-inversive rigidity certificate.

    `c1`, `c2`: `(re, im)` rational pairs (Gaussian rationals).  `lam1`, `lam2`: rational frequencies.

    REFUSES (``ValueError``):
      * non-rational input;
      * a zero coefficient (`|cᵢ|² = 0`);
      * `lam1 = lam2` (degenerate — no two-frequency structure);
      * `|c₁|² ≠ |c₂|²` (the negative control: unequal modulus does NOT force real-rootedness).
    """
    re1, im1 = sp.nsimplify(c1[0]), sp.nsimplify(c1[1])
    re2, im2 = sp.nsimplify(c2[0]), sp.nsimplify(c2[1])
    l1, l2 = sp.nsimplify(lam1), sp.nsimplify(lam2)
    for nm, v in (("re1", re1), ("im1", im1), ("re2", re2), ("im2", im2),
                  ("lam1", l1), ("lam2", l2)):
        if not v.is_rational:
            raise ValueError(f"selfinversive_rigidity: {nm} must be rational; got {v!r}")
    ns1 = re1 ** 2 + im1 ** 2
    ns2 = re2 ** 2 + im2 ** 2
    if ns1 == 0 or ns2 == 0:
        raise ValueError("selfinversive_rigidity: coefficients must be nonzero (|cᵢ|² > 0)")
    if l1 == l2:
        raise ValueError(f"selfinversive_rigidity: frequencies must differ; got λ₁=λ₂={l1}")
    # THE equal-modulus self-check (and the negative control).
    if ns1 != ns2:
        raise ValueError(
            f"selfinversive_rigidity: |c₁|²={ns1} ≠ |c₂|²={ns2} — unequal modulus does NOT force "
            f"real-rootedness (every zero sits off the real line); refused")
    return SelfInversiveRigidityCertificate(
        re1=re1, im1=im1, re2=re2, im2=im2, lam1=l1, lam2=l2, normsq=sp.nsimplify(ns1))


def certify_selfinversive_rigidity_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` — a dict with keys ``c1``, ``c2``
    ((re,im) pairs) and ``lam1``, ``lam2`` (rational frequencies)."""
    spec = family.special[1](pt)
    cert = selfinversive_rigidity_certificate(spec["c1"], spec["c2"], spec["lam1"], spec["lam2"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class SelfInversiveRigidityEmitter(Emitter):
    """Emit equal-modulus real-rootedness — `‖c₁‖ = ‖c₂‖` (from the exact rational normSq equality)
    fed into `Quasicrystal.twoFreq_realRooted_iff`.  One theorem per instance.  The emitted file
    imports the in-island `TwoFreqRigidity`, so it must be built inside the quasicrystal island."""

    def __post_init__(self):
        self.kind = "selfinversive_rigidity"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: SelfInversiveRigidityCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            re1, im1 = rat_lean(cert.re1), rat_lean(cert.im1)
            re2, im2 = rat_lean(cert.re2), rat_lean(cert.im2)
            l1, l2 = rat_lean(cert.lam1), rat_lean(cert.lam2)

            lines.append(
                f"/-- Concrete two-frequency sum `F(x) = c₁·e^{{iλ₁x}} + c₂·e^{{iλ₂x}}` with Gaussian-\n"
                f"    rational coefficients `c₁ = {re1} + {im1}i`, `c₂ = {re2} + {im2}i` and frequencies\n"
                f"    `λ₁ = {l1}`, `λ₂ = {l2}`. -/\n"
                f"noncomputable def {base}_c1 : ℂ := ⟨({re1}), ({im1})⟩\n"
                f"noncomputable def {base}_c2 : ℂ := ⟨({re2}), ({im2})⟩\n\n"
                f"/-- **Equal-modulus rigidity** ({base}): since `|c₁|² = |c₂|²` exactly, `‖c₁‖ = ‖c₂‖`,\n"
                f"    so by `Quasicrystal.twoFreq_realRooted_iff` the two-frequency sum is REAL-ROOTED —\n"
                f"    every zero has zero imaginary part.  Reverse-Dyson R3(n=2): reality of the support\n"
                f"    is forced by an equal-modulus condition on the coefficients alone.\n"
                f"    conjecture1_proved = False. -/\n"
                f"theorem {base} :\n"
                f"    ∀ x : ℂ, Quasicrystal.twoFreq {base}_c1 {base}_c2 ({l1}) ({l2}) x = 0 → x.im = 0 := by\n"
                f"  have hc1 : {base}_c1 ≠ 0 := by\n"
                f"    have h : Complex.normSq {base}_c1 ≠ 0 := by\n"
                f"      unfold {base}_c1; simp only [Complex.normSq_mk]; norm_num\n"
                f"    exact fun hz => h (by rw [hz]; simp)\n"
                f"  have hc2 : {base}_c2 ≠ 0 := by\n"
                f"    have h : Complex.normSq {base}_c2 ≠ 0 := by\n"
                f"      unfold {base}_c2; simp only [Complex.normSq_mk]; norm_num\n"
                f"    exact fun hz => h (by rw [hz]; simp)\n"
                f"  have hlam : ({l1} : ℝ) ≠ ({l2}) := by norm_num\n"
                f"  have hmod : ‖{base}_c1‖ = ‖{base}_c2‖ := by\n"
                f"    have hns : Complex.normSq {base}_c1 = Complex.normSq {base}_c2 := by\n"
                f"      unfold {base}_c1 {base}_c2; simp only [Complex.normSq_mk]; norm_num\n"
                f"    rw [Complex.norm_def, Complex.norm_def, hns]\n"
                f"  exact (Quasicrystal.twoFreq_realRooted_iff {base}_c1 {base}_c2 ({l1}) ({l2}) hc1 hc2 hlam).mpr hmod\n\n"
            )
            nthm += 1
        return "".join(lines), nthm


def selfinversive_rigidity_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a selfinversive_rigidity family (kind='selfinversive_rigidity').  ``spec``: ``pt -> dict``
    with keys ``c1``, ``c2`` ((re,im) rational pairs), ``lam1``, ``lam2``.  Refuses unequal modulus
    (the negative control), a zero coefficient, or equal frequencies."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("selfinversive_rigidity", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert (c1=(3/5,4/5), c2=(1,0), |c|²=1) ===")
    c = selfinversive_rigidity_certificate(("3/5", "4/5"), ("1", "0"), "1", "2")
    print(f"cert OK: |c₁|²=|c₂|²={c.normsq}")
    print("\n=== NEGATIVE CONTROL: unequal modulus (must raise) ===")
    try:
        selfinversive_rigidity_certificate(("3/5", "4/5"), ("2", "0"), "1", "2")
        raise SystemExit("FAIL: unequal modulus not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean ===")
    fam = selfinversive_rigidity_family(
        "T", GridSpec([("case", [0])]), lambda pt: "rigidity_demo",
        spec=lambda pt: {"c1": ("3/5", "4/5"), "c2": ("1", "0"), "lam1": "1", "lam2": "2"})
    inst, _ = certify_selfinversive_rigidity_point(fam, {"case": 0}, "rigidity_demo")

    class _V:
        instances = [inst]

    body, nthm = SelfInversiveRigidityEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")

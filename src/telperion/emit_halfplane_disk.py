"""Half-plane -> disk positivity emitter (Borel-Caratheodory / Moebius-Schwarz core).

The quantitative heart of the classical zeta zero-free region: the Moebius map
``w |-> w / (2B - w)`` sends the closed half-plane ``Re w <= B`` (for a positive
rational ``B``) into the closed unit disk.  The single Positivstellensatz identity

    ‖2B - w‖² − ‖w‖² = 4·B·(B − Re w)

is a PRODUCT OF TWO NONNEGATIVES whenever ``Re w <= B`` and ``B > 0``, so
``‖w‖ <= ‖2B - w‖`` and therefore ``‖w / (2B - w)‖ <= 1``.  The certificate is
just the rational fact ``B > 0``; the emitted Lean is a copy — parameterized by
the concrete ``B`` — of the ALREADY-PROVEN, sorry-free lemma
``norm_div_two_mul_sub_le_one`` from
``examples/borel_caratheodory/lean/BorelCaratheodory.lean``.

Emitted theorem (universally quantified in ``w : ℂ``):

    theorem <name>_core (w : ℂ) (hw : w.re ≤ B) : ‖w / (2*B - w)‖ ≤ 1

Optional companions, adapted from the same file:

  * ``<name>_inv``     : the algebraic inversion ``g = 2B·w/(1+w)`` (from
    ``moebius_inv``), stated for a symbol ``g`` with the half-plane hypothesis.
  * ``<name>_reverse`` : the reverse-triangle norm bound
    ``‖w‖ ≤ t < 1  ⟹  ‖g‖ ≤ 2B·t/(1−t)`` (from ``norm_g_le_of_norm_w_le``).

NEGATIVE CONTROL: ``B <= 0`` breaks the ``4B(B − Re w) >= 0`` core (the product
is no longer a product of nonnegatives) and is REFUSED at certification with a
``ValueError``.
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
except ImportError:  # run directly: `python src/telperion/emit_halfplane_disk.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class HalfPlaneDiskCertificate:
    """A verified half-plane -> disk Moebius certificate for a positive rational B.

    The certified fact is the Positivstellensatz identity
    ``‖2B − w‖² − ‖w‖² = 4·B·(B − Re w)`` (checked EXACTLY in sympy over the
    real coordinates ``w = a + b i``), whose right side is a product of two
    nonnegatives under ``Re w = a <= B`` and ``B > 0``.
    """

    B: sp.Rational          # the half-plane bound, strictly positive
    emit_inv: bool          # also emit the algebraic inversion lemma
    emit_reverse: bool      # also emit the reverse-triangle norm bound


def halfplane_disk_certificate(
    B, *, emit_inv: bool = False, emit_reverse: bool = False
) -> HalfPlaneDiskCertificate:
    """Build and EXACTLY self-check a half-plane -> disk certificate.

    Refuses (``ValueError``) any ``B <= 0`` — the negative control: the core
    ``4B(B − Re w) >= 0`` is no longer a product of nonnegatives, so the Moebius
    map does not land in the unit disk.
    """
    Bq = sp.nsimplify(B)
    if not Bq.is_rational:
        raise ValueError(f"half-plane bound B must be rational; got {B!r}")
    if Bq <= 0:
        raise ValueError(
            f"half-plane -> disk needs strictly positive B (Re w <= B, B > 0); got B={Bq}"
        )
    # EXACT Positivstellensatz self-check over w = a + b*i (a, b real symbols):
    #   ‖2B - w‖² − ‖w‖² = 4·B·(B − a).
    a, b = sp.symbols("a b", real=True)
    normsq_den = (2 * Bq - a) ** 2 + b ** 2      # ‖2B − w‖²
    normsq_num = a ** 2 + b ** 2                  # ‖w‖²
    identity = sp.expand((normsq_den - normsq_num) - 4 * Bq * (Bq - a))
    if identity != 0:
        raise ValueError(
            "half-plane -> disk Positivstellensatz self-check failed — certificate rejected"
        )
    return HalfPlaneDiskCertificate(
        B=sp.nsimplify(Bq), emit_inv=bool(emit_inv), emit_reverse=bool(emit_reverse)
    )


def certify_halfplane_disk_point(family, pt, name):
    """Certify one half-plane -> disk instance from ``family.special[1](pt) -> B``.

    ``spec(pt)`` returns either the bound ``B`` directly, or a dict/tuple
    ``{"B": ..., "inv": bool, "reverse": bool}`` selecting the optional
    companion lemmas.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = halfplane_disk_certificate(
            spec["B"],
            emit_inv=bool(spec.get("inv", False)),
            emit_reverse=bool(spec.get("reverse", False)),
        )
    elif isinstance(spec, (tuple, list)):
        B = spec[0]
        emit_inv = bool(spec[1]) if len(spec) > 1 else False
        emit_reverse = bool(spec[2]) if len(spec) > 2 else False
        cert = halfplane_disk_certificate(B, emit_inv=emit_inv, emit_reverse=emit_reverse)
    else:
        cert = halfplane_disk_certificate(spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class HalfPlaneDiskEmitter(Emitter):
    """Emit ``‖w / (2B − w)‖ ≤ 1`` for ``Re w ≤ B`` — the Moebius half-plane -> disk
    core, one theorem per instance.  The proof is a B-parameterized copy of the
    proven ``norm_div_two_mul_sub_le_one`` in BorelCaratheodory.lean: reduce
    ``‖w‖ ≤ ‖2B − w‖`` to squared norms via ``Complex.normSq``, then close the
    ``4B(B − Re w) ≥ 0`` core with ``nlinarith``."""

    def __post_init__(self):
        self.kind = "halfplane_disk"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: HalfPlaneDiskCertificate = inst.payload  # type: ignore[assignment]
            # Two Lean representations of the SAME rational bound:
            #   Br : the real literal, used in real-typed positions (`w.re ≤ Br`);
            #   Bc : the COERCED-real complex form `((Br : ℝ) : ℂ)`, used in every
            #        complex-typed position.  Emitting Bc as a real coercion (NOT a
            #        raw complex literal) is what makes `Complex.ofReal_re`,
            #        `Complex.ofReal_im`, and `Complex.norm_real` fire exactly as in
            #        the PROVEN BorelCaratheodory.lean lemmas (where `B : ℝ` and the
            #        complex occurrence is the coercion `(B : ℂ)`).  A raw complex
            #        literal like `(1/2 : ℂ)` would break `Complex.norm_real`.
            Br = rat_lean(cert.B)
            Bc = f"(({Br} : ℝ) : ℂ)"
            base = inst.lean_name

            # --- _core: ‖w / (2B − w)‖ ≤ 1  (copy of norm_div_two_mul_sub_le_one) ---
            lines.append(
                f"/-- Moebius half-plane -> disk: `Re w ≤ {Br}` (with `{Br} > 0`) implies\n"
                f"    `‖w / (2*{Br} - w)‖ ≤ 1`.  Core: `4*{Br}*({Br} - Re w) ≥ 0`. -/\n"
                f"theorem {base}_core (w : ℂ) (hw : w.re ≤ {Br}) :\n"
                f"    ‖w / (2 * {Bc} - w)‖ ≤ 1 := by\n"
                f"  have hB : (0:ℝ) < {Br} := by norm_num\n"
                f"  have hden : (2 * {Bc} - w) ≠ 0 := by\n"
                f"    intro hzero\n"
                f"    have hre : (2 * {Bc} - w).re = 0 := by rw [hzero]; simp\n"
                f"    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat,\n"
                f"      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,\n"
                f"      Complex.one_re, Complex.one_im, Complex.ofReal_one] at hre\n"
                f"    nlinarith [hw, hB, hre]\n"
                f"  have hpos : 0 < ‖2 * {Bc} - w‖ := norm_pos_iff.mpr hden\n"
                f"  rw [norm_div, div_le_one hpos]\n"
                f"  have hsq : ‖w‖ ^ 2 ≤ ‖2 * {Bc} - w‖ ^ 2 := by\n"
                f"    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]\n"
                f"    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,\n"
                f"      Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,\n"
                f"      Complex.ofReal_re, Complex.ofReal_im,\n"
                f"      Complex.one_re, Complex.one_im, Complex.ofReal_one]\n"
                f"    nlinarith [hw, hB, sq_nonneg w.im, sq_nonneg w.re,\n"
                f"      mul_nonneg hB.le (sub_nonneg.mpr hw)]\n"
                f"  have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _\n"
                f"  nlinarith [hsq, hnn, hpos.le]\n"
            )
            nthm += 1

            # --- _inv: algebraic inversion g = 2B·w/(1+w)  (copy of moebius_inv) ---
            if cert.emit_inv:
                lines.append(
                    f"/-- Algebraic inversion: `w = g/(2*{Br}−g)` with `2*{Br}−g ≠ 0` implies\n"
                    f"    `1 + w ≠ 0` and `g = 2*{Br}*w/(1+w)`. -/\n"
                    f"theorem {base}_inv {{g w : ℂ}}\n"
                    f"    (hden : (2 * {Bc} - g) ≠ 0)\n"
                    f"    (hw : w = g / (2 * {Bc} - g)) :\n"
                    f"    (1 + w) ≠ 0 ∧ g = 2 * {Bc} * w / (1 + w) := by\n"
                    f"  have hBne : (2 * {Bc}) ≠ 0 := by\n"
                    f"    have hBc : {Bc} ≠ 0 := by norm_num\n"
                    f"    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]\n"
                    f"    exact hBc\n"
                    f"  subst hw\n"
                    f"  have h1w : (1 : ℂ) + g / (2 * {Bc} - g)\n"
                    f"      = 2 * {Bc} / (2 * {Bc} - g) := by\n"
                    f"    field_simp\n"
                    f"    ring\n"
                    f"  have h1wne : (1 + g / (2 * {Bc} - g)) ≠ 0 := by\n"
                    f"    rw [h1w]; exact div_ne_zero hBne hden\n"
                    f"  refine ⟨h1wne, ?_⟩\n"
                    f"  rw [eq_div_iff h1wne]\n"
                    f"  field_simp\n"
                    f"  ring\n"
                )
                nthm += 1

            # --- _reverse: reverse-triangle norm bound  (copy of norm_g_le_of_norm_w_le) ---
            if cert.emit_reverse:
                lines.append(
                    f"/-- Reverse-triangle bound: `‖w‖ ≤ t < 1` and `g = 2*{Br}*w/(1+w)` implies\n"
                    f"    `‖g‖ ≤ 2*{Br}*t/(1−t)`. -/\n"
                    f"theorem {base}_reverse {{t : ℝ}} (ht0 : 0 ≤ t) (ht1 : t < 1)\n"
                    f"    {{g w : ℂ}} (hwt : ‖w‖ ≤ t) (h1w : (1 + w) ≠ 0)\n"
                    f"    (hg : g = 2 * {Bc} * w / (1 + w)) :\n"
                    f"    ‖g‖ ≤ 2 * {Br} * t / (1 - t) := by\n"
                    f"  have hB : (0:ℝ) < {Br} := by norm_num\n"
                    f"  have hden_pos : 0 < ‖1 + w‖ := norm_pos_iff.mpr h1w\n"
                    f"  have hrev : (1 : ℝ) - ‖w‖ ≤ ‖1 + w‖ := by\n"
                    f"    have := norm_sub_norm_le (1 : ℂ) (-w)\n"
                    f"    simp only [norm_one, norm_neg, sub_neg_eq_add] at this\n"
                    f"    simpa [sub_neg_eq_add] using this\n"
                    f"  have h1mt_pos : 0 < 1 - t := by linarith\n"
                    f"  have hlb : (1 : ℝ) - t ≤ ‖1 + w‖ := by linarith [hrev, hwt]\n"
                    f"  have hnum : ‖2 * {Bc} * w‖ = 2 * {Br} * ‖w‖ := by\n"
                    f"    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,\n"
                    f"      abs_of_pos hB, Complex.norm_ofNat]\n"
                    f"  rw [hg, norm_div, hnum]\n"
                    f"  rw [div_le_div_iff₀ hden_pos h1mt_pos]\n"
                    f"  have hlhs : 2 * {Br} * ‖w‖ * (1 - t) ≤ 2 * {Br} * t * ‖1 + w‖ := by\n"
                    f"    have hBt : (0 : ℝ) ≤ 2 * {Br} := by positivity\n"
                    f"    nlinarith [hwt, hlb, ht0, hden_pos.le, mul_nonneg hBt ht0, hB.le]\n"
                    f"  linarith [hlhs]\n"
                )
                nthm += 1
        return "".join(lines), nthm


def halfplane_disk_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a half-plane -> disk family (kind='halfplane_disk').

    ``spec``: a callable ``pt -> B`` (a strictly positive rational bound), or
    ``pt -> {"B": ..., "inv": bool, "reverse": bool}`` / ``pt -> (B, inv, reverse)``
    to additionally emit the inversion / reverse-triangle companion lemmas.
    Refuses a non-positive ``B`` at certification."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("halfplane_disk", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: positive cert, negative control, print emitted Lean ---
    print("=== positive certificate B=1 (with inv + reverse companions) ===")
    cert = halfplane_disk_certificate(1, emit_inv=True, emit_reverse=True)
    print(f"cert OK: B={cert.B}, inv={cert.emit_inv}, reverse={cert.emit_reverse}")

    print("\n=== NEGATIVE CONTROL: B=0 must raise ValueError ===")
    try:
        halfplane_disk_certificate(0)
        raise SystemExit("FAIL: B=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: B=-1 must raise ValueError ===")
    try:
        halfplane_disk_certificate(-1)
        raise SystemExit("FAIL: B=-1 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean for B=1 (core only) and B=1/2 (core+inv+reverse) ===")
    _SPECS = {0: 1, 1: {"B": sp.Rational(1, 2), "inv": True, "reverse": True}}
    _NAMES = {0: "halfplane_disk_one", 1: "halfplane_disk_half"}
    fam = halfplane_disk_family(
        "HalfPlaneDiskSelfTest",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )

    # Build certified instances directly (no full certify() pipeline needed here).
    insts = []
    for case in (0, 1):
        pt = {"case": case}
        inst, _ = certify_halfplane_disk_point(fam, pt, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = HalfPlaneDiskEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n")
    print(body)

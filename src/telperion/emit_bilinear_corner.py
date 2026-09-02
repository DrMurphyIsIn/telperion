"""Bilinear-corner box-positivity emitter — worst-corner positivity of a
bilinear form on an axis-aligned box.

A bilinear form ``f(s,t) = A + B·s + C·t + E·(s·t)`` is *affine in s for fixed t*
and *affine in t for fixed s*; on a box ``[s0,s1]×[t0,t1]`` it therefore attains
its minimum at one of the four CORNERS.  Hence

    0 ≤ f(s0,t0),  f(s0,t1),  f(s1,t0),  f(s1,t1)   ⟹   0 ≤ f(s,t)  ∀ (s,t)∈box.

The exact certificate is the barycentric convex-combination identity

    f(s,t) = λ00·f(s0,t0) + λ01·f(s0,t1) + λ10·f(s1,t0) + λ11·f(s1,t1)

with the nonnegative box weights (for s∈[s0,s1], t∈[t0,t1])

    λ00 = (s1−s)/(s1−s0) · (t1−t)/(t1−t0),  λ01 = (s1−s)/(s1−s0) · (t−t0)/(t1−t0),
    λ10 = (s−s0)/(s1−s0) · (t1−t)/(t1−t0),  λ11 = (s−s0)/(s1−s0) · (t−t0)/(t1−t0).

``bilinear_corner_certificate`` computes the four corner values, EXACTLY
self-checks the convex-combination identity in sympy (``expand(f − Σλ·corner)==0``),
and RAISES ``ValueError`` (the anti-phantom negative control) if any corner value
is < 0 or if the box is degenerate (``s1 ≤ s0`` or ``t1 ≤ t0``).

The emitted Lean models the PROVEN ``h_floors`` pattern (examples/h_floors —
``bilinear_corner_nonneg`` + ``*_cell``): a reusable lemma

    theorem bilinear_corner_nonneg {A B C E s t s0 s1 t0 t1 : ℝ}
        (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
        (h00 …) (h01 …) (h10 …) (h11 …) : 0 ≤ A + B*s + C*t + E*(s*t)

is stated ONCE at the top of the file (its proof: fix s at each end via the
affine-in-t split, then split affine-in-s — closed by ``nlinarith`` on the
sign-cased ``mul_nonneg`` products, exactly as h_floors does), and each instance
is one theorem that supplies the four ``by norm_num`` corner facts and applies it.

NEGATIVE CONTROL: a form with a negative corner value (or a degenerate box) is
refused at certification with ``ValueError``.
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
except ImportError:  # run directly as a script: `python src/telperion/emit_bilinear_corner.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# The reusable worst-corner lemma, emitted once at the top of every file this
# emitter produces.  Copied verbatim from the PROVEN h_floors proof
# (examples/h_floors/frozen/floors/HFloors.lean, `bilinear_corner_nonneg`) —
# it compiles against Mathlib v4.32.0.
BILINEAR_CORNER_LEMMA = """\
/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it. -/
theorem bilinear_corner_nonneg {A B C E s t s0 s1 t0 t1 : ℝ}
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h00 : 0 ≤ A + B * s0 + C * t0 + E * (s0 * t0))
    (h01 : 0 ≤ A + B * s0 + C * t1 + E * (s0 * t1))
    (h10 : 0 ≤ A + B * s1 + C * t0 + E * (s1 * t0))
    (h11 : 0 ≤ A + B * s1 + C * t1 + E * (s1 * t1)) :
    0 ≤ A + B * s + C * t + E * (s * t) := by
  have hfix : ∀ sv : ℝ, 0 ≤ A + B * sv + C * t0 + E * (sv * t0) →
      0 ≤ A + B * sv + C * t1 + E * (sv * t1) →
      0 ≤ A + B * sv + C * t + E * (sv * t) := by
    intro sv e0 e1
    rcases le_total 0 (C + E * sv) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr ht1)]
  have H0 := hfix s0 h00 h01
  have H1 := hfix s1 h10 h11
  rcases le_total 0 (B + E * t) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hs0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hs1)]
"""


@dataclass(frozen=True)
class BilinearCornerCertificate:
    """A verified worst-corner certificate for ``0 ≤ A + B·s + C·t + E·(s·t)``
    on ``[s0,s1]×[t0,t1]``, given the four corner values are ≥ 0."""

    A: sp.Rational
    B: sp.Rational
    C: sp.Rational
    E: sp.Rational
    s0: sp.Rational
    s1: sp.Rational
    t0: sp.Rational
    t1: sp.Rational
    corner00: sp.Rational          # f(s0, t0)
    corner01: sp.Rational          # f(s0, t1)
    corner10: sp.Rational          # f(s1, t0)
    corner11: sp.Rational          # f(s1, t1)


def bilinear_corner_certificate(
    A, B, C, E, s0, s1, t0, t1
) -> BilinearCornerCertificate:
    """Build and EXACTLY self-check a worst-corner certificate.

    Computes the four corner values, verifies the barycentric convex-combination
    identity symbolically, and REFUSES (``ValueError``) a degenerate box or any
    negative corner value (the anti-phantom negative control)."""
    A, B, C, E, s0, s1, t0, t1 = (sp.nsimplify(v) for v in (A, B, C, E, s0, s1, t0, t1))
    if s1 <= s0:
        raise ValueError(f"bilinear_corner needs s0 < s1; got s0={s0}, s1={s1}")
    if t1 <= t0:
        raise ValueError(f"bilinear_corner needs t0 < t1; got t0={t0}, t1={t1}")

    def f(sv, tv):
        return A + B * sv + C * tv + E * (sv * tv)

    c00, c01, c10, c11 = f(s0, t0), f(s0, t1), f(s1, t0), f(s1, t1)
    for label, val in (("00", c00), ("01", c01), ("10", c10), ("11", c11)):
        if val < 0:
            raise ValueError(
                f"bilinear_corner corner f{label} = {val} < 0 — form is NOT "
                f"box-positive; certificate rejected"
            )

    # Exact self-check of the barycentric convex-combination identity:
    #   f(s,t) = Σ_corner λ_corner · f(corner),  λ ≥ 0 on the box.
    s, t = sp.symbols("s t")
    ws0, ws1 = (s1 - s) / (s1 - s0), (s - s0) / (s1 - s0)
    wt0, wt1 = (t1 - t) / (t1 - t0), (t - t0) / (t1 - t0)
    combo = (
        ws0 * wt0 * c00 + ws0 * wt1 * c01 + ws1 * wt0 * c10 + ws1 * wt1 * c11
    )
    if sp.expand(f(s, t) - combo) != 0:
        raise ValueError(
            "bilinear_corner convex-combination self-check failed — "
            "certificate rejected"
        )

    return BilinearCornerCertificate(
        A=A, B=B, C=C, E=E, s0=s0, s1=s1, t0=t0, t1=t1,
        corner00=c00, corner01=c01, corner10=c10, corner11=c11,
    )


def certify_bilinear_corner_point(family, pt, name):
    """Certify one bilinear-corner instance from
    ``family.special[1](pt) -> (A, B, C, E, s0, s1, t0, t1)``."""
    coeffs = family.special[1](pt)
    cert = bilinear_corner_certificate(*coeffs)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BilinearCornerBoxEmitter(Emitter):
    """Emit ``0 ≤ A + B·s + C·t + E·(s·t)`` on a box, via the reusable proven
    ``bilinear_corner_nonneg`` lemma applied to four ``by norm_num`` corner facts.

    The lemma is emitted ONCE at the top of the file; each instance is one
    theorem.  This mirrors the compiling h_floors ``*_cell`` proof exactly."""

    def __post_init__(self):
        self.kind = "bilinear_corner"

    def _instance_text(self, cert: BilinearCornerCertificate, lean_name: str) -> str:
        A, B, C, E = rat_lean(cert.A), rat_lean(cert.B), rat_lean(cert.C), rat_lean(cert.E)
        s0, s1 = rat_lean(cert.s0), rat_lean(cert.s1)
        t0, t1 = rat_lean(cert.t0), rat_lean(cert.t1)
        form = f"{A} + {B} * s + {C} * t + {E} * (s * t)"
        # corner facts, closed by norm_num on the (concrete rational) value
        c00, c01 = rat_lean(cert.corner00), rat_lean(cert.corner01)
        c10, c11 = rat_lean(cert.corner10), rat_lean(cert.corner11)
        return (
            f"theorem {lean_name} (s t : ℝ)\n"
            f"    (hs0 : {s0} ≤ s) (hs1 : s ≤ {s1})\n"
            f"    (ht0 : {t0} ≤ t) (ht1 : t ≤ {t1}) :\n"
            f"    0 ≤ {form} := by\n"
            f"  have hc00 : (0:ℝ) ≤ {c00} := by norm_num\n"
            f"  have hc01 : (0:ℝ) ≤ {c01} := by norm_num\n"
            f"  have hc10 : (0:ℝ) ≤ {c10} := by norm_num\n"
            f"  have hc11 : (0:ℝ) ≤ {c11} := by norm_num\n"
            f"  have h00 : 0 ≤ {A} + {B} * {s0} + {C} * {t0} + {E} * ({s0} * {t0}) := by\n"
            f"    have : {A} + {B} * {s0} + {C} * {t0} + {E} * ({s0} * {t0}) = {c00} := by norm_num\n"
            f"    rw [this]; exact hc00\n"
            f"  have h01 : 0 ≤ {A} + {B} * {s0} + {C} * {t1} + {E} * ({s0} * {t1}) := by\n"
            f"    have : {A} + {B} * {s0} + {C} * {t1} + {E} * ({s0} * {t1}) = {c01} := by norm_num\n"
            f"    rw [this]; exact hc01\n"
            f"  have h10 : 0 ≤ {A} + {B} * {s1} + {C} * {t0} + {E} * ({s1} * {t0}) := by\n"
            f"    have : {A} + {B} * {s1} + {C} * {t0} + {E} * ({s1} * {t0}) = {c10} := by norm_num\n"
            f"    rw [this]; exact hc10\n"
            f"  have h11 : 0 ≤ {A} + {B} * {s1} + {C} * {t1} + {E} * ({s1} * {t1}) := by\n"
            f"    have : {A} + {B} * {s1} + {C} * {t1} + {E} * ({s1} * {t1}) = {c11} := by norm_num\n"
            f"    rw [this]; exact hc11\n"
            f"  exact bilinear_corner_nonneg hs0 hs1 ht0 ht1 h00 h01 h10 h11\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [BILINEAR_CORNER_LEMMA]
        nthm = 0
        for inst in fam.instances:
            cert: BilinearCornerCertificate = inst.payload  # type: ignore[assignment]
            lines.append(self._instance_text(cert, inst.lean_name))
            nthm += 1
        # nthm counts the instance theorems; the reusable lemma is prelude-like
        # scaffolding but IS a theorem the kernel checks — count it too so the
        # header's theorem count matches the file.
        return "\n".join(lines), nthm + 1


def bilinear_corner_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a bilinear-corner box-positivity family (kind='bilinear_corner').

    ``spec``: a callable ``pt -> (A, B, C, E, s0, s1, t0, t1)`` of rationals with
    ``s0 < s1``, ``t0 < t1`` and every corner value ≥ 0.  Refuses otherwise."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("bilinear_corner", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # ---- Positive case: a genuinely bilinear box-positive form ----------------
    # f(s,t) = 1 + s + t + s*t = (1+s)(1+t), on [0,1]×[0,1]; corners all ≥ 0.
    fam = bilinear_corner_family(
        "BilinearCorner",
        GridSpec([("case", [0])]),
        lambda pt: "bc_product_unit",
        spec=lambda pt: (1, 1, 1, 1, 0, 1, 0, 1),
    )
    inst, n = certify_bilinear_corner_point(fam, {"case": 0}, "bc_product_unit")

    # A second, less trivial instance: f(s,t) = 3 − s − 2t + s*t on [0,1]×[0,1].
    #   corners: f(0,0)=3, f(0,1)=1, f(1,0)=2, f(1,1)=1  (all ≥ 0);
    #   this is NOT monotone (E flips the t-slope), a real bilinear case.
    cert2 = bilinear_corner_certificate(3, -1, -2, 1, 0, 1, 0, 1)
    inst2 = CertifiedInstance(
        point={"case": 1}, lean_name="bc_mixed_slopes", corners=(), payload=cert2
    )

    emitter = BilinearCornerBoxEmitter()

    class _FamView:
        instances = (inst, inst2)

    text, nthm = emitter.emit_body(_FamView(), LeanProfile(namespace=("BilinearCorner",)))
    print("=" * 72)
    print(f"EMITTED LEAN ({nthm} theorems):")
    print("=" * 72)
    print(text)

    # ---- Negative control: a form with a NEGATIVE corner must be refused ------
    print("=" * 72)
    print("NEGATIVE CONTROL (expect ValueError):")
    try:
        # f(s,t) = -1 + s + t on [0,1]×[0,1]: f(0,0) = -1 < 0.
        bilinear_corner_certificate(-1, 1, 1, 0, 0, 1, 0, 1)
        print("  FAIL: no ValueError raised — negative control did NOT fire!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  OK: refused as expected -> {e}")

    # ---- Negative control 2: degenerate box (s1 ≤ s0) must be refused --------
    print("NEGATIVE CONTROL 2 — degenerate box (expect ValueError):")
    try:
        bilinear_corner_certificate(1, 1, 1, 1, 1, 1, 0, 1)
        print("  FAIL: no ValueError raised on degenerate box!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  OK: refused as expected -> {e}")

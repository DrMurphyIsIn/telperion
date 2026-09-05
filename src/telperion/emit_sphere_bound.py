"""Sphere-bound emitter — turn a strip-type pointwise growth bound into a UNIFORM bound on
a sphere, as a kernel-checked Lean certificate.

Distilled from the de la Vallee Poussin frontier (`DlvpZetaDisk.zeta_sphere_bound`),
generalized to ANY `f` with a strip-type bound (no ζ specifics).  On a sphere about `c`
with `c.re > R + 1`, from the pointwise bound

    ‖f z‖ ≤ ‖z‖/‖z-1‖ + ‖z‖/Re z      (a Dirichlet/strip growth shape)

the disk geometry (`‖z‖ ≤ ‖c‖+R`, `Re z ≥ Re c - R`, `‖z-1‖ ≥ Re c - R - 1`) gives the
UNIFORM bound

    ‖f z‖ ≤ (‖c‖+R)/(Re c-R-1) + (‖c‖+R)/(Re c-R).

The emitter emits this for a chosen rational radius `R > 0`, with `f`, `c`, and the strip
bound as HYPOTHESES (fully general, self-contained ``import Mathlib``).  A NONPOSITIVE `R`
is REFUSED at cert time (a degenerate/empty sphere) — the negative control.

Reusable for any Borel-Caratheodory / Jensen setup that needs a boundary bound `M` on a
sphere (the RH/dVP zero-count is one client: `f = ζ`, strip bound = `zeta_strip_bound`,
giving `M = O(|γ|)`).  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


def _lean_rat(q: Fraction) -> str:
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"


@dataclass
class SphereBoundCertificate:
    """A sphere-bound instance: the sphere radius ``R > 0``."""

    R: Fraction


def sphere_bound_certificate(*, R) -> SphereBoundCertificate:
    """Build and self-check a sphere-bound instance for radius ``R > 0``.

    A nonpositive `R` gives a degenerate/empty sphere and is REFUSED (the negative
    control); the theorem's `c.re > R + 1` is carried as a hypothesis (it constrains the
    unknown center, so it is not a compile-time rational check)."""
    RR = Fraction(R)
    if RR <= 0:
        raise ValueError(f"REFUSED: radius R = {RR} ≤ 0 (degenerate sphere; negative control)")
    return SphereBoundCertificate(R=RR)


class SphereBoundEmitter(Emitter):
    """Emit the strip→sphere uniform-bound theorem for a certified radius."""

    def __post_init__(self):
        self.kind = "sphere_bound"

    def _emit(self, cert: SphereBoundCertificate, name: str) -> str:
        R = _lean_rat(cert.R)
        return (
            f"-- strip→sphere bound (R = {cert.R}): a strip-type growth bound on f becomes a\n"
            f"-- UNIFORM bound on the sphere about c (c.re > R+1), via disk geometry.\n"
            f"theorem {name} {{f : ℂ → ℂ}} {{c : ℂ}} (hcR : {R} + 1 < c.re)\n"
            f"    (hstrip : ∀ z ∈ Metric.sphere c {R}, ‖f z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re)\n"
            f"    {{z : ℂ}} (hz : z ∈ Metric.sphere c {R}) :\n"
            f"    ‖f z‖ ≤ (‖c‖ + {R}) / (c.re - {R} - 1) + (‖c‖ + {R}) / (c.re - {R}) := by\n"
            f"  have hzc : ‖z - c‖ = {R} := by\n"
            f"    rw [Metric.mem_sphere, Complex.dist_eq] at hz; exact hz\n"
            f"  have hre_dist : |z.re - c.re| ≤ {R} := by\n"
            f"    calc |z.re - c.re| = |(z - c).re| := by rw [Complex.sub_re]\n"
            f"      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _\n"
            f"      _ = {R} := hzc\n"
            f"  have hzre : c.re - {R} ≤ z.re := by have := (abs_le.mp hre_dist).1; linarith\n"
            f"  have hd1 : 0 < c.re - {R} - 1 := by linarith\n"
            f"  have hd2 : 0 < c.re - {R} := by linarith\n"
            f"  have hsb := hstrip z hz\n"
            f"  have hznorm : ‖z‖ ≤ ‖c‖ + {R} := by\n"
            f"    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]\n"
            f"      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _\n"
            f"      _ = ‖c‖ + {R} := by rw [hzc]; ring\n"
            f"  have hz1 : c.re - {R} - 1 ≤ ‖z - 1‖ := by\n"
            f"    calc c.re - {R} - 1 ≤ z.re - 1 := by linarith\n"
            f"      _ = (z - 1).re := by rw [Complex.sub_re, Complex.one_re]\n"
            f"      _ ≤ |(z - 1).re| := le_abs_self _\n"
            f"      _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _\n"
            f"  have hb1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + {R}) / (c.re - {R} - 1) := by gcongr\n"
            f"  have hb2 : ‖z‖ / z.re ≤ (‖c‖ + {R}) / (c.re - {R}) := by gcongr\n"
            f"  linarith [hsb, hb1, hb2]\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        for inst in fam.instances:
            cert: SphereBoundCertificate = inst.payload  # type: ignore[assignment]
            lines.append(self._emit(cert, inst.lean_name))
        return "\n".join(lines), len(fam.instances)


def sphere_bound_family(name, grid, lean_name, spec, constants=None):
    """Build a sphere-bound family (kind='sphere_bound').  ``spec``: ``pt -> {"R": q}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("sphere_bound", spec),
        constants=dict(constants or {}),
    )


def certify_sphere_bound_point(family, pt, name):
    """Certify one sphere-bound instance from ``family.special[1](pt)`` (spec: ``{"R": q}``)."""
    spec = family.special[1](pt)
    cert = sphere_bound_certificate(R=spec["R"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


if __name__ == "__main__":
    print("=== positive: radius 1/2 ===")
    c = sphere_bound_certificate(R=Fraction(1, 2))
    print(f"  cert OK: R={c.R}")
    e = SphereBoundEmitter(); e.__post_init__()
    print(e._emit(c, "sphere_bound_half"))
    print("=== NEGATIVE CONTROL: R = 0 (degenerate sphere) ===")
    try:
        sphere_bound_certificate(R=0)
        raise SystemExit("FAIL: R=0 was NOT refused")
    except ValueError as ex:
        print(f"  correctly REFUSED: {str(ex)[:90]}...")

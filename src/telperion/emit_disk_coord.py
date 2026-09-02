"""Disk -> coordinate-bounds emitter (Farkas-style linear coordinate certificate).

From membership of a point ``z : ℂ`` in the closed disk of radius ``ρ`` about a
rational center ``w = wr + wi·I`` one derives the four LINEAR coordinate bounds

    wr − ρ ≤ z.re ≤ wr + ρ,      wi − ρ ≤ z.im ≤ wi + ρ.

These are a Farkas-style linear certificate: each side follows from the single
scalar fact ``|(z − w).re| ≤ ‖z − w‖ ≤ ρ`` (resp. the imaginary part), because
``(z − w).re = z.re − wr`` and ``(z − w).im = z.im − wi``.  The certificate is
just the rational data ``(wr, wi, ρ)`` with ``ρ > 0``; the emitted Lean is a
``(wr, wi, ρ)``-parameterized copy of the coordinate-bound derivation inside the
PROVEN, sorry-free ``zeta_sphere_bound`` lemma of
``examples/zero_free_bridge/lean/ZeroFreeElementary.lean`` (which establishes
``Re z ≥ 1/4`` etc. from ``z ∈ Metric.closedBall`` via ``Metric.mem_closedBall``,
``dist_eq_norm``, ``Complex.abs_re_le_norm``, ``Complex.abs_im_le_norm``,
``abs_le`` and ``linarith``).

Emitted theorem (universally quantified in ``z : ℂ``):

    theorem <name> (z : ℂ)
        (hz : z ∈ Metric.closedBall (((wr:ℝ):ℂ) + ((wi:ℝ):ℂ) * Complex.I) ρ) :
        (wr - ρ : ℝ) ≤ z.re ∧ z.re ≤ wr + ρ ∧ (wi - ρ) ≤ z.im ∧ z.im ≤ wi + ρ

NEGATIVE CONTROL: ``ρ ≤ 0`` is REFUSED at certification with a ``ValueError`` —
with a non-positive radius the closed disk is empty or a single point and the
"bounds" carry no content (indeed ``ρ = 0`` would still be provable but ``ρ < 0``
is vacuous; we refuse ``ρ ≤ 0`` to keep the certificate a genuine box bound).
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
except ImportError:  # run directly: `python src/telperion/emit_disk_coord.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class DiskCoordCertificate:
    """A verified disk -> coordinate-bounds certificate for a rational center
    ``w = wr + wi·I`` and a strictly-positive rational radius ``ρ``.

    The certified fact is the pair of coordinate identities
    ``(z − w).re = z.re − wr`` and ``(z − w).im = z.im − wi`` (checked EXACTLY
    in sympy), which combine with ``|(z − w).re| ≤ ‖z − w‖ ≤ ρ`` (resp. im) to
    give the four linear bounds ``wr ∓ ρ ≤ z.re`` and ``wi ∓ ρ ≤ z.im``.
    """

    wr: sp.Rational          # real part of the center
    wi: sp.Rational          # imaginary part of the center
    rho: sp.Rational         # the disk radius, strictly positive


def disk_coord_certificate(wr, wi, rho) -> DiskCoordCertificate:
    """Build and EXACTLY self-check a disk -> coordinate-bounds certificate.

    Refuses (``ValueError``) a non-rational parameter or any ``ρ ≤ 0`` — the
    negative control: with a non-positive radius the closed disk is not a
    genuine axis-aligned box, so the coordinate bounds carry no content.
    """
    wrq, wiq, rhoq = (sp.nsimplify(v) for v in (wr, wi, rho))
    for label, v in (("wr", wrq), ("wi", wiq), ("rho", rhoq)):
        if not v.is_rational:
            raise ValueError(f"disk_coord parameter {label} must be rational; got {v!r}")
    if rhoq <= 0:
        raise ValueError(
            f"disk_coord needs a strictly positive radius (ρ > 0); got ρ={rhoq}"
        )
    # EXACT self-check of the two coordinate identities over z = a + b*i:
    #   (z - w).re = z.re - wr,   (z - w).im = z.im - wi.
    a, b = sp.symbols("a b", real=True)
    z = a + b * sp.I
    w = wrq + wiq * sp.I
    if sp.expand(sp.re(z - w) - (a - wrq)) != 0:
        raise ValueError("disk_coord real-part identity self-check failed — rejected")
    if sp.expand(sp.im(z - w) - (b - wiq)) != 0:
        raise ValueError("disk_coord imag-part identity self-check failed — rejected")
    return DiskCoordCertificate(
        wr=sp.nsimplify(wrq), wi=sp.nsimplify(wiq), rho=sp.nsimplify(rhoq)
    )


def certify_disk_coord_point(family, pt, name):
    """Certify one disk -> coordinate-bounds instance from
    ``family.special[1](pt) -> (wr, wi, rho)`` (or a dict ``{"wr","wi","rho"}``)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = disk_coord_certificate(spec["wr"], spec["wi"], spec["rho"])
    else:
        cert = disk_coord_certificate(*spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class DiskCoordBoundsEmitter(Emitter):
    """Emit the four linear coordinate bounds ``wr∓ρ ≤ z.re``, ``wi∓ρ ≤ z.im``
    from ``z ∈ Metric.closedBall (wr + wi·I) ρ`` — one theorem per instance.

    The proof mirrors the coordinate-bound derivation in the PROVEN
    ``zeta_sphere_bound`` (examples/zero_free_bridge): rewrite membership to
    ``‖z − w‖ ≤ ρ`` via ``Metric.mem_closedBall``/``dist_eq_norm``, compute the
    center's ``.re``/``.im`` by ``simp``, rewrite ``(z − w).re``/``.im`` with
    ``Complex.sub_re``/``Complex.sub_im``, bound them by ``Complex.abs_re_le_norm``
    / ``Complex.abs_im_le_norm`` + ``abs_le``, and close each of the four bounds
    with ``linarith``."""

    def __post_init__(self):
        self.kind = "disk_coord"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: DiskCoordCertificate = inst.payload  # type: ignore[assignment]
            # ℝ-ascribed rational literals (avoid the ℤ-default pitfall that cost
            # a build round on a sibling emitter): every bare literal is `(… : ℝ)`.
            wr = rat_lean(cert.wr)
            wi = rat_lean(cert.wi)
            rho = rat_lean(cert.rho)
            wrR = f"({wr} : ℝ)"
            wiR = f"({wi} : ℝ)"
            rhoR = f"({rho} : ℝ)"
            # complex center coordinates as real coercions, exactly as
            # zeta_sphere_bound writes `(u : ℂ) + γ * Complex.I`.
            wrC = f"(({wr} : ℝ) : ℂ)"
            wiC = f"(({wi} : ℝ) : ℂ)"
            base = inst.lean_name
            lines.append(
                f"/-- Disk -> coordinate bounds: `z ∈ closedBall ({wr} + {wi}·I) {rho}`\n"
                f"    implies `{wr} - {rho} ≤ z.re ≤ {wr} + {rho}` and\n"
                f"    `{wi} - {rho} ≤ z.im ≤ {wi} + {rho}`.  Farkas-style linear\n"
                f"    certificate (radius {rho} > 0). -/\n"
                f"theorem {base} (z : ℂ)\n"
                f"    (hz : z ∈ Metric.closedBall ({wrC} + {wiC} * Complex.I) {rhoR}) :\n"
                f"    ({wr} - {rho} : ℝ) ≤ z.re ∧ z.re ≤ {wrR} + {rhoR} ∧\n"
                f"    ({wi} - {rho} : ℝ) ≤ z.im ∧ z.im ≤ {wiR} + {rhoR} := by\n"
                f"  rw [Metric.mem_closedBall, dist_eq_norm] at hz\n"
                f"  set w : ℂ := {wrC} + {wiC} * Complex.I with hw\n"
                f"  have hwre : w.re = {wrR} := by simp [hw]\n"
                f"  have hwim : w.im = {wiR} := by simp [hw]\n"
                f"  have hre1 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _\n"
                f"  have hre2 : (z - w).re = z.re - {wrR} := by rw [Complex.sub_re, hwre]\n"
                f"  rw [hre2] at hre1\n"
                f"  have hreb := abs_le.mp (le_trans hre1 hz)\n"
                f"  have him1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _\n"
                f"  have him2 : (z - w).im = z.im - {wiR} := by rw [Complex.sub_im, hwim]\n"
                f"  rw [him2] at him1\n"
                f"  have himb := abs_le.mp (le_trans him1 hz)\n"
                f"  refine ⟨?_, ?_, ?_, ?_⟩\n"
                f"  · linarith [hreb.1]\n"
                f"  · linarith [hreb.2]\n"
                f"  · linarith [himb.1]\n"
                f"  · linarith [himb.2]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def disk_coord_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a disk -> coordinate-bounds family (kind='disk_coord').

    ``spec``: a callable ``pt -> (wr, wi, rho)`` of rationals with ``rho > 0``
    (or ``pt -> {"wr":…, "wi":…, "rho":…}``).  Refuses a non-positive radius at
    certification."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("disk_coord", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: positive cert, negative control, print emitted Lean ---
    print("=== positive certificate: center 2+3i, radius 1/2 ===")
    cert = disk_coord_certificate(2, 3, sp.Rational(1, 2))
    print(f"cert OK: wr={cert.wr}, wi={cert.wi}, rho={cert.rho}")

    print("\n=== NEGATIVE CONTROL: rho=0 must raise ValueError ===")
    try:
        disk_coord_certificate(2, 3, 0)
        raise SystemExit("FAIL: rho=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: rho=-1 must raise ValueError ===")
    try:
        disk_coord_certificate(2, 3, -1)
        raise SystemExit("FAIL: rho=-1 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean (3 instances) ===")
    _SPECS = {
        0: (sp.Integer(2), sp.Integer(3), sp.Rational(1, 2)),
        1: (sp.Rational(-1, 2), sp.Integer(1), sp.Integer(1)),
        2: (sp.Integer(0), sp.Rational(5, 4), sp.Rational(3, 2)),
    }
    _NAMES = {0: "disk_coord_2_3i", 1: "disk_coord_neg_half", 2: "disk_coord_origin"}
    fam = disk_coord_family(
        "DiskCoordSelfTest",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1, 2):
        pt = {"case": case}
        inst, _ = certify_disk_coord_point(fam, pt, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = DiskCoordBoundsEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n")
    print(body)

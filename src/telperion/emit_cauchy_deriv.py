"""Cauchy derivative-estimate emitter — a reusable wrapper for Cauchy's bound on a disk.

Cauchy's derivative estimate: for a function `f : ℂ → ℂ` holomorphic on the open
disk `Metric.ball z0 R` and continuous up to the boundary (`DiffContOnCl`), if
`‖f z‖ ≤ M` on the boundary sphere `Metric.sphere z0 R`, then

    ‖deriv f z0‖ ≤ M / R          (for R > 0).

This is exactly Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
(v4.32.0), whose argument order is `(0 < R) → DiffContOnCl → sphere-bound → bound`;
see `examples/zero_free_bridge/lean/ZeroFreeElementary.lean:zeta_deriv_bound`
(lines 200-203), which calls it as

    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1 / 2) hd hC

and also `examples/borel_caratheodory/lean/BorelCaratheodory.lean` (line 358-359).
The emitter packages this as a `(M, R)`-parameterized wrapper theorem so any
downstream file can invoke a concrete Cauchy estimate without re-deriving it.

COMPANION rational identity.  In the Borel-Caratheodory derivative argument one
picks an inner radius `ρ' = (R − r)/2` (`r` = radius of the target subdisk); the
Cauchy constant at that radius simplifies

    (2·(r + ρ') / (R − (r + ρ'))) · (1/ρ')  =  4·(R + r) / (R − r)²

a `field_simp; ring` identity for rationals with `R > r ≥ 0`.  This is precisely
the `hsimp` step in `borel_caratheodory_deriv` (BorelCaratheodory.lean:388-394).
The emitter can emit this constant-companion theorem alongside (or instead of)
the main wrapper.

Certificate:
  * main wrapper: (M, R) with R > 0 (refuse R ≤ 0 — the estimate M/R is
    meaningless / division degenerate);
  * constant companion: (R, r) with R > r ≥ 0 (refuse otherwise — the box is
    degenerate and (R−r)² would sit in a denominator that could vanish).

NEGATIVE CONTROL: R ≤ 0 (main) or R ≤ r / r < 0 (companion) is REFUSED at
certification with a ``ValueError``.
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
except ImportError:  # run directly: `python src/telperion/emit_cauchy_deriv.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class CauchyDerivCertificate:
    """A verified Cauchy derivative-estimate certificate.

    Two modes, both self-checked exactly in sympy:

      * main wrapper (``emit_main``): the sphere bound ``M`` and radius ``R > 0``.
        The certified fact is the well-posedness ``R > 0`` (so ``M / R`` is a
        genuine bound); the Lean is a copy of
        ``Complex.norm_deriv_le_of_forall_mem_sphere_norm_le``.

      * constant companion (``emit_const``): radii ``R > r ≥ 0``.  The certified
        fact is the EXACT rational identity
        ``(2(r+ρ')/(R−(r+ρ')))·(1/ρ') = 4(R+r)/(R−r)²`` at ``ρ' = (R−r)/2``
        (checked symbolically over ℚ), whose Lean proof is ``field_simp; ring``.
    """

    M: sp.Rational | None      # sphere bound (main wrapper); None if const-only
    R: sp.Rational             # outer radius, strictly positive
    r: sp.Rational | None      # inner target radius (companion); None if main-only
    emit_main: bool
    emit_const: bool


def cauchy_deriv_certificate(
    R, M=None, r=None, *, emit_main: bool = True, emit_const: bool = False
) -> CauchyDerivCertificate:
    """Build and EXACTLY self-check a Cauchy derivative-estimate certificate.

    ``R`` is the outer disk radius (strictly positive).  For the main wrapper
    give ``M`` (the boundary sup bound).  For the constant companion give ``r``
    (the inner radius, ``0 ≤ r < R``).

    Refuses (``ValueError``):
      * ``R ≤ 0`` — the estimate ``M / R`` is degenerate (the negative control);
      * ``emit_const`` with ``r`` missing, ``r < 0``, or ``r ≥ R`` — a degenerate
        box whose ``(R − r)²`` denominator could vanish.
    """
    Rq = sp.nsimplify(R)
    if not Rq.is_rational:
        raise ValueError(f"Cauchy derivative radius R must be rational; got {R!r}")
    if Rq <= 0:
        raise ValueError(
            f"Cauchy derivative estimate needs strictly positive radius R > 0; got R={Rq}"
        )

    Mq = None
    if emit_main:
        if M is None:
            raise ValueError("Cauchy derivative main wrapper needs a sphere bound M")
        Mq = sp.nsimplify(M)
        if not Mq.is_rational:
            raise ValueError(f"Cauchy derivative bound M must be rational; got {M!r}")

    rq = None
    if emit_const:
        if r is None:
            raise ValueError("Cauchy derivative constant companion needs an inner radius r")
        rq = sp.nsimplify(r)
        if not rq.is_rational:
            raise ValueError(f"Cauchy derivative inner radius r must be rational; got {r!r}")
        if rq < 0:
            raise ValueError(
                f"Cauchy derivative constant companion needs r ≥ 0; got r={rq}"
            )
        if rq >= Rq:
            raise ValueError(
                f"Cauchy derivative constant companion needs r < R (non-degenerate box); "
                f"got r={rq}, R={Rq}"
            )
        # EXACT self-check of the constant identity at ρ' = (R − r)/2:
        #   (2·(r + ρ') / (R − (r + ρ'))) · (1/ρ') = 4·(R + r) / (R − r)².
        rho = (Rq - rq) / 2
        lhs = (2 * (rq + rho) / (Rq - (rq + rho))) * (1 / rho)
        rhs = 4 * (Rq + rq) / (Rq - rq) ** 2
        if sp.simplify(lhs - rhs) != 0:
            raise ValueError(
                "Cauchy derivative constant-identity self-check failed — certificate rejected"
            )

    if not (emit_main or emit_const):
        raise ValueError("Cauchy derivative certificate must emit main and/or const")

    return CauchyDerivCertificate(
        M=Mq, R=Rq, r=rq, emit_main=bool(emit_main), emit_const=bool(emit_const)
    )


def certify_cauchy_deriv_point(family, pt, name):
    """Certify one Cauchy derivative instance from ``family.special[1](pt)``.

    ``spec(pt)`` returns either:
      * a dict ``{"R": ..., "M": ..., "r": ..., "main": bool, "const": bool}``, or
      * a tuple ``(R, M)`` (main wrapper only), or ``(R, M, r)`` (main + const).
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = cauchy_deriv_certificate(
            spec["R"],
            M=spec.get("M"),
            r=spec.get("r"),
            emit_main=bool(spec.get("main", spec.get("M") is not None)),
            emit_const=bool(spec.get("const", spec.get("r") is not None)),
        )
    elif isinstance(spec, (tuple, list)):
        R = spec[0]
        M = spec[1] if len(spec) > 1 else None
        r = spec[2] if len(spec) > 2 else None
        cert = cauchy_deriv_certificate(
            R, M=M, r=r, emit_main=M is not None, emit_const=r is not None
        )
    else:  # a bare R with no M/r makes no sense — force explicit spec
        raise ValueError(
            "cauchy_deriv spec must be a dict or (R, M[, r]) tuple; "
            f"got {spec!r}"
        )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class CauchyDerivBoundEmitter(Emitter):
    """Emit Cauchy's derivative estimate ``‖deriv f z0‖ ≤ M / R`` on a disk (a
    concrete-``R`` copy of ``Complex.norm_deriv_le_of_forall_mem_sphere_norm_le``),
    plus the optional Borel-Caratheodory constant identity
    ``(2(r+ρ')/(R−(r+ρ')))·(1/ρ') = 4(R+r)/(R−r)²`` at ``ρ' = (R−r)/2`` (proved by
    ``field_simp; ring``).  One or two theorems per instance."""

    def __post_init__(self):
        self.kind = "cauchy_deriv"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: CauchyDerivCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name

            if cert.emit_main:
                # R and M as concrete real literals.  The first argument to
                # `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` is `0 < R`;
                # `hd : DiffContOnCl ℂ f (Metric.ball z0 R)` and
                # `hC : ∀ z ∈ Metric.sphere z0 R, ‖f z‖ ≤ M` are the caller's
                # hypotheses.  Conclusion: `‖deriv f z0‖ ≤ M / R`.
                Rr = rat_lean(cert.R)
                Mr = rat_lean(cert.M)
                lines.append(
                    f"/-- Cauchy's derivative estimate on the disk of radius `{Rr}` about `z0`:\n"
                    f"    `f` holomorphic on `ball z0 {Rr}` (continuous up to the boundary) with\n"
                    f"    `‖f z‖ ≤ {Mr}` on `sphere z0 {Rr}` implies `‖deriv f z0‖ ≤ {Mr} / {Rr}`.\n"
                    f"    A concrete-radius copy of `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. -/\n"
                    f"theorem {base} (f : ℂ → ℂ) (z0 : ℂ)\n"
                    f"    (hd : DiffContOnCl ℂ f (Metric.ball z0 ({Rr} : ℝ)))\n"
                    f"    (hC : ∀ z ∈ Metric.sphere z0 ({Rr} : ℝ), ‖f z‖ ≤ ({Mr} : ℝ)) :\n"
                    f"    ‖deriv f z0‖ ≤ ({Mr} : ℝ) / ({Rr} : ℝ) :=\n"
                    f"  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le\n"
                    f"    (by norm_num : (0 : ℝ) < {Rr}) hd hC\n"
                )
                nthm += 1

            if cert.emit_const:
                # The ρ' = (R − r)/2 constant identity, `field_simp; ring`.  The
                # `(R − r) ≠ 0` fact is discharged first so field_simp can clear
                # the (R−r)² denominator (R > r ≥ 0, both concrete rationals).
                Rr = rat_lean(cert.R)
                rr = rat_lean(cert.r)
                lines.append(
                    f"/-- Borel-Caratheodory constant identity at inner radius `ρ' = ({Rr} - {rr})/2`:\n"
                    f"    the Cauchy constant `(2(r+ρ')/(R−(r+ρ')))·(1/ρ')` collapses to\n"
                    f"    `4(R+r)/(R−r)²` (a `field_simp; ring` fact for `R > r ≥ 0`). -/\n"
                    f"theorem {base}_const :\n"
                    f"    (2 * (({rr} : ℝ) + ({Rr} - {rr}) / 2) / ({Rr} - (({rr} : ℝ) + ({Rr} - {rr}) / 2)))\n"
                    f"        * (1 / (({Rr} - {rr}) / 2))\n"
                    f"      = 4 * (({Rr} : ℝ) + {rr}) / ({Rr} - {rr}) ^ 2 := by\n"
                    f"  have hRr : (({Rr} : ℝ) - {rr}) ≠ 0 := by norm_num\n"
                    f"  field_simp\n"
                    f"  ring\n"
                )
                nthm += 1
        return "".join(lines), nthm


def cauchy_deriv_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Cauchy derivative-estimate family (kind='cauchy_deriv').

    ``spec``: a callable ``pt -> {"R":…, "M":…, "r":…, "main":bool, "const":bool}``
    or ``pt -> (R, M)`` / ``pt -> (R, M, r)``.  Refuses ``R ≤ 0`` (and, for the
    constant companion, ``r < 0`` or ``r ≥ R``) at certification."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("cauchy_deriv", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: positive certs, negative controls, print emitted Lean ---
    print("=== positive certificate R=1/2, M=12 (main wrapper, like zeta_deriv_bound) ===")
    cert = cauchy_deriv_certificate(sp.Rational(1, 2), M=12)
    print(f"cert OK: R={cert.R}, M={cert.M}, main={cert.emit_main}, const={cert.emit_const}")

    print("\n=== positive certificate R=2, r=1 (constant companion) ===")
    cert2 = cauchy_deriv_certificate(2, r=1, emit_main=False, emit_const=True)
    print(f"cert OK: R={cert2.R}, r={cert2.r}, main={cert2.emit_main}, const={cert2.emit_const}")

    print("\n=== NEGATIVE CONTROL: R=0 must raise ValueError ===")
    try:
        cauchy_deriv_certificate(0, M=12)
        raise SystemExit("FAIL: R=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: R=-1 must raise ValueError ===")
    try:
        cauchy_deriv_certificate(-1, M=12)
        raise SystemExit("FAIL: R=-1 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: const companion with r ≥ R (r=2, R=1) must raise ===")
    try:
        cauchy_deriv_certificate(1, r=2, emit_main=False, emit_const=True)
        raise SystemExit("FAIL: r ≥ R was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean: main (R=1/2,M=12), const (R=2,r=1), both (R=1,M=3,r=1/2) ===")
    _SPECS = {
        0: {"R": sp.Rational(1, 2), "M": 12},
        1: {"R": 2, "r": 1, "main": False, "const": True},
        2: {"R": 1, "M": 3, "r": sp.Rational(1, 2), "main": True, "const": True},
    }
    _NAMES = {0: "cauchy_deriv_half", 1: "cauchy_deriv_two_one", 2: "cauchy_deriv_both"}
    fam = cauchy_deriv_family(
        "CauchyDerivSelfTest",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )

    insts = []
    for case in (0, 1, 2):
        pt = {"case": case}
        inst, _ = certify_cauchy_deriv_point(fam, pt, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = CauchyDerivBoundEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n")
    print(body)

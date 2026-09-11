"""Unit-modulus (conjugate-pair) SOS emitter — Hermitian positivity from |u| = 1.

The recurring shape: for a complex `u` on the unit circle (`normSq u = 1`) and any power
`m ≥ 1`, since `u^m` and `conj(u^m)` are reciprocals,

    2 - u^m - conj(u^m)  =  (1 - u^m)·conj(1 - u^m)  =  ‖1 - u^m‖²  ≥ 0,

a MANIFEST sum of squares.  This is the certificate behind the on-line Riemann-zero Li
positivity (`RvMOnLinePositivity`): for a nontrivial zero `ρ` with `re ρ = 1/2`, the atom
`w := 1 - 1/ρ` has `|w| = 1`, and the genus-1 paired Li summand is exactly `‖1 - w^(n+1)‖²`.
It is the "+" (definite) half of the Weil-form `(1,1)` signature dichotomy that the recent
two-thirds-on-line result exploits (off the line `|u| ≠ 1` and the square breaks).

Distinct from `SOSEmitter` (real-polynomial SDP-SOS) and `PSDFormEmitter` (real LDLᵀ): this
is the COMPLEX / Hermitian primitive, discharged deterministically by the `Complex.mul_conj`
identity — no SDP, no search.  The `|u| = 1` side condition is carried as a hypothesis, so the
emitted theorem is honest even when the caller cannot supply it.

NEGATIVE CONTROL: `m < 1` (a vacuous / degenerate power) is refused.

conjecture1_proved = False — this certifies a Hermitian SOS identity, nothing about RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class UnitModulusCertificate:
    """A verified conjugate-pair SOS certificate: `2 - v - conj v = ‖1 - v‖²` at `v = u^power`.

    `residual` is the exact coefficient of the unit-modulus constraint `(v·conj v - 1)` in the
    completing-the-square identity (it is `-1`); its vanishing on `|u| = 1` is what makes the
    Hermitian form a manifest square."""

    power: int
    residual: sp.Rational


def unit_modulus_certificate(power: int) -> UnitModulusCertificate:
    """Build and EXACTLY self-check the conjugate-pair SOS identity for exponent `power`.

    Works in the ring `ℚ[v, vc]` with `v = u^power`, `vc = conj(u^power)`: verifies that
    `2 - v - vc - (1 - v)·(1 - vc)` equals `-(v·vc - 1)` — i.e. the Hermitian form differs
    from the manifest square `(1-v)(1-vc)` by exactly the constraint `(v·vc - 1)`, which
    vanishes when `|u| = 1`.  Refuses `power < 1` (vacuous, the negative control)."""
    if power < 1:
        raise ValueError(
            f"unit-modulus SOS needs power ≥ 1 (a nondegenerate conjugate pair); got {power}"
        )
    v, vc = sp.symbols("v vc")
    hermitian = 2 - v - vc                    # 2 - v - conj v
    square = sp.expand((1 - v) * (1 - vc))    # ‖1 - v‖² as v·conj v structure
    constraint = v * vc - 1                   # the |u| = 1 condition, = 0 on the circle
    # hermitian - square must be a rational multiple of the constraint
    residual_expr = sp.expand(hermitian - square)
    quotient = sp.simplify(residual_expr / constraint)
    if not quotient.is_number:
        raise ValueError(
            f"conjugate-pair identity self-check failed: (2 - v - vc) - (1-v)(1-vc) = "
            f"{residual_expr} is not a scalar multiple of (v·vc - 1)"
        )
    residual = sp.nsimplify(quotient)
    # exact identity self-check: hermitian == square + residual·constraint
    if sp.expand(hermitian - (square + residual * constraint)) != 0:
        raise ValueError("unit-modulus SOS self-check failed — certificate rejected")
    return UnitModulusCertificate(power=power, residual=residual)


def certify_unit_modulus_point(family, pt, name):
    """Certify one unit-modulus SOS instance from ``family.special[1](pt) -> power``."""
    power = int(family.special[1](pt))
    cert = unit_modulus_certificate(power)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2  # identity self-check + scalar-multiple check


def _pow_lean(power: int) -> str:
    """`u` for power 1, else `u ^ m` — the atom whose modulus is 1."""
    return "u" if power == 1 else f"u ^ {power}"


@dataclass
class UnitModulusSOSEmitter(Emitter):
    """Emit `0 ≤ (2 - u^m - conj(u^m)).re` for `|u| = 1`, via the manifest square `‖1 - u^m‖²`.

    Deterministic Hermitian SOS: the `Complex.mul_conj` identity gives the square, `positivity`
    (here `Complex.normSq_nonneg`) discharges the sign.  No SDP, no search."""

    def __post_init__(self):
        self.kind = "unit_modulus_sos"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: UnitModulusCertificate = inst.payload  # type: ignore[assignment]
            um = _pow_lean(cert.power)
            hum_line = (
                ""
                if cert.power == 1
                else f"  have hum : Complex.normSq ({um}) = 1 := by rw [map_pow, hu, one_pow]\n"
            )
            normsq_u = "hu" if cert.power == 1 else "hum"
            lines.append(
                f"-- {inst.lean_name}: conjugate-pair SOS at |u| = 1 — "
                f"2 - {um} - conj({um}) = ‖1 - {um}‖² ≥ 0.\n"
                f"theorem {inst.lean_name} (u : ℂ) (hu : Complex.normSq u = 1) :\n"
                f"    (0 : ℝ) ≤ (2 - {um} - (starRingEnd ℂ) ({um})).re := by\n"
                f"{hum_line}"
                f"  have huc : {um} * (starRingEnd ℂ) ({um}) = 1 := by\n"
                f"    rw [Complex.mul_conj, {normsq_u}, Complex.ofReal_one]\n"
                f"  have hid : 2 - {um} - (starRingEnd ℂ) ({um}) "
                f"= ((Complex.normSq (1 - {um}) : ℝ) : ℂ) := by\n"
                f"    rw [← Complex.mul_conj (1 - {um}), map_sub, map_one]\n"
                f"    linear_combination -huc\n"
                f"  rw [hid, Complex.ofReal_re]\n"
                f"  exact Complex.normSq_nonneg _\n"
            )
            nthm += 1
        return "\n".join(lines), nthm


def unit_modulus_sos_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    power: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a unit-modulus conjugate-pair SOS family (kind='unit_modulus_sos').

    ``power``: a callable ``pt -> int (≥ 1)`` giving the exponent `m` of the unit-modulus atom
    `u` in the Hermitian form `2 - u^m - conj(u^m)`."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("unit_modulus_sos", power),
        constants=dict(constants or {}),
    )

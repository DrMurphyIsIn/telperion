"""Endpoint geometric-factor cap emitter — the entire-part factor is maximised at the endpoint.

The recurring dVP numeric-coupling crux (distilled from `DlvpZetaConcreteClose.lean:hBg1_le`): the
Borel-Caratheodory / entire-part bound produced by `hg_bound_gamma` carries a geometric factor

    (R + z) / (R − z)²        with  z = ‖z₀‖ = 2 − σ ∈ [0, 1]

that depends on the optimization width σ.  To DECOUPLE σ from the scale L (the fixpoint break in the
dVP closing), this factor is capped by its σ-INDEPENDENT endpoint value at `z = 1`:

    (R + z) / (R − z)²  ≤  (R + 1) / (R − 1)²        for  z ≤ 1,  R > 1 .

Why: the numerator increases and the denominator decreases as `z → 1`, and on `(−∞, 1]` the whole
factor is monotone up to its endpoint maximum (the other stationary point sits at `z = 3R`).  The
polynomial numerator of the difference factors as `(R+1)(z−1)(z−z⋆)` with `z⋆ = R(3R−1)/(R+1) ≥ 1`
for `R ≥ 1`, so it is `≥ 0` on `[0, 1]`.

Certificate: a single rational radius `R` with `R > 1`.

NEGATIVE CONTROL: `R ≤ 1` is REFUSED at certification with a ``ValueError`` (the cap denominator
`(R−1)²` degenerates and the bound is vacuous/false).  conjecture1_proved = False.
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
class EndpointGeomCapCertificate:
    """A verified endpoint geometric-factor cap: radius `R > 1`.  The certified fact is
    `(R + z)/(R − z)² ≤ (R + 1)/(R − 1)²` for all `z ≤ 1` (the endpoint maximum at `z = 1`)."""

    R: sp.Rational


def endpoint_geom_cap_certificate(R) -> EndpointGeomCapCertificate:
    """Build and EXACTLY self-check an endpoint geometric-factor cap certificate.

    Refuses (``ValueError``): ``R ≤ 1`` — the cap denominator `(R − 1)²` degenerates (the negative
    control).  Self-check: the difference numerator `N(z) = (R+1)(R−z)² − (R+z)(R−1)²` factors as
    `(R+1)(z−1)(z−z⋆)` with `z⋆ = R(3R−1)/(R+1) ≥ 1`, hence `N(z) ≥ 0` on `[0, 1]`.
    """
    Rq = sp.nsimplify(R)
    if not Rq.is_rational:
        raise ValueError(f"endpoint_geom_cap radius R must be rational; got {Rq!r}")
    if Rq <= 1:
        raise ValueError(
            f"endpoint_geom_cap needs R > 1 (else the cap denominator (R-1)² degenerates); got R={Rq}"
        )
    # EXACT self-check: N(z) = (R+1)(R-z)² - (R+z)(R-1)² = (R+1)(z-1)(z-z⋆), z⋆ = R(3R-1)/(R+1) ≥ 1.
    z = sp.Symbol("z")
    N = (Rq + 1) * (Rq - z) ** 2 - (Rq + z) * (Rq - 1) ** 2
    zstar = Rq * (3 * Rq - 1) / (Rq + 1)
    if sp.expand(N - (Rq + 1) * (z - 1) * (z - zstar)) != 0:
        raise ValueError(f"endpoint_geom_cap self-check failed: N(z) factorization mismatch for R={Rq}")
    if zstar < 1:
        raise ValueError(
            f"endpoint_geom_cap self-check failed: z⋆={zstar} < 1, so N(z) is not ≥ 0 on [0,1] (R={Rq})"
        )
    return EndpointGeomCapCertificate(R=Rq)


def certify_endpoint_geom_cap_point(family, pt, name):
    """Certify one endpoint-geom-cap instance from ``family.special[1](pt)`` (dict ``{"R":…}`` or a
    bare rational ``R``)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = endpoint_geom_cap_certificate(spec["R"])
    else:
        cert = endpoint_geom_cap_certificate(spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class EndpointGeomCapEmitter(Emitter):
    """Emit the endpoint geometric-factor cap `(R + z)/(R − z)² ≤ (R + 1)/(R − 1)²` for `z ≤ 1`
    (concrete radius `R > 1`), a reusable copy of `DlvpZetaConcreteClose.hBg1_le`'s core.  One
    theorem per instance."""

    def __post_init__(self):
        self.kind = "endpoint_geom_cap"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: EndpointGeomCapCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr = rat_lean(cert.R)
            lines.append(
                f"/-- Endpoint geometric-factor cap (R = {Rr} > 1): for `z ≤ 1` (here `z = ‖·‖ ∈ [0,1]`)\n"
                f"    the entire-part factor `(R + z)/(R - z)²` is maximised at the endpoint `z = 1`,\n"
                f"    `({Rr} + z) / ({Rr} - z)^2 ≤ ({Rr} + 1) / ({Rr} - 1)^2`.  The σ-independent cap that\n"
                f"    breaks the σ↔L fixpoint in the dVP numeric coupling. -/\n"
                f"theorem {base} (z : ℝ) (hz : z ≤ 1) :\n"
                f"    ({Rr} + z) / ({Rr} - z) ^ 2 ≤ ({Rr} + 1) / ({Rr} - 1) ^ 2 := by\n"
                f"  have hd1 : (0 : ℝ) < {Rr} - 1 := by norm_num\n"
                f"  have hnz : (0 : ℝ) < {Rr} - z := by linarith\n"
                f"  gcongr\n"
            )
            nthm += 1
        return "".join(lines), nthm


def endpoint_geom_cap_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build an endpoint-geom-cap family (kind='endpoint_geom_cap').  ``spec``: ``pt -> {"R":…}`` or
    ``pt -> R``.  Refuses ``R ≤ 1`` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("endpoint_geom_cap", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert R=3/2 ===")
    c = endpoint_geom_cap_certificate(sp.Rational(3, 2))
    print(f"cert OK: R={c.R}")
    print("\n=== NEGATIVE CONTROL: R ≤ 1 (R=1) must raise ===")
    try:
        endpoint_geom_cap_certificate(1)
        raise SystemExit("FAIL: R ≤ 1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean (R=3/2) ===")
    fam = endpoint_geom_cap_family(
        "T", GridSpec([("case", [0])]), lambda pt: "endpoint_geom_cap_a", spec=lambda pt: {"R": "3/2"}
    )
    inst, _ = certify_endpoint_geom_cap_point(fam, {"case": 0}, "endpoint_geom_cap_a")

    class _V:
        instances = [inst]

    body, nthm = EndpointGeomCapEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")

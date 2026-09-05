"""Jensen zero-count emitter — bound the number of zeros of an analytic function in a
disk by its boundary growth, as a kernel-checked Lean certificate.

Distilled from the de la Vallee Poussin frontier (`DlvpZetaDisk.zeta_zero_count_le`),
generalized to ANY analytic `f` (no ζ specifics).  Jensen's inequality bounds the zero
count in an inner disk of radius `r` by the growth on an outer disk of radius `R`:

    f analytic on closedBall c R,  f c ≠ 0,  ‖f‖ ≤ M on sphere c R
        ⟹   ∑ᶠ u, divisor f (closedBall c r) u  ≤  log(M/‖f c‖) / log(R/r).

The emitter wraps Mathlib's `AnalyticOnNhd.sum_divisor_le` for a chosen rational radius
pair `(r, R)` with `0 < r < R` (so `|r| < |R|`); the two positivity/order side goals are
discharged by `norm_num`.  A NON-ordered pair (`r ≥ R`, or `r ≤ 0`) is REFUSED at cert time
— the negative control (Jensen needs a genuinely larger outer disk).

Reusable for any zero-counting argument (the RH/dVP zero-free-region core is one client:
`f = ζ`, `c = 2+iγ`, `M = C|γ|`, giving the `O(log|γ|)` count).  Emits ONE self-contained
theorem (``import Mathlib``).  conjecture1_proved = False.
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
class JensenZeroCountCertificate:
    """A Jensen zero-count instance: the inner/outer radii ``0 < r < R``."""

    r: Fraction
    R: Fraction


def jensen_zero_count_certificate(*, r, R) -> JensenZeroCountCertificate:
    """Build and self-check a Jensen zero-count instance for radii ``0 < r < R``.

    Jensen's inequality needs `0 < |r| < |R|`.  We take positive rationals with `r < R`;
    a pair with `r ≤ 0` or `r ≥ R` is REFUSED (the outer disk must strictly contain the
    inner one) — the negative control.
    """
    rr, RR = Fraction(r), Fraction(R)
    if rr <= 0:
        raise ValueError(f"REFUSED: inner radius r = {rr} ≤ 0 (negative control)")
    if not (rr < RR):
        raise ValueError(
            f"REFUSED: need r < R (a strictly larger outer disk); got r = {rr}, "
            f"R = {RR} (Jensen's inequality is vacuous otherwise — negative control)"
        )
    return JensenZeroCountCertificate(r=rr, R=RR)


class JensenZeroCountEmitter(Emitter):
    """Emit the Jensen zero-count theorem for a certified radius pair."""

    def __post_init__(self):
        self.kind = "jensen_zero_count"

    def _emit(self, cert: JensenZeroCountCertificate, name: str) -> str:
        r, R = _lean_rat(cert.r), _lean_rat(cert.R)
        return (
            f"-- Jensen zero-count on radii (r, R) = ({cert.r}, {cert.R}): the number of\n"
            f"-- zeros of an analytic f in the inner disk is bounded by its boundary growth.\n"
            f"theorem {name} {{f : ℂ → ℂ}} {{c : ℂ}} {{M : ℝ}}\n"
            f"    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |{R}|))\n"
            f"    (hfc : f c ≠ 0) (hM : 1 ≤ M)\n"
            f"    (hbound : ∀ z ∈ Metric.sphere c |{R}|, ‖f z‖ ≤ M) :\n"
            f"    ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall c |{r}|) u\n"
            f"      ≤ Real.log (M / ‖f c‖) / Real.log ({R} / {r}) :=\n"
            f"  hf.sum_divisor_le (by norm_num) (by norm_num) hM hfc hbound\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        for inst in fam.instances:
            cert: JensenZeroCountCertificate = inst.payload  # type: ignore[assignment]
            lines.append(self._emit(cert, inst.lean_name))
        return "\n".join(lines), len(fam.instances)


def jensen_zero_count_family(name, grid, lean_name, spec, constants=None):
    """Build a Jensen zero-count family (kind='jensen_zero_count').  ``spec``: ``pt ->
    {"r": q, "R": q}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("jensen_zero_count", spec),
        constants=dict(constants or {}),
    )


def certify_jensen_zero_count_point(family, pt, name):
    """Certify one Jensen zero-count instance from ``family.special[1](pt)`` (spec:
    ``{"r": q, "R": q}``)."""
    spec = family.special[1](pt)
    cert = jensen_zero_count_certificate(r=spec["r"], R=spec["R"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


if __name__ == "__main__":
    print("=== positive: radii (1/2, 1) ===")
    c = jensen_zero_count_certificate(r=Fraction(1, 2), R=1)
    print(f"  cert OK: r={c.r}, R={c.R}")
    e = JensenZeroCountEmitter(); e.__post_init__()
    print(e._emit(c, "jensen_half_one"))
    print("=== NEGATIVE CONTROL: r = R = 1 (no larger outer disk) ===")
    try:
        jensen_zero_count_certificate(r=1, R=1)
        raise SystemExit("FAIL: r=R was NOT refused")
    except ValueError as ex:
        print(f"  correctly REFUSED: {str(ex)[:90]}...")
    print("=== NEGATIVE CONTROL: r = -1/2 (nonpositive inner radius) ===")
    try:
        jensen_zero_count_certificate(r=Fraction(-1, 2), R=1)
        raise SystemExit("FAIL: r<=0 was NOT refused")
    except ValueError as ex:
        print(f"  correctly REFUSED: {str(ex)[:90]}...")

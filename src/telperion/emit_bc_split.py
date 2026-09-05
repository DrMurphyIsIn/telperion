"""BC-split emitter — the log-derivative "split + entire bound" combine, as a
kernel-checked Lean certificate.

Distilled from the de la Vallee Poussin frontier (`DlvpBCSum.bc_sum_of_split`).  The
Borel-Caratheodory / Herglotz argument writes a log-derivative `w = ζ'/ζ(s)` as a
SPLIT `w = Z + E` — `Z` the zero sum `Σ_ρ 1/(s-ρ)`, `E` the entire part — and bounds
the entire part `‖E‖ ≤ B`.  The COMBINE step is the pure inequality

    w = Z + E,  ‖E‖ ≤ B    ⟹    -Re(w) ≤ B - Re(Z) + slack     (slack ≥ 0),

from `|Re E| ≤ ‖E‖`.  The tight bound is ``slack = 0``; a NEGATIVE ``slack`` would
STRENGTHEN the tight inequality and is REFUSED (the negative control).

This is a GENERAL complex-analytic atom (no ζ specifics): any decomposition of a
log-derivative into a bounded-entire part plus a Herglotz sum yields the BC-SUM
inequality the region argument consumes.  Emits ONE self-contained theorem
(``import Mathlib``).  conjecture1_proved = False.
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
    """Render a rational as an ℝ literal for Lean."""
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"


@dataclass
class BCSplitCertificate:
    """A BC-split combine instance: the (nonnegative) slack in `-Re w ≤ B - Re Z + slack`."""

    slack: Fraction


def bc_split_certificate(*, slack=0) -> BCSplitCertificate:
    """Build and self-check a BC-split combine instance.

    The tight combine is ``-Re(w) ≤ B - Re(Z)`` (``slack = 0``); any ``slack ≥ 0``
    weakens it and stays true.  A NEGATIVE ``slack`` claims a STRICTER bound than the
    ``|Re E| ≤ ‖E‖`` estimate supports and is REFUSED — the negative control.
    """
    s = Fraction(slack)
    if s < 0:
        raise ValueError(
            f"REFUSED: slack = {s} < 0 would strengthen the tight combine "
            f"-Re(w) ≤ B - Re(Z); the |Re E| ≤ ‖E‖ estimate gives no such margin "
            f"(negative control)"
        )
    return BCSplitCertificate(slack=s)


class BCSplitEmitter(Emitter):
    """Emit the BC-split combine theorem for a certified (nonnegative-slack) instance."""

    def __post_init__(self):
        self.kind = "bc_split"

    def _emit(self, cert: BCSplitCertificate, name: str) -> str:
        slack = cert.slack
        rhs_slack = "" if slack == 0 else f" + {_lean_rat(slack)}"
        note = ("tight combine" if slack == 0
                else f"combine with a {slack} slack margin")
        return (
            f"-- BC-split combine ({note}): from w = Z + E with ‖E‖ ≤ B,\n"
            f"-- the entire part costs at most ‖E‖, so -Re(w) ≤ B - Re(Z){rhs_slack}.\n"
            f"theorem {name} (w Z E : ℂ) (B : ℝ) (hw : w = Z + E) (hE : ‖E‖ ≤ B) :\n"
            f"    (-w).re ≤ B - Z.re{rhs_slack} := by\n"
            f"  have h1 : (-w).re = -Z.re - E.re := by rw [hw]; simp; ring\n"
            f"  have h2 : -E.re ≤ ‖E‖ :=\n"
            f"    le_trans (neg_le_abs E.re) (Complex.abs_re_le_norm E)\n"
            f"  rw [h1]; linarith [h2, hE]\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        for inst in fam.instances:
            cert: BCSplitCertificate = inst.payload  # type: ignore[assignment]
            lines.append(self._emit(cert, inst.lean_name))
        return "\n".join(lines), len(fam.instances)


def bc_split_family(name, grid, lean_name, spec, constants=None):
    """Build a BC-split family (kind='bc_split').  ``spec``: ``pt -> {"slack": q}``
    (optional; defaults to the tight ``slack = 0``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("bc_split", spec),
        constants=dict(constants or {}),
    )


def certify_bc_split_point(family, pt, name):
    """Certify one BC-split instance from ``family.special[1](pt)`` (spec: ``{"slack": q}``)."""
    spec = family.special[1](pt)
    cert = bc_split_certificate(slack=spec.get("slack", 0))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


if __name__ == "__main__":
    print("=== positive: tight combine (slack=0) ===")
    c = bc_split_certificate()
    print(f"  cert OK: slack={c.slack}")
    print(BCSplitEmitter().__class__.__name__, "emits:")
    e = BCSplitEmitter(); e.__post_init__()
    print(e._emit(c, "bc_split_tight"))

    print("=== positive: weakened combine (slack=1/10) ===")
    c2 = bc_split_certificate(slack=Fraction(1, 10))
    print(f"  cert OK: slack={c2.slack}")

    print("=== NEGATIVE CONTROL: slack=-1/10 (strengthens the tight bound) ===")
    try:
        bc_split_certificate(slack=Fraction(-1, 10))
        raise SystemExit("FAIL: negative slack was NOT refused")
    except ValueError as ex:
        print(f"  correctly REFUSED: {str(ex)[:90]}...")

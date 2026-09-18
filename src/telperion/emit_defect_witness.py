"""Defect-witness emitter — the two-configuration inertia gap (MIRRORMERE QC-B3).

The certified perturbation experiment distilled from the zeta island's `BraggDefect.lean` +
`DefectDictionary.lean`: a finite Weil/diffraction DEFECT functional read at two configurations,
producing a kernel-observable negative direction (the Alpöge–Furman signature-(1,1) leakage).

The functional is `q(d) = FLOOR − d²` at test vector `w = (0,1)` on the pure off-line channel
(here `FLOOR = 0`, so `q(d) = −d²`).  Two configurations:

  * ON-LINE  (β = 1/2): amplification excess `d = 0`, so `q(0) = 0` — consistent with defect 0,
    and `0 ∈ [A, B]` for any claimed on-line interval with `A ≤ 0 ≤ B`.
  * OFF-LINE (β ≠ 1/2): excess `d ∈ [d_lo, d_hi]` with `d_lo > 0`, so `q(d) = −d² ∈ [−d_hi², −d_lo²]`
    — strictly negative.

The EMITTED Lean instantiates the `defect_witness_online` / `defect_witness_offline` /
`defect_leakage_gap` pattern on the GIVEN rational excess bracket (self-contained — no Arb `exp`
hypothesis; the excess is supplied as certified rational data, the honest analogue of BraggDefect's
`hexp`-discharged `excess_bracket`).  The leakage gap `−d_lo² < 0 = q(0)` is the kernel-observable
separation: no test vector reads the off-line configuration as crystalline.

Self-check (EXACT rational): `d_lo > 0` and `d_lo ≤ d_hi`; the off-line functional interval is
`[−d_hi², −d_lo²]` and its upper end `−d_lo²` is strictly below the on-line value `q(0) = 0` that
sits in `[A, B]` (so `A ≤ 0 ≤ B` too).

NEGATIVE CONTROL: swapping the two configurations — presenting a NON-separated gap, i.e. the off-line
upper bound `−d_lo² ≥ 0` (which forces `d_lo = 0`, no excess) — is REFUSED at certification (a
degenerate on-line pair carries no leakage).  Also refused: `d_lo ≤ 0`, `d_lo > d_hi`, `A > 0` or
`B < 0` (the on-line value 0 not inside `[A,B]`).  conjecture1_proved = False — a finite synthetic-pair
diffraction fact, nothing about RH.
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
class DefectWitnessCertificate:
    """A verified two-configuration defect witness: on-line value `0 ∈ [A, B]`, off-line excess
    bracket `[d_lo, d_hi]` (`d_lo > 0`), off-line functional interval `[−d_hi², −d_lo²]`, and the
    leakage gap `−d_lo² < 0`."""

    d_lo: sp.Rational
    d_hi: sp.Rational
    off_lo: sp.Rational       # = −d_hi²
    off_hi: sp.Rational       # = −d_lo²  (the gap witness, < 0)
    A: sp.Rational            # on-line interval lower  (≤ 0)
    B: sp.Rational            # on-line interval upper  (≥ 0)


def defect_witness_certificate(d_lo, d_hi, A=0, B=0) -> DefectWitnessCertificate:
    """Build and EXACTLY self-check a defect-witness certificate.

    `[d_lo, d_hi]`: certified off-line amplification-excess bracket (rational, `d_lo > 0`).
    `[A, B]`: claimed on-line interval containing the value `q(0) = 0` (defaults to `[0, 0]`).

    REFUSES (``ValueError``):
      * non-rational input;
      * `d_lo ≤ 0` (no excess — the degenerate on-line pair; the swapped/negative control);
      * `d_lo > d_hi` (inverted bracket);
      * `A > 0` or `B < 0` (the on-line value 0 not inside `[A, B]`);
      * the gap failing to separate: `−d_lo² ≥ 0` (would require `d_lo = 0`, no leakage).
    """
    dlo = sp.nsimplify(d_lo)
    dhi = sp.nsimplify(d_hi)
    Aq = sp.nsimplify(A)
    Bq = sp.nsimplify(B)
    for nm, v in (("d_lo", dlo), ("d_hi", dhi), ("A", Aq), ("B", Bq)):
        if not v.is_rational:
            raise ValueError(f"defect_witness: {nm} must be rational; got {v!r}")
    if dlo <= 0:
        raise ValueError(
            f"defect_witness: excess lower bound d_lo={dlo} must be > 0 (a degenerate on-line pair "
            f"carries no leakage — the swapped negative control)")
    if dlo > dhi:
        raise ValueError(f"defect_witness: inverted excess bracket [{dlo}, {dhi}]")
    if Aq > 0:
        raise ValueError(f"defect_witness: on-line interval lower A={Aq} > 0 excludes q(0)=0")
    if Bq < 0:
        raise ValueError(f"defect_witness: on-line interval upper B={Bq} < 0 excludes q(0)=0")
    off_lo = -(dhi ** 2)
    off_hi = -(dlo ** 2)
    # THE separation self-check (and the negative control): off-line upper strictly below q(0)=0.
    if not (off_hi < 0):
        raise ValueError(
            f"defect_witness: off-line upper bound −d_lo²={off_hi} not strictly below the on-line "
            f"value 0 — the gap does not separate (refused)")
    return DefectWitnessCertificate(
        d_lo=dlo, d_hi=dhi, off_lo=sp.nsimplify(off_lo), off_hi=sp.nsimplify(off_hi), A=Aq, B=Bq)


def certify_defect_witness_point(family, pt, name):
    """Certify one defect-witness instance from ``family.special[1](pt)`` — a dict with keys
    ``d_lo``, ``d_hi`` and optional ``A``, ``B`` (on-line interval, default [0,0])."""
    spec = family.special[1](pt)
    cert = defect_witness_certificate(
        spec["d_lo"], spec["d_hi"], spec.get("A", 0), spec.get("B", 0))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class DefectWitnessEmitter(Emitter):
    """Emit the two-configuration defect witness — `defectFunctional`, the on-line value 0, the
    off-line strictly-negative bracket, and the leakage gap — a self-contained copy of
    `BraggDefect`'s `defect_witness_online` / `_offline` / `defect_leakage_gap` on given rational
    excess data.  Three theorems per instance."""

    def __post_init__(self):
        self.kind = "defect_witness"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: DefectWitnessCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            dlo = rat_lean(cert.d_lo)
            dhi = rat_lean(cert.d_hi)
            off_lo = rat_lean(cert.off_lo)
            off_hi = rat_lean(cert.off_hi)
            A = rat_lean(cert.A)
            B = rat_lean(cert.B)

            lines.append(
                f"/-- The defect functional `q(d) = FLOOR − d² = −d²` (test vector `w = (0,1)`, FLOOR = 0):\n"
                f"    on the pure off-line channel it reads the amplification excess `d`. -/\n"
                f"def {base}_defectFunctional (d : ℝ) : ℝ := -(d ^ 2)\n\n"
                # (1) on-line witness: q(0) = 0, inside [A, B]
                f"/-- **On-line witness** ({base}): the honest (all on-line) configuration's defect\n"
                f"    functional is 0, consistently inside `[{A}, {B}]` (no negative direction). -/\n"
                f"theorem {base}_online :\n"
                f"    {base}_defectFunctional 0 = 0 ∧ (({A}) : ℝ) ≤ {base}_defectFunctional 0 ∧ {base}_defectFunctional 0 ≤ ({B}) := by\n"
                f"  unfold {base}_defectFunctional\n"
                f"  refine ⟨by norm_num, by norm_num, by norm_num⟩\n\n"
                # (2) off-line witness: for excess in [d_lo, d_hi], q(d) in [off_lo, off_hi], strictly < 0
                f"/-- **Off-line witness** ({base}): for the synthetic off-line pair with amplification\n"
                f"    excess `d ∈ [{dlo}, {dhi}]` (`d > 0`), the defect functional is bracketed strictly\n"
                f"    negative, `q(d) ∈ [{off_lo}, {off_hi}]` with `{off_hi} < 0` — the measured\n"
                f"    signature-(1,1) leakage. -/\n"
                f"theorem {base}_offline (d : ℝ) (hlo : (({dlo}) : ℝ) ≤ d) (hhi : d ≤ ({dhi})) :\n"
                f"    (({off_lo}) : ℝ) ≤ {base}_defectFunctional d ∧ {base}_defectFunctional d ≤ ({off_hi}) := by\n"
                f"  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hlo\n"
                f"  unfold {base}_defectFunctional\n"
                f"  constructor\n"
                f"  · nlinarith [hhi, hlo, hdpos]\n"
                f"  · nlinarith [hlo, hdpos]\n\n"
                # (3) leakage gap: off-line upper bound < on-line value
                f"/-- **Leakage gap** ({base}): the off-line functional's upper bound `{off_hi}` is strictly\n"
                f"    below the on-line value `q(0) = 0`.  The defect is a kernel-observable separation, not\n"
                f"    a rounding artifact. -/\n"
                f"theorem {base}_leakage_gap (d : ℝ) (hlo : (({dlo}) : ℝ) ≤ d) (hhi : d ≤ ({dhi})) :\n"
                f"    {base}_defectFunctional d ≤ ({off_hi}) ∧ (({off_hi}) : ℝ) < {base}_defectFunctional 0 := by\n"
                f"  refine ⟨({base}_offline d hlo hhi).2, ?_⟩\n"
                f"  have h0 : {base}_defectFunctional 0 = 0 := by unfold {base}_defectFunctional; norm_num\n"
                f"  rw [h0]; norm_num\n\n"
            )
            nthm += 3
        return "".join(lines), nthm


def defect_witness_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a defect_witness family (kind='defect_witness').  ``spec``: ``pt -> dict`` with keys
    ``d_lo``, ``d_hi`` (excess bracket) and optional ``A``, ``B`` (on-line interval).  Refuses a
    non-separated / degenerate configuration (the swapped negative control)."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("defect_witness", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert (excess [1/10, 11/100]) ===")
    c = defect_witness_certificate("1/10", "11/100")
    print(f"cert OK: off-line q ∈ [{float(c.off_lo):.4f}, {float(c.off_hi):.4f}], gap {float(c.off_hi)} < 0")
    print("\n=== NEGATIVE CONTROL: swapped/degenerate (d_lo = 0) must raise ===")
    try:
        defect_witness_certificate("0", "11/100")
        raise SystemExit("FAIL: d_lo=0 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean ===")
    fam = defect_witness_family(
        "T", GridSpec([("case", [0])]), lambda pt: "defect_demo",
        spec=lambda pt: {"d_lo": "1/10", "d_hi": "11/100"})
    inst, _ = certify_defect_witness_point(fam, {"case": 0}, "defect_demo")

    class _V:
        instances = [inst]

    body, nthm = DefectWitnessEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")

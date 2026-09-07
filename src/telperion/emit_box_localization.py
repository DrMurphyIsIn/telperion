"""Box-localization emitter — RH-in-a-box capstone counting step (Stage 3).

The crowning localization: if the TOTAL multiplicity-weighted zero count of a function in a box `B`
equals `n_total` (argument principle) and we already exhibit `n_line` DISTINCT zeros of `B` on the
critical line `Re = 1/2`, then WHEN `n_line == n_total` those on-line zeros EXHAUST the divisor —
every zero in `B` is one of them, hence on `Re = 1/2` and simple.

Emitted theorem `box_localization_<name>` (pure Finset counting, real-geometry — the integral is
already discharged upstream): a sub-Finset `T ⊆ s` of `n` distinct on-line points, each divisor
`≥ 1`, with `∑_{s} d = n`, forces `s = T` and every `d ρ = 1`; hence every `ρ ∈ s` has `Re = 1/2`.

Certificate: `box` (a rational rectangle), `n_line`, `n_total`.  The localization hypothesis is the
EQUALITY `n_line == n_total` (with `n_line ≥ 1`).  NEGATIVE CONTROL: `n_line > n_total` is impossible
(more on-line zeros than the total count) and is REFUSED; `n_line != n_total` is likewise REFUSED —
without equality the on-line zeros cannot be shown to exhaust the divisor, so no localization claim
may be emitted.  conjecture1_proved = False (this VERIFIES RH inside the box; it is NOT a proof of RH).
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
class BoxLocalizationCertificate:
    """A verified box-localization certificate.

    ``re_lo, re_hi, im_lo, im_hi`` describe the rational box `B`; ``n`` is the (equal) on-line and
    total zero count.  The equality `n_line == n_total == n` is the localization hypothesis.
    """

    re_lo: sp.Rational
    re_hi: sp.Rational
    im_lo: sp.Rational
    im_hi: sp.Rational
    n: int


def box_localization_certificate(
    n_line: int, n_total: int, re_lo="2/5", re_hi="3/5", im_lo="10", im_hi="35"
) -> BoxLocalizationCertificate:
    """Build and EXACTLY self-check a box-localization certificate.

    Refuses `n_line > n_total` (impossible: more on-line zeros than total count), `n_line != n_total`
    (no exhaustion without equality — cannot emit a localization claim), and `n_line < 1` (vacuous).
    These are the negative controls.
    """
    if not (isinstance(n_line, int) and isinstance(n_total, int)):
        raise ValueError(f"box_localization counts must be ints; got n_line={n_line!r}, n_total={n_total!r}")
    if n_line > n_total:
        raise ValueError(
            f"box_localization: n_line ({n_line}) exceeds n_total ({n_total}) — impossible "
            f"(cannot have more on-line zeros than the total count); refused"
        )
    if n_line != n_total:
        raise ValueError(
            f"box_localization: n_line ({n_line}) != n_total ({n_total}) — without equality the "
            f"on-line zeros do not exhaust the divisor; no localization claim may be emitted; refused"
        )
    if n_line < 1:
        raise ValueError(f"box_localization needs n_line >= 1 (non-vacuous); got n_line={n_line}")
    rl, rh, il, ih = (sp.nsimplify(x) for x in (re_lo, re_hi, im_lo, im_hi))
    if not all(v.is_rational for v in (rl, rh, il, ih)):
        raise ValueError("box_localization box corners must be rational")
    if not (rl < rh and il < ih):
        raise ValueError(f"box_localization needs a non-degenerate box; got [{rl},{rh}]x[{il},{ih}]")
    return BoxLocalizationCertificate(re_lo=rl, re_hi=rh, im_lo=il, im_hi=ih, n=n_line)


def certify_box_localization_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys n_line, n_total, and
    optionally the box corners)."""
    spec = family.special[1](pt)
    cert = box_localization_certificate(
        int(spec["n_line"]), int(spec["n_total"]),
        spec.get("re_lo", "2/5"), spec.get("re_hi", "3/5"),
        spec.get("im_lo", "10"), spec.get("im_hi", "35"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BoxLocalizationEmitter(Emitter):
    """Emit the box-localization counting capstone `box_localization_<name>` for a fixed count `n`."""

    def __post_init__(self):
        self.kind = "box_localization"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Finset\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: BoxLocalizationCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            rl, rh, il, ih = (rat_lean(v) for v in (cert.re_lo, cert.re_hi, cert.im_lo, cert.im_hi))
            n = cert.n
            lines.append(
                f"/-- Box-localization capstone (counting step) on `B = [{rl},{rh}] x [{il},{ih}]`,\n"
                f"    n_line = n_total = {n}.  Given a support `s` with total divisor `= {n}`, each\n"
                f"    multiplicity `>= 1`, and `{n}` DISTINCT on-line (`Re = 1/2`) elements of `s`, the\n"
                f"    on-line zeros EXHAUST the divisor: every `rho in s` has `Re rho = 1/2`.\n"
                f"    The integral is already discharged upstream; this is pure Finset counting.\n"
                f"    conjecture1_proved = False. -/\n"
                f"theorem {base} (s T : Finset ℂ) (d : ℂ → ℤ)\n"
                f"    (hTsub : T ⊆ s) (hTcard : T.card = {n})\n"
                f"    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)\n"
                f"    (hsum : (∑ ρ ∈ s, d ρ) = ({n} : ℤ))\n"
                f"    (hline : ∀ ρ ∈ T, ρ.re = 1 / 2) :\n"
                f"    ∀ ρ ∈ s, ρ.re = 1 / 2 := by\n"
                f"  -- Split the sum over `s` into `T` and `s \\ T`.\n"
                f"  have hsplit : (∑ ρ ∈ s, d ρ) = (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \\ T, d ρ) := by\n"
                f"    rw [← Finset.sum_sdiff hTsub, add_comm]\n"
                f"  have hTlb : (({n} : ℤ)) ≤ ∑ ρ ∈ T, d ρ := by\n"
                f"    calc (({n} : ℤ)) = ∑ _ρ ∈ T, (1 : ℤ) := by\n"
                f"            rw [Finset.sum_const, hTcard, nsmul_eq_mul, mul_one]; norm_num\n"
                f"      _ ≤ ∑ ρ ∈ T, d ρ := Finset.sum_le_sum (fun ρ hρ => hd1 ρ (hTsub hρ))\n"
                f"  have hSlb : ((s \\ T).card : ℤ) ≤ ∑ ρ ∈ s \\ T, d ρ := by\n"
                f"    calc ((s \\ T).card : ℤ) = ∑ _ρ ∈ s \\ T, (1 : ℤ) := by\n"
                f"            rw [Finset.sum_const, nsmul_eq_mul, mul_one]\n"
                f"      _ ≤ ∑ ρ ∈ s \\ T, d ρ :=\n"
                f"          Finset.sum_le_sum (fun ρ hρ => hd1 ρ (Finset.mem_sdiff.mp hρ).1)\n"
                f"  have hcard0 : (s \\ T).card = 0 := by\n"
                f"    have hchain : (({n} : ℤ)) + ((s \\ T).card : ℤ) ≤ (({n} : ℤ)) := by\n"
                f"      calc (({n} : ℤ)) + ((s \\ T).card : ℤ)\n"
                f"          ≤ (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \\ T, d ρ) := add_le_add hTlb hSlb\n"
                f"        _ = (∑ ρ ∈ s, d ρ) := hsplit.symm\n"
                f"        _ = (({n} : ℤ)) := hsum\n"
                f"    have hle : ((s \\ T).card : ℤ) ≤ 0 := by linarith\n"
                f"    exact_mod_cast le_antisymm hle (by positivity)\n"
                f"  have hsubT : s ⊆ T := by\n"
                f"    have hempty : s \\ T = ∅ := Finset.card_eq_zero.mp hcard0\n"
                f"    intro x hx\n"
                f"    by_contra hxT\n"
                f"    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)\n"
                f"      (by rw [hempty]; exact Finset.notMem_empty x)\n"
                f"  have hsT : s = T := le_antisymm hsubT hTsub\n"
                f"  intro ρ hρ\n"
                f"  rw [hsT] at hρ\n"
                f"  exact hline ρ hρ\n"
            )
            nthm += 1
        return "".join(lines), nthm


def box_localization_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a box-localization family (kind='box_localization').  ``spec``: ``pt -> {"n_line",
    "n_total", ...box corners}``.  Refuses `n_line > n_total` or `n_line != n_total` at
    certification (the negative controls)."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("box_localization", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert: n_line = n_total = 5 on [2/5,3/5]x[10,35] ===")
    c = box_localization_certificate(5, 5)
    print(f"cert OK: box=[{c.re_lo},{c.re_hi}]x[{c.im_lo},{c.im_hi}] n={c.n}")
    print("\n=== NEGATIVE CONTROL: n_line > n_total must raise ===")
    try:
        box_localization_certificate(6, 5)
        raise SystemExit("FAIL: n_line>n_total not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== NEGATIVE CONTROL: n_line != n_total must raise ===")
    try:
        box_localization_certificate(4, 5)
        raise SystemExit("FAIL: n_line!=n_total not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = box_localization_family(
        "T", GridSpec([("case", [0])]), lambda pt: "box_localization_a",
        spec=lambda pt: {"n_line": 5, "n_total": 5},
    )
    inst, _ = certify_box_localization_point(fam, {"case": 0}, "box_localization_a")

    class _V:
        instances = [inst]

    body, nthm = BoxLocalizationEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:500]}\n...[truncated]")

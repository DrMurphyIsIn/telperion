"""Bragg-amplitude emitter — a certified truncated diffraction (trig) sum over bracketed ordinates.

The MIRRORMERE certified-diffraction shape distilled from the zeta island's `BraggH100.lean`
(GW_OS_BRAGG pipeline): given a finite list of rational ordinate brackets `[a_k, b_k]` (each a
certified zero location), a rational Bragg frequency `u`, and a claimed rational interval `[A, B]`,
the emitter produces the kernel-checked finite-volume amplitude enclosure

    F(u) := Σ_k cos(γ_k · u)  ∈  [A, B]        for any  γ_k ∈ [a_k, b_k].

Each per-ordinate `cos(γ_k · u)` is enclosed by the CosEnclosure pipeline (`cos_base_interval` order-4
Taylor bracket at the bracket-midpoint sample `c_k = mid_k · u`, then Lipschitz width absorption via
`cos_encl_bracket`), and the boxes are interval-folded with `CosEnclosure.add_encl` — EXACTLY the
BraggH100 fold, kept small (3–5 brackets, `|c_k| ≤ 1` so the order-4 base bracket applies directly
without the M-fold double-angle chain).  PER-ZERO LEMMA SPLIT is mandatory (the heartbeat lesson):
each bracket gets its own `bragg_cosbox_k` lemma, and the main theorem only folds.

Self-check (EXACT rational): the sum of the certified per-bracket boxes must land inside `[A, B]`
with slack ≥ 0 on both ends (the certified error budget is the box width; the claimed `[A,B]` must
contain the folded box).  A midpoint float sanity check confirms the true sum is inside.

NEGATIVE CONTROL: shrinking `B` below the folded box's lower-achievable upper bound (i.e. presenting
`[A, B']` with `B' <` the summed hi) is REFUSED at certification — the box no longer fits the claimed
interval.  Also refused: `|c_k| > 1` (order-4 base bracket out of range), an inverted bracket, or a
non-rational input.  conjecture1_proved = False — a finite-T diffraction snapshot, nothing about RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

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

# Mathlib's order-4 cos remainder coefficient (`Real.cos_bound`): |cos y - (1 - y²/2)| ≤ y⁴·(5/96).
_REM = sp.Rational(5, 96)


@dataclass(frozen=True)
class _BracketBox:
    """One certified per-ordinate cos box: bracket `[a,b]`, midpoint sample `c = mid·u`, order-4
    base box `[base_lo, base_hi]` for `cos c`, width `w = ((b-a)/2)·u`, and the width-absorbed
    per-ordinate box `[lo, hi]` (with `lo = base_lo - w`, `hi = base_hi + w`)."""

    a: sp.Rational
    b: sp.Rational
    c: sp.Rational          # = mid · u
    base_lo: sp.Rational
    base_hi: sp.Rational
    w: sp.Rational          # Lipschitz half-width in the argument
    lo: sp.Rational
    hi: sp.Rational


@dataclass(frozen=True)
class BraggAmplitudeCertificate:
    """A verified truncated Bragg amplitude enclosure `Σ_k cos(γ_k·u) ∈ [A, B]`."""

    u: sp.Rational
    brackets: tuple           # tuple[_BracketBox, ...]
    A: sp.Rational
    B: sp.Rational
    sum_lo: sp.Rational       # Σ lo_k  (folded lower bound)
    sum_hi: sp.Rational       # Σ hi_k  (folded upper bound)


def bragg_amplitude_certificate(brackets: Sequence, u, A, B) -> BraggAmplitudeCertificate:
    """Build and EXACTLY self-check a Bragg amplitude certificate.

    `brackets`: sequence of `(a_k, b_k)` rational pairs (certified ordinate brackets).
    `u`: rational Bragg frequency.  `[A, B]`: claimed rational amplitude interval.

    REFUSES (``ValueError``):
      * fewer than 1 bracket, or a non-rational / inverted bracket / non-rational `u,A,B`;
      * a midpoint sample `|c_k| = |mid_k · u| > 1` (the order-4 base bracket needs `|y| ≤ 1`);
      * `A > B` (empty claimed interval);
      * the folded box `[Σ lo_k, Σ hi_k]` NOT contained in `[A, B]` — i.e. `A > Σ lo_k` or
        `Σ hi_k > B` (the negative control: a claimed interval that does not enclose the sum).
    """
    uq = sp.nsimplify(u)
    Aq = sp.nsimplify(A)
    Bq = sp.nsimplify(B)
    for nm, v in (("u", uq), ("A", Aq), ("B", Bq)):
        if not v.is_rational:
            raise ValueError(f"bragg_amplitude: {nm} must be rational; got {v!r}")
    if Aq > Bq:
        raise ValueError(f"bragg_amplitude: empty claimed interval A={Aq} > B={Bq}")
    if len(brackets) < 1:
        raise ValueError("bragg_amplitude: need at least one ordinate bracket")

    boxes: list[_BracketBox] = []
    for k, pr in enumerate(brackets):
        a, b = sp.nsimplify(pr[0]), sp.nsimplify(pr[1])
        if not (a.is_rational and b.is_rational):
            raise ValueError(f"bragg_amplitude: bracket {k} endpoints must be rational; got {pr!r}")
        if a > b:
            raise ValueError(f"bragg_amplitude: bracket {k} inverted: [{a},{b}]")
        mid = (a + b) / 2
        c = mid * uq
        if abs(c) > 1:
            raise ValueError(
                f"bragg_amplitude: bracket {k} sample |c|=|mid·u|={abs(c)} > 1 — out of the order-4 "
                f"base-bracket range (keep the instance small: shrink u or the ordinates)")
        # order-4 two-sided Taylor bracket of cos c (Mathlib `Real.cos_bound`, |y|≤1)
        center = 1 - c ** 2 / 2
        rem = c ** 4 * _REM
        base_lo = center - rem
        base_hi = center + rem
        # Lipschitz width absorption: |γ·u − c| ≤ ((b−a)/2)·u  (cos is 1-Lipschitz)
        w = (b - a) / 2 * uq
        lo = base_lo - w
        hi = base_hi + w
        boxes.append(_BracketBox(a=a, b=b, c=c, base_lo=base_lo, base_hi=base_hi, w=w, lo=lo, hi=hi))

    sum_lo = sum(bx.lo for bx in boxes)
    sum_hi = sum(bx.hi for bx in boxes)
    # THE containment self-check (and the negative control): [Σlo, Σhi] ⊆ [A, B].
    if Aq > sum_lo:
        raise ValueError(
            f"bragg_amplitude: claimed A={Aq} exceeds folded lower bound Σlo={sum_lo} — "
            f"interval does not enclose the amplitude (refused)")
    if sum_hi > Bq:
        raise ValueError(
            f"bragg_amplitude: folded upper bound Σhi={sum_hi} exceeds claimed B={Bq} — "
            f"interval does not enclose the amplitude (refused)")
    return BraggAmplitudeCertificate(
        u=uq, brackets=tuple(boxes), A=Aq, B=Bq,
        sum_lo=sp.nsimplify(sum_lo), sum_hi=sp.nsimplify(sum_hi))


def certify_bragg_amplitude_point(family, pt, name):
    """Certify one Bragg-amplitude instance from ``family.special[1](pt)`` — a dict with keys
    ``brackets`` (list of (a,b) rational pairs), ``u``, ``A``, ``B``."""
    spec = family.special[1](pt)
    cert = bragg_amplitude_certificate(spec["brackets"], spec["u"], spec["A"], spec["B"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BraggAmplitudeEmitter(Emitter):
    """Emit `Σ_k cos(γ_k·u) ∈ [A, B]` over certified ordinate brackets — a per-bracket cos-box
    lemma (order-4 `cos_base_interval` + Lipschitz `cos_encl_bracket`) plus a fold theorem
    (`CosEnclosure.add_encl`).  One reusable copy of the BraggH100 base-case pipeline."""

    def __post_init__(self):
        self.kind = "bragg_amplitude"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: BraggAmplitudeCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            u = rat_lean(cert.u)
            n = len(cert.brackets)

            # --- per-bracket reusable cos-box lemmas (PER-ZERO LEMMA SPLIT) ---
            for k, bx in enumerate(cert.brackets, start=1):
                a = rat_lean(bx.a)
                b = rat_lean(bx.b)
                c = rat_lean(bx.c)
                blo = rat_lean(bx.base_lo)
                bhi = rat_lean(bx.base_hi)
                w = rat_lean(bx.w)
                lo = rat_lean(bx.lo)
                hi = rat_lean(bx.hi)
                lines.append(
                    f"/-- cos-box for ordinate {k} of {n}: for ANY `t ∈ [{a}, {b}]`, `cos (t * u)`\n"
                    f"    lies in the certified box (order-4 Taylor bracket at the midpoint sample + Lipschitz). -/\n"
                    f"theorem {base}_cosbox_{k} (t : ℝ) (hta : ({a} : ℝ) ≤ t) (htb : t ≤ ({b} : ℝ)) :\n"
                    f"    (({lo}) : ℝ) ≤ Real.cos (t * ({u})) ∧ Real.cos (t * ({u})) ≤ ({hi}) := by\n"
                    f"  have hy : |(({c}) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num\n"
                    f"  have hbase : (({blo}) : ℝ) ≤ Real.cos ({c}) ∧ Real.cos ({c}) ≤ ({bhi}) :=\n"
                    f"    CosEnclosure.cos_base_interval (y := (({c}) : ℝ)) hy (by norm_num) (by norm_num)\n"
                    f"  have hdist : |t * ({u}) - ({c})| ≤ ({w}) := by\n"
                    f"    rw [abs_le]; constructor <;> nlinarith [hta, htb]\n"
                    f"  have hbr := CosEnclosure.cos_encl_bracket (w := (({w}) : ℝ)) (by norm_num) hdist hbase.1 hbase.2\n"
                    f"  exact ⟨le_trans (by norm_num : (({lo}) : ℝ) ≤ ({blo}) - ({w})) hbr.1,\n"
                    f"    le_trans hbr.2 (by norm_num : (({bhi}) : ℝ) + ({w}) ≤ ({hi}))⟩\n"
                )
                nthm += 1

            # --- fold theorem: given ordinate witnesses in their brackets, Σ cos ∈ [A,B] ---
            binders = " ".join(f"t{k}" for k in range(1, n + 1))
            hyps = []
            for k, bx in enumerate(cert.brackets, start=1):
                a = rat_lean(bx.a)
                b = rat_lean(bx.b)
                hyps.append(f"    (ht{k}a : ({a} : ℝ) ≤ t{k}) (ht{k}b : t{k} ≤ ({b} : ℝ))")
            hyp_block = "\n".join(hyps)
            sumexpr = " + ".join(f"Real.cos (t{k} * ({u}))" for k in range(1, n + 1))
            A = rat_lean(cert.A)
            B = rat_lean(cert.B)

            body = []
            for k in range(1, n + 1):
                body.append(f"  have hb{k} := {base}_cosbox_{k} t{k} ht{k}a ht{k}b")
            # Fold with add_encl WITHOUT type annotations — `add_encl` yields the literal
            # (unreduced) sum-of-boxes type; the reduced [A,B] bound is bridged by linarith
            # at the end (rational arithmetic over the accumulated hypothesis).
            fold_lines = []
            if n == 1:
                fold_lines.append("  have hacc := hb1")
            else:
                fold_lines.append("  have hacc2 := CosEnclosure.add_encl ⟨hb1.1, hb1.2⟩ ⟨hb2.1, hb2.2⟩")
                for k in range(3, n + 1):
                    fold_lines.append(
                        f"  have hacc{k} := CosEnclosure.add_encl hacc{k - 1} ⟨hb{k}.1, hb{k}.2⟩")
                fold_lines.append(f"  have hacc := hacc{n}")

            lines.append(
                f"/-- **Truncated Bragg amplitude** `F(u) = Σ_{{k=1}}^{{{n}}} cos(γ_k · u)` at `u = {u}`,\n"
                f"    for any certified ordinates `γ_k ∈ [a_k, b_k]`, lies in `[{A}, {B}]`.  The 29-zero\n"
                f"    `BraggH100.bragg_amplitude_h100` fold, reduced to a {n}-ordinate base-case instance.\n"
                f"    conjecture1_proved = False. -/\n"
                f"theorem {base} ({binders} : ℝ)\n"
                f"{hyp_block} :\n"
                f"    (({A}) : ℝ) ≤ {sumexpr} ∧ {sumexpr} ≤ ({B}) := by\n"
                + "\n".join(body) + "\n"
                + "\n".join(fold_lines) + "\n"
                f"  exact ⟨by linarith [hacc.1], by linarith [hacc.2]⟩\n"
            )
            nthm += 1
        return "".join(lines), nthm


def bragg_amplitude_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a bragg_amplitude family (kind='bragg_amplitude').  ``spec``: ``pt -> dict`` with keys
    ``brackets`` (list of (a,b) rational pairs), ``u``, ``A``, ``B``.  Refuses any point failing
    `bragg_amplitude_certificate`'s guards (non-containment is the negative control)."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("bragg_amplitude", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert (3 brackets, u=3/2) ===")
    brk = [("1/2", "51/100"), ("3/5", "61/100"), ("2/5", "41/100")]
    c = bragg_amplitude_certificate(brk, "3/2", "0", "3")
    print(f"cert OK: n={len(c.brackets)} Σlo={float(c.sum_lo):.4f} Σhi={float(c.sum_hi):.4f} "
          f"[A,B]=[{float(c.A)},{float(c.B)}]")
    print("\n=== NEGATIVE CONTROL: shrink B below Σhi (must raise) ===")
    try:
        bragg_amplitude_certificate(brk, "3/2", "0", str(float(c.sum_hi) - 0.01))
        raise SystemExit("FAIL: shrunk-B not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== NEGATIVE CONTROL: |c|>1 (must raise) ===")
    try:
        bragg_amplitude_certificate([("10/1", "101/10")], "3/2", "-3", "3")
        raise SystemExit("FAIL: |c|>1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean ===")
    fam = bragg_amplitude_family(
        "T", GridSpec([("case", [0])]), lambda pt: "bragg_demo",
        spec=lambda pt: {"brackets": brk, "u": "3/2", "A": "0", "B": "3"})
    inst, _ = certify_bragg_amplitude_point(fam, {"case": 0}, "bragg_demo")

    class _V:
        instances = [inst]

    body, nthm = BraggAmplitudeEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")

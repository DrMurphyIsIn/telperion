"""Disjoint-discs emitter -- the CONCRETE-INSTANCE shape of the MIRRORMERE E4b isolation lemma.

The general lemma (registry node ``MM_offline_disjoint_discs``, proved in the quasicrystal island's
``OfflineDiscs.lean``) says: any finite set of points strictly inside the open critical strip admits
SOME common positive radius whose closed discs are pairwise disjoint and stay inside the strip.  It
is an existence statement with no numbers in it.

What the E5 Rouche-template leg actually consumes is the INSTANCE: a concrete list of certified
ordinates (say Platt/Turing-verified zero locations, or any rational strip points) together with an
EXPLICIT rational radius, so that the discs can be handed to a winding/Rouche count.  This emitter
is that shape -- the certificate is

    points  = ((re_0, im_0), ..., (re_{n-1}, im_{n-1}))   Gaussian-rational strip points
    r       = an explicit positive rational radius

and the kernel checks, per instance:

  * PAIRWISE SEPARATION   (2r)^2 < (re_i - re_j)^2 + (im_i - im_j)^2   for every i < j
    -- exactly the hypothesis of `Metric.closedBall_disjoint_closedBall (h : d + e < dist x y)`,
    reached through `Complex.dist_eq`, `Complex.norm_def` and `Real.lt_sqrt`, all closed by
    `norm_num` on rational data.  Squaring is what keeps it rational: no square root is ever
    approximated, the `√` is eliminated by `Real.lt_sqrt` before any arithmetic happens.
  * STRIP MARGIN          0 < re_i - r   and   re_i + r < 1
    -- the closed disc of radius r about a point of real part `re_i` lies in the OPEN strip iff
    the radius is strictly below both margins; the containment proof is the 1-Lipschitz bound
    |s.re - z.re| <= dist s z (`Quasicrystal.abs_re_sub_le_dist`, the island lemma).

The emitted theorem is the registry node's own conclusion with `S` instantiated to the concrete
`Finset`, so the instance literally witnesses the general lemma's existential at explicit data.

SELF-CHECK (exact rational arithmetic, no floats): r > 0; the points pairwise distinct; the squared
separation and both strip margins STRICT.

NEGATIVE CONTROL (refused at certification with ``ValueError``, and kernel-rejected if forged past
Layer 1 -- see ``negctrl_adapters/adapter_disjoint_discs.py``):
  * a radius too large for some pair, `(2r)^2 >= dist^2` -- the discs touch or overlap, so
    `closedBall_disjoint_closedBall` has no hypothesis to take and `norm_num` refutes the emitted
    strict inequality;
  * a point ON the strip boundary (re = 0 or re = 1), or a radius reaching it (`re <= r` or
    `re + r >= 1`) -- the disc leaves the OPEN strip;
  * a duplicate point (the pair would demand `Disjoint` of a ball with itself), or r <= 0.

conjecture1_proved = False -- a finite, unconditional geometry certificate about explicitly given
points.  It says NOTHING about where the zeros of zeta are; the points are INPUT.
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
class DisjointDiscsCertificate:
    """A verified isolation certificate: distinct Gaussian-rational points of the OPEN strip and an
    explicit rational radius `r > 0` with `(2r)^2 < dist^2` for every pair and `r` strictly below
    every strip margin `min(re, 1 - re)`."""

    points: tuple[tuple[sp.Rational, sp.Rational], ...]
    r: sp.Rational
    min_sep_sq: sp.Rational     # the smallest pairwise squared distance (0 for < 2 points)
    min_margin: sp.Rational     # the smallest min(re, 1 - re) over the points


def disjoint_discs_certificate(points, r) -> DisjointDiscsCertificate:
    """Build and EXACTLY self-check a disjoint-discs certificate.

    ``points``: an iterable of ``(re, im)`` rational pairs.  ``r``: a positive rational radius.

    REFUSES (``ValueError``): non-rational input; ``r <= 0``; a duplicate point; a point outside the
    OPEN strip; a radius reaching the strip boundary (``r >= min(re, 1 - re)``); a pair with
    ``(2r)^2 >= dist^2`` (touching or overlapping discs).
    """
    pts = []
    for k, p in enumerate(points):
        if len(tuple(p)) != 2:
            raise ValueError(f"disjoint_discs: point {k} must be an (re, im) pair; got {p!r}")
        re_, im_ = sp.nsimplify(p[0]), sp.nsimplify(p[1])
        for nm, v in ((f"re[{k}]", re_), (f"im[{k}]", im_)):
            if not v.is_rational:
                raise ValueError(f"disjoint_discs: {nm} must be rational; got {v!r}")
        pts.append((sp.Rational(re_), sp.Rational(im_)))
    rq = sp.nsimplify(r)
    if not rq.is_rational:
        raise ValueError(f"disjoint_discs: radius must be rational; got {r!r}")
    rq = sp.Rational(rq)
    if rq <= 0:
        raise ValueError(f"disjoint_discs: radius must be positive; got r={rq}")
    if not pts:
        raise ValueError("disjoint_discs: need at least one point (the empty instance is vacuous)")

    # strip membership + margin (the boundary negative control)
    margins = []
    for k, (re_, im_) in enumerate(pts):
        if not (0 < re_ < 1):
            raise ValueError(
                f"disjoint_discs: point {k} = ({re_}, {im_}) is not in the OPEN strip 0 < re < 1; "
                f"refused (a boundary point has no disc inside the strip)")
        m = min(re_, 1 - re_)
        if rq >= m:
            raise ValueError(
                f"disjoint_discs: radius r={rq} reaches the strip boundary at point {k} "
                f"(margin min(re, 1-re) = {m}); the closed disc leaves the OPEN strip; refused")
        margins.append(m)

    # pairwise strict separation (the overlap negative control)
    seps = []
    two_r_sq = (2 * rq) ** 2
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            dx = pts[i][0] - pts[j][0]
            dy = pts[i][1] - pts[j][1]
            d2 = dx ** 2 + dy ** 2
            if d2 == 0:
                raise ValueError(
                    f"disjoint_discs: points {i} and {j} coincide ({pts[i]}); distinct centres are "
                    f"required (a ball is never disjoint from itself); refused")
            if two_r_sq >= d2:
                raise ValueError(
                    f"disjoint_discs: pair ({i},{j}) has (2r)^2 = {two_r_sq} >= dist^2 = {d2} — the "
                    f"discs touch or overlap, so they are NOT disjoint; refused")
            seps.append(d2)

    return DisjointDiscsCertificate(
        points=tuple(pts), r=rq,
        min_sep_sq=(min(seps) if seps else sp.Integer(0)),
        min_margin=min(margins),
    )


def certify_disjoint_discs_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` — a dict with keys ``points`` and ``r``."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = disjoint_discs_certificate(spec["points"], spec["r"])
    elif isinstance(spec, (tuple, list)):
        cert = disjoint_discs_certificate(spec[0], spec[1])
    else:
        raise ValueError(f"disjoint_discs spec must be a dict or (points, r) tuple; got {spec!r}")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


_STRIP = "{s : ℂ | 0 < s.re ∧ s.re < 1}"


@dataclass
class DisjointDiscsEmitter(Emitter):
    """Emit the concrete isolation instance: point defs, the `Finset`, one disjointness theorem per
    pair, one strip-containment theorem per point, and the assembled existential — the registry
    node `MM_offline_disjoint_discs`'s conclusion at explicit data.

    The emitted file uses `Quasicrystal.abs_re_sub_le_dist` from the island's `OfflineDiscs` lib, so
    it must be built inside the quasicrystal island (profile imports `Mathlib` and `OfflineDiscs`).
    """

    def __post_init__(self):
        self.kind = "disjoint_discs"
        self.requires_prelude = ()

    def _gate_type(self, base: str) -> str:
        return (
            f"∃ r : ℝ, 0 < r ∧\n"
            f"      (∀ z ∈ {base}_S, ∀ w ∈ {base}_S, z ≠ w →\n"
            f"        Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧\n"
            f"      (∀ z ∈ {base}_S, Metric.closedBall z r ⊆ {_STRIP})"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: DisjointDiscsCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            n = len(cert.points)
            rr = rat_lean(cert.r)

            lines.append(
                f"/-- Isolation instance `{base}`: {n} explicitly given point(s) of the open\n"
                f"    critical strip, with the rational radius `r = {rr}`.  Certified separation\n"
                f"    `min dist² = {cert.min_sep_sq}` and strip margin `min (re, 1 - re) = {cert.min_margin}`,\n"
                f"    both strictly beating `(2r)² = {(2 * cert.r) ** 2}` resp. `r`.\n"
                f"    conjecture1_proved = False — the points are INPUT, not a claim about ζ. -/\n"
            )
            for k, (re_, im_) in enumerate(cert.points):
                lines.append(
                    f"noncomputable def {base}_p{k} : ℂ := ⟨({rat_lean(re_)}), ({rat_lean(im_)})⟩\n")
            elems = ", ".join(f"{base}_p{k}" for k in range(n))
            lines.append(f"\nnoncomputable def {base}_S : Finset ℂ := {{{elems}}}\n\n")

            # per-pair disjointness
            for i in range(n):
                for j in range(i + 1, n):
                    lines.append(
                        f"/-- Pair ({i},{j}): `(2·{rr})² < dist²`, so the closed discs are disjoint. -/\n"
                        f"theorem {base}_pair_{i}_{j} :\n"
                        f"    Disjoint (Metric.closedBall {base}_p{i} (({rr}) : ℝ))\n"
                        f"      (Metric.closedBall {base}_p{j} (({rr}) : ℝ)) := by\n"
                        f"  apply Metric.closedBall_disjoint_closedBall\n"
                        f"  rw [Complex.dist_eq, Complex.norm_def, Real.lt_sqrt (by norm_num)]\n"
                        f"  simp only [{base}_p{i}, {base}_p{j}, Complex.normSq_apply,\n"
                        f"    Complex.sub_re, Complex.sub_im]\n"
                        f"  norm_num\n\n"
                    )
                    nthm += 1

            # per-point strip containment
            for k, (re_, _im) in enumerate(cert.points):
                lines.append(
                    f"/-- Point {k}: the closed disc of radius `{rr}` about `{base}_p{k}`\n"
                    f"    (real part `{rat_lean(re_)}`) stays inside the OPEN strip. -/\n"
                    f"theorem {base}_strip_{k} :\n"
                    f"    Metric.closedBall {base}_p{k} (({rr}) : ℝ) ⊆ {_STRIP} := by\n"
                    f"  intro s hs\n"
                    f"  have hd : dist s {base}_p{k} ≤ (({rr}) : ℝ) := Metric.mem_closedBall.mp hs\n"
                    f"  have hre := abs_le.mp (Quasicrystal.abs_re_sub_le_dist s {base}_p{k})\n"
                    f"  have hz : ({base}_p{k}).re = (({rat_lean(re_)}) : ℝ) := by\n"
                    f"    simp only [{base}_p{k}]\n"
                    f"  rw [hz] at hre\n"
                    f"  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩\n\n"
                )
                nthm += 1

            # the assembly: the registry node's conclusion at this concrete Finset
            pair_arms = []
            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue
                    a, b = min(i, j), max(i, j)
                    suffix = "" if (i, j) == (a, b) else ".symm"
                    pair_arms.append(f"        | exact {base}_pair_{a}_{b}{suffix}\n")
            pair_block = "".join(sorted(set(pair_arms)))
            strip_arms = "".join(f"    · exact {base}_strip_{k}\n" for k in range(n))
            rcases_z = " | ".join(["rfl"] * n)

            lines.append(
                f"/-- **Isolation instance** ({base}): the concrete witness for the registry node\n"
                f"    `MM_offline_disjoint_discs` at these {n} point(s) — radius `r = {rr}` makes the\n"
                f"    closed discs pairwise disjoint and keeps each inside the open critical strip.\n"
                f"    conjecture1_proved = False. -/\n"
                f"theorem {base} :\n"
                f"    {self._gate_type(base)} := by\n"
                f"  refine ⟨(({rr}) : ℝ), by norm_num, ?_, ?_⟩\n"
                f"  · intro z hz w hw hzw\n"
                f"    simp only [{base}_S, Finset.mem_insert, Finset.mem_singleton] at hz hw\n"
                f"    rcases hz with {rcases_z} <;> rcases hw with {rcases_z} <;>\n"
                f"      first\n"
                f"        | exact absurd rfl hzw\n"
                f"{pair_block}"
                f"  · intro z hz\n"
                f"    simp only [{base}_S, Finset.mem_insert, Finset.mem_singleton] at hz\n"
                f"    rcases hz with {rcases_z}\n"
                f"{strip_arms}\n"
            )
            nthm += 1
            gate = self.emit_gate(base, self._gate_type(base))
            if gate:
                lines.append(gate + "\n")
        return "".join(lines), nthm


def disjoint_discs_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a disjoint_discs family (kind='disjoint_discs').  ``spec``: ``pt -> {"points": [...],
    "r": ...}`` or ``pt -> (points, r)``.  Refuses overlapping discs, boundary-reaching radii,
    duplicate points and non-positive radii at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("disjoint_discs", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    PTS = [("1/2", "7067/500"), ("1/2", "10511/500"), ("2/5", "10511/500")]
    print("=== positive cert (3 strip points, r = 1/50) ===")
    c = disjoint_discs_certificate(PTS, "1/50")
    print(f"cert OK: min dist² = {c.min_sep_sq}, (2r)² = {(2 * c.r) ** 2}, margin = {c.min_margin}")
    print("\n=== NEGATIVE CONTROL 1: radius too large (r = 1/20, pair (1,2) at dist 1/10) ===")
    try:
        disjoint_discs_certificate(PTS, "1/20")
        raise SystemExit("FAIL: overlapping discs not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== NEGATIVE CONTROL 2: a point on the strip boundary (re = 1) ===")
    try:
        disjoint_discs_certificate([("1", "5"), ("1/2", "9")], "1/100")
        raise SystemExit("FAIL: boundary point not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean ===")
    fam = disjoint_discs_family(
        "T", GridSpec([("case", [0])]), lambda pt: "disjoint_discs_demo",
        spec=lambda pt: {"points": PTS, "r": "1/50"})
    inst, _ = certify_disjoint_discs_point(fam, {"case": 0}, "disjoint_discs_demo")

    class _V:
        instances = [inst]

    body, nthm = DisjointDiscsEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")

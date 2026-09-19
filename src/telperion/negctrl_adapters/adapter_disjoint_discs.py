"""Negative-control adapter for DisjointDiscsEmitter (MIRRORMERE E4b isolation instances).

The load-bearing content of an isolation instance is the per-pair STRICT separation
`(2r)^2 < dist^2`, emitted as a `norm_num` goal after `Real.lt_sqrt` eliminates the square root.
The radius `r` is a supplied number: inflate it past half the true separation and the emitted
theorem becomes FALSE (the two closed discs genuinely intersect), so the trusted kernel must reject
it.  Layer 1 (`disjoint_discs_certificate`) already refuses such an r; this adapter mints the frozen
dataclass BY HAND to bypass that guard and let the kernel be the arbiter.

FALSE forgery: the two points `1/2 + (7067/500) i` and `2/5 + (7067/500) i` are exactly `1/10` apart,
with the forged radius `r = 1/10` -- so `(2r)^2 = 1/25` is FOUR times the true `dist^2 = 1/100`, the
discs overlap grossly, and `norm_num` refutes the emitted strict inequality.

TRUE twin: the same two points with the honest radius `r = 1/50` -- `(2r)^2 = 1/625 < 1/100`, and
both strip margins (`1/2` and `2/5`) clear `1/50` -- a genuine isolation instance, compiles clean.

The emitted strip-containment proofs call the island lemma `Quasicrystal.abs_re_sub_le_dist`
(`OfflineDiscs.lean`), so the adapter supplies it verbatim as its Lean `prelude`; it is a two-line
consequence of `Complex.abs_re_le_norm`, proved from plain Mathlib, so the control still runs against
a bare Mathlib env.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_disjoint_discs import DisjointDiscsCertificate, DisjointDiscsEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# The two strip points used by both twins: real parts 1/2 and 2/5 at a common height, so the true
# separation is exactly 1/10 and dist^2 = 1/100 -- small, exact, and easy to read off.
_PTS = (
    (sp.Rational(1, 2), sp.Rational(7067, 500)),
    (sp.Rational(2, 5), sp.Rational(7067, 500)),
)

# The island lemma the emitted strip-containment proofs call, restated from plain Mathlib.
_PRELUDE = """namespace Quasicrystal

theorem abs_re_sub_le_dist (s z : ℂ) : |s.re - z.re| ≤ dist s z := by
  have h := Complex.abs_re_le_norm (s - z)
  rw [Complex.sub_re] at h
  rwa [dist_eq_norm]

end Quasicrystal
"""


def make_false_cert() -> DisjointDiscsCertificate:
    """Hand-forged FALSE cert: r = 1/10, so (2r)^2 = 1/25 EXCEEDS dist^2 = 1/100 -- the discs
    overlap and the emitted pair theorem is false (Layer 1 would refuse this cert)."""
    return DisjointDiscsCertificate(
        points=_PTS, r=sp.Rational(1, 10),
        min_sep_sq=sp.Rational(1, 100), min_margin=sp.Rational(2, 5),
    )


def make_true_cert() -> DisjointDiscsCertificate:
    """Paired TRUE twin: the same points with r = 1/50 -- (2r)^2 = 1/625 < 1/100 = dist^2 and both
    strip margins clear the radius; a genuine isolation instance."""
    return DisjointDiscsCertificate(
        points=_PTS, r=sp.Rational(1, 50),
        min_sep_sq=sp.Rational(1, 100), min_margin=sp.Rational(2, 5),
    )


def _emit(cert: DisjointDiscsCertificate, name: str) -> str:
    return emit_via_single_instance_family(
        DisjointDiscsEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="DisjointDiscsEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=_PRELUDE,
        allow_axioms=(),
        label=(
            "forged isolation instance with r = 1/10 on two points 1/10 apart: (2r)^2 = 1/25 "
            "exceeds dist^2 = 1/100, the closed discs overlap, kernel rejects the norm_num "
            "separation goal; true twin (same points, r = 1/50) compiles"
        ),
        imports_line="import Mathlib",
    )
)

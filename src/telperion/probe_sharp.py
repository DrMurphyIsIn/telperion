"""The sharpness probe: where does the CERTIFICATE break, and where does the
TRUTH break?

G3/G4's breakthrough came from widening the environment cap from 3/16 to 1/5
and discovering 35/36 cells survive — the question "how far does my
certificate method stretch, relative to the claim itself?" drove the
gap-narrowing phase.  This probe answers it for any cap-parametrized family:
bisect the cap between certification-success and certification-failure (the
certificate boundary), then hunt for actual counterexamples beyond it (the
truth boundary).  The gap between the two boundaries is exactly the room a
better certificate method could win.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .certify import CertificationError, certify
from .hunt import hunt_minimum


@dataclass(frozen=True)
class SharpnessReport:
    cert_lo: sp.Rational        # certification still succeeds here
    cert_hi: sp.Rational        # certification fails here
    truth_witness: dict | None  # exact counterexample at some cap > cert bound
    truth_cap: sp.Rational | None

    def render(self) -> str:
        out = [
            f"certificate boundary: succeeds at cap = {self.cert_lo}, "
            f"fails by cap = {self.cert_hi}"
        ]
        if self.truth_witness is not None:
            wit = ", ".join(f"{k} = {v}" for k, v in self.truth_witness.items())
            out.append(
                f"truth boundary: claim FALSE at cap = {self.truth_cap} ({wit}) — "
                "the certificate method is near-sharp"
            )
        else:
            out.append(
                "no counterexample found beyond the certificate boundary — the "
                "gap between method and truth may be real room to improve "
                "(or the hunt budget was too small)"
            )
        return "\n".join(out)


def sharpness(
    builder,
    lo: sp.Rational,
    hi: sp.Rational,
    steps: int = 6,
    hunt_iters: int = 300,
    workers: int = 1,
) -> SharpnessReport:
    """builder(cap: sympy Rational) -> InequalityFamily.  Requires
    certification to succeed at `lo` and fail by `hi` (raises otherwise).
    Bisects `steps` times; then hunts for a truth counterexample at `hi`
    (direct families: the minimum of any instance's target)."""

    def certifies(cap) -> bool:
        try:
            certify(builder(cap), workers=workers)
            return True
        except CertificationError:
            return False

    if not certifies(lo):
        raise ValueError(f"certification already fails at lo = {lo}")
    if certifies(hi):
        raise ValueError(f"certification still succeeds at hi = {hi} — widen hi")
    a, b = sp.Rational(lo), sp.Rational(hi)
    for _ in range(steps):
        mid = (a + b) / 2
        if certifies(mid):
            a = mid
        else:
            b = mid
    # truth hunt at the failing end
    fam = builder(b)
    witness, wit_cap = None, None
    if fam.kind == "direct":
        for pt in fam.grid.points():
            res = hunt_minimum(fam.target(pt), fam.symbols, iters=hunt_iters)
            if res.is_disproof:
                witness = dict(res.argmin)
                witness["grid_point"] = dict(pt)
                wit_cap = b
                break
    return SharpnessReport(cert_lo=a, cert_hi=b, truth_witness=witness, truth_cap=wit_cap)

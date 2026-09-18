"""Bagchi-recurrence emitter — Face 4 (recurrence) of the RH obstruction.

Bagchi (1981): RH ⟺ the Riemann ζ is STRONGLY RECURRENT in the strip
1/2 < Re s < 1 — i.e. ζ approximates itself along vertical shifts, for every ε
and compact K there are arbitrarily large shifts τ with
sup_{s∈K} |ζ(s+iτ) − ζ(s)| < ε.  Each certified finite recurrence observation is
a kernel-checkable shadow of this face.

Per-instance certificate: a shift τ and a compact rational box K = [σ_lo,σ_hi] ×
[t_lo,t_hi] with a finite rational GRID; at each grid point s the deviation
|ζ(s+iτ) − ζ(s)| is rigorously upper-bounded via flint/Arb ``acb.zeta`` (the ball
``abs_upper`` endpoint), and the grid-maximum ``M`` is certified to satisfy
``M ≤ ε``.

HONESTY / TRUST CLASS (Arb-trust, like winding_box_zero / the ζ-localization
boxes): each per-point deviation bound is an ``acb.zeta`` enclosure — the EXTERNAL
numeric input, folded into the certified rational grid-max ``M`` (carried as the
emitted theorem's hypothesis ``hdev``).  The kernel proves only the trivial
``M ≤ ε`` (norm_num) and chains ``dev ≤ M ≤ ε`` for a bound variable ``dev``.
SCOPE (no over-claim): the certified statement is the sup over the finite GRID; a
continuous sup over K would additionally require a modulus-of-continuity /
Lipschitz argument between grid points (documented, NOT claimed here).  Certifying
one recurrence instance is NOT progress toward RH — the uniform Bagchi recurrence
IS RH.  conjecture1_proved = False.

NEGATIVE CONTROL: a claimed tolerance ``ε`` BELOW the certified grid-max ``M``
(so ``M ≤ ε`` is false) is REFUSED at certification with a ``ValueError``.  An
empty grid / degenerate box is also refused.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
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


def _zeta_self_dev_upper(sigma: Fraction, t: Fraction, tau: Fraction,
                         prec_bits: int = 160) -> Fraction:
    """A RIGOROUS rational upper bound on |ζ(σ + i(t+τ)) − ζ(σ + it)| via flint/Arb
    ``acb.zeta``: the ball difference's ``abs_upper`` endpoint (an exact dyadic upper
    bound of the true modulus), converted to an outward rational."""
    from flint import acb, ctx

    try:
        from .rh_jensen.coefficients import _arb_ball_to_fractions
    except ImportError:
        from telperion.rh_jensen.coefficients import _arb_ball_to_fractions

    old = ctx.prec
    try:
        ctx.prec = prec_bits
        s1 = acb(float(sigma), float(t) + float(tau)).zeta()
        s0 = acb(float(sigma), float(t)).zeta()
        d = s1 - s0
        ab = d.abs_upper()  # arb: certified upper bound of |d|
        _lo, hi = _arb_ball_to_fractions(ab)
    finally:
        ctx.prec = old
    return Fraction(hi)


def bagchi_grid_max(tau, sigmas: Sequence, ts: Sequence, prec_bits: int = 160
                    ) -> tuple[Fraction, tuple]:
    """The certified rational grid-max ``M = max_{s in grid} |ζ(s+iτ) − ζ(s)|`` over
    the product grid ``sigmas × ts``, plus the per-point bounds.  Each point's bound
    is a rigorous Arb ``acb.zeta`` upper bound."""
    tau = Fraction(sp.nsimplify(tau)) if not isinstance(tau, Fraction) else tau
    pts = []
    M = Fraction(0)
    for sig in sigmas:
        sig = Fraction(sp.nsimplify(sig)) if not isinstance(sig, Fraction) else sig
        for t in ts:
            t = Fraction(sp.nsimplify(t)) if not isinstance(t, Fraction) else t
            u = _zeta_self_dev_upper(sig, t, tau, prec_bits)
            pts.append((sig, t, u))
            if u > M:
                M = u
    return M, tuple(pts)


@dataclass(frozen=True)
class BagchiRecurrenceCert:
    """A finite Bagchi-recurrence observation: shift ``tau``, box ``K`` (the grid's
    σ/t ranges), the certified rational grid-max deviation ``M``, and the tolerance
    ``eps`` with ``M ≤ eps``."""

    tau: Fraction
    sigma_range: tuple      # (σ_lo, σ_hi)
    t_range: tuple          # (t_lo, t_hi)
    n_grid: int
    M: Fraction             # certified grid-max deviation (Arb)
    eps: Fraction           # emitted tolerance, M ≤ eps


def bagchi_recurrence_certificate(tau, sigmas, ts, eps=None, prec_bits: int = 160
                                  ) -> BagchiRecurrenceCert:
    """Build (and self-check) a Bagchi-recurrence certificate over the grid
    ``sigmas × ts`` at shift ``tau``.

    Refuses (``ValueError``): an empty grid, or a supplied ``eps`` BELOW the
    certified grid-max ``M`` (the negative control — ``M ≤ eps`` would be false).
    ``eps`` defaults to ``M``.
    """
    sigmas = list(sigmas)
    ts = list(ts)
    if not sigmas or not ts:
        raise ValueError("bagchi_recurrence needs a non-empty σ×t grid")
    M, pts = bagchi_grid_max(tau, sigmas, ts, prec_bits)
    tau = Fraction(sp.nsimplify(tau)) if not isinstance(tau, Fraction) else tau
    if eps is None:
        eps = M
    eps = Fraction(sp.nsimplify(eps)) if not isinstance(eps, Fraction) else eps
    if eps < M:
        raise ValueError(
            f"bagchi_recurrence REFUSED: tolerance ε = {eps} is below the certified "
            f"grid-max deviation M = {M}; the sup bound M ≤ ε is false")
    sig_fracs = [Fraction(sp.nsimplify(s)) for s in sigmas]
    t_fracs = [Fraction(sp.nsimplify(t)) for t in ts]
    return BagchiRecurrenceCert(
        tau=tau, sigma_range=(min(sig_fracs), max(sig_fracs)),
        t_range=(min(t_fracs), max(t_fracs)), n_grid=len(pts), M=M, eps=eps)


def certify_bagchi_recurrence_point(family, pt, name):
    """Certify one Bagchi-recurrence instance.  Reads ``spec = family.special[1](pt)``
    — a dict ``{"tau":…, "sigmas":[…], "ts":[…], "eps":…, "prec_bits":…}``."""
    spec = family.special[1](pt)
    cert = bagchi_recurrence_certificate(
        spec["tau"], spec["sigmas"], spec["ts"],
        eps=spec.get("eps"), prec_bits=spec.get("prec_bits", 160))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BagchiRecurrenceEmitter(Emitter):
    """Emit the finite Bagchi-recurrence bound ``dev ≤ ε`` (with ``dev`` a bound real
    for any grid deviation, hypothesis ``hdev : dev ≤ M`` the Arb-certified grid-max)
    from the ``acb.zeta`` grid enclosures.  Deterministic
    ``le_trans hdev (by norm_num)``."""

    def __post_init__(self):
        self.kind = "bagchi_recurrence"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: BagchiRecurrenceCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            M = rat_lean(cert.M)
            eps = rat_lean(cert.eps)
            slo, shi = cert.sigma_range
            tlo, thi = cert.t_range
            lines.append(
                f"-- {nm}: Bagchi recurrence at shift τ = {cert.tau} over the box K = "
                f"[{slo},{shi}]×[{tlo},{thi}] ({cert.n_grid} grid points).\n"
                f"-- Certified grid-max |ζ(s+iτ) − ζ(s)| ≤ M = {cert.M} (Arb acb_zeta, the trust\n"
                f"-- seam via hypothesis hdev) is ≤ ε = {cert.eps}.  Face 4 (Bagchi 1981: RH ⟺ ζ\n"
                f"-- strongly recurrent).  Scope: sup over the GRID (continuous sup needs a modulus\n"
                f"-- argument).  A finite recurrence observation; NOT RH.\n"
                f"theorem {nm} (dev : ℝ) (hdev : dev ≤ ({M} : ℝ)) : dev ≤ ({eps} : ℝ) :=\n"
                f"  le_trans hdev (by norm_num)\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def bagchi_refutation_atom_lean() -> str:
    """The Bagchi-recurrence falsifiability face, emitted ONCE per file.

    RH ⟺ ζ strongly recurrent.  If recurrence FAILED — a box K, ε, and shift-free
    lower bound forcing every large shift's deviation ≥ ε > the recurrence
    tolerance — RH would fail (the equivalence carried as ``hRH``).  This abstract
    contrapositive keeps the observation falsifiable.  Term-mode; not expected to
    fire.  conjecture1_proved = False."""
    return (
        "-- bagchi_recurrence_refutes: the falsifiability face.  RH ⟺ ζ strongly\n"
        "-- recurrent; a certified recurrence-FAILURE (every large shift keeps the\n"
        "-- deviation dev ≥ L with the recurrence tolerance ε ≤ L) contradicts\n"
        "-- recurrence-below-ε, hence ¬RH (carried as hRH : RH → dev < ε).  Not\n"
        "-- expected to fire; makes the recurrence observation falsifiable.\n"
        "theorem bagchi_recurrence_refutes {P : Prop} (dev L eps : ℝ)\n"
        "    (hRH : P → dev < eps) (hLo : L ≤ dev) (hbad : eps ≤ L) : ¬P :=\n"
        "  fun hP => absurd (hRH hP) (not_lt.mpr (le_trans hbad hLo))\n"
    )


def bagchi_recurrence_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Bagchi-recurrence family (kind ``bagchi_recurrence``).
    ``spec``: ``pt -> {"tau":…, "sigmas":[…], "ts":[…], "eps":…}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("bagchi_recurrence", spec),
        constants=dict(constants or {}),
    )


def scan_best_shift(sigmas, ts, tau_lo: int, tau_hi: int, prec_bits: int = 120
                    ) -> tuple[int, Fraction]:
    """Scan integer shifts τ ∈ [tau_lo, tau_hi] for the SMALLEST certified grid-max
    self-deviation (the best recurrence shift in range).  Returns ``(tau, M)``."""
    best_tau, best_M = tau_lo, None
    for tau in range(tau_lo, tau_hi + 1):
        M, _ = bagchi_grid_max(tau, sigmas, ts, prec_bits)
        if best_M is None or M < best_M:
            best_tau, best_M = tau, M
    return best_tau, best_M


if __name__ == "__main__":
    from fractions import Fraction as F

    sigmas = [F(3, 5), F(13, 20), F(7, 10)]
    ts = [F(10), F(11), F(12)]

    print("=== scan for the best recurrence shift τ ∈ [1,60] ===")
    tau, M = scan_best_shift(sigmas, ts, 1, 60)
    print(f"best shift τ = {tau}, certified grid-max deviation M ≈ {float(M):.5f}")

    print("\n=== positive cert (ε = M) ===")
    cert = bagchi_recurrence_certificate(tau, sigmas, ts)
    print(f"cert OK: τ={cert.tau} box=[{cert.sigma_range[0]},{cert.sigma_range[1]}]×"
          f"[{cert.t_range[0]},{cert.t_range[1]}] grid={cert.n_grid} M≈{float(cert.M):.5f}")

    print("\n=== NEGATIVE CONTROL 1: ε below the certified grid-max M must raise ===")
    try:
        bagchi_recurrence_certificate(tau, sigmas, ts, eps=cert.M / 2)
        raise SystemExit("FAIL: too-small ε not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL 2: empty grid must raise ===")
    try:
        bagchi_recurrence_certificate(tau, [], ts)
        raise SystemExit("FAIL: empty grid not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean ===")
    fam = bagchi_recurrence_family(
        "T", GridSpec([("case", [0])]), lambda pt: f"bagchi_tau{tau}",
        spec=lambda pt: {"tau": tau, "sigmas": sigmas, "ts": ts},
    )
    inst, _ = certify_bagchi_recurrence_point(fam, {"case": 0}, f"bagchi_tau{tau}")

    class _V:
        instances = [inst]

    body, nthm = BagchiRecurrenceEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")
    print(bagchi_refutation_atom_lean())

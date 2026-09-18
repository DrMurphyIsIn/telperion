"""exp-enclosure emitter -- kernel-checked RATIONAL BRACKETS of `Real.exp` (and of the
recurrence deficit `e^d + e^-d - 2` and `Real.cosh`) from Mathlib's `Real.exp_bound`.

WHY THIS EMITTER EXISTS
-----------------------
MIRRORMERE's `MM_bragg_defect_witness` (artifact
`examples/zeta_zero_localization/lean/BraggDefect.lean`) states its off-line leakage witness
UNDER a named hypothesis

    hexp : expLo <= Real.exp (1 / 10) /\\ Real.exp (1 / 10) <= expHi ,

an Arb (python-flint) enclosure carried as an assumption -- the node's read-back says
`closure_clean` stays false "until that enclosure is itself reflected".  The registry had no
emitter for `exp` brackets: `emit_transcendental_enclosure` ships only a `log` face, and
`emit_log_combination` uses `Real.exp_bound'` as an internal degree-3 step, never as a
standalone certificate.  This emitter is that missing face: it turns the Arb seam into a
kernel theorem, so the hypothesis can be discharged and the witness stated unconditionally.

THE MATHEMATICS (one Mathlib fact, no analysis of our own)
----------------------------------------------------------
    Real.exp_bound {x : R} (hx : |x| <= 1) {n : N} (hn : 0 < n) :
        |Real.exp x - sum_{m in range n} x^m / m!| <= |x|^n * (n.succ / (n! * n))

For a RATIONAL `x` with `|x| <= 1` both the partial sum `S_n = sum_{m<n} x^m/m!` and the
remainder `r_n = |x|^n * (n+1)/(n! * n)` are EXACT rationals, so `Real.exp x` lies in the
exact rational TAYLOR BOX `[S_n - r_n, S_n + r_n]`.  A certificate is a CLAIMED rational
bracket `[lo, hi]`; it is honest exactly when the Taylor box is contained in the claim, and
the emitted proof is then pure `norm_num` + `linarith` on that containment.

WHAT THE CERTIFICATE CERTIFIES (read this before citing it)
-----------------------------------------------------------
Only the stated rational enclosure of a transcendental constant at ONE rational point.  It is
a finite, kernel-checkable arithmetic fact.  It says nothing whatever about RH, about the
zeros of zeta, or about the diffraction experiment whose hypothesis it discharges -- it
discharges a NUMERIC hypothesis, and the experiment's own scope statements are unchanged.

ANTI-PHANTOM REFUSALS (the forge face)
--------------------------------------
`exp_enclosure_certificate` REFUSES, never widens or weakens:

* `|x| > 1`            -- outside `Real.exp_bound`'s hypothesis.  (The halving trick
                          `exp x = (exp (x/2))^2` would extend the range; it is deliberately
                          NOT implemented silently -- a follow-on, stated here so the
                          limitation is visible rather than worked around.)
* `n < 1` or `n > 64`  -- the order cap; beyond it the `norm_num [Nat.factorial]` step is not
                          the intended cheap kernel check, so we refuse rather than emit Lean
                          we have not sized.
* `lo > hi`            -- an inverted claim.
* `lo > S_n - r_n` or `hi < S_n + r_n` -- THE FORGE CASE: a claimed bracket the Taylor box
                          does NOT imply.  This is refused at EVERY order up to the cap, so a
                          too-tight (or simply false) claim can never ship.
* deficit mode with `x <= 0` -- the deficit is 0 at `x = 0`, and the QC_RECURRENCE row-(a)
                          reading needs a strictly positive displacement.
* non-rational input   -- symbolic or float `x`/`lo`/`hi` (a float would silently smuggle in
                          its binary expansion).

MODES
-----
* `exp`      -- `lo <= Real.exp x <= hi`
* `exp_neg`  -- `lo <= Real.exp (-x) <= hi`
* `deficit`  -- `lo <= Real.exp x + Real.exp (-x) - 2 <= hi` (QC_RECURRENCE row a; the numeric
                twin of `MM_recurrence_deficit_eq_excess`, and `BraggDefect.excess`'s bracket).
                Carries BOTH Taylor boxes and self-checks the claim against their sum.
* `cosh`     -- `lo <= Real.cosh x <= hi` via `Real.cosh_eq` on the same two boxes (the
                `ZooDH.cosh_bracket` input shape).

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import factorial
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

#: Taylor orders above this are refused (the `norm_num [Nat.factorial]` step is sized for
#: orders the BraggDefect / ZooDH literals actually need -- `n = 14` at `x = 1/10`).
MAX_ORDER = 64

MODES = ("exp", "exp_neg", "deficit", "cosh")


def _rat(v, what: str) -> sp.Rational:
    """Exactly-rational coercion; REFUSES floats and symbolic values."""
    if isinstance(v, float):
        raise ValueError(
            f"exp_enclosure REFUSED: {what} was given as a float ({v!r}); a float carries its "
            "binary expansion, not the rational you wrote -- pass a str/Fraction/sp.Rational")
    try:
        q = sp.Rational(v)
    except (TypeError, ValueError) as exc:
        raise ValueError(
            f"exp_enclosure REFUSED: {what} = {v!r} is not rational ({exc})") from None
    if not isinstance(q, sp.Rational):
        raise ValueError(f"exp_enclosure REFUSED: {what} = {v!r} is not rational")
    return q


def _F(q: sp.Rational) -> Fraction:
    return Fraction(int(q.p), int(q.q))


def taylor_box(x: sp.Rational, n: int) -> tuple[sp.Rational, sp.Rational]:
    """The EXACT rational order-`n` Taylor box `[S_n - r_n, S_n + r_n]` for `Real.exp x`."""
    S, r = taylor_parts(x, n)
    return S - r, S + r


def taylor_parts(x: sp.Rational, n: int) -> tuple[sp.Rational, sp.Rational]:
    """`(S_n, r_n)`: the exact partial sum and the exact `Real.exp_bound` remainder."""
    xf = _F(x)
    S = sum((xf ** m / factorial(m) for m in range(n)), Fraction(0))
    r = abs(xf) ** n * Fraction(n + 1, factorial(n) * n)
    return sp.Rational(S.numerator, S.denominator), sp.Rational(r.numerator, r.denominator)


@dataclass(frozen=True)
class ExpEnclosureCert:
    """One exp-enclosure certificate.

    `partial_sum`/`remainder` are the EXACT order-`n` `Real.exp_bound` data at `x`
    (`remainder` depends only on `|x|`, so it serves the `-x` box too);
    `partial_sum_neg` is the partial sum at `-x`, carried in the two-sided modes
    (`deficit`, `cosh`).  `lo`/`hi` are the CLAIMED bracket -- the statement itself.
    """

    x: sp.Rational
    n: int
    partial_sum: sp.Rational
    remainder: sp.Rational
    lo: sp.Rational
    hi: sp.Rational
    mode: str
    partial_sum_neg: sp.Rational | None = None

    @property
    def box(self) -> tuple[sp.Rational, sp.Rational]:
        """The Taylor box of the QUANTITY THIS CERTIFICATE CLAIMS (mode-dependent)."""
        S, r = self.partial_sum, self.remainder
        if self.mode == "exp":
            return S - r, S + r
        if self.mode == "exp_neg":
            Sm = self.partial_sum_neg if self.partial_sum_neg is not None else S
            return Sm - r, Sm + r
        Sm = self.partial_sum_neg
        if Sm is None:  # pragma: no cover -- constructor always supplies it
            raise ValueError(f"exp_enclosure REFUSED: mode {self.mode} needs partial_sum_neg")
        if self.mode == "deficit":
            return (S - r) + (Sm - r) - 2, (S + r) + (Sm + r) - 2
        if self.mode == "cosh":
            return ((S - r) + (Sm - r)) / 2, ((S + r) + (Sm + r)) / 2
        raise ValueError(f"exp_enclosure REFUSED: unknown mode {self.mode!r}")

    @property
    def slack(self) -> tuple[sp.Rational, sp.Rational]:
        """`(box_lo - lo, hi - box_hi)` -- both must be >= 0 for the claim to be implied."""
        blo, bhi = self.box
        return blo - self.lo, self.hi - bhi


def _mode_box(x: sp.Rational, n: int, mode: str) -> tuple[sp.Rational, sp.Rational]:
    plo, phi = taylor_box(x, n)
    if mode == "exp":
        return plo, phi
    mlo, mhi = taylor_box(-x, n)
    if mode == "exp_neg":
        return mlo, mhi
    if mode == "deficit":
        return plo + mlo - 2, phi + mhi - 2
    return (plo + mlo) / 2, (phi + mhi) / 2  # cosh


def exp_enclosure_certificate(x, lo, hi, *, mode: str = "exp", n: int | None = None,
                              max_order: int = MAX_ORDER) -> ExpEnclosureCert:
    """Build (and exactly re-check) an exp-enclosure certificate.

    `n=None` selects the LEAST Taylor order (<= `max_order`) whose exact box fits inside the
    CLAIMED `[lo, hi]`; if no order fits, the claim is REFUSED -- never widened.  An explicit
    `n` is checked at that order alone.  See the module docstring for the refusal list.
    """
    if mode not in MODES:
        raise ValueError(
            f"exp_enclosure REFUSED: unknown mode {mode!r} (expected one of {MODES})")
    xq = _rat(x, "x")
    loq = _rat(lo, "lo")
    hiq = _rat(hi, "hi")
    if abs(xq) > 1:
        raise ValueError(
            f"exp_enclosure REFUSED: |x| = {abs(xq)} > 1 is outside Real.exp_bound's hypothesis "
            "(the halving identity exp x = (exp (x/2))^2 would extend the range; it is a "
            "deliberate follow-on, not applied silently)")
    if loq > hiq:
        raise ValueError(f"exp_enclosure REFUSED: inverted bracket lo = {loq} > hi = {hiq}")
    if mode == "deficit" and xq <= 0:
        raise ValueError(
            f"exp_enclosure REFUSED: deficit mode needs x > 0, got x = {xq} (the deficit "
            "e^x + e^-x - 2 vanishes at 0; the QC_RECURRENCE row-(a) reading needs d > 0)")
    if n is not None:
        if not isinstance(n, int) or isinstance(n, bool):
            raise ValueError(f"exp_enclosure REFUSED: Taylor order n = {n!r} is not an int")
        if n < 1:
            raise ValueError(f"exp_enclosure REFUSED: Taylor order n = {n} < 1 "
                             "(Real.exp_bound needs 0 < n)")
        if n > max_order:
            raise ValueError(
                f"exp_enclosure REFUSED: Taylor order n = {n} exceeds the cap {max_order}")
        orders = [n]
    else:
        orders = list(range(1, max_order + 1))

    chosen = None
    for k in orders:
        blo, bhi = _mode_box(xq, k, mode)
        if loq <= blo and bhi <= hiq:
            chosen = k
            break
    if chosen is None:
        blo, bhi = _mode_box(xq, orders[-1], mode)
        raise ValueError(
            f"exp_enclosure REFUSED at x = {xq} (mode {mode}): the claimed bracket "
            f"[{loq}, {hiq}] is NOT implied by the Taylor box -- at order {orders[-1]} the box "
            f"is [{blo}, {bhi}] (box_lo - lo = {blo - loq}, hi - box_hi = {hiq - bhi}; both must "
            "be >= 0).  Widen the claim or raise the order cap; the emitter does neither for you")

    S, r = taylor_parts(xq, chosen)
    Sneg, _ = taylor_parts(-xq, chosen)
    cert = ExpEnclosureCert(
        x=xq, n=chosen, partial_sum=S, remainder=r, lo=loq, hi=hiq, mode=mode,
        partial_sum_neg=Sneg,
    )
    slo, shi = cert.slack
    if slo < 0 or shi < 0:  # pragma: no cover -- the search above already guarantees this
        raise ValueError(
            f"exp_enclosure REFUSED: post-check failed, slack = ({slo}, {shi})")
    return cert


def certify_exp_enclosure_point(family, pt, name):
    """Certify one exp-enclosure point: ``(CertifiedInstance, 1)``.

    Reads the spec dict from ``family.special[1](pt)`` -- keys ``x``, ``lo``, ``hi`` and the
    optional ``mode`` / ``n`` / ``max_order`` -- and re-checks it via
    :func:`exp_enclosure_certificate` (which raises on every dishonest claim)."""
    spec = family.special[1](pt)
    cert = exp_enclosure_certificate(
        spec["x"], spec["lo"], spec["hi"],
        mode=spec.get("mode", "exp"),
        n=spec.get("n"),
        max_order=spec.get("max_order", MAX_ORDER),
    )
    return CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert), 1


# --- Lean rendering ---------------------------------------------------------

_TACTIC = (
    "  have hb := Real.exp_bound {habs} (n := {n}) (by norm_num)\n"
    "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb\n"
    "  rw [abs_le] at hb\n"
    "  obtain ⟨h1, h2⟩ := hb\n"
    "  constructor\n"
    "  · norm_num [Nat.factorial] at h1 ⊢; linarith\n"
    "  · norm_num [Nat.factorial] at h2 ⊢; linarith\n"
)


def _exp_lemma(nm: str, xs: str, n: int, lo: str, hi: str, *, neg: bool) -> str:
    """One `Real.exp_bound` bracket lemma, for `exp x` (`neg=False`) or `exp (-x)`."""
    arg = f"(-({xs}))" if neg else f"({xs})"
    habs = (f"  have hx : |(({xs}) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num\n"
            f"  have hx' : |((-({xs})) : ℝ)| ≤ 1 := by rwa [abs_neg]\n") if neg else (
        f"  have hx : |(({xs}) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num\n")
    return (
        f"theorem {nm} : (({lo}) : ℝ) ≤ Real.exp {arg} ∧ Real.exp {arg} ≤ (({hi}) : ℝ) := by\n"
        + habs
        + _TACTIC.format(habs="hx'" if neg else "hx", n=n)
    )


@dataclass
class ExpEnclosureEmitter(Emitter):
    """Emit rational brackets of `Real.exp` / the recurrence deficit / `Real.cosh` at a
    rational point, each proved from Mathlib's `Real.exp_bound` at the certified order by
    `norm_num [Nat.factorial]` + `linarith`.  No `decide`, no `sorry`; the claimed bracket IS
    the statement and `exp_enclosure_certificate` refuses any claim the exact Taylor box does
    not imply.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "exp_enclosure"

    def _header(self, cert: ExpEnclosureCert, nm: str) -> str:
        slo, shi = cert.slack
        blo, bhi = cert.box
        what = {
            "exp": f"Real.exp ({cert.x})",
            "exp_neg": f"Real.exp (-({cert.x}))",
            "deficit": f"Real.exp ({cert.x}) + Real.exp (-({cert.x})) - 2",
            "cosh": f"Real.cosh ({cert.x})",
        }[cert.mode]
        return (
            f"/-- `{nm}` -- a certified RATIONAL ENCLOSURE of `{what}`.\n"
            f"    Order-{cert.n} `Real.exp_bound` box `[S - r, S + r]` (exact rationals,\n"
            f"    S = sum_(m < {cert.n}) x^m/m!, r = |x|^{cert.n} * ({cert.n}+1)/({cert.n}! * {cert.n})),\n"
            f"    which lies inside the claimed bracket with slack ({slo}, {shi}) >= 0;\n"
            f"    box = [{blo}, {bhi}].  The order is the LEAST one whose box fits -- the\n"
            f"    generator REFUSES a bracket the box does not imply rather than widening it.\n"
            f"    A finite arithmetic fact about a transcendental constant at one rational\n"
            f"    point; nothing about RH.  conjecture1_proved = False. -/\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: ExpEnclosureCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            xs = rat_lean(cert.x)
            lo = rat_lean(cert.lo)
            hi = rat_lean(cert.hi)
            lines.append(self._header(cert, nm))
            if cert.mode in ("exp", "exp_neg"):
                lines.append(_exp_lemma(nm, xs, cert.n, lo, hi, neg=(cert.mode == "exp_neg")))
                n_thm += 1
                continue

            # two-sided modes: both exp faces as named lemmas, then the combination
            plo, phi = taylor_box(cert.x, cert.n)
            mlo, mhi = taylor_box(-cert.x, cert.n)
            lines.append(
                f"-- the `exp ({cert.x})` face of {nm} (its own exact order-{cert.n} box)\n"
                + _exp_lemma(f"{nm}_pos", xs, cert.n, rat_lean(plo), rat_lean(phi), neg=False))
            lines.append(
                f"-- the `exp (-({cert.x}))` face of {nm} (same order, same remainder)\n"
                + _exp_lemma(f"{nm}_neg", xs, cert.n, rat_lean(mlo), rat_lean(mhi), neg=True))
            n_thm += 2
            if cert.mode == "deficit":
                lines.append(
                    f"theorem {nm} : (({lo}) : ℝ) ≤ Real.exp ({xs}) + Real.exp (-({xs})) - 2 ∧\n"
                    f"    Real.exp ({xs}) + Real.exp (-({xs})) - 2 ≤ (({hi}) : ℝ) := by\n"
                    f"  constructor <;> linarith [{nm}_pos.1, {nm}_pos.2, {nm}_neg.1, {nm}_neg.2]\n"
                )
            else:  # cosh
                lines.append(
                    f"theorem {nm} : (({lo}) : ℝ) ≤ Real.cosh ({xs}) ∧ "
                    f"Real.cosh ({xs}) ≤ (({hi}) : ℝ) := by\n"
                    f"  rw [Real.cosh_eq]\n"
                    f"  constructor <;> linarith [{nm}_pos.1, {nm}_pos.2, {nm}_neg.1, {nm}_neg.2]\n"
                )
            n_thm += 1
        return "\n".join(lines), n_thm


def exp_enclosure_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an exp-enclosure family (kind ``exp_enclosure``).

    ``spec: pt -> {"x", "lo", "hi", optional "mode"/"n"/"max_order"}`` -- the rational point
    and the CLAIMED bracket; the order is chosen (least fitting) at certify time."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("exp_enclosure", spec),
        constants=dict(constants or {}),
    )

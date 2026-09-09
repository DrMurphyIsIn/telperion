"""EnclosureIntervalFold emitter (kind ``enclosure_interval_fold``) — the
integer near-CUE row-band checker, distilled from the ``anthropics/zeta-23-lean``
PairCeiling development (``NumericCert.lean`` / ``RowCert.lean``).

The upstream ``ceiling_nearCUE`` bound controls a discrepancy ``|E| ≤ 1/(6N²) +
τ/(2N)`` from the fact that every scaled row value ``N·S(j)`` lies within a near-
CUE band ``|N·S(j) − j| ≤ τ`` (j = 1 .. N−1).  That analytic prelude is CITED,
NOT emitted here.  What IS emitted is the SELF-CONTAINED integer core of that
band check: a running interval-propagation predicate ``rowsOK`` that verifies, in
pure ℤ arithmetic, that each supplied interval enclosure ``[loⱼ, hiⱼ]`` of the
scaled value ``K·S(j)`` sits inside the scaled band ``[K·j − τK, K·j + τK]``
(τK = K·τ).  The whole predicate is decidable and the theorem is closed by the
Lean kernel via ``decide`` (or ``native_decide`` for large N).

TRUST SEAM (documented, honest): the interval enclosures ``[loⱼ, hiⱼ]`` come from
EXTERNAL Arb interval arithmetic on the actual row values — they are INPUTS to
the certificate, not something the kernel establishes.  The kernel checks only
that those integer enclosures lie in the integer band; it does not re-derive the
enclosures from ζ.  The emitted theorem is therefore a genuine, non-vacuous
kernel-checked integer fact about the supplied data — and no more.

``conjecture1_proved = False``.  This is a per-instance band-membership
certificate, NOT a proof of RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean  # noqa: F401  (kept for parity with sibling emitters)
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# `decide` on a list of length N unfolds `rowsOK` N times; each step is a pair of
# ℤ comparisons.  Beyond this ceiling the kernel `decide` becomes impractical and
# the certify builder REFUSES rather than emit a theorem that will time out in CI
# (the R7 972-cell "never grind blind" lesson).  Larger N should route through a
# `native_decide` variant deliberately, not by accident.
DECIDE_N_CEILING = 64


@dataclass(frozen=True)
class EnclosureIntervalFoldCert:
    """The integer near-CUE row-band certificate for one instance.

    ``encl`` is the tuple of integer interval enclosures ``(loⱼ, hiⱼ)`` of the
    scaled row values ``K·S(j)`` for j = 1 .. N−1 (so ``N = len(encl) + 1``).
    ``K`` is the integer scale, ``tauK = K·τ`` the integer near-CUE tolerance
    numerator.  The kernel-checkable claim is: for every j,
    ``K·j − tauK ≤ loⱼ`` AND ``hiⱼ ≤ K·j + tauK``.
    """

    K: int
    tauK: int
    encl: tuple[tuple[int, int], ...]
    use_native: bool = False

    @property
    def N(self) -> int:
        return len(self.encl) + 1


def enclosure_interval_fold_certificate(
    K, tauK, encl: Sequence[Sequence[int]], *, use_native: bool = False
) -> EnclosureIntervalFoldCert:
    """Build (and exactly re-check) the integer near-CUE row-band certificate.

    REFUSES: ``K ≤ 0``; ``tauK < 0``; an empty enclosure list; any enclosure with
    ``loⱼ > hiⱼ`` (an inconsistent interval); a period ``N`` beyond
    ``DECIDE_N_CEILING`` unless ``use_native=True`` (then the emitted proof uses
    ``native_decide``); and — crucially — any row whose enclosure does NOT sit in
    the integer band (a FALSE claim, refused before any Lean is written).
    """
    K = int(K)
    tauK = int(tauK)
    if K <= 0:
        raise ValueError(
            f"enclosure_interval_fold REFUSED: need integer scale K > 0; got K={K}")
    if tauK < 0:
        raise ValueError(
            f"enclosure_interval_fold REFUSED: need tolerance numerator τK ≥ 0; got τK={tauK}")
    encl_t = tuple((int(lo), int(hi)) for lo, hi in encl)
    if not encl_t:
        raise ValueError(
            "enclosure_interval_fold REFUSED: empty enclosure list (nothing to certify)")
    for j, (lo, hi) in enumerate(encl_t, start=1):
        if lo > hi:
            raise ValueError(
                f"enclosure_interval_fold REFUSED: inconsistent enclosure at j={j}: "
                f"lo={lo} > hi={hi}")
    N = len(encl_t) + 1
    if N > DECIDE_N_CEILING and not use_native:
        raise ValueError(
            f"enclosure_interval_fold REFUSED: N={N} exceeds the `decide` ceiling "
            f"{DECIDE_N_CEILING} (kernel decide would be impractical); pass "
            f"use_native=True to emit a `native_decide` proof deliberately")
    # exact re-check of the band-membership claim (the certificate gate): the SAME
    # integer predicate the Lean kernel will re-decide.  A false row is refused now.
    for j, (lo, hi) in enumerate(encl_t, start=1):
        if not (K * j - tauK <= lo and hi <= K * j + tauK):
            raise ValueError(
                f"enclosure_interval_fold REFUSED: row j={j} enclosure [{lo}, {hi}] "
                f"is OUTSIDE the near-CUE band [{K * j - tauK}, {K * j + tauK}] "
                f"(K={K}, τK={tauK}) — the claim is FALSE, nothing to certify")
    return EnclosureIntervalFoldCert(K=K, tauK=tauK, encl=encl_t, use_native=use_native)


def certify_enclosure_interval_fold_point(family, pt, name):
    """Certify one enclosure-fold instance: ``(CertifiedInstance, n_checks)``.

    Reads ``spec = family.special[1](pt)`` as either ``(K, tauK, encl)`` or
    ``(K, tauK, encl, use_native)``.  ``n_checks`` is the number of rows whose
    band membership was re-verified exactly (= N − 1), the non-vacuity witness.
    """
    spec = family.special[1](pt)
    if len(spec) == 4:
        K, tauK, encl, use_native = spec
    else:
        K, tauK, encl = spec
        use_native = False
    cert = enclosure_interval_fold_certificate(K, tauK, encl, use_native=use_native)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.encl)


@dataclass
class EnclosureIntervalFoldEmitter(Emitter):
    """Emit the self-contained integer near-CUE row-band checker + its ``decide``
    theorem.  For each instance:

      * ``rowsOK K τK j encl`` — a fueled ℤ interval-propagation predicate
        (structural recursion on the enclosure list; kernel-reducible);
      * ``enclData_<name>`` — the generator's integer enclosures;
      * ``theorem <name> : rowsOK <K> <τK> 0 enclData_<name> = true := by decide``.

    ``rowsOK`` is emitted ONCE (shared across all instances in the family).  The
    Arb enclosures are the documented trust seam; the kernel checks only integer
    band membership.  Self-contained over ℤ (no Mathlib row lemmas)."""

    def __post_init__(self):
        self.kind = "enclosure_interval_fold"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [
            "-- Integer near-CUE row-band checker (self-contained ℤ interval",
            "-- propagation).  `rowsOK K τK j encl` holds iff every enclosure",
            "-- [loⱼ, hiⱼ] (of the scaled row value K·S(j)) lies in the scaled band",
            "-- [K·j − τK, K·j + τK].  Trust seam: the enclosures are supplied by",
            "-- external Arb interval arithmetic (INPUTS); the kernel checks only",
            "-- that they sit in the integer band.  The analytic discrepancy bound",
            "-- |E| ≤ 1/(6N²) + τ/(2N) (ceiling_nearCUE) is the CITED prelude, NOT",
            "-- emitted here.  conjecture1_proved = False.",
            "def rowsOK (K τK : Int) : Nat → List (Int × Int) → Bool",
            "  | _, [] => true",
            "  | j, (lo, hi) :: t =>",
            "      decide (K * (Int.ofNat j + 1) - τK ≤ lo)",
            "        && decide (hi ≤ K * (Int.ofNat j + 1) + τK)",
            "        && rowsOK K τK (j + 1) t",
            "",
        ]
        n_thm = 0
        for inst in fam.instances:
            cert: EnclosureIntervalFoldCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            data = ", ".join(
                f"({_int_lean(lo)}, {_int_lean(hi)})" for lo, hi in cert.encl)
            tactic = "native_decide" if cert.use_native else "decide"
            lines.append(
                f"-- {nm}: near-CUE band check for N={cert.N}, scale K={cert.K}, "
                f"tolerance numerator τK={cert.tauK} "
                f"(exact-evaluated pre-emission; kernel {tactic} is the final gate).\n"
                f"def enclData_{nm} : List (Int × Int) := [{data}]\n"
                f"\n"
                f"set_option maxRecDepth 100000 in\n"
                f"theorem {nm} : rowsOK {_int_lean(cert.K)} {_int_lean(cert.tauK)} 0 "
                f"enclData_{nm} = true := by {tactic}\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def _int_lean(v: int) -> str:
    """Render an integer literal as Lean source, parenthesizing negatives."""
    v = int(v)
    return str(v) if v >= 0 else f"(-{-v})"


def enclosure_interval_fold_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an enclosure-interval-fold family (kind ``enclosure_interval_fold``).

    ``spec: pt -> (K, tauK, encl)`` (or ``(K, tauK, encl, use_native)``) with
    ``encl`` a sequence of integer ``(loⱼ, hiⱼ)`` enclosures of ``K·S(j)`` for
    j = 1 .. N−1.  The claim is evaluated exactly in Python at certification; the
    Lean kernel re-decides the integer band membership."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("enclosure_interval_fold", spec),
        constants=dict(constants or {}),
    )

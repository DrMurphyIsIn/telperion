"""AdmissibleTuple emitter (kind ``admissible_tuple``) — the prime-gaps admissible
k-tuple certificate, distilled from the ``bgp212`` Lemma 12.1 shape (the 45-tuple
H45 is admissible with diameter 212).

BACKGROUND.  A finite set of integers H = {h1 < ... < hk} is ADMISSIBLE iff for
every prime p the residues {hi mod p} omit at least one residue class mod p (i.e.
they do not cover all of Z/pZ).  The Dickson–Hardy–Littlewood / GPY–Maynard–Tao
sieve machinery gives the implication:

    DHL[k, 2]  +  an admissible k-tuple of diameter d   ==>   H1 <= d

(bounded gaps between primes).  That sieve implication is the CITED theorem; it is
NOT emitted here.  What IS emitted is the SELF-CONTAINED, fully decidable core:
the admissibility check itself.

KEY FINITENESS FACT (why this is decidable at all).  Only primes p <= k need to
be checked.  For p > k, a set of k residues cannot cover all p residue classes
mod p (pigeonhole: k < p classes), so the omit-a-class condition is automatic.
Hence admissibility reduces to a FINITE conjunction over the primes p <= k, each
of which is a finite scan over p residue classes -- a fully decidable Bool check
that the Lean kernel closes by ``decide``.

The emitted checker is core-Lean only (no Mathlib): ``coversAllResidues`` and
``admissibleCheck`` over ``List Int`` / ``List Nat``, plus inline fold-based
max/min for the diameter theorem.  Int ``%`` (Int.emod) returns a residue in
[0, p) for positive p, matching the mathematical residue convention; the Python
re-check uses the same convention (Python ``%`` on a positive modulus).

TRUST SEAM (documented, honest): the generator supplies both the tuple H and the
list of primes p <= k.  ``certify`` RE-VERIFIES in Python that the prime list is
*exactly* the primes <= k (so the finiteness reduction is not silently
under-checked), that H is distinct and sorted, that the diameter matches, and --
crucially -- that H really is admissible (an INADMISSIBLE tuple is REFUSED before
any Lean is written; the canonical negative control {0, 2, 4}, which covers all
residues mod 3, is refused).  The kernel then re-decides the same finite check.

``conjecture1_proved = False``.  This is a per-instance admissibility certificate,
NOT a proof of the bounded-gaps theorem (the DHL implication is cited, not proven).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# `decide` unfolds the admissibility conjunction over the primes p <= k, and for
# each such p scans p residue classes against all k tuple entries.  Beyond this
# ceiling the kernel `decide` becomes impractical and the certify builder REFUSES
# rather than emit a theorem that will time out in CI (the R7 "never grind blind"
# lesson).  bgp212's k = 45 must fit under this cap, so it is set at 60.
K_CEILING = 60


def _primes_upto(k: int) -> tuple[int, ...]:
    """The primes p with p <= k (a small sieve; k is capped at K_CEILING)."""
    if k < 2:
        return ()
    sieve = bytearray([1]) * (k + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(k ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, k + 1, i):
                sieve[j] = 0
    return tuple(i for i in range(2, k + 1) if sieve[i])


def _covers_all_residues(p: int, H: Sequence[int]) -> bool:
    """Do the residues {h mod p : h in H} cover ALL classes mod p?  (Python ``%``
    on positive p yields a residue in [0, p), matching Lean's Int.emod.)"""
    return {h % p for h in H} >= set(range(p))


@dataclass(frozen=True)
class AdmissibleTupleCert:
    """The admissible k-tuple certificate for one instance.

    ``H`` is the tuple (strictly increasing tuple of integers), ``primes`` the
    list of primes p <= k that the check ranges over (= exactly the primes <= k,
    re-verified at certification), and ``diameter`` = max H - min H.  The
    kernel-checkable claim is ``admissibleCheck primes H = true`` together with
    the diameter equality.
    """

    H: tuple[int, ...]
    primes: tuple[int, ...]
    diameter: int

    @property
    def k(self) -> int:
        return len(self.H)


def admissible_tuple_certificate(H: Sequence[int]) -> AdmissibleTupleCert:
    """Build (and exactly re-check) the admissible k-tuple certificate for ``H``.

    The prime list is DERIVED here as exactly the primes <= k (the finiteness
    reduction), so a caller cannot under-supply it.

    REFUSES: an empty tuple or a singleton (nothing to certify -- a single point
    is trivially admissible/vacuous); non-integer entries; a tuple that is not
    strictly increasing (duplicates or out-of-order); a size k beyond
    ``K_CEILING`` (kernel decide impractical); and -- crucially -- any
    INADMISSIBLE tuple (some prime p <= k whose residues cover all of Z/pZ; a
    FALSE admissibility claim, refused before any Lean is written).  The canonical
    negative control {0, 2, 4} (covers all residues mod 3) is refused here.
    """
    H_t = tuple(int(h) for h in H)
    if len(H_t) < 2:
        raise ValueError(
            "admissible_tuple REFUSED: need at least 2 distinct entries "
            f"(a k-tuple with k >= 2); got {list(H_t)}")
    for a, b in zip(H_t, H_t[1:]):
        if a >= b:
            raise ValueError(
                "admissible_tuple REFUSED: entries must be strictly increasing "
                f"(distinct and sorted); got {list(H_t)}")
    k = len(H_t)
    if k > K_CEILING:
        raise ValueError(
            f"admissible_tuple REFUSED: k={k} exceeds the `decide` ceiling "
            f"{K_CEILING} (kernel decide would be impractical)")
    primes = _primes_upto(k)
    # exact re-check of admissibility (the certificate gate): the SAME finite
    # conjunction the Lean kernel will re-decide.  A prime whose residues cover
    # every class mod p makes the tuple inadmissible -- refuse now.
    for p in primes:
        if _covers_all_residues(p, H_t):
            covered = sorted({h % p for h in H_t})
            raise ValueError(
                f"admissible_tuple REFUSED: tuple {list(H_t)} is INADMISSIBLE -- "
                f"residues mod {p} cover ALL classes (residues={covered}); "
                "the admissibility claim is FALSE, nothing to certify")
    diameter = H_t[-1] - H_t[0]
    return AdmissibleTupleCert(H=H_t, primes=primes, diameter=diameter)


def certify_admissible_tuple_point(family, pt, name):
    """Certify one admissible-tuple instance: ``(CertifiedInstance, n_checks)``.

    Reads ``H = family.special[1](pt)`` (a sequence of integers).  ``n_checks`` is
    the number of primes p <= k whose omit-a-class condition was re-verified
    exactly (= len(primes)), the non-vacuity witness -- at least one prime (p=2)
    for every admissible tuple with k >= 2.
    """
    H = family.special[1](pt)
    cert = admissible_tuple_certificate(H)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.primes)


@dataclass
class AdmissibleTupleEmitter(Emitter):
    """Emit the self-contained core-Lean admissibility checker + its ``decide``
    theorems.  For each instance:

      * ``tupleH_<name>`` -- the generator's tuple as a ``List Int``;
      * ``theorem <name>_admissible : admissibleCheck [<primes<=k>] tupleH_<name>
        = true := by decide``;
      * ``theorem <name>_diameter : tupleMax tupleH_<name> - tupleMin
        tupleH_<name> = <d> := by decide``.

    The shared checker (``coversAllResidues``, ``admissibleCheck``, and the inline
    fold-based ``tupleMax`` / ``tupleMin``) is emitted ONCE across the family.
    Core-Lean only (no Mathlib).  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "admissible_tuple"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [
            "-- Admissible k-tuple checker (self-contained, core Lean only).  A set",
            "-- H = {h1 < ... < hk} is ADMISSIBLE iff for every prime p the residues",
            "-- {hi mod p} omit at least one class mod p.  KEY FINITENESS FACT: only",
            "-- primes p <= k need checking -- for p > k, k residues cannot cover all",
            "-- p classes (pigeonhole), so admissibility is a FINITE decidable check.",
            "-- The generator supplies the exact prime list p <= k (re-verified in",
            "-- Python).  Int `%` (Int.emod) yields a residue in [0, p) for positive",
            "-- p, matching the residue convention.  The DHL[k,2] + diameter => H1<=d",
            "-- sieve implication (bgp212 Lemma 12.1 shape) is the CITED theorem, NOT",
            "-- emitted here.  conjecture1_proved = False.",
            "def coversAllResidues (p : Nat) (H : List Int) : Bool :=",
            "  (List.range p).all (fun r => H.any (fun h => h % (p : Int) == (r : Int)))",
            "",
            "def admissibleCheck (ps : List Nat) (H : List Int) : Bool :=",
            "  ps.all (fun p => !(coversAllResidues p H))",
            "",
            "-- Inline fold-based diameter endpoints (core-only; no List.maximum?).",
            "def tupleMax (H : List Int) : Int :=",
            "  H.foldl (fun a b => if a < b then b else a) (H.headD 0)",
            "",
            "def tupleMin (H : List Int) : Int :=",
            "  H.foldl (fun a b => if b < a then b else a) (H.headD 0)",
            "",
        ]
        n_thm = 0
        for inst in fam.instances:
            cert: AdmissibleTupleCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            data = ", ".join(_int_lean(h) for h in cert.H)
            primes = ", ".join(str(p) for p in cert.primes)
            lines.append(
                f"-- {nm}: admissible {cert.k}-tuple, diameter {cert.diameter}, "
                f"checked over primes p <= {cert.k} = [{primes}] "
                f"(exact-evaluated pre-emission; kernel decide is the final gate).\n"
                f"def tupleH_{nm} : List Int := [{data}]\n"
                f"\n"
                f"set_option maxRecDepth 100000 in\n"
                f"theorem {nm}_admissible : "
                f"admissibleCheck [{primes}] tupleH_{nm} = true := by decide\n"
                f"\n"
                f"set_option maxRecDepth 100000 in\n"
                f"theorem {nm}_diameter : "
                f"tupleMax tupleH_{nm} - tupleMin tupleH_{nm} = {_int_lean(cert.diameter)} "
                f":= by decide\n"
            )
            n_thm += 2
        return "\n".join(lines), n_thm


def _int_lean(v: int) -> str:
    """Render an integer literal as Lean source, parenthesizing negatives."""
    v = int(v)
    return str(v) if v >= 0 else f"(-{-v})"


def admissible_tuple_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an admissible-tuple family (kind ``admissible_tuple``).

    ``spec: pt -> H`` with ``H`` a strictly-increasing sequence of integers.  The
    admissibility claim (and the exact prime list p <= k) is evaluated exactly in
    Python at certification; the Lean kernel re-decides the finite check."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("admissible_tuple", spec),
        constants=dict(constants or {}),
    )

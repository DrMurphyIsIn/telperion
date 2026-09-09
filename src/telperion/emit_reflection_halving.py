"""ReflectionHalving emitter (kind ``reflection_halving``) — the finite
instance of the reflection / functional-equation halving bound

    N ≤ 2 · N_large       (total count ≤ twice the "large"/``Re ≥ 1/2`` part)

ported from the Anthropic ``zeta-23-lean`` development (RvM/Halving.lean,
``N_le_two_mul_half``).  A reflection involution (here: the functional
equation ``s ↦ 1 − s̄``) pairs each item of the "small" part (``Re < 1/2``)
injectively with an item of the "large" part (``Re ≥ 1/2``); consequently the
total weight of the small part is bounded by that of the large part, and the
grand total is at most twice the large part.

This emitter ships the SELF-CONTAINED, KERNEL-CHECKED finite instance
(honesty option (A)):

* the generator supplies a FINITE list of items, each a positive integer
  weight ``w_i`` with a Boolean ``large_i`` tag (is it in the ``Re ≥ 1/2``
  part), together with the involution's OUTPUT — the guarantee that the small
  part's total weight is ≤ the large part's;
* the ``certify_*`` builder RE-COMPUTES both totals exactly in Python and
  REFUSES any data where ``small > large`` (i.e. where the pairing witness
  would be missing) — no false-shaped certificate is ever emitted;
* the emitted theorem states the concrete integer fact ``total ≤ 2 * large``
  with ``total`` and ``large`` as literal integer sums, discharged by kernel
  ``decide``.  Because the builder guarantees ``small ≤ large`` (hence
  ``total = small + large ≤ 2 * large``), the emitted ``decide`` fact is a
  TRUE, NON-VACUOUS arithmetic statement — the kernel is the final gate.

GENERAL LEMMA it instantiates (honesty option (B), the hypothesis-driven
prelude this concrete instance is a decidable witness of):

    theorem N_le_two_mul_half {ι} (s : Finset ι) (w : ι → ℤ)
        (large : ι → Prop) [DecidablePred large]
        (hpos : ∀ i ∈ s, 0 ≤ w i)
        (hfold : (∑ i ∈ s.filter (fun i => ¬ large i), w i)
                   ≤ (∑ i ∈ s.filter (fun i => large i), w i)) :
        (∑ i ∈ s, w i) ≤ 2 * (∑ i ∈ s.filter (fun i => large i), w i)

proved by ``Finset.sum_filter_add_sum_filter_not`` + ``linarith``.  Here
``hfold`` is exactly the involution's output (the trust seam of the general
form); the concrete emitter needs no such hypothesis because it re-derives
``small ≤ large`` from the explicit weights and REFUSES otherwise.

Reusable for palindromic / reciprocal-polynomial root counts and
functional-equation zero counts.  ``conjecture1_proved = False``.  This is a
generic finite-combinatorial certificate, NOT a step toward RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class ReflectionHalvingCert:
    """One finite reflection-halving instance.

    ``items`` is the tuple of ``(w_i, large_i)`` pairs (positive integer
    weight, Boolean "is in the large/``Re ≥ 1/2`` part" tag).  ``small`` and
    ``large`` are the exact integer part-totals; the certified fact is
    ``total = small + large ≤ 2 * large``, which holds because the builder has
    verified ``small ≤ large`` (the involution's output)."""

    items: tuple[tuple[int, bool], ...]
    small: int
    large: int

    @property
    def total(self) -> int:
        return self.small + self.large


def reflection_halving_certificate(items: Sequence[tuple[int, bool]]) -> ReflectionHalvingCert:
    """Build (and exactly re-check) a finite reflection-halving certificate.

    ``items``: a sequence of ``(w_i, large_i)`` — positive integer weight and a
    Boolean tag marking membership of the "large"/``Re ≥ 1/2`` part.

    REFUSES (raises ``ValueError``, the negative control):
      * empty data (nothing to fold);
      * any non-positive weight ``w_i ≤ 0``;
      * data where the small-part total exceeds the large-part total
        (``small > large``) — the involution witness would be MISSING, so the
        halving bound is not a theorem here; refuse rather than emit a
        false-shaped certificate.
    """
    norm: list[tuple[int, bool]] = []
    for it in items:
        w, large = it
        wv = int(w)
        if wv <= 0:
            raise ValueError(
                f"reflection_halving REFUSED: weights must be positive integers; got w={w}")
        norm.append((wv, bool(large)))
    if not norm:
        raise ValueError(
            "reflection_halving REFUSED: empty data (no items to fold)")
    small = sum(w for w, lg in norm if not lg)
    large = sum(w for w, lg in norm if lg)
    if small > large:
        raise ValueError(
            f"reflection_halving REFUSED: small-part total {small} > large-part total "
            f"{large} — the pairing involution witness is missing, so N ≤ 2·N_large is "
            "not a theorem for this data")
    # exact re-validation of the emitted decide fact: total = small + large and
    # total ≤ 2 * large (equivalently small ≤ large), both over ℤ.
    total = small + large
    assert total == sum(w for w, _ in norm)
    assert total <= 2 * large
    return ReflectionHalvingCert(items=tuple(norm), small=small, large=large)


def certify_reflection_halving_point(family, pt, name):
    """Certify one reflection-halving instance: ``(CertifiedInstance, n_checks)``.

    Reads ``items = family.special[1](pt)``.  ``n_checks = 2`` (the
    ``total = small + large`` identity and the ``total ≤ 2·large`` bound), both
    re-verified exactly in ``reflection_halving_certificate``."""
    items = family.special[1](pt)
    cert = reflection_halving_certificate(items)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


@dataclass
class ReflectionHalvingEmitter(Emitter):
    """Emit the finite reflection-halving fact ``total ≤ 2 * large`` (with
    ``total`` and ``large`` as literal integer sums), discharged by kernel
    ``decide`` over ℤ.  Self-contained and non-vacuous — the builder has
    already verified ``small ≤ large`` (the involution's output), so the
    emitted decide fact is true.  Instantiates the general
    ``N_le_two_mul_half`` lemma documented in the module docstring."""

    def __post_init__(self):
        self.kind = "reflection_halving"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: ReflectionHalvingCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            # literal integer sums, rendered deterministically in input order.
            all_terms = " + ".join(rat_lean(w) for w, _ in cert.items)
            large_terms = [rat_lean(w) for w, lg in cert.items if lg]
            large_sum = " + ".join(large_terms) if large_terms else "0"
            lines.append(
                f"-- {nm}: finite reflection/functional-equation halving instance "
                f"N ≤ 2·N_large (RvM/Halving N_le_two_mul_half).\n"
                f"-- {len(cert.items)} items; small-part total = {cert.small}, "
                f"large-part total = {cert.large}, grand total = {cert.total}.\n"
                f"-- The reflection involution (s ↦ 1 − s̄) pairs the small (Re<1/2) part\n"
                f"-- injectively into the large (Re≥1/2) part; its OUTPUT small ≤ large is\n"
                f"-- re-derived exactly and REFUSED otherwise, so this decide fact is true.\n"
                f"theorem {nm} : ({all_terms} : ℤ) ≤ 2 * ({large_sum}) := by decide\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def reflection_halving_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a reflection-halving family (kind ``reflection_halving``).

    ``spec: pt -> items`` where ``items`` is a sequence of ``(w_i, large_i)``
    pairs (positive integer weight, Boolean "large"/``Re ≥ 1/2`` tag).  The
    theorem is a closed ℤ statement, so a single dummy symbol carries the grid.
    """
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("reflection_halving", spec),
        constants=dict(constants or {}),
    )

"""p-adic valuation emitter — first-class Tier-1 arm.

Promotes the hand-assembled padic_valuation block into a pipeline-enforced
family of ValuationFact instances.  Each fact `v_p(n) = k` is emitted as a
decidable divisibility theorem:

    theorem <name> : (p^k ∣ n) ∧ ¬ (p^(k+1) ∣ n) := by norm_num

The tactic is always `norm_num` (the frozen shape is decidable divisibility —
no reliance on `padicValNat` reduction).  Ordering is fixed (grid iteration
order, then fact order within each point) so the output is byte-stable across
Python runs.

When the family declares product / telescoping structure the SPLIT_LEMMA and
TELESCOPE_LEMMA primitives from `padic.py` may be included in the prelude; add
them to `LeanProfile(prelude=SPLIT_LEMMA + TELESCOPE_LEMMA)` at the call site.

HONEST SCOPE: these are the 23-adic PRIMITIVES (the node-by-node cancellation
accounting), NOT the Brualdi-Goldwasser crux.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from .certify import CertifiedInstance
from .certify import CertificationError as _CE
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .padic import ValuationFact
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_valuation_point(family, pt, name):
    """Certify one valuation instance: (CertifiedInstance, n_checks).

    Iterates every ValuationFact in family.valuation_facts(pt), calls
    fact.check() (exact Fraction re-derivation via padic_val), and raises
    ValueError naming the first failing fact.  A correct fact has padic_val(n,
    p) == k; the negative control is refused here before any Lean is produced.

    Returns (CertifiedInstance, n_checks_performed) on green.
    """
    raw_facts = list(family.valuation_facts(pt))
    n_checks = 0
    for f in raw_facts:
        if not isinstance(f, ValuationFact):
            raise ValueError(
                f"valuation_facts returned a non-ValuationFact object: {f!r}"
            )
        if not f.check():
            from .padic import padic_val as _pv
            actual = _pv(f.n, f.p) if f.n != 0 else "undefined"
            raise ValueError(
                f"ValuationFact '{f.name}' REFUSED: claimed v_{f.p}({f.n}) = "
                f"{f.k}, engine says {actual}"
            )
        n_checks += 1

    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        valuation=tuple(raw_facts),
    )
    return inst, n_checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class PadicValuationEmitter(Emitter):
    """Emit one Lean `norm_num` divisibility theorem per ValuationFact.

    Each certified instance contributes one theorem per fact stored on
    `inst.valuation`, using `ValuationFact.lean(tactic='norm_num')` — the
    exact frozen shape:

        theorem <name> : (p^k ∣ n) ∧ ¬ (p^(k+1) ∣ n) := by norm_num

    Ordering is deterministic: grid-iteration order, facts in the order
    returned by the family's valuation_facts callable."""

    def __post_init__(self):
        self.kind = "valuation"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_theorems = 0
        for inst in fam.instances:
            facts: tuple[ValuationFact, ...] = inst.valuation  # type: ignore[assignment]
            if not facts:
                continue
            for f in facts:
                lines.append(f.lean(tactic="norm_num"))
                n_theorems += 1
        return "".join(lines), n_theorems


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def valuation_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    facts: Callable,
    prime: int = 23,
    constants: dict | None = None,
) -> InequalityFamily:
    """Convenience constructor for a valuation family (kind='valuation').

    Parameters
    ----------
    name
        Family name (used in the Lean file header and manifest).
    grid
        The finite parameter grid (GridSpec).
    lean_name
        A callable ``pt -> str`` mapping each grid point to a Lean theorem
        base name.  The emitter appends per-fact suffixes if a point has
        multiple facts.
    facts
        A callable ``pt -> Sequence[ValuationFact]`` returning the valuation
        facts for each grid point.  Certified by certify_valuation_point before
        any Lean is emitted.
    prime
        The prime whose valuation this family certifies (default 23).  Stored
        as a family constant for the input hash.
    constants
        Additional family constants (passed through to InequalityFamily).
    """
    consts = dict(constants or {})
    consts["prime"] = prime
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        valuation_facts=facts,
        constants=consts,
    )

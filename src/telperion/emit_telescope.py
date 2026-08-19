"""Telescoping-potential emitter — the README-tracked-open "generic induction
emission for telescoping potentials", as a first-class shape.

A large class of recursive/tree bounds have the form "a sum of per-node local
terms is bounded", closed by a POTENTIAL `P` satisfying a per-node
super-solution inequality:

    local(v) + Σ_{c ∈ children(v)} P(c)  ≤  P(v)     (super-solution, per node)
    ────────────────────────────────────────────────────────────────────────
    Σ_{v ∈ tree} local(v)  ≤  P(root)               (telescopes)

The sum telescopes: every node's `P` appears once as `+P(v)` (its own term) and
once as `−P(v)` (in its parent's child-sum), leaving only `P(root)`.  FINDING a
closed-form `P` is the hard part (and, for the Brualdi–Goldwasser crux,
provably impossible for any finite-basis `P` — see `docs/R1_WIRING_SCOPING`);
but the ASSEMBLY — per-node inequality ⟹ global bound — is mechanical and
reusable, which is what this emitter ships.

Per certified instance (one per node-class), a kernel-checkable super-solution
fact:

    theorem <name>_<class> : (0:ℝ) ≤ <P(v) − Σ P(children) − local(v)> := by positivity

plus the reusable rose-tree telescoping lemma `RTree.telescope`, proven once in
`TELESCOPE_PRELUDE` (structural recursion + `List.sum_le_sum`).  Together they
give `Σ local ≤ P(root)` for any tree; the final application is a one-line
`RTree.telescope` invocation against the caller's tree encoding.

The engine stays free of the BG research lab: the rose-tree lemma and the
super-solution shape are inlined here (they are general, not BG-specific).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .certify import polya_certify
from .expr import expr_lean_from_parts
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# The reusable rose-tree telescoping lemma, proved once (structural recursion),
# reusable for any (local, P).  No `sorry`, no added axioms.
TELESCOPE_PRELUDE = r"""namespace Telperion

/-- Finitely-branching (rose) trees, for telescoping tree inductions. -/
inductive RTree where
  | node : List RTree → RTree

/-- Sum of a node functional over every node of the tree. -/
def RTree.sumOver (loc : RTree → ℝ) : RTree → ℝ
  | .node cs => loc (.node cs) + (cs.map (RTree.sumOver loc)).sum

/-- Telescoping closure: a per-node super-solution `local + Σ_children P ≤ P`
    gives the telescoped global bound `Σ_nodes local ≤ P root`.  Every node's `P`
    cancels between its own term and its parent's child-sum, leaving `P root`. -/
theorem RTree.telescope {loc P : RTree → ℝ}
    (h : ∀ cs : List RTree, loc (.node cs) + (cs.map P).sum ≤ P (.node cs)) :
    ∀ t : RTree, RTree.sumOver loc t ≤ P t
  | .node cs => by
    have hchild : (cs.map (RTree.sumOver loc)).sum ≤ (cs.map P).sum :=
      List.sum_le_sum (by
        intro c hc
        exact RTree.telescope h c)
    have hnode := h cs
    simp only [RTree.sumOver]
    linarith

end Telperion
"""


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_telescope_point(family, pt, name):
    """Certify one telescoping-super-solution instance: (CertifiedInstance, n_checks).

    Reads (slacks, symbols) = family.special[1](pt), where each `slack` is the
    per-node super-solution margin  `P(v) − Σ P(children) − local(v)`  (a sympy
    expression in `symbols`, nonnegative over the nonnegative orthant).  Each is
    Pólya-certified `0 ≤ slack`.  Raises ValueError (refusal) when any slack is
    not certifiably nonnegative — i.e. the candidate `P` is NOT a super-solution
    (the telescoping overclaim trap).
    """
    slacks, syms = family.special[1](pt)
    slacks = tuple(sp.sympify(s) for s in slacks)
    syms = tuple(syms)
    certs = []
    for i, slack in enumerate(slacks):
        try:
            certs.append(polya_certify(sp.together(slack), syms, lift_max=4))
        except ValueError as e:
            raise ValueError(
                f"telescope instance '{name}' class {i} REFUSED: super-solution "
                f"margin not certifiably nonnegative — the candidate potential is "
                f"not a super-solution here ({e})"
            ) from e
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=(tuple(certs), syms),
    )
    return inst, len(certs)


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class TelescopingPotentialEmitter(Emitter):
    """Emit the per-node super-solution facts of a telescoping potential.  One
    `0 ≤ margin := by positivity` theorem per node-class; with the reusable
    `Telperion.RTree.telescope` lemma (in `TELESCOPE_PRELUDE`) these give the
    global bound `Σ local ≤ P root`.  Deterministic order: grid order, class
    order as supplied."""

    def __post_init__(self):
        self.kind = "telescope"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            certs, syms = inst.payload  # type: ignore[misc]
            for i, cert in enumerate(certs):
                body = expr_lean_from_parts(cert.numerator, cert.denominator, syms)
                lines.append(
                    f"theorem {inst.lean_name}_c{i} : (0:ℝ) ≤ {body} := by positivity\n"
                )
                n += 1
        return "".join(lines), n


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def telescope_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a telescoping-potential family (kind='telescope').

    spec: a callable ``pt -> (slacks, symbols)`` where each element of ``slacks``
    is the per-node super-solution margin ``P(v) − Σ P(children) − local(v)`` (a
    sympy expression, nonnegative over the nonnegative orthant).
    ``certify_telescope_point`` Pólya-certifies each ``0 ≤ slack`` and refuses if
    the candidate potential fails to be a super-solution.
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("telescope", spec),
        constants=dict(constants or {}),
    )

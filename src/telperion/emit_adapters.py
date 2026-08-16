"""Kind-2 and Kind-3 emitters: reparameterization adapters and case-dispatch
assemblies.

Kind 2 (`ReparamAdapterEmitter`): re-state an emitted theorem over ℕ
parameters, with `Nat.cast_sub` cast bookkeeping — the origin campaign's
36-dispatch shape.  The tool contributes batching, naming, provenance, and
hole-checked templates; the substitution data comes from the family author
(a `Reparam` per instance), because the cast algebra is intrinsically
statement-specific.

Kind 3 (`CaseDispatchAssemblyEmitter`): one assembled theorem quantified over
a finite ℕ grid axis, proved by `interval_cases` with one branch per grid
point.  For DIRECT families the branches are self-contained Polya blocks
(re-proved from the instance's own certificate — no cross-spelling glue, the
most robust branch shape); custom branch skeletons can override.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping

import sympy as sp

from .certify import CertifiedFamily, CertifiedInstance
from .emit import _hyp_lines, _den_factor_hyps
from .expr import expr_lean_factored, poly_lean, den_lean
from .lean import LeanProfile, render
from .workflow import Emitter

# Default skeleton for a ℕ-reparameterized adapter of a direct certificate.
# The origin shape: cast equation by push_cast [Nat.cast_sub h...]; ring,
# nonnegativity of the image by positivity, then exact the base theorem.
REPARAM_SKELETON = """theorem «name» «nat_binders» :
    0 ≤ «nat_body» := by
  have e : «cast_eq_lhs» = «cast_eq_rhs» := by
    push_cast [«cast_lemmas»]
    ring
  rw [e]
  have himg : (0 : ℝ) ≤ «image» := by positivity
  exact «base_name» «image» himg
"""

ASSEMBLY_SKELETON = """theorem «name» «binders» :
    0 ≤ «body» := by
  interval_cases «axis»
«branches»"""

ASSEMBLY_BRANCH_SKELETON = """  · push_cast
«hyp_lines»    have hkey : «branch_body»
        = («num»)
          / («den») := by
      field_simp
      try ring
    rw [hkey]
    positivity
"""


@dataclass(frozen=True)
class Reparam:
    """Per-instance substitution data for a ℕ adapter.

    nat_binders: the full binder text, e.g. ``(n : ℕ) (h1 : 1 ≤ n)``.
    nat_body:    the statement body over the casted ℕ vars, e.g. spelled with
                 ``((n : ℝ) - 1)``.
    cast_eq:     (lhs, rhs) with lhs the ℝ-arithmetic spelling in the statement
                 and rhs the ``((n - 1 : ℕ) : ℝ)``-style image the base theorem
                 is instantiated at.
    cast_lemmas: the ``Nat.cast_sub h``-style lemma list for push_cast.
    image:       the Lean term the base theorem's real variable is set to.
    """

    nat_binders: str
    nat_body: str
    cast_eq: tuple[str, str]
    cast_lemmas: tuple[str, ...]
    image: str


@dataclass
class ReparamAdapterEmitter(Emitter):
    """One ℕ-adapter theorem per instance, from user-supplied Reparam data."""

    reparam: Callable[[CertifiedInstance], Reparam] = None
    name_suffix: str = "_nat"

    def __post_init__(self):
        self.kind = "reparam_adapter"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        out: list[str] = []
        skeleton = profile.skeletons.get("reparam_adapter", REPARAM_SKELETON)
        for inst in fam.instances:
            rp = self.reparam(inst)
            out.append(
                render(
                    skeleton,
                    {
                        "name": inst.lean_name + self.name_suffix,
                        "nat_binders": rp.nat_binders,
                        "nat_body": rp.nat_body,
                        "cast_eq_lhs": rp.cast_eq[0],
                        "cast_eq_rhs": rp.cast_eq[1],
                        "cast_lemmas": ", ".join(rp.cast_lemmas),
                        "image": rp.image,
                        "base_name": inst.lean_name,
                    },
                )
            )
        return "\n".join(out), len(fam.instances)


@dataclass
class CaseDispatchAssemblyEmitter(Emitter):
    """One assembled theorem over a finite ℕ grid axis (direct families).

    ``body_template`` is a uniform Lean spelling of the claim body containing
    the token ``«axisR»`` wherever the real-cast axis value appears.  The
    statement substitutes ``((axis : ℝ))``; each `interval_cases` branch
    substitutes the literal grid value, so the branch's `hkey` left-hand side
    matches the post-`push_cast` goal syntactically (the origin campaign's own
    spelling trick).  Branches are self-contained Polya blocks re-proved from
    that instance's certificate — no cross-spelling glue.  v0.1: single-axis
    grids, direct families.
    """

    name: str = "assembled"
    axis: str = "a"
    binders: str = ""
    body_template: str = ""

    def __post_init__(self):
        self.kind = "case_dispatch_assembly"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        if len(fam.family.grid.axes) != 1:
            raise ValueError("v0.1 assembly supports a single grid axis")
        if fam.family.kind != "direct":
            raise ValueError("v0.1 assembly supports direct families")
        syms = fam.family.symbols
        branch_skel = profile.skeletons.get(
            "assembly_branch", ASSEMBLY_BRANCH_SKELETON
        )
        branches: list[str] = []
        for inst in fam.instances:
            cert = inst.corners[0]
            hyp_text = _hyp_lines(_den_factor_hyps(inst, syms))
            # indent the hyp block two extra spaces for the branch bullet
            hyp_text = "".join(f"  {line}\n" for line in hyp_text.splitlines())
            (axis_val,) = inst.point.values()
            branches.append(
                render(
                    branch_skel,
                    {
                        "hyp_lines": hyp_text,
                        "branch_body": self.body_template.replace(
                            "«axisR»", str(axis_val)
                        ),
                        "num": poly_lean(sp.Poly(cert.numerator, *syms), syms),
                        "den": den_lean(cert.denominator, syms),
                    },
                )
            )
        text = render(
            profile.skeletons.get("assembly", ASSEMBLY_SKELETON),
            {
                "name": self.name,
                "binders": self.binders,
                "body": self.body_template.replace("«axisR»", f"({self.axis} : ℝ)"),
                "axis": self.axis,
                "branches": "".join(branches).rstrip() + "\n",
            },
        )
        return text, 1

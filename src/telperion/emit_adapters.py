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

    def emit_units(self, fam: CertifiedFamily, profile: LeanProfile) -> list[tuple[str, int]]:
        # one assembled theorem spanning all instances -> a single indivisible unit
        return [self.emit_body(fam, profile)]

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


@dataclass
class CustomAssemblyEmitter(Emitter):
    """The escape hatch: a single hand-designed assembled theorem, rendered
    from user templates with per-instance branch fills.

    When the built-in assembly shape doesn't fit (bilinear-family assemblies
    with domain-specific branch glue — the origin's head_merge_le class), the
    Lean design is yours; the tool still contributes batching, exhaustive hole
    checking, provenance stamping, and the lint gate.  The statement template
    gets a «branches» hole plus whatever fills(fam) returns; each branch is
    branch_template rendered with branch_fills(instance).
    """

    statement_template: str = ""
    branch_template: str = ""
    fills: Callable[[CertifiedFamily], Mapping[str, str]] = None
    branch_fills: Callable[[CertifiedInstance], Mapping[str, str]] = None
    theorems: int = 1

    def __post_init__(self):
        self.kind = "custom_assembly"

    def emit_units(self, fam: CertifiedFamily, profile: LeanProfile) -> list[tuple[str, int]]:
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        branches = "".join(
            render(self.branch_template, dict(self.branch_fills(inst)))
            for inst in fam.instances
        )
        top = dict(self.fills(fam)) if self.fills is not None else {}
        top["branches"] = branches.rstrip() + "\n"
        return render(self.statement_template, top), self.theorems


GLUE_SKELETON = """theorem «name»_cell «binders»
    (hQ0 : «hyp_q0») (hQ1 : «q» ≤ «q_hi»)
    (hS0 : «hyp_r0») (hS1 : «r» ≤ «r_hi») :
    «before» ≤ «after» := by
  rcases le_total «split_var» («mid») with h | h
  · exact «left»_cell «call_args» «left_hyps»
  · exact «right»_cell «call_args» «right_hyps»
"""


@dataclass
class SubdivisionGlueEmitter(Emitter):
    """Reconstructs the ORIGINAL cell theorem of every subdivided box from its
    leaf cells, one `le_total` case split per internal node (deepest first, so
    every referenced child theorem is already defined).  Pair with
    BilinearBoxEmitter, which emits the leaves."""

    def __post_init__(self):
        self.kind = "subdivision_glue"

    def emit_units(self, fam: CertifiedFamily, profile: LeanProfile) -> list[tuple[str, int]]:
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        from .expr import expr_lean_factored

        family = fam.family
        syms = family.symbols
        args = " ".join(str(s) for s in syms)
        skeleton = profile.skeletons.get("subdivision_glue", GLUE_SKELETON)
        out: list[str] = []
        n = 0

        def emit_node(node) -> None:
            nonlocal n
            if "children" not in node:
                return
            for child in node["children"]:
                emit_node(child)
            qa, ra = node["q_axis"], node["r_axis"]
            q, r = qa.symbol, ra.symbol
            pt = node["point"]
            hyps = " ".join(f"h{s}" for s in syms)
            call_args = f"{args} {q} {r} {hyps}".strip()
            if node["axis"] == "q":
                split_var, left_hyps, right_hyps = str(q), "hQ0 h hS0 hS1", "h hQ1 hS0 hS1"
            else:
                split_var, left_hyps, right_hyps = str(r), "hQ0 hQ1 hS0 h", "hQ0 hQ1 h hS1"
            out.append(
                render(
                    skeleton,
                    {
                        "name": node["name"],
                        "binders": f"({args} {q} {r} : ℝ) "
                        + " ".join(f"(h{s} : 0 ≤ {s})" for s in syms),
                        "hyp_q0": (
                            f"({expr_lean_factored(qa.lo, syms)}) ≤ {q}"
                            if qa.lo_is_floor
                            else f"0 ≤ {q}"
                        ),
                        "hyp_r0": (
                            f"({expr_lean_factored(ra.lo, syms)}) ≤ {r}"
                            if ra.lo_is_floor
                            else f"0 ≤ {r}"
                        ),
                        "q": str(q),
                        "r": str(r),
                        "q_hi": f"({expr_lean_factored(qa.hi, syms)})",
                        "r_hi": f"({expr_lean_factored(ra.hi, syms)})",
                        "before": expr_lean_factored(
                            family.before(pt), tuple(syms) + (q, r)
                        ),
                        "after": expr_lean_factored(
                            family.after(pt), tuple(syms) + (q, r)
                        ),
                        "split_var": split_var,
                        "mid": expr_lean_factored(node["mid"], syms),
                        "left": node["children"][0]["name"],
                        "right": node["children"][1]["name"],
                        "call_args": call_args,
                        "left_hyps": left_hyps,
                        "right_hyps": right_hyps,
                    },
                )
            )
            n += 1

        for tree in fam.subdivisions:
            emit_node(tree)
        return "\n".join(out), n

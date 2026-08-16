"""Variable-map adapters: the campaign's most-used maneuver as one primitive.

The proof moved by substitution constantly: ``(x, y) = (pT, q−1)`` onto the
orthant, ``K = K₀ + t`` for tails, ``w = ρ − lo`` for brackets, the
compactification ``u = c·σ/(1+σ)``, the dispatch adapters' ℕ-casts.  Tails
(`TailNatEmitter`) and reparam (`ReparamAdapterEmitter`) are single-equation
instances of this shape; `VarMapAdapterEmitter` is the general one: certify in
the mapped variables (where the claim is Polya), emit the theorem in the
ORIGINAL variables with the substitution identities as `have`-glue and the
base theorem's instantiation at the images.

The tool contributes batching, typed-hole checking, provenance, and lint; the
map's algebra (which cast lemmas, which side conditions) is family data —
declared once per family in a `MapSpec`.
"""
from __future__ import annotations

from dataclasses import dataclass

from .certify import CertifiedFamily
from .lean import LeanProfile, render
from .workflow import Emitter

VARMAP_SKELETON = """theorem «name»«suffix» «binders» :
    0 ≤ «body» := by
«eq_lines»«img_lines»  «rw_line»
  exact «base_name» «call»
"""


@dataclass(frozen=True)
class MapSpec:
    """Everything the adapter theorem needs, per instance.

    binders:  original-variable binder text (with side-condition hypotheses).
    body:     the claim body spelled in the ORIGINAL variables.
    eqs:      (eq_name, lhs_text, rhs_text, tactic_text) — substitution
              identities proved inline (`have eq_name : lhs = rhs := by tac`).
    images:   (img_hyp_name, image_text, tactic_text) — nonnegativity (or
              other) facts about the images the base theorem's hypotheses
              need (`have h : 0 ≤ image := by tac`).
    call:     the base theorem's full argument list (images + hypothesis
              names, in the base binder order).
    """

    binders: str
    body: str
    eqs: tuple[tuple[str, str, str, str], ...]
    images: tuple[tuple[str, str, str], ...]
    call: str


@dataclass
class VarMapAdapterEmitter(Emitter):
    """One original-variable adapter theorem per instance, from MapSpec data."""

    spec: object = None            # Callable[[CertifiedInstance], MapSpec]
    name_suffix: str = "_orig"

    def __post_init__(self):
        self.kind = "varmap_adapter"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        out: list[str] = []
        skeleton = profile.skeletons.get("varmap_adapter", VARMAP_SKELETON)
        for inst in fam.instances:
            sp_ = self.spec(inst)
            eq_lines = "".join(
                f"  have {nm} : {lhs} = {rhs} := by\n    {tac}\n"
                for nm, lhs, rhs, tac in sp_.eqs
            )
            img_lines = "".join(
                f"  have {nm} : (0 : ℝ) ≤ {img} := by {tac}\n"
                for nm, img, tac in sp_.images
            )
            rw_line = (
                "rw [" + ", ".join(nm for nm, *_ in sp_.eqs) + "]"
                if sp_.eqs
                else "skip"
            )
            out.append(
                render(
                    skeleton,
                    {
                        "name": inst.lean_name,
                        "suffix": self.name_suffix,
                        "binders": sp_.binders,
                        "body": sp_.body,
                        "eq_lines": eq_lines,
                        "img_lines": img_lines,
                        "rw_line": rw_line,
                        "base_name": inst.lean_name,
                        "call": sp_.call,
                    },
                )
            )
        return "\n".join(out), len(fam.instances)

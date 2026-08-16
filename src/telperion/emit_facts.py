"""IdentityEmitter and ExactFactEmitter: the equality half of a campaign.

Half of the origin campaign's Lean is identities, not inequalities — the
objective identity `pi_utree`, the head identities (validated 60/60 in exact
rationals before formalizing), the backbone recursions.  And its deepest
moments bottom out in kernel integer facts: `3^317 * 2^81 <= 23^129`, the
726-digit legs crux, the rhoB brackets `(1+t)^11 <= 621/64`.  These emitters
extend the pipeline to both shapes.

IdentityEmitter: one `lhs = rhs` theorem per equation instance, discharged by
the proven `field_simp` + `try ring` shape with factored-denominator `≠ 0`
hypotheses (both sides rendered factored — the spelling rule).

ExactFactEmitter: for SYMBOL-FREE direct families (pure rational facts), one
theorem per instance in an UNEVALUATED power spelling — `(3:ℤ)^317 * 2^81`
stays written that way, not as a 152-digit numeral — closed by `decide` (ℤ
facts) or `norm_num` (ℚ).  This also makes the validation layer's
VerifiedConstant brackets emittable: a bracket IS a pair of such facts.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .certify import CertifiedFamily
from .emit import _binders, _hyp_lines
from .expr import _poly_any_lean, expr_lean_raw, rat_lean
from .lean import LeanProfile, render
from .workflow import Emitter


def fact_pow(base: int, exp: int) -> sp.Expr:
    """An UNEVALUATED integer power for exact-fact spellings — `fact_pow(3, 317)`
    stays `3^317`, never the 152-digit numeral sympy would otherwise build at
    construction time.  Combine with sp.Mul(..., evaluate=False)."""
    return sp.Pow(sp.Integer(base), sp.Integer(exp), evaluate=False)


IDENTITY_SKELETON = """theorem «name» «binders» :
    «lhs» = «rhs» := by
«hyp_lines»  «simp_clause»field_simp
  try ring
"""

FACT_SKELETON = """theorem «name» : «statement» := by «tactic»
"""


def _identity_hyps(inst, syms) -> list[str]:
    """Distinct positive denominator factors across both sides of the identity."""
    seen: list[str] = []
    for side in inst.equation:
        _, den = sp.fraction(sp.together(side))
        _, factors = sp.factor_list(sp.expand(den))
        for base, _ in sorted(
            factors, key=lambda t: (sp.total_degree(t[0]), sp.sstr(t[0]))
        ):
            rendered = _poly_any_lean(sp.expand(base), syms)
            if rendered not in seen and rendered != "1":
                seen.append(rendered)
    for atom in inst.den_atoms:
        rendered = _poly_any_lean(sp.expand(atom), syms)
        if rendered not in seen:
            seen.append(rendered)
    return seen


@dataclass
class IdentityEmitter(Emitter):
    """One `lhs = rhs` theorem per equation instance."""

    def __post_init__(self):
        self.kind = "identity"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        syms = fam.family.symbols
        out: list[str] = []
        n = 0
        for inst in fam.instances:
            if inst.equation is None:
                continue
            lhs, rhs = inst.equation
            simp = (
                f"simp only [{', '.join(profile.unfold_lemmas)}]\n  "
                if profile.unfold_lemmas
                else ""
            )
            out.append(
                render(
                    profile.skeletons.get("identity", IDENTITY_SKELETON),
                    {
                        "name": inst.lean_name,
                        "binders": _binders(syms),
                        "lhs": expr_lean_raw(lhs, syms),
                        "rhs": expr_lean_raw(rhs, syms),
                        "hyp_lines": _hyp_lines(_identity_hyps(inst, syms)),
                        "simp_clause": simp,
                    },
                )
            )
            n += 1
        return "\n".join(out), n


def int_expr_lean(e: sp.Expr, type_ascription: str = "ℤ") -> str:
    """Render a symbol-free product-of-powers expression WITHOUT evaluating —
    `(3 : ℤ) ^ 317 * 2 ^ 81`, never the 152-digit numeral.  Supports Integer,
    Rational, Pow (integer exponent), Mul, Add."""

    def rec(e, top=False):
        if e.is_Integer:
            return f"({int(e)} : {type_ascription})" if top else str(int(e))
        if e.is_Rational:
            return f"(({e.p} : {type_ascription}) / {e.q})" if top else rat_lean(e)
        if e.is_Pow:
            base, exp = e.args
            if not (exp.is_Integer and exp >= 0):
                raise ValueError(f"non-natural exponent in fact: {e}")
            return f"{rec(base, top)} ^ {int(exp)}"
        if e.is_Mul:
            parts = [rec(a, top=(i == 0)) for i, a in enumerate(e.args)]
            return " * ".join(parts)
        if e.is_Add:
            return " + ".join(rec(a, top=(i == 0)) for i, a in enumerate(e.args))
        raise ValueError(f"unsupported node in exact fact: {e.func}")

    return rec(e, top=True)


@dataclass
class ExactFactEmitter(Emitter):
    """Kernel facts for symbol-free direct families: `0 <= target` restated as
    `rhs_of(pt) relation lhs_of(pt)` in unevaluated-power spelling.

    The family author supplies `spelling(pt) -> (lhs_expr, rel, rhs_expr)`
    (rel in {"≤", "<", "="}) — the UNREDUCED form whose difference equals the
    certified target; certification already proved the reduced fact, and this
    emitter re-checks `rhs - lhs == target` (or sign-flipped) before
    rendering.  tactic: `decide` (integer facts; kernel-computes) or
    `norm_num` (rationals; the default)."""

    spelling: object = None                 # Callable[[pt], (lhs, rel, rhs)]
    tactic: str = "norm_num"
    type_ascription: str = "ℤ"

    def __post_init__(self):
        self.kind = "exact_fact"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        if fam.family.symbols:
            raise ValueError("ExactFactEmitter is for symbol-free families")
        out: list[str] = []
        n = 0
        for inst in fam.instances:
            lhs, rel, rhs = self.spelling(inst.point)
            lhs_v, rhs_v = lhs.doit(), rhs.doit()
            diff = (
                sp.expand(rhs_v - lhs_v) if rel in ("≤", "<") else sp.expand(lhs_v - rhs_v)
            )
            target = sp.expand(
                inst.corners[0].numerator / inst.corners[0].denominator
            )
            if rel in ("≤", "<") and sp.simplify(diff - target) != 0:
                raise ValueError(
                    f"{inst.lean_name}: spelling does not match the certified "
                    f"target (rhs - lhs != target)"
                )
            if rel == "=" and sp.simplify(diff) != 0:
                raise ValueError(f"{inst.lean_name}: equality spelling is false")
            statement = (
                f"{int_expr_lean(lhs, self.type_ascription)} {rel} "
                f"{int_expr_lean(rhs, self.type_ascription)}"
            )
            out.append(
                render(
                    profile.skeletons.get("exact_fact", FACT_SKELETON),
                    {
                        "name": inst.lean_name,
                        "statement": statement,
                        "tactic": self.tactic,
                    },
                )
            )
            n += 1
        return "\n".join(out), n

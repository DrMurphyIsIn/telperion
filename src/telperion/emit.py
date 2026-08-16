"""Kind-1 emitters: certificate batches (direct Polya and bilinear box).

Rendering is pure and deterministic: all self-checks already ran in
certify(); templates come from the LeanProfile; term ordering is owned by
expr.py.  The proof shapes mirror, exactly, the CI-validated templates of the
R47 campaign (see docs/TACTIC_CONTRACT.md): identities by
`simp only + push_cast + field_simp + ring`, nonnegativity by `positivity`.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .certify import CertifiedFamily, CertifiedInstance
from .expr import _poly_any_lean, den_lean, expr_lean_factored, poly_lean
from .lean import LeanProfile, render
from .workflow import Emitter


def _binders(syms, nonneg=True) -> str:
    if not syms:
        return ""
    names = " ".join(str(s) for s in syms)
    b = f"({names} : ℝ)"
    if nonneg:
        b += " " + " ".join(f"(h{s} : 0 ≤ {s})" for s in syms)
    return b


def _den_factor_hyps(instance: CertifiedInstance, syms) -> list[str]:
    """Distinct denominator factors across the instance's certificates, rendered
    in the same spelling the defs use, as `≠ 0` hypotheses for field_simp."""
    seen: list[str] = []
    exprs = list(instance.corners)
    for cert in exprs:
        _, factors = sp.factor_list(cert.denominator)
        for base, _ in sorted(
            factors, key=lambda t: (sp.total_degree(t[0]), sp.sstr(t[0]))
        ):
            rendered = _poly_any_lean(sp.expand(base), syms)
            if rendered not in seen and rendered != "1":
                seen.append(rendered)
    if instance.den_atoms:
        for atom in instance.den_atoms:
            rendered = _poly_any_lean(sp.expand(atom), syms)
            if rendered not in seen:
                seen.append(rendered)
    return seen


def _hyp_lines(hyps: list[str]) -> str:
    if not hyps:
        return ""
    return (
        "\n".join(
            f"  have hd{j} : ({h} : ℝ) ≠ 0 := by positivity"
            for j, h in enumerate(hyps, 1)
        )
        + "\n"
    )


def _simp_clause(profile: LeanProfile, extra: tuple[str, ...] = ()) -> str:
    lemmas = tuple(extra) + tuple(profile.unfold_lemmas)
    if not lemmas:
        return ""
    return f"simp only [{', '.join(lemmas)}]\n    "


@dataclass
class DirectPolyaEmitter(Emitter):
    """One `0 ≤ body` theorem per instance, from its Polya certificate."""

    def __post_init__(self):
        self.kind = "direct_polya"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        syms = fam.family.symbols
        out: list[str] = []
        for inst in fam.instances:
            cert = inst.corners[0]
            body = expr_lean_factored(cert.expr, syms)
            num = poly_lean(sp.Poly(cert.numerator, *syms), syms) if syms else str(
                cert.numerator
            )
            trivial_den = sp.simplify(cert.denominator - 1) == 0
            if trivial_den:
                text = render(
                    profile.skeleton("polya_nonneg_poly"),
                    {
                        "name": inst.lean_name,
                        "binders": _binders(syms),
                        "body": body,
                        "num": num,
                        "simp_clause": _simp_clause(profile),
                    },
                )
            else:
                text = render(
                    profile.skeleton("polya_nonneg"),
                    {
                        "name": inst.lean_name,
                        "binders": _binders(syms),
                        "body": body,
                        "num": num,
                        "den": den_lean(cert.denominator, syms),
                        "hyp_lines": _hyp_lines(_den_factor_hyps(inst, syms)),
                        "simp_clause": _simp_clause(profile),
                    },
                )
            out.append(text)
        return "\n".join(out), len(fam.instances)


@dataclass
class BilinearBoxEmitter(Emitter):
    """Per instance: c1..c4 defs, the decomposition theorem, four corner
    certificates, and the assembled box theorem via the user's combinator."""

    combinator: str = "bilinear_corner_nonneg"

    def __post_init__(self):
        self.kind = "bilinear_box"

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        syms = fam.family.symbols
        args = " ".join(str(s) for s in syms)
        out: list[str] = []
        n_theorems = 0
        for inst in fam.instances:
            d = inst.decomposition
            q, r = d.q_axis.symbol, d.r_axis.symbol
            name = inst.lean_name
            pt_title = ", ".join(f"{k} = {v}" for k, v in inst.point.items())
            out.append(f"/-! ### Instance ({pt_title}) -/\n")

            # coefficient defs
            unfold_names = []
            for i, ci in enumerate((d.c1, d.c2, d.c3, d.c4), 1):
                cname = f"{name}c{i}"
                unfold_names.append(cname)
                out.append(
                    f"noncomputable def {cname} ({args} : ℝ) : ℝ :=\n"
                    f"  {expr_lean_factored(ci, syms)}\n"
                )

            before_l = expr_lean_factored(fam.family.before(inst.point), tuple(syms) + (q, r))
            after_l = expr_lean_factored(fam.family.after(inst.point), tuple(syms) + (q, r))
            all_binders = (
                f"({args} {q} {r} : ℝ) "
                + " ".join(f"(h{s} : 0 ≤ {s})" for s in syms)
            )
            hyps = _hyp_lines(_den_factor_hyps(inst, syms))
            out.append(
                render(
                    profile.skeleton("bilinear_identity"),
                    {
                        "name": name,
                        "binders": all_binders,
                        "after": after_l,
                        "before": before_l,
                        "args": args,
                        "q": str(q),
                        "r": str(r),
                        "hyp_lines": hyps,
                        "unfold": ", ".join(unfold_names + list(profile.unfold_lemmas)),
                    },
                )
            )
            n_theorems += 1

            # corner certificates
            corner_refs: list[str] = []
            corner_vals = [
                (d.q_axis.lo, d.r_axis.lo),
                (d.q_axis.lo, d.r_axis.hi),
                (d.q_axis.hi, d.r_axis.lo),
                (d.q_axis.hi, d.r_axis.hi),
            ]
            for (qi_ri, cert), (qv, rv) in zip(
                enumerate(inst.corners), corner_vals
            ):
                qi, ri = divmod(qi_ri, 2)
                cn = f"{name}_corner{qi}{ri}"
                qv_l = f"({expr_lean_factored(qv, syms)})"
                rv_l = f"({expr_lean_factored(rv, syms)})"
                body = (
                    f"{name}c1 {args} + {name}c2 {args} * {qv_l} + {name}c3 {args} * {rv_l}\n"
                    f"        + {name}c4 {args} * ({qv_l} * {rv_l})"
                )
                from .expr import rat_lean

                num = (
                    poly_lean(sp.Poly(cert.numerator, *syms), syms)
                    if syms
                    else rat_lean(cert.numerator)
                )
                out.append(
                    render(
                        profile.skeleton("polya_nonneg"),
                        {
                            "name": cn,
                            "binders": _binders(syms),
                            "body": body,
                            "num": num,
                            "den": den_lean(cert.denominator, syms),
                            "hyp_lines": hyps,
                            "simp_clause": _simp_clause(profile, tuple(unfold_names)),
                        },
                    )
                )
                corner_refs.append(
                    f"({cn} {args} " + " ".join(f"h{s}" for s in syms) + ")"
                )
                n_theorems += 1

            # assembled box theorem
            q_hi_l = f"({expr_lean_factored(d.q_axis.hi, syms)})"
            r_hi_l = f"({expr_lean_factored(d.r_axis.hi, syms)})"
            hyp_q0 = (
                f"({expr_lean_factored(d.q_axis.lo, syms)}) ≤ {q}"
                if d.q_axis.lo_is_floor
                else f"0 ≤ {q}"
            )
            hyp_r0 = (
                f"({expr_lean_factored(d.r_axis.lo, syms)}) ≤ {r}"
                if d.r_axis.lo_is_floor
                else f"0 ≤ {r}"
            )
            out.append(
                render(
                    profile.skeleton("box_assemble"),
                    {
                        "name": name,
                        "binders": all_binders,
                        "q": str(q),
                        "r": str(r),
                        "q_hi": q_hi_l,
                        "r_hi": r_hi_l,
                        "hyp_q0": hyp_q0,
                        "hyp_r0": hyp_r0,
                        "before": before_l,
                        "after": after_l,
                        "binder_names": f"{args} {q} {r} "
                        + " ".join(f"h{s}" for s in syms),
                        "combinator": self.combinator,
                        "c00": corner_refs[0],
                        "c01": corner_refs[1],
                        "c10": corner_refs[2],
                        "c11": corner_refs[3],
                    },
                )
            )
            n_theorems += 1
        return "\n".join(out), n_theorems

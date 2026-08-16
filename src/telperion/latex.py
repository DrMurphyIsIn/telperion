"""LaTeX appendix emitter: the certified family as paper-ready mathematics,
provably in sync with the Lean.

Hand-transcribing certificate tables into a paper guarantees drift between the
PDF and the formalization.  This emitter renders the SAME CertifiedFamily the
Lean emitters consume, and stamps the output with the SAME input hash — the
appendix and the Lean files carry matching fingerprints, so a reviewer can
check sync by comparing two hex strings.

Two modes:
* appendix (default): a summary table (instance, certificate shape, lift
  exponent, tie faces) followed by one statement environment per instance
  with the exact certificate identity.
* blueprint: `\\begin{theorem}...\\lean{name}\\leanok` nodes compatible with
  leanblueprint's dependency-graph tooling.
"""
from __future__ import annotations

import sympy as sp

from .certify import CertifiedFamily
from .margins import tie_faces


def _tex(e: sp.Expr) -> str:
    return sp.latex(sp.nsimplify(e), fold_short_frac=False)


def _statement_tex(inst, syms) -> str:
    cert = inst.corners[0]
    return (
        f"0 \\le {_tex(cert.expr)}"
        if inst.decomposition is None
        else "\\text{before} \\le \\text{after on the certified box}"
    )


def latex_appendix(
    cf: CertifiedFamily, input_hash: str, blueprint: bool = False
) -> str:
    """Render the appendix (or blueprint nodes) for a certified family."""
    fam = cf.family
    syms = fam.symbols
    sym_list = ", ".join(str(s) for s in syms)
    head = (
        f"% telperion-generated appendix for family {fam.name}\n"
        f"% input-hash {input_hash[:16]} — matches the emitted Lean header\n"
        f"% DO NOT EDIT BY HAND; regenerate with `telperion latex`\n"
    )
    out = [head]
    if blueprint:
        for inst in cf.instances:
            cert = inst.corners[0]
            out.append(
                "\\begin{theorem}\n"
                f"  \\label{{thm:{inst.lean_name}}}\n"
                f"  \\lean{{{inst.lean_name}}}\n"
                "  \\leanok\n"
                f"  For ${sym_list} \\ge 0$: ${_statement_tex(inst, syms)}$.\n"
                "\\end{theorem}\n"
            )
        return "\n".join(out)

    out.append(f"\\subsection*{{The certified family \\texttt{{{fam.name}}}}}\n")
    out.append(
        f"All {len(cf.instances)} instances are machine-checked in Lean\\,4 "
        f"(input hash \\texttt{{{input_hash[:16]}}}); "
        f"symbols ${sym_list} \\ge 0$.\n"
    )
    # summary table
    out.append("\\begin{center}\\begin{tabular}{llll}")
    out.append("\\toprule")
    out.append("instance & grid point & certificate & ties \\\\")
    out.append("\\midrule")
    for inst in cf.instances:
        cert = inst.corners[0]
        if inst.decomposition is None:
            shape = (
                f"P\\'olya (lift $N={cert.lift_n}$)" if cert.lift_n else "P\\'olya"
            )
        else:
            shape = "bilinear box (4 corners)"
        try:
            faces = tie_faces(cert.numerator, syms) if syms else []
        except ValueError:
            faces = []
        tie_s = (
            "; ".join("$" + ", ".join(f"{s}=0" for s in f) + "$" for f in faces)
            if faces
            else "---"
        )
        pt_s = ", ".join(f"{k}={v}" for k, v in inst.point.items())
        out.append(
            f"\\texttt{{{inst.lean_name}}} & ${pt_s}$ & {shape} & {tie_s} \\\\"
        )
    out.append("\\bottomrule")
    out.append("\\end{tabular}\\end{center}\n")
    # per-instance statements with the certificate identity
    for inst in cf.instances:
        pt_s = ", ".join(f"{k}={v}" for k, v in inst.point.items())
        out.append(
            f"\\paragraph{{\\texttt{{{inst.lean_name}}} (${pt_s}$).}}"
        )
        if inst.decomposition is None:
            cert = inst.corners[0]
            out.append(
                "\\begin{equation*}\n"
                f"{_tex(cert.expr)} \\;=\\; "
                f"\\frac{{{_tex(cert.numerator)}}}{{{_tex(cert.denominator)}}}"
                " \\;\\ge\\; 0,\n\\end{equation*}"
            )
            out.append(
                "the numerator having nonnegative coefficients and the "
                "denominator factoring positively."
                + (
                    f" (P\\'olya lift $N={cert.lift_n}$: both sides multiplied "
                    f"by $(1+{'+'.join(map(str, syms))})^{{{cert.lift_n}}}$.)"
                    if cert.lift_n
                    else ""
                )
            )
        else:
            d = inst.decomposition
            out.append(
                "The difference decomposes bilinearly on the box "
                f"${_tex(d.q_axis.symbol)} \\in [{_tex(d.q_axis.lo)}, {_tex(d.q_axis.hi)}]$, "
                f"${_tex(d.r_axis.symbol)} \\in [{_tex(d.r_axis.lo)}, {_tex(d.r_axis.hi)}]$ "
                "with corner certificates"
            )
            out.append("\\begin{align*}")
            labels = ["c_{00}", "c_{01}", "c_{10}", "c_{11}"]
            rows = []
            for lab, cert in zip(labels, inst.corners):
                rows.append(
                    f"{lab} &= \\frac{{{_tex(cert.numerator)}}}{{{_tex(cert.denominator)}}} \\ge 0"
                )
            out.append(" \\\\\n".join(rows))
            out.append("\\end{align*}")
        out.append("")
    return "\n".join(out)

"""CAS-neutral certificate interchange: export certificates as JSON that any
system can recheck without reading Python or trusting sympy.

The export carries, per instance: the claimed expression as a small recursive
AST (add/mul/pow/div/rat/sym — evaluable in any language with rationals), the
certificate numerator as a monomial→coefficient map, the denominator as a
factor list, lift exponents, bilinear decomposition data and boxes.  The
companion `recheck` module verifies everything using ONLY the Python standard
library (fractions) — no sympy import — via coefficient checks plus
Schwartz–Zippel-style exact-rational identity spot-checks.  Three independent
verifications of the same mathematics: Lean kernel, sympy certifier, stdlib
rechecker.
"""
from __future__ import annotations

import json
from fractions import Fraction

import sympy as sp

from .certify import CertifiedFamily


def expr_to_ast(e: sp.Expr) -> list | str | dict:
    """Sympy expression -> JSON-able AST: ["+", ...], ["*", ...], ["^", b, e],
    ["/", n, d], {"rat": "p/q"}, {"sym": "u"}."""
    if e.is_Symbol:
        return {"sym": str(e)}
    if e.is_Rational:
        return {"rat": f"{e.p}/{e.q}"}
    if e.is_Add:
        return ["+"] + [expr_to_ast(a) for a in e.args]
    if e.is_Mul:
        num, den = sp.fraction(e)
        if den != 1:
            return ["/", expr_to_ast(num), expr_to_ast(den)]
        return ["*"] + [expr_to_ast(a) for a in e.args]
    if e.is_Pow:
        base, exp = e.args
        if exp.is_Integer and exp < 0:
            return ["/", {"rat": "1/1"}, expr_to_ast(base ** (-exp))]
        return ["^", expr_to_ast(base), int(exp)]
    raise ValueError(f"non-rational-arithmetic node in expression: {e.func}")


def _poly_dict(p: sp.Expr, syms) -> dict[str, str]:
    poly = sp.Poly(sp.expand(p), *syms) if syms else None
    if poly is None:
        q = sp.Rational(p)
        return {"": f"{q.p}/{q.q}"}
    out = {}
    for monom, coeff in zip(poly.monoms(), poly.coeffs()):
        key = ",".join(str(e) for e in monom)
        c = sp.Rational(coeff)
        out[key] = f"{c.p}/{c.q}"
    return out


def export_certificates(cf: CertifiedFamily, input_hash: str) -> dict:
    fam = cf.family
    syms = [str(s) for s in fam.symbols]
    instances = []
    for inst in cf.instances:
        entry: dict = {
            "lean_name": inst.lean_name,
            "point": {k: v for k, v in inst.point.items() if isinstance(v, (int, str))},
            "corners": [],
        }
        if inst.witness is not None:
            entry["witness"] = inst.witness
        if inst.equation is not None:
            lhs, rhs = inst.equation
            entry["equation"] = {
                "lhs": expr_to_ast(sp.together(lhs)),
                "rhs": expr_to_ast(sp.together(rhs)),
            }
        for cert in inst.corners:
            entry["corners"].append(
                {
                    "expr": expr_to_ast(sp.together(cert.expr)),
                    "numerator": _poly_dict(cert.numerator, fam.symbols),
                    "denominator_factors": [
                        {
                            "poly": _poly_dict(base, fam.symbols),
                            "power": int(exp),
                        }
                        for base, exp in sp.factor_list(cert.denominator)[1]
                    ]
                    + [
                        {
                            "poly": {"": f"{sp.Rational(sp.factor_list(cert.denominator)[0]).p}/{sp.Rational(sp.factor_list(cert.denominator)[0]).q}"},
                            "power": 1,
                        }
                    ],
                    "lift_n": cert.lift_n,
                }
            )
        if inst.decomposition is not None:
            d = inst.decomposition
            entry["box"] = {
                "q": {"symbol": str(d.q_axis.symbol),
                      "lo": expr_to_ast(sp.together(d.q_axis.lo)),
                      "hi": expr_to_ast(sp.together(d.q_axis.hi)),
                      "lo_is_floor": d.q_axis.lo_is_floor},
                "r": {"symbol": str(d.r_axis.symbol),
                      "lo": expr_to_ast(sp.together(d.r_axis.lo)),
                      "hi": expr_to_ast(sp.together(d.r_axis.hi)),
                      "lo_is_floor": d.r_axis.lo_is_floor},
            }
        instances.append(entry)
    return {
        "format": "telperion-certificates-v1",
        "family": fam.name,
        "input_hash": input_hash,
        "symbols": syms,
        "claim": "for symbols >= 0: 0 <= expr; expr == numerator/denominator; "
        "numerator coefficients all >= 0; denominator factors all-positive",
        "instances": instances,
    }


def write_certificates(cf: CertifiedFamily, input_hash: str, path) -> None:
    with open(path, "w") as f:
        json.dump(export_certificates(cf, input_hash), f, indent=1)

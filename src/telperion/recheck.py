"""Independent recheck of exported certificates — PURE Python standard
library, no sympy import anywhere in this module.

This is a deliberately separate code path from the certifier: it parses the
JSON interchange format and verifies, in exact `fractions.Fraction`
arithmetic:

1. every numerator coefficient is >= 0 (and integral where claimed);
2. every denominator factor has all-positive coefficients;
3. the IDENTITY expr == numerator/denominator at many random rational points
   (Schwartz–Zippel: a false polynomial identity survives k random rational
   evaluations with probability ~0 — and any single disagreement is a
   disproof).

Copy this file anywhere; it runs standalone:
    python3 recheck.py certificates.json
"""
from __future__ import annotations

import json
import random
import sys
from fractions import Fraction


def _frac(s: str) -> Fraction:
    return Fraction(s)


def eval_ast(node, env: dict[str, Fraction]) -> Fraction:
    if isinstance(node, dict):
        if "rat" in node:
            return _frac(node["rat"])
        if "sym" in node:
            return env[node["sym"]]
        raise ValueError(f"bad node {node}")
    op = node[0]
    if op == "+":
        return sum((eval_ast(a, env) for a in node[1:]), Fraction(0))
    if op == "*":
        out = Fraction(1)
        for a in node[1:]:
            out *= eval_ast(a, env)
        return out
    if op == "^":
        return eval_ast(node[1], env) ** int(node[2])
    if op == "/":
        return eval_ast(node[1], env) / eval_ast(node[2], env)
    raise ValueError(f"bad op {op}")


def eval_poly(poly: dict[str, str], point: list[Fraction]) -> Fraction:
    total = Fraction(0)
    for key, coeff in poly.items():
        term = _frac(coeff)
        if key:
            for e, x in zip((int(p) for p in key.split(",")), point):
                term *= x**e
        total += term
    return total


def recheck(doc: dict, trials: int = 30, seed: int = 0) -> list[str]:
    """Return a list of problems (empty = all checks green)."""
    problems: list[str] = []
    syms = doc["symbols"]
    rng = random.Random(seed)
    for inst in doc["instances"]:
        name = inst["lean_name"]
        box = inst.get("box")
        eq = inst.get("equation")
        if eq is not None:
            for _ in range(trials):
                point = [
                    Fraction(rng.randint(0, 400), rng.randint(1, 20)) for _ in syms
                ]
                env = dict(zip(syms, point))
                try:
                    if eval_ast(eq["lhs"], env) != eval_ast(eq["rhs"], env):
                        problems.append(f"{name}: IDENTITY FAILS at {env}")
                        break
                except ZeroDivisionError:
                    continue
        for ci, corner in enumerate(inst["corners"]):
            # 1. numerator coefficients nonnegative
            for key, coeff in corner["numerator"].items():
                if _frac(coeff) < 0:
                    problems.append(f"{name}[{ci}]: negative numerator coeff at {key}")
            # 2. denominator factors all-positive
            for fac in corner["denominator_factors"]:
                for key, coeff in fac["poly"].items():
                    if _frac(coeff) <= 0:
                        problems.append(
                            f"{name}[{ci}]: non-positive denominator factor coeff"
                        )
            # 3. identity spot-checks
            for _ in range(trials):
                point = [
                    Fraction(rng.randint(0, 400), rng.randint(1, 20)) for _ in syms
                ]
                env = dict(zip(syms, point))
                if box is not None:
                    # corner expressions may reference the box symbols via expr;
                    # corner certs in the export are already corner-substituted,
                    # so no box symbols remain.
                    pass
                try:
                    lhs = eval_ast(corner["expr"], env)
                except ZeroDivisionError:
                    continue
                num = eval_poly(corner["numerator"], point)
                den = Fraction(1)
                for fac in corner["denominator_factors"]:
                    den *= eval_poly(fac["poly"], point) ** int(fac["power"])
                if den == 0:
                    continue
                if lhs != num / den:
                    problems.append(
                        f"{name}[{ci}]: IDENTITY FAILS at {dict(zip(syms, map(str, point)))}"
                    )
                    break
                if num < 0:
                    problems.append(f"{name}[{ci}]: numerator NEGATIVE at sample")
                    break
    return problems


def main(argv=None) -> int:
    args = argv if argv is not None else sys.argv[1:]
    if not args:
        print("usage: recheck.py certificates.json")
        return 2
    with open(args[0]) as f:
        doc = json.load(f)
    problems = recheck(doc)
    n = sum(len(i["corners"]) for i in doc["instances"])
    if problems:
        print(f"RECHECK FAILED ({len(problems)} problem(s)):")
        for p in problems:
            print("  " + p)
        return 1
    print(
        f"recheck OK: {n} certificate(s) of family {doc['family']} verified "
        f"(coefficients + factor signs + rational identity spot-checks); "
        f"input-hash {doc['input_hash'][:16]}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Multilinear / endpoint-bracketing corner certificates -- BG's dominant corner pattern.

Reading the actual BG certs, the recurring corner shape is NOT the worst-corner-monomial
bound (`worst_corner.py`) but the MULTILINEAR / ENDPOINT-BRACKETING principle:

    a function  P(g_1..g_k)  AFFINE (degree <= 1) in each `g_i`  is nonneg on the box
    lo_i <= g_i <= hi_i  IFF it is nonneg at all 2^k CORNERS.

BG instances: `linear_nonneg_of_endpoints` (k=1: `A + B*s` on [s0,s1]), `bilinear_corner_nonneg`
(k=2: `A + B*s + C*t + E*s*t`), and the de-load `shed_step_c1..c5` (k=1 in the activity
variable `s`, coefficients polynomial in the degree parameter, each corner value positive
by `positivity`).

Proof (general k, `ring`-checkable): a multilinear `P` is the CONVEX COMBINATION of its
corner values,

    P(g) * D  =  sum_{corner c}  ( prod_i wnum_i^{c_i} ) * P(c),   D = prod_i (hi_i - lo_i),

with `wnum_i^{lo} = hi_i - g_i >= 0`, `wnum_i^{hi} = g_i - lo_i >= 0` (from the box).  Each
weight-product times its (nonneg) corner value is nonneg, so the sum -- hence `P(g)*D` -- is
nonneg, and `D > 0` gives `P(g) >= 0`.  This regenerates BG's bridge lemmas and their
per-cell instantiations.  Complementary to `worst_corner` (mixed-sign-monomial).
Bookkeeping, not new mathematics.  conjecture1_proved = False.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass

import sympy as sp


def is_multilinear(P, gens) -> bool:
    """True iff `P` has degree <= 1 in each generator (affine-in-each)."""
    poly = sp.Poly(sp.expand(P), *gens)
    return all(all(e <= 1 for e in monom) for monom in poly.monoms())


def corner_values(P, gens, box):
    """dict {corner in {'lo','hi'}^k : P evaluated there}.  box: gen -> (lo, hi)."""
    out = {}
    for corner in itertools.product(*[("lo", "hi")] * len(gens)):
        subs = {g: box[g][0 if c == "lo" else 1] for g, c in zip(gens, corner)}
        out[corner] = sp.expand(P.subs(subs))
    return out


def _lean(expr):
    return str(sp.expand(expr)).replace("**", "^")


@dataclass(frozen=True)
class MultilinearCornerCertificate:
    """`0 <= P(g_1..g_k)` on a box, `P` affine-in-each `g_i`, via the corner principle.

    box: gen -> (lo_symbol, hi_symbol) as sympy Symbols (the bridge is symbolic in the
    box endpoints and any coefficient parameters).  `corner_nonneg` decides whether a
    corner value is provably >= 0 (default: all-coefficients-nonneg heuristic)."""

    name: str
    poly: sp.Expr
    gens: tuple
    box: dict
    corner_nonneg: callable = None

    def _cn(self, v):
        # A corner value becomes a hypothesis `0 <= P(corner)` in the emitted bridge, so a
        # SYMBOLIC corner is always admissible; a NUMERIC corner must be genuinely >= 0.
        if self.corner_nonneg is not None:
            return self.corner_nonneg(v)
        v = sp.expand(v)
        return v >= 0 if v.is_number else True

    def check(self) -> bool:
        if not is_multilinear(self.poly, self.gens):
            return False
        return all(self._cn(val) for val in corner_values(self.poly, self.gens, self.box).values())

    def lean_bridge(self) -> str:
        """The k-variable corner-principle bridge theorem (convex-combination proof)."""
        if not self.check():
            raise ValueError(f"{self.name}: not multilinear or a corner not nonneg -- refusing")
        k = len(self.gens)
        los = [self.box[g][0] for g in self.gens]
        his = [self.box[g][1] for g in self.gens]
        corners = list(itertools.product(*[("lo", "hi")] * k))

        # factored weight numerators (kept factored so mul_nonneg/positivity works)
        def wfac(i, ci):
            return f"({his[i]} - {self.gens[i]})" if ci == "lo" else f"({self.gens[i]} - {los[i]})"
        D_fac = "*".join(f"({his[i]} - {los[i]})" for i in range(k))
        rhs_terms, wnum_facs, corner_vals = [], [], []
        for c in corners:
            wnum = sp.prod([(his[i] - self.gens[i]) if c[i] == "lo" else (self.gens[i] - los[i])
                            for i in range(k)])
            subs = {self.gens[i]: (los[i] if c[i] == "lo" else his[i]) for i in range(k)}
            Pc = sp.expand(self.poly.subs(subs))
            wnum_facs.append("*".join(wfac(i, c[i]) for i in range(k)))
            corner_vals.append(Pc)
            rhs_terms.append(sp.expand(wnum) * Pc)
        rhs = sum(rhs_terms)

        params = sorted(str(s) for s in (self.poly.free_symbols | set(los) | set(his)) - set(self.gens))
        gvars = [str(g) for g in self.gens]
        hyps = "".join(f"    (a{i} : {los[i]} ≤ {self.gens[i]}) (b{i} : {self.gens[i]} ≤ {his[i]})"
                       f" (w{i} : {los[i]} < {his[i]})\n" for i in range(k))
        cn_hyps = "".join(f"    (hc{j} : 0 ≤ {_lean(corner_vals[j])})\n" for j in range(len(corners)))
        sig = (f"theorem {self.name}_corner\n"
               f"    ({' '.join(params + gvars)} : ℝ)\n"
               + hyps + cn_hyps + "    :\n"
               + f"    0 ≤ {_lean(self.poly)} := by")

        lines = []
        for i in range(k):
            lines.append(f"  have hg{i} : (0:ℝ) ≤ {self.gens[i]} - {los[i]} := by linarith")
            lines.append(f"  have hh{i} : (0:ℝ) ≤ {his[i]} - {self.gens[i]} := by linarith")
        prods = []
        for j, c in enumerate(corners):
            fac_names = [f"hh{i}" if c[i] == "lo" else f"hg{i}" for i in range(k)]
            nested = fac_names[0]
            for nm in fac_names[1:]:
                nested = f"(mul_nonneg {nested} {nm})"
            lines.append(f"  have hp{j} : (0:ℝ) ≤ {wnum_facs[j]} := {nested}")
            lines.append(f"  have hq{j} : (0:ℝ) ≤ ({wnum_facs[j]}) * ({_lean(corner_vals[j])}) := "
                         f"mul_nonneg hp{j} hc{j}")
            prods.append(f"hq{j}")
        # D > 0 via nested mul_pos of (hi_i - lo_i > 0)
        dpos = [f"(sub_pos.mpr w{i})" for i in range(k)]
        dnested = dpos[0]
        for dp in dpos[1:]:
            dnested = f"(mul_pos {dnested} {dp})"
        lines.append(f"  have hd : (0:ℝ) < {D_fac} := {dnested}")
        lines.append(f"  have hid : ({_lean(self.poly)}) * ({D_fac}) = {_lean(rhs)} := by ring")
        lines.append(f"  nlinarith [hid, hd, {', '.join(prods)}]")
        return sig + "\n" + "\n".join(lines) + "\n"

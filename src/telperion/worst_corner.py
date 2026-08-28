"""Worst-corner polynomial-positivity certificates (`worst_corner_positivity`).

The primitive that three independent investigations converged on: BG's ~40 corner
certs (`R47R4Kelmans*Cert`, `R47R6DeloadCert`, `R47Cert*`, `bilinear_corner_nonneg`,
`HypFloors`, …), the RH Turán/Jensen/Toeplitz enclosure bridges
(`toeplitz3_pos_of_enclosure`), and the `hub_dom` domination certs are ALL instances
of one shape:

    given a polynomial  P(g_1..g_n)  and a box  lo_i <= g_i <= hi_i  (lo_i >= 0),
    certify  P > 0  over the box.

Since every `g_i >= 0`, each monomial `c * prod g_i^e_i` is minimized over the box at
a CORNER: at the floor `g_i = lo_i` if `c > 0`, at the ceiling `g_i = hi_i` if `c < 0`
(a negative coefficient times the largest product is the smallest term).  So the
"worst-corner" lower bound

    wc(P) = sum_{c>0} c * prod lo_i^e_i  +  sum_{c<0} c * prod hi_i^e_i

satisfies  wc(P) <= P  over the whole box; if `wc(P) > 0` then `P > 0` there.  Each
monomial bound `prod lo^e <= prod g^e` (or `prod g^e <= prod hi^e`) is a `gcongr` (a
monotone product of the box facts), and `nlinarith`/`linarith` assembles the
nonnegative combination -- exactly the hand-written BG/RH pattern, now generated.

This module supplies the exact worst-corner arithmetic (`worst_corner_bound`,
`WorstCornerCertificate.check`) and the Lean emitter (`.lean_bridge` -- the general
symbolic-box bridge, `.lean_concrete` -- a self-contained theorem for numeric boxes).
Refuses to emit when the corner bound is not positive.  RH-necessary / BG-corner scope
unchanged by this tool; it is bookkeeping, not new mathematics.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp


def _mono_str(gens, exps):
    """Lean product form of a monomial, e.g. (g1,g1,g4) -> 'g1*g1*g4' (matches nlinarith)."""
    factors = []
    for g, e in zip(gens, exps):
        factors += [str(g)] * e
    return "*".join(factors) if factors else "1"


def _pt_str(exps, pts):
    """Corner-point product string, e.g. lo1*lo1*lo4, from a point map (symbol->str)."""
    factors = []
    for g, e in zip(pts.keys(), exps):
        factors += [pts[g]] * e
    return "*".join(factors) if factors else "1"


def worst_corner_bound(P, gens, lo, hi):
    """Exact worst-corner lower bound of `P` over `lo_i <= g_i <= hi_i`.

    lo, hi: dict symbol -> Fraction.  Returns (wc: Fraction, terms: list) where each
    term is (coeff, exps, corner) with corner in {'lo','hi'}.
    """
    poly = sp.Poly(sp.expand(P), *gens)
    wc = Fr(0)
    terms = []
    for exps, coeff in poly.terms():
        c = Fr(int(sp.Integer(coeff.p)), int(sp.Integer(coeff.q))) if hasattr(coeff, "p") else Fr(coeff)
        pts = lo if c > 0 else hi
        val = c
        for g, e in zip(gens, exps):
            val *= pts[g] ** e
        wc += val
        terms.append((c, exps, "lo" if c > 0 else "hi"))
    return wc, terms


@dataclass(frozen=True)
class WorstCornerCertificate:
    """`P(g_1..g_n) > 0` over a box `lo_i <= g_i <= hi_i` via the worst-corner bound."""

    name: str
    poly: sp.Expr
    gens: tuple
    lo: dict
    hi: dict

    def _boxes(self):
        return ({g: Fr(v) for g, v in self.lo.items()},
                {g: Fr(v) for g, v in self.hi.items()})

    def worst_corner(self) -> Fr:
        lo, hi = self._boxes()
        return worst_corner_bound(self.poly, self.gens, lo, hi)[0]

    def check(self) -> bool:
        lo, hi = self._boxes()
        if any(not (0 <= lo[g] <= hi[g]) for g in self.gens):
            return False
        return self.worst_corner() > 0

    # ---- Lean emission ----
    def _monomial_haves(self, gens_lean, lo_names, hi_names):
        """Per-monomial gcongr bounds; returns (lines, hint_names)."""
        poly = sp.Poly(sp.expand(self.poly), *self.gens)
        lo_map = {g: lo_names[i] for i, g in enumerate(self.gens)}
        hi_map = {g: hi_names[i] for i, g in enumerate(self.gens)}
        lines, hints = [], []
        for j, (exps, coeff) in enumerate(poly.terms()):
            c = Fr(coeff)
            if all(e == 0 for e in exps):
                continue  # constant term needs no bound
            gm = _mono_str(gens_lean, exps)
            if c > 0:
                lom = _pt_str(exps, lo_map)
                lines.append(f"  have hwc{j} : ({lom} : ℝ) ≤ {gm} := by gcongr")
            else:
                him = _pt_str(exps, hi_map)
                lines.append(f"  have hwc{j} : ({gm} : ℝ) ≤ {him} := by gcongr")
            hints.append(f"hwc{j}")
        return lines, hints

    def _poly_lean(self, name_map, corner=None):
        """Render `sum coeff * monomial` in Lean, monomial factors from `name_map`.

        If `corner` is None, every monomial uses `name_map` (the goal, in g_i).
        If `corner` is (lo_map, hi_map), each monomial uses lo_map when its coeff is
        positive and hi_map when negative -- the worst-corner expression.
        """
        poly = sp.Poly(sp.expand(self.poly), *self.gens)
        parts = []
        for exps, coeff in poly.terms():
            c = Fr(coeff)
            nm = name_map if corner is None else (corner[0] if c > 0 else corner[1])
            factors = []
            for g, e in zip(self.gens, exps):
                factors += [nm[g]] * e
            m = "*".join(factors) if factors else "1"
            cstr = f"{c.numerator}" if c.denominator == 1 else f"({c.numerator}/{c.denominator})"
            if m == "1":
                parts.append(cstr)
            elif c == 1:
                parts.append(m)
            elif c == -1:
                parts.append(f"-{m}")
            else:
                parts.append(f"{cstr}*{m}")
        return " + ".join(parts).replace("+ -", "- ")

    def lean_bridge(self) -> str:
        """The general SYMBOLIC-box bridge theorem (lo_i, hi_i abstract; `hwc` a hypothesis).

        Generalizes `toeplitz3_pos_of_enclosure`: any polynomial, any box.
        """
        if not self.check():
            raise ValueError(f"{self.name}: worst-corner bound not positive -- refusing to emit")
        n = len(self.gens)
        gs = [f"g{i+1}" for i in range(n)]
        los = [f"lo{i+1}" for i in range(n)]
        his = [f"hi{i+1}" for i in range(n)]
        g_map = {g: gs[i] for i, g in enumerate(self.gens)}
        lo_map = {g: los[i] for i, g in enumerate(self.gens)}
        hi_map = {g: his[i] for i, g in enumerate(self.gens)}
        Pg = self._poly_lean(g_map)
        wc_expr = self._poly_lean(g_map, corner=(lo_map, hi_map))
        sig = (f"theorem {self.name}_bridge\n"
               f"    {{{' '.join(gs)} {' '.join(los)} {' '.join(his)} : ℝ}}\n"
               + "".join(f"    (l{i+1} : 0 ≤ {los[i]}) (a{i+1} : {los[i]} ≤ {gs[i]}) (b{i+1} : {gs[i]} ≤ {his[i]})\n"
                         for i in range(n))
               + f"    (hwc : 0 < {wc_expr}) :\n"
               + f"    0 < {Pg} := by")
        nn = [f"  have n{i+1} : (0:ℝ) ≤ {gs[i]} := le_trans l{i+1} a{i+1}" for i in range(n)]
        haves, hints = self._monomial_haves(gs, los, his)
        body = "\n".join(nn + haves + [f"  nlinarith [{', '.join(hints)}, hwc]"])
        return sig + "\n" + body + "\n"

"""Flag-discharge certificate for the Brualdi-Goldwasser walk-count cut (route b).

Certifies a LOWER bound on the walk moment  m_2(T) = (1/n) sum_v [2 S_v^2/d_v^2 - Q_v/d_v^2]
(S_v = sum_{a~v} 1/d_a, Q_v = sum 1/d_a^2) in terms of  m_1(T) = (1/n) sum_v S_v/d_v, valid for
every tree whose degrees are bounded by `dmax`.  The object is an antisymmetric edge potential
`w(d,e) = -w(e,d)` plus scalars (b0, b1, b2), giving the PER-VERTEX inequality

    2 x^2 - q  >=  b0 + b1*d + b2*x + sum_{a~v} w(d, d_a),      x = S_v/d_v, q = Q_v/d_v^2   (*)

for every local degree profile (d; {d_a}) with degrees <= dmax.  Because the tree sum of an
antisymmetric edge function telescopes to 0 (sum_v sum_{a~v} w(d_v,d_a) = 0) and the handshake gives
sum_v d_v = 2n-2, summing (*) over the tree yields the certified cut

    m_2(T)  >=  b0 + b1*(2 - 2/n) + b2 * m_1(T)          [exact rational; -2 b1 / n = the W5 surface term].

The multipliers come from the flag-LP dual (mass-transport / unimodularity duals = the potential w);
`b0` is set to the EXACT infimum of the per-type residual, so (*) holds by construction and `check()`
re-verifies it exactly over all degree-<=dmax types.  The generator is untrusted; each emitted atom is a
rational inequality the Lean kernel re-checks by `norm_num`.  This certifies the ATOMS of the discharge
cut; the tree-level assembly (telescoping + handshake) is the stated structural conclusion.

conjecture1_proved = False -- this is one finite level of a convergent hierarchy (see BG_WALK_COUNT_SUBPROBLEM.md, W9),
not a closed proof of Brualdi-Goldwasser.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction as Fr


def _rat(f: Fr) -> str:
    return f"(({f.numerator} : ℚ)/{f.denominator})" if f.denominator != 1 else f"(({f.numerator} : ℚ))"


def profile_moment_terms(d: int, nbrs: tuple):
    """Exact (x, q, lhs) for a local profile: x = (sum 1/e)/d, q = (sum 1/e^2)/d^2, lhs = 2 x^2 - q."""
    S = sum(Fr(1, e) for e in nbrs)
    Q = sum(Fr(1, e * e) for e in nbrs)
    x = S / d
    q = Q / (d * d)
    return x, q, 2 * x * x - q


@dataclass(frozen=True)
class FlagDischargeCertificate:
    """The BG walk-count m_2 cut as an antisymmetric edge-discharge potential + scalars (exact rationals)."""

    name: str
    dmax: int
    b0: Fr
    b1: Fr
    b2: Fr
    w: dict                       # {(d, e): Fr}  with w[(d,e)] = -w[(e,d)], w[(d,d)] = 0

    # ---- potential ----
    def wval(self, d: int, e: int) -> Fr:
        if d == e:
            return Fr(0)
        if (d, e) in self.w:
            return self.w[(d, e)]
        if (e, d) in self.w:
            return -self.w[(e, d)]
        return Fr(0)

    def antisymmetric(self) -> bool:
        for (d, e), val in self.w.items():
            if self.wval(e, d) != -val:
                return False
        return all(self.wval(k, k) == 0 for k in range(1, self.dmax + 1))

    # ---- per-type residual (*) ----
    def residual(self, d: int, nbrs: tuple) -> Fr:
        x, q, lhs = profile_moment_terms(d, nbrs)
        disc = sum(self.wval(d, e) for e in nbrs)
        return lhs - (self.b0 + self.b1 * d + self.b2 * x + disc)

    def _types(self):
        for d in range(1, self.dmax + 1):
            for nbrs in itertools.combinations_with_replacement(range(1, self.dmax + 1), d):
                yield d, nbrs

    def worst_slack(self) -> Fr:
        return min(self.residual(d, nbrs) for d, nbrs in self._types())

    def check(self) -> bool:
        """Exact: antisymmetric potential AND every degree-<=dmax per-type inequality (*) holds."""
        return self.antisymmetric() and self.worst_slack() >= 0

    def certified_bound(self, n: int | None = None) -> Fr:
        """The certified lower bound on m_2 given m_1: b0 + b1*(2 - 2/n) + b2*m_1 (n=None -> bulk 2)."""
        deg_term = self.b1 * (Fr(2) - Fr(2, n)) if n else self.b1 * 2
        return self.b0 + deg_term  # + self.b2 * m_1  (added by the caller with the actual m_1)

    # ---- Lean emission: the rational per-type atoms ----
    def lean_atom(self, d: int, nbrs: tuple, tag: str) -> str:
        x, q, lhs = profile_moment_terms(d, nbrs)
        disc = sum(self.wval(d, e) for e in nbrs)
        rhs = self.b0 + self.b1 * d + self.b2 * x + disc
        deg_seq = ",".join(str(e) for e in nbrs)
        return (
            f"-- profile deg={d} nbrs=[{deg_seq}]  (slack {self.residual(d, nbrs)})\n"
            f"theorem {self.name}_{tag} : {_rat(rhs)} ≤ {_rat(lhs)} := by norm_num\n"
        )

    def lean(self, atoms=None) -> str:
        """Emit the certificate: the discharge scalars, the telescoping/handshake assembly as a docstring,
        and the kernel-checked per-type rational atoms (default: the extremal caterpillar vertex types)."""
        if not self.check():
            raise ValueError(f"{self.name}: per-type inequality fails -- refusing to emit")
        if atoms is None:
            atoms = self._default_atoms()
        head = (
            f"/-- Flag-discharge certificate `{self.name}` for the Brualdi-Goldwasser m_2 cut (route b).\n"
            f"    Antisymmetric edge potential w(d,e) + scalars b0={self.b0}, b1={self.b1}, b2={self.b2},\n"
            f"    degrees <= {self.dmax}.  Per-vertex:  2x^2 - q >= b0 + b1 d + b2 x + sum w(d,d_a).\n"
            f"    Tree sum telescopes (sum w = 0) + handshake (sum d = 2n-2)  =>\n"
            f"      m_2(T) >= {self.b0} + {self.b1}*(2 - 2/n) + {self.b2}*m_1(T).\n"
            f"    conjecture1_proved = False (one finite level of the W9 convergent hierarchy). -/\n"
        )
        body = "\n".join(self.lean_atom(d, nbrs, tag) for tag, (d, nbrs) in atoms.items())
        return head + "\n" + body

    def lean_module(self, namespace: str, atoms=None) -> str:
        """Complete frozen Lean module: Mathlib import + namespace + the kernel-checked atoms."""
        return (
            f"/- Flag-discharge certificate for the Brualdi-Goldwasser walk-count m_2 cut (route b).\n"
            f"   Antisymmetric edge potential w(d,e)=-w(e,d) + scalars (b0,b1,b2), degrees <= {self.dmax}.\n"
            f"   Per-vertex 2x^2-q >= b0+b1 d+b2 x+sum w(d,d_a); tree sum telescopes (sum w=0) +\n"
            f"   handshake (sum d=2n-2) => m_2(T) >= {self.b0} + {self.b1}*(2-2/n) + {self.b2}*m_1(T).\n"
            f"   Each atom is a rational per-type inequality the kernel re-checks by norm_num; tight at\n"
            f"   the extremal caterpillar profile. One finite level of the W9 convergent hierarchy --\n"
            f"   NOT a proof of Brualdi-Goldwasser.  conjecture1_proved = False. -/\n"
            f"import Mathlib\n\n"
            f"namespace {namespace}\n\n"
            + "\n".join(self.lean_atom(d, nbrs, tag)
                        for tag, (d, nbrs) in (atoms or self._default_atoms()).items())
            + f"\nend {namespace}\n"
        )

    def _default_atoms(self) -> dict:
        """Extremal caterpillar vertex types (hub degree = dmax): leaf/arm-mid/hub, + the worst-slack type."""
        a = self.dmax - 2  # arms per hub; hub degree = a + 2 = dmax
        atoms = {
            "leaf": (1, (2,)),
            "arm": (2, (self.dmax, 1)),
            "hub": (self.dmax, tuple(sorted([self.dmax, self.dmax] + [2] * a))),
        }
        worst = min(self._types(), key=lambda t: self.residual(*t))
        atoms["tight"] = worst
        return atoms

    # ---- builder: solve flag-LP, rationalize dual, set exact b0 ----
    @staticmethod
    def from_flag_lp(name: str, dmax: int, m1_target, denom: int = 720):
        """Solve the mass-transport flag-LP at (dmax, m1_target), rationalize the dual potential to
        multiples of 1/denom, and set b0 to the exact infimum so (*) holds by construction."""
        import numpy as np
        from scipy.optimize import linprog

        types = [(d, c) for d in range(1, dmax + 1)
                 for c in itertools.combinations_with_replacement(range(1, dmax + 1), d)]
        NT = len(types)
        xv = np.array([float(profile_moment_terms(d, c)[0]) for d, c in types])
        m2c = np.array([float(profile_moment_terms(d, c)[2]) for d, c in types])
        dv = np.array([d for d, _ in types], float)
        rows = [np.ones(NT), dv.copy()]
        rhs = [1.0, 2.0]
        pairs = [(d, e) for d in range(1, dmax + 1) for e in range(d + 1, dmax + 1)]
        for (d, e) in pairs:
            row = np.zeros(NT)
            for i, (dd, c) in enumerate(types):
                if dd == d:
                    row[i] += sum(1 for z in c if z == e)
                if dd == e:
                    row[i] -= sum(1 for z in c if z == d)
            rows.append(row)
            rhs.append(0.0)
        A_eq = np.vstack([np.array(rows), xv])
        b_eq = np.append(np.array(rhs), float(m1_target))
        res = linprog(m2c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * NT, method="highs")
        if not res.success:
            raise RuntimeError(f"flag-LP infeasible: {res.message}")
        y = res.eqlin.marginals
        b1 = Fr(round(y[1] * denom), denom)
        b2 = Fr(round(y[-1] * denom), denom)
        w = {}
        for k, (d, e) in enumerate(pairs):
            val = Fr(round(y[2 + k] * denom), denom)
            if val != 0:
                w[(d, e)] = val
        cert = FlagDischargeCertificate(name=name, dmax=dmax, b0=Fr(0), b1=b1, b2=b2, w=w)
        b0 = min(cert.residual(d, c) + cert.b0 for d, c in types)   # exact infimum of lhs - b1 d - b2 x - disc
        return FlagDischargeCertificate(name=name, dmax=dmax, b0=b0, b1=b1, b2=b2, w=w)

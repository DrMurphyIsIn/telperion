"""MonomialBudgetLadder emitter — one master smallness budget absorbing a
family of monomial rung obligations, distilled from the OpenAI Euler blowup
formalization (``github.com/openai/NavierStokesAndEuler``,
``Euler/PacketGeometryGuards.lean`` ``ray_error_small`` + siblings /
``Euler/PacketSourceScaleGuards.lean``, Apache-2.0; 6+ instances per file).

Given the MASTER budget ``Cm·e·Θ^Kmax ≤ 1`` (with ``0 ≤ e``, ``1 ≤ Θ``), every
rung ``(c, k, b)`` with ``k ≤ Kmax`` and ``c ≤ Cm·b`` follows:

    c·e·Θ^k  ≤  c·e·Θ^Kmax  =  (c/Cm)·(Cm·e·Θ^Kmax)  ≤  c/Cm  ≤  b.

The exponent-monotone absorption over a SYMBOLIC base ``Θ ≥ 1`` is what fixed
numeric boxes (``sos``/``handelman``) cannot express.  Per-instance data: the
master ``(Cm, Kmax)`` and a rung list ``[(c, k, b), …]``; the side conditions
``Cm > 0``, ``0 ≤ c``, ``k ≤ Kmax``, ``c ≤ Cm·b`` are certified EXACTLY
(violations refused — negative controls).  One lemma per rung, discharged by
``pow_le_pow_right₀`` + ``mul_le_mul`` + ``linarith``.

HONESTY SEAM: the master budget is a HYPOTHESIS supplied by the analytic side.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class MonomialLadderCert:
    """Master ``(Cm, Kmax)`` and rungs ``(c, k, b)`` with all side conditions
    re-verified exactly (``q = c/Cm ≤ b`` per rung)."""

    Cm: sp.Rational
    Kmax: int
    rungs: tuple[tuple[sp.Rational, int, sp.Rational], ...]


def monomial_ladder_certificate(Cm, Kmax, rungs) -> MonomialLadderCert:
    """Build and EXACTLY re-check a monomial-ladder instance."""
    Cm = sp.Rational(sp.nsimplify(Cm))
    Kmax = int(Kmax)
    if not Cm > 0:
        raise ValueError(f"monomial_ladder REFUSED: need master constant Cm > 0; got {Cm}")
    if Kmax < 0:
        raise ValueError(f"monomial_ladder REFUSED: need Kmax ≥ 0; got {Kmax}")
    out = []
    for c, k, b in rungs:
        c = sp.Rational(sp.nsimplify(c))
        k = int(k)
        b = sp.Rational(sp.nsimplify(b))
        if not c >= 0:
            raise ValueError(f"monomial_ladder REFUSED: rung constant {c} < 0")
        if not 0 <= k <= Kmax:
            raise ValueError(
                f"monomial_ladder REFUSED: rung exponent {k} ∉ [0, Kmax={Kmax}]")
        if not c <= Cm * b:
            raise ValueError(
                f"monomial_ladder REFUSED: rung budget c ≤ Cm·b violated "
                f"({c} > {Cm}·{b} = {Cm*b}) — the master cannot absorb this rung")
        out.append((c, k, b))
    if not out:
        raise ValueError("monomial_ladder REFUSED: empty rung list")
    return MonomialLadderCert(Cm=Cm, Kmax=Kmax, rungs=tuple(out))


def certify_monomial_ladder_point(family, pt, name):
    """``spec(pt) -> (Cm, Kmax, [(c, k, b), …])``.  n_checks = 2 + 3·rungs."""
    Cm, Kmax, rungs = family.special[1](pt)
    cert = monomial_ladder_certificate(Cm, Kmax, rungs)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2 + 3 * len(cert.rungs)


@dataclass
class MonomialLadderEmitter(Emitter):
    """Emit one rung lemma per ``(c, k, b)`` off the shared master budget."""

    def __post_init__(self):
        self.kind = "monomial_ladder"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: MonomialLadderCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            cm, kmax = rat_lean(cert.Cm), cert.Kmax
            for i, (c, k, b) in enumerate(cert.rungs, start=1):
                q = rat_lean(sp.Rational(c) / cert.Cm)
                cs, bs = rat_lean(c), rat_lean(b)
                lines.append(
                    f"-- {nm}_rung{i}: monomial rung (c,k,b)=({c},{k},{b}) off the master\n"
                    f"-- budget Cm·e·Θ^Kmax ≤ 1 (Cm={cert.Cm}, Kmax={kmax}); c/Cm = {sp.Rational(c)/cert.Cm}\n"
                    f"-- ≤ b certified exactly.  Trust seam: the master budget is a HYPOTHESIS.\n"
                    f"theorem {nm}_rung{i} (e Θ : ℝ) (he : 0 ≤ e) (hΘ : 1 ≤ Θ)\n"
                    f"    (hmaster : ({cm}) * e * Θ ^ {kmax} ≤ 1) :\n"
                    f"    ({cs}) * e * Θ ^ {k} ≤ ({bs}) := by\n"
                    f"  have hp : Θ ^ {k} ≤ Θ ^ {kmax} := "
                    f"pow_le_pow_right₀ hΘ (by norm_num)\n"
                    f"  have hstep : ({cs}) * e * Θ ^ {k} ≤ ({cs}) * e * Θ ^ {kmax} := by\n"
                    f"    have h := mul_le_mul_of_nonneg_left hp\n"
                    f"      (mul_nonneg (by norm_num : (0:ℝ) ≤ ({cs})) he)\n"
                    f"    linarith [h]\n"
                    f"  have hscale : ({q}) * (({cm}) * e * Θ ^ {kmax}) ≤ ({q}) * 1 :=\n"
                    f"    mul_le_mul_of_nonneg_left hmaster (by norm_num)\n"
                    f"  have heq : ({q}) * (({cm}) * e * Θ ^ {kmax}) = "
                    f"({cs}) * e * Θ ^ {kmax} := by ring\n"
                    f"  linarith [hstep, hscale, heq]\n"
                )
                n_thm += 1
        return "\n".join(lines), n_thm


def monomial_ladder_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``monomial_ladder``; ``spec: pt -> (Cm, Kmax, [(c, k, b), …])``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("monomial_ladder", spec),
        constants=dict(constants or {}),
    )

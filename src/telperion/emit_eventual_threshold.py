"""EventualScalingThreshold emitter — "holds for all sufficiently large scale"
with a computed max-of-ratios witness, distilled from the OpenAI Navier--Stokes
blowup formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/ConeAlgebra.lean`` ``sufficiently_large_amplitude_cone``,
Apache-2.0).

No prior kind produces EXISTENTIAL large-scale certificates (``monotone_tail``
is sequence tails, ``affine_param_endpoint`` is box endpoints).  The generic
core of the source's cone theorem: for finitely many affine threshold
conditions ``aᵢ < p·cᵢ`` with positive slopes, the explicit witness
``p₀ = max(a₁/c₁, …, aₙ/cₙ)`` makes ALL of them hold for every ``p > p₀``:

    ∃ p₀, ∀ p > p₀,  a₁ < p·c₁ ∧ … ∧ aₙ < p·cₙ,

each conjunct by ``div_lt_iff₀`` + a ``le_max`` chain.  Per-instance data: the
arity ``n ∈ [1, 6]`` (the aᵢ, cᵢ are fully symbolic theorem variables with
``0 < cᵢ`` hypotheses).  Domain-specific consequents (the source's
``coneBound``) then compose downstream, e.g. with ``sqrt_root_elimination``.

HONESTY SEAM: the slope positivity is a HYPOTHESIS; the kernel certifies the
witness assembly.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class EventualThresholdCert:
    """The arity ``n ∈ [1, 6]`` of the conjunction."""

    n: int


def eventual_threshold_certificate(n) -> EventualThresholdCert:
    """Build and re-check an eventual-threshold instance."""
    n = int(n)
    if not (1 <= n <= 6):
        raise ValueError(f"eventual_threshold REFUSED: arity 1 ≤ n ≤ 6; got {n}")
    return EventualThresholdCert(n=n)


def certify_eventual_threshold_point(family, pt, name):
    """``spec(pt) -> n`` (arity).  One structural check."""
    n = family.special[1](pt)
    cert = eventual_threshold_certificate(n)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def _nested_max(terms: list[str]) -> str:
    if len(terms) == 1:
        return terms[0]
    return f"max {terms[0]} ({_nested_max(terms[1:])})"


@dataclass
class EventualThresholdEmitter(Emitter):
    """Emit the arity-n large-scale threshold with the explicit nested-max
    witness; each conjunct by ``div_lt_iff₀`` + a generated ``le_max`` chain."""

    def __post_init__(self):
        self.kind = "eventual_threshold"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: EventualThresholdCert = inst.payload  # type: ignore[assignment]
            nm, n = inst.lean_name, cert.n
            avars = [f"a{i+1}" for i in range(n)]
            cvars = [f"c{i+1}" for i in range(n)]
            binder = " ".join(avars + cvars)
            hyps = " ".join(f"(hc{i+1} : 0 < c{i+1})" for i in range(n))
            ratios = [f"(a{i+1} / c{i+1})" for i in range(n)]
            witness = _nested_max(ratios)
            concl = " ∧ ".join(f"a{i+1} < p * c{i+1}" for i in range(n))
            body: list[str] = []
            # per-conjunct: ratio_i ≤ p₀ via a le_max chain into the right-nested
            # max (position i = i × le_max_right wraps around a le_max_left, or
            # le_refl for the last), then div_lt_iff₀ against p₀ < p.
            for i in range(n):
                expr = "le_max_left _ _" if i < n - 1 else "le_refl _"
                for _ in range(i):
                    expr = f"le_trans ({expr}) (le_max_right _ _)"
                body.append(
                    f"  have hm{i+1} : a{i+1} / c{i+1} ≤ p₀ := {expr}")
                body.append(
                    f"  have hp{i+1} : a{i+1} < p * c{i+1} := "
                    f"(div_lt_iff₀ hc{i+1}).mp (lt_of_le_of_lt hm{i+1} hlarge)")
            tuple_expr = ("hp1" if n == 1
                          else "⟨" + ", ".join(f"hp{i+1}" for i in range(n)) + "⟩")
            lines.append(
                f"-- {nm}: eventual scaling threshold, arity {n} — explicit witness\n"
                f"-- p₀ = max of the {n} coefficient ratio(s).  Ported/genericized from\n"
                f"-- NavierStokesAndEuler ConeAlgebra.lean\n"
                f"-- sufficiently_large_amplitude_cone (Apache-2.0).\n"
                f"-- Trust seam: slope positivity 0 < cᵢ are HYPOTHESES.\n"
                f"theorem {nm} ({binder} : ℝ) {hyps} :\n"
                f"    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p → ({concl}) := by\n"
                f"  refine ⟨{witness}, fun p hlarge => ?_⟩\n"
                f"  set p₀ : ℝ := {witness} with hp₀\n"
                + "\n".join(body) + "\n"
                f"  exact {tuple_expr}\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def eventual_threshold_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``eventual_threshold``; ``spec: pt -> n`` (arity 1–6)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("eventual_threshold", spec),
        constants=dict(constants or {}),
    )

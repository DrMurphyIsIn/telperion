"""MultilinearProductPerturbation emitter — the Leibniz telescoping first-order
comparison distilled from the OpenAI Navier--Stokes blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``NavierStokes/MovingFrameODE.lean``
``product_perturbation_le``, Apache-2.0; 5 miner reports across 4 files).

For an n-factor product with per-factor bounds ``|Fᵢ|, |Gᵢ| ≤ Mᵢ`` and a shared
perturbation ``|Fᵢ − Gᵢ| ≤ η``, the exact telescoping identity

    ∏Fᵢ − ∏Gᵢ = Σᵢ (∏_{j<i} Gⱼ)·(Fᵢ − Gᵢ)·(∏_{j>i} Fⱼ)

yields the first-order envelope

    |∏Fᵢ − ∏Gᵢ|  ≤  C·η,      C = Σᵢ ∏_{j≠i} Mⱼ   (exact rational).

The catalogued affine PerturbationTriangleBound covers only linear forms; this
is the product/multilinear case with an auto-generated ``ring`` telescoping
identity and a deterministic ``mul_le_mul`` chain discharge (no ``nlinarith``).
The arity-2 instance with ``M = (M, 1)`` is the source's ``(1+M)·η``.

Per-instance data: arity ``n ∈ [2, 6]`` and rational bounds ``(M₁, …, Mₙ)``
(each ``≥ 0``); the envelope ``C`` is computed and re-verified exactly.
Negative controls: arity out of range, negative bound.

HONESTY SEAM: the factor and perturbation bounds are HYPOTHESES; the kernel
certifies only the telescoping arithmetic.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class MultilinearPerturbationCert:
    """Arity, rational per-factor bounds, and the exact envelope C = Σᵢ∏_{j≠i}Mⱼ."""

    n: int
    M: tuple[sp.Rational, ...]
    C: sp.Rational


def multilinear_perturbation_certificate(bounds) -> MultilinearPerturbationCert:
    """Build and EXACTLY re-check a multilinear-perturbation instance."""
    M = tuple(sp.Rational(sp.nsimplify(b)) for b in bounds)
    n = len(M)
    if not (2 <= n <= 6):
        raise ValueError(f"multilinear_perturbation REFUSED: arity 2 ≤ n ≤ 6; got {n}")
    for b in M:
        if not b >= 0:
            raise ValueError(f"multilinear_perturbation REFUSED: need Mᵢ ≥ 0; got {b}")
    C = sum(sp.prod([M[j] for j in range(n) if j != i]) for i in range(n))
    C = sp.Rational(C)
    return MultilinearPerturbationCert(n=n, M=M, C=C)


def certify_multilinear_perturbation_point(family, pt, name):
    """``spec(pt) -> (M₁, …, Mₙ)``.  n_checks = n (bound signs) + 1 (envelope)."""
    bounds = family.special[1](pt)
    cert = multilinear_perturbation_certificate(bounds)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, cert.n + 1


def _prod_lean(names) -> str:
    return " * ".join(names)


@dataclass
class MultilinearPerturbationEmitter(Emitter):
    """Emit the telescoped product-perturbation bound at concrete arity and
    rational bounds: ``ring`` telescoping identity + ``abs_add_le`` chain +
    deterministic ``mul_le_mul`` per-term chains, closed by ``linarith``."""

    def __post_init__(self):
        self.kind = "multilinear_perturbation"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: MultilinearPerturbationCert = inst.payload  # type: ignore[assignment]
            nm, n, M, C = inst.lean_name, cert.n, cert.M, cert.C
            F = [f"F{i+1}" for i in range(n)]
            G = [f"G{i+1}" for i in range(n)]
            binder = " ".join(F + G) + " η"
            hyps = (
                " ".join(f"(hF{i+1} : |{F[i]}| ≤ ({rat_lean(M[i])}))" for i in range(n))
                + " " + " ".join(f"(hG{i+1} : |{G[i]}| ≤ ({rat_lean(M[i])}))" for i in range(n))
                + " " + " ".join(f"(hd{i+1} : |{F[i]} - {G[i]}| ≤ η)" for i in range(n))
            )
            # telescoping terms: term_i = G1*…*G_{i-1} * (F_i - G_i) * F_{i+1}*…*Fn
            terms = []
            for i in range(n):
                fac = G[:i] + [f"({F[i]} - {G[i]})"] + F[i + 1:]
                terms.append(_prod_lean(fac))
            body: list[str] = []
            body.append("  have hη : 0 ≤ η := (abs_nonneg _).trans hd1")
            # per-term bound haves via deterministic mul_le_mul chains
            for i in range(n):
                fac_bounds = (
                    [(f"|{G[j]}|", f"({rat_lean(M[j])})", f"hG{j+1}",
                      f"(by norm_num : (0:ℝ) ≤ ({rat_lean(M[j])}))") for j in range(i)]
                    + [(f"|{F[i]} - {G[i]}|", "η", f"hd{i+1}", "hη")]
                    + [(f"|{F[j]}|", f"({rat_lean(M[j])})", f"hF{j+1}",
                        f"(by norm_num : (0:ℝ) ≤ ({rat_lean(M[j])}))") for j in range(i + 1, n)]
                )
                # chain: acc ≤ ACC, extend by one factor at a time
                steps = [f"  have hc{i+1}_1 : {fac_bounds[0][0]} ≤ {fac_bounds[0][1]} := "
                         f"{fac_bounds[0][2]}"]
                acc_lhs, acc_rhs = fac_bounds[0][0], fac_bounds[0][1]
                acc_nonneg = fac_bounds[0][3]
                for k in range(1, len(fac_bounds)):
                    lhs_k, rhs_k, h_k, nn_k = fac_bounds[k]
                    steps.append(
                        f"  have hc{i+1}_{k+1} : {acc_lhs} * {lhs_k} ≤ {acc_rhs} * {rhs_k} := "
                        f"mul_le_mul hc{i+1}_{k} {h_k} (abs_nonneg _) "
                        f"(le_trans (by positivity) hc{i+1}_{k})")
                    acc_lhs = f"{acc_lhs} * {lhs_k}"
                    acc_rhs = f"{acc_rhs} * {rhs_k}"
                # |term_i| = product of abs (abs_mul flattening), then the chain
                abs_rws = ", ".join(["abs_mul"] * (n - 1))
                steps.append(
                    f"  have ht{i+1} : |{terms[i]}| ≤ {acc_rhs} := by\n"
                    f"    rw [{abs_rws}]\n"
                    f"    exact hc{i+1}_{len(fac_bounds)}")
                body.extend(steps)
                _ = acc_nonneg
            # abs_add_le chain over the left-assoc telescoped sum
            for k in range(n, 1, -1):
                sub = " + ".join(terms[:k])
                prev = " + ".join(terms[: k - 1])
                body.append(
                    f"  have hS{k} : |{sub}| ≤ |{prev}| + |{terms[k-1]}| := abs_add_le _ _")
            sum_terms = " + ".join(terms)
            hint_names = ([f"hS{k}" for k in range(2, n + 1)]
                          + [f"ht{i+1}" for i in range(n)])
            lines.append(
                f"-- {nm}: multilinear product-perturbation envelope, arity {n},\n"
                f"-- bounds M={list(M)}, C = Σᵢ∏_{{j≠i}}Mⱼ = {C} (exact).\n"
                f"-- Ported/generalized from NavierStokesAndEuler MovingFrameODE.lean\n"
                f"-- product_perturbation_le (arity 2; Apache-2.0).  Trust seam: the factor\n"
                f"-- and perturbation bounds are HYPOTHESES.  (All 2n factor bounds are kept\n"
                f"-- for statement symmetry; the telescoping uses new-after/old-before, so the\n"
                f"-- first new and last old bound are unused — hence the linter suppression.)\n"
                f"set_option linter.unusedVariables false in\n"
                f"theorem {nm} ({binder} : ℝ)\n"
                f"    {hyps} :\n"
                f"    |{_prod_lean(F)} - {_prod_lean(G)}| ≤ ({rat_lean(C)}) * η := by\n"
                + "\n".join(body) + "\n"
                f"  have hid : |{_prod_lean(F)} - {_prod_lean(G)}| = |{sum_terms}| := by\n"
                f"    congr 1\n"
                f"    ring\n"
                f"  rw [hid]\n"
                f"  linarith [{', '.join(hint_names)}]\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def multilinear_perturbation_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``multilinear_perturbation``; ``spec: pt -> (M₁, …, Mₙ)`` rationals."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("multilinear_perturbation", spec),
        constants=dict(constants or {}),
    )

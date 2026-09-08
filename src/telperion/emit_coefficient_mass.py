"""CoefficientMassEval emitter — the ℓ¹-coefficient sup-envelope distilled from
the OpenAI Navier--Stokes blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``NavierStokes/EdgeWeightJets.lean``
``polynomial_eval_bound``, Apache-2.0; same shape in 3 Euler files).

The amplitude-constant workhorse: for any polynomial and any ``|x| ≤ T`` with
``T ≥ 1``,

    |p(x)|  ≤  ‖p‖₁ · T^deg(p),        ‖p‖₁ := Σ |coeff i|.

Two modes:

* ``generic`` — the fixed ``Polynomial ℝ`` atom (``coefficientMass`` +
  ``polynomial_eval_bound``), ported verbatim;
* ``scalar``  — a CONCRETE rational coefficient list ``[a₀, …, a_d]`` and
  rational ``T ≥ 1``: the mass ``M = Σ|aᵢ|`` and degree are computed EXACTLY in
  sympy and the specialized scalar bound

      |x| ≤ T  ⟹  |a₀ + a₁x + ⋯ + a_d x^d| ≤ M·T^d

  is emitted with a generated, sign-aware discharge (per-term ``abs_mul`` /
  ``abs_of_nonneg`` / ``abs_of_nonpos`` haves + ``abs_add_le`` chain + power
  bounds, closed by ``linarith`` — no fragile ``nlinarith``).  Refusals:
  ``T < 1``, zero leading coefficient, degree 0 (trivial) — negative controls.

HONESTY SEAM: nothing analytic here — this is a finitary bound; the certificate
content is the exact mass/degree arithmetic.  ``conjecture1_proved = False``.
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

COEFF_MASS_PRELUDE = r"""
-- l1-coefficient sup-envelope, ported from OpenAI's Navier-Stokes blowup
-- formalization (github.com/openai/NavierStokesAndEuler,
-- NavierStokes/EdgeWeightJets.lean polynomial_eval_bound; Apache-2.0).

noncomputable def coefficientMass (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

theorem coefficientMass_nonneg (p : Polynomial ℝ) : 0 ≤ coefficientMass p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem polynomial_eval_bound (p : Polynomial ℝ) {x T : ℝ} (hT : 1 ≤ T)
    (hx : |x| ≤ T) : |p.eval x| ≤ coefficientMass p * T ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * T ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (abs_nonneg x) hx i).trans
        (pow_le_pow_right₀ hT (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by rw [← Finset.sum_mul]; rfl
""".strip("\n")


@dataclass(frozen=True)
class CoefficientMassCert:
    """``generic`` or a concrete scalar instance: exact rational coefficients
    ``coeffs = (a₀, …, a_d)`` (``a_d ≠ 0``, ``d ≥ 1``), radius ``T ≥ 1``, and
    the re-verified mass ``M = Σ|aᵢ|``."""

    mode: str
    coeffs: tuple[sp.Rational, ...] | None = None
    T: sp.Rational | None = None
    M: sp.Rational | None = None


def coefficient_mass_certificate(mode, coeffs=None, T=None) -> CoefficientMassCert:
    """Build and EXACTLY re-check a coefficient-mass instance."""
    if mode == "generic":
        return CoefficientMassCert(mode="generic")
    if mode != "scalar":
        raise ValueError(f"coefficient_mass REFUSED: mode ∈ {{generic, scalar}}; got {mode}")
    coeffs = tuple(sp.Rational(sp.nsimplify(a)) for a in coeffs)
    T = sp.Rational(sp.nsimplify(T))
    if len(coeffs) < 2:
        raise ValueError("coefficient_mass REFUSED: need degree ≥ 1 (constant is trivial)")
    if coeffs[-1] == 0:
        raise ValueError(
            "coefficient_mass REFUSED: zero leading coefficient (the degree is the statement)")
    if not T >= 1:
        raise ValueError(f"coefficient_mass REFUSED: need 1 ≤ T; got {T}")
    M = sum(abs(a) for a in coeffs)
    assert M >= abs(coeffs[-1]) > 0  # exact re-validation
    return CoefficientMassCert(mode="scalar", coeffs=coeffs, T=T, M=sp.Rational(M))


def certify_coefficient_mass_point(family, pt, name):
    """``spec(pt) -> ("generic",) | ("scalar", coeffs, T)``."""
    spec = family.special[1](pt)
    mode, *args = spec
    if mode == "scalar":
        cert = coefficient_mass_certificate("scalar", coeffs=args[0], T=args[1])
        n_checks = 3
    else:
        cert = coefficient_mass_certificate("generic")
        n_checks = 1
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


def _poly_lean(coeffs: Sequence[sp.Rational]) -> str:
    """Render ``a₀ + a₁*x + a₂*x^2 + …`` (left-associated, all terms kept)."""
    parts = [f"({rat_lean(coeffs[0])})"]
    for i, a in enumerate(coeffs[1:], start=1):
        pw = "x" if i == 1 else f"x ^ {i}"
        parts.append(f"({rat_lean(a)}) * {pw}")
    return " + ".join(parts)


@dataclass
class CoefficientMassEmitter(Emitter):
    """Emit the generic ``Polynomial ℝ`` atom (once per file) plus concrete
    scalar instances with a generated sign-aware ``abs`` discharge closed by
    ``linarith``."""

    def __post_init__(self):
        self.kind = "coefficient_mass"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [COEFF_MASS_PRELUDE, ""]
        n_thm = 2  # coefficientMass_nonneg + polynomial_eval_bound
        for inst in fam.instances:
            cert: CoefficientMassCert = inst.payload  # type: ignore[assignment]
            if cert.mode == "generic":
                continue
            nm = inst.lean_name
            coeffs, T, M = cert.coeffs, cert.T, cert.M
            d = len(coeffs) - 1
            t, mm = rat_lean(T), rat_lean(M)
            poly = _poly_lean(coeffs)
            body: list[str] = []
            # per-term |aᵢ·xⁱ| = |aᵢ|·|x|ⁱ haves, sign-aware (no norm_num-on-abs)
            for i, a in enumerate(coeffs):
                ai, Ai = rat_lean(a), rat_lean(abs(a))
                sign_rw = (
                    f"abs_of_nonneg (by norm_num : (0:ℝ) ≤ ({ai}))" if a >= 0
                    else f"abs_of_nonpos (by norm_num : ({ai}:ℝ) ≤ 0)")
                if i == 0:
                    body.append(
                        f"  have hT0 : |({ai} : ℝ)| = ({Ai}) := by rw [{sign_rw}]"
                        + ("" if a >= 0 else "; norm_num"))
                else:
                    pw = "x" if i == 1 else f"x ^ {i}"
                    apw = "|x|" if i == 1 else f"|x| ^ {i}"
                    body.append(
                        f"  have hT{i} : |({ai}) * {pw}| = ({Ai}) * {apw} := by\n"
                        f"    rw [abs_mul{'' if i == 1 else ', abs_pow'}, {sign_rw}]"
                        + ("" if a >= 0 else "; ring"))
            # abs_add_le chain over the left-associated sum
            for k in range(d, 0, -1):
                sub = _poly_lean(coeffs[: k + 1])
                prev = _poly_lean(coeffs[:k])
                lastpw = "x" if k == 1 else f"x ^ {k}"
                body.append(
                    f"  have hA{k} : |{sub}| ≤ |{prev}| + |({rat_lean(coeffs[k])}) * {lastpw}| := "
                    f"abs_add_le _ _")
            # power bounds |x|^i ≤ T^d (and 1 ≤ T^d for the constant term)
            body.append(
                f"  have hP0 : (1:ℝ) ≤ ({t}) ^ {d} := one_le_pow₀ (by norm_num)")
            for i in range(1, d + 1):
                apw = "|x|" if i == 1 else f"|x| ^ {i}"
                if i == d:
                    body.append(
                        f"  have hP{i} : {apw} ≤ ({t}) ^ {d} := by\n"
                        f"    simpa using (pow_le_pow_left₀ (abs_nonneg x) hx {i})")
                else:
                    body.append(
                        f"  have hP{i} : {apw} ≤ ({t}) ^ {d} := by\n"
                        f"    have h1 := pow_le_pow_left₀ (abs_nonneg x) hx {i}\n"
                        f"    have h2 := pow_le_pow_right₀ (show (1:ℝ) ≤ ({t}) by norm_num)\n"
                        f"      (show {i} ≤ {d} by norm_num)\n"
                        f"    simpa using h1.trans h2")
            names = ([f"hT{i}" for i in range(d + 1)]
                     + [f"hA{k}" for k in range(1, d + 1)]
                     + [f"hP{i}" for i in range(d + 1)])
            lines.append(
                f"-- {nm}: scalar coefficient-mass envelope, coeffs={list(coeffs)}, "
                f"T={T}, mass M={M} (exact), degree {d}.\n"
                f"theorem {nm} (x : ℝ) (hx : |x| ≤ ({t})) :\n"
                f"    |{poly}| ≤ ({mm}) * ({t}) ^ {d} := by\n"
                + "\n".join(body) + "\n"
                f"  linarith [{', '.join(names)}]\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def coefficient_mass_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``coefficient_mass``; ``spec: pt -> ("generic",) | ("scalar", coeffs, T)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("coefficient_mass", spec),
        constants=dict(constants or {}),
    )

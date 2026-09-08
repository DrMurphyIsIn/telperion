"""LogConvexEndpointProduct emitter — zero-tolerant log-convexity interpolation
distilled from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``Euler/NonnegativeLogConvex.lean``,
Apache-2.0).

For a nonnegative sequence with the division- and log-free log-convexity law
``x(n+1)² ≤ x(n)·x(n+2)``, products of intermediate entries are dominated by
the corresponding endpoint products:

    cross   :  x(a+1)·x(a+d)   ≤ x(a)·x(a+d+1)
    pair    :  x(a+k)·x(a+k+d) ≤ x(a)·x(a+2k+d)
    between :  s ≤ a ≤ b  ⟹  x(a)·x(b) ≤ x(s)·x(a+b−s)

The engine for moment sequences, Sobolev norm ladders, and Hamburger-type
interpolation — with ZERO ENTRIES PERMITTED (the induction case-splits on a
vanishing entry and propagates it forward), so no positivity side conditions.

Modes: ``calculus`` (the fixed three-lemma chain) and ``between`` at concrete
naturals ``(s, a, b)`` with ``s ≤ a ≤ b`` certified exactly (violation
refused — the negative control).

HONESTY SEAM: nonnegativity and the log-convexity law are HYPOTHESES on the
abstract sequence; the kernel certifies only the interpolation arithmetic.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

LOGCONVEX_PRELUDE = r"""
-- Zero-tolerant log-convexity interpolation, ported from OpenAI's Euler blowup
-- formalization (github.com/openai/NavierStokesAndEuler,
-- Euler/NonnegativeLogConvex.lean; Apache-2.0).  Division- and log-free.

theorem logconvex_cross (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (hc : ∀ n, (x (n+1))^2 ≤ x n * x (n+2)) (a d : ℕ) :
    x (a+1) * x (a+d) ≤ x a * x (a+d+1) := by
  induction d with
  | zero => simp only [Nat.add_zero]; exact le_of_eq (mul_comm _ _)
  | succ d ih =>
    by_cases hz : x (a+d) = 0
    · have hz' : x (a+d+1) = 0 := by
        have h := hc (a+d)
        rw [hz, zero_mul] at h
        nlinarith [hx (a+d+1)]
      simpa only [Nat.add_succ, hz', mul_zero] using
        mul_nonneg (hx a) (hx (a+d+2))
    · have hp : 0 < x (a+d) := lt_of_le_of_ne (hx (a+d)) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hp).mp
      calc
        x (a+d) * (x (a+1) * x (a+d.succ)) =
            (x (a+1) * x (a+d)) * x (a+d+1) := by simp only [Nat.add_succ]; ring
        _ ≤ (x a * x (a+d+1)) * x (a+d+1) :=
          mul_le_mul_of_nonneg_right ih (hx _)
        _ = x a * (x (a+d+1))^2 := by ring
        _ ≤ x a * (x (a+d) * x (a+d+2)) := mul_le_mul_of_nonneg_left (hc _) (hx a)
        _ = x (a+d) * (x a * x (a+d.succ+1)) := by simp only [Nat.add_succ]; ring

theorem logconvex_pair (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (hc : ∀ n, (x (n+1))^2 ≤ x n * x (n+2)) (a k d : ℕ) :
    x (a+k) * x (a+k+d) ≤ x a * x (a+2*k+d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    have h := logconvex_cross x hx hc (a+k) (d+1)
    have hh := ih (d+2)
    convert h.trans hh using 1 <;> congr 2 <;> omega

theorem logconvex_between (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (hc : ∀ n, (x (n+1))^2 ≤ x n * x (n+2)) (s a b : ℕ)
    (hsa : s ≤ a) (hab : a ≤ b) :
    x a * x b ≤ x s * x (a+b-s) := by
  have h := logconvex_pair x hx hc s (a-s) (b-a)
  convert h using 1 <;> congr 2 <;> omega
""".strip("\n")


@dataclass(frozen=True)
class LogConvexInterpCert:
    """``calculus`` or a concrete ``between`` triple ``s ≤ a ≤ b``."""

    mode: str
    s: int | None = None
    a: int | None = None
    b: int | None = None


def logconvex_interp_certificate(mode, s=None, a=None, b=None) -> LogConvexInterpCert:
    """Build and EXACTLY re-check a log-convexity interpolation instance."""
    if mode == "calculus":
        return LogConvexInterpCert(mode="calculus")
    if mode != "between":
        raise ValueError(f"logconvex_interp REFUSED: mode ∈ {{calculus, between}}; got {mode}")
    s, a, b = int(s), int(a), int(b)
    if not (0 <= s <= a <= b):
        raise ValueError(
            f"logconvex_interp REFUSED: need 0 ≤ s ≤ a ≤ b; got (s,a,b)=({s},{a},{b})")
    return LogConvexInterpCert(mode="between", s=s, a=a, b=b)


def certify_logconvex_interp_point(family, pt, name):
    """``spec(pt) -> ("calculus",) | ("between", s, a, b)``."""
    spec = family.special[1](pt)
    mode, *args = spec
    if mode == "between":
        cert = logconvex_interp_certificate("between", *args)
        n_checks = 2
    else:
        cert = logconvex_interp_certificate("calculus")
        n_checks = 1
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


@dataclass
class LogConvexInterpEmitter(Emitter):
    """Emit the fixed cross/pair/between chain plus per-instance ``between``
    specializations (index side conditions by ``norm_num``).  Nonnegativity and
    the log-convexity law are hypotheses (the trust seam)."""

    def __post_init__(self):
        self.kind = "logconvex_interp"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [LOGCONVEX_PRELUDE, ""]
        n_thm = 3
        for inst in fam.instances:
            cert: LogConvexInterpCert = inst.payload  # type: ignore[assignment]
            if cert.mode == "calculus":
                continue
            nm = inst.lean_name
            s, a, b = cert.s, cert.a, cert.b
            lines.append(
                f"-- {nm}: endpoint-product interpolation at (s,a,b)=({s},{a},{b})\n"
                f"-- (0 ≤ {s} ≤ {a} ≤ {b} certified exactly; a+b−s = {a+b-s}).\n"
                f"-- Trust seam: nonnegativity + log-convexity law are HYPOTHESES.\n"
                f"theorem {nm} (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)\n"
                f"    (hc : ∀ n, (x (n+1))^2 ≤ x n * x (n+2)) :\n"
                f"    x {a} * x {b} ≤ x {s} * x {a + b - s} :=\n"
                f"  logconvex_between x hx hc {s} {a} {b} (by norm_num) (by norm_num)\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def logconvex_interp_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``logconvex_interp``; ``spec: pt -> ("calculus",) | ("between", s, a, b)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("logconvex_interp", spec),
        constants=dict(constants or {}),
    )

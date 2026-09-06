"""Borel–Carathéodory bound — packaging the (now UPSTREAM) Mathlib theorem.

The zero-free-region plan flagged Borel–Carathéodory as "the single missing Mathlib theorem"
(a ~500-line Möbius–Schwarz build). That is now OUT OF DATE: Mathlib (v4.32, `Mathlib.Analysis.
Complex.BorelCaratheodory`, author M. Radziwill) proves it in full:

    Complex.borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
      (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball 0 R) :
      ‖f z‖ ≤ 2*M*‖z‖/(R-‖z‖) + ‖f 0‖*(R+‖z‖)/(R-‖z‖)
    Complex.borelCaratheodory_zero  — the `f 0 = 0` version (RHS `2*M*‖z‖/(R-‖z‖)`).

So `emit_borel_caratheodory` is now a PACKAGING emitter (like `emit_order_residue` wraps
`residue_logDeriv`): given the target instantiation it emits a ready-to-use re-export of the
Mathlib theorem, `:= Complex.borelCaratheodory …`. Nothing is proved anew; the value is a
uniform entry point for zero-free/subconvexity code and a kernel-checkable dogfood that the
packaging is well-typed. The gate the plan worried about is GONE — the region assembly can cite
Mathlib directly. UNTRUSTED like every emitter: the kernel re-checks. conjecture1_proved = False.
"""
from __future__ import annotations

__all__ = ["emit_borel_caratheodory_cert", "BC_LEMMA"]

#: the Mathlib theorem names, general and vanishing-at-origin.
BC_LEMMA = {"general": "Complex.borelCaratheodory", "zero": "Complex.borelCaratheodory_zero"}


def emit_borel_caratheodory_cert(
    name: str,
    *,
    form: str = "general",
    doc: str | None = None,
) -> str:
    """Emit a Lean re-export of Mathlib's Borel–Carathéodory bound.

    ``form='general'`` → the full bound `‖f z‖ ≤ 2M‖z‖/(R−‖z‖) + ‖f 0‖(R+‖z‖)/(R−‖z‖)`.
    ``form='zero'``    → the `f 0 = 0` version (extra hypothesis `hf₂ : f 0 = 0`, RHS
    `2M‖z‖/(R−‖z‖)`).  Discharged by the direct application of the Mathlib theorem, so it
    type-checks exactly when that theorem has the stated type.
    """
    if form not in BC_LEMMA:
        raise ValueError(f"{name}: form must be 'general' or 'zero', got {form!r}")
    lemma = BC_LEMMA[form]
    hyps = (
        "(hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))\n"
        "    (hf₁ : Set.MapsTo f (Metric.ball 0 R) {z | z.re ≤ M})\n"
        "    (hR : 0 < R) (hz : z ∈ Metric.ball 0 R)"
    )
    if form == "zero":
        hyps += " (hf₂ : f 0 = 0)"
        rhs = "2 * M * ‖z‖ / (R - ‖z‖)"
        args = "hM hf hf₁ hR hz hf₂"
    else:
        rhs = "2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)"
        args = "hM hf hf₁ hR hz"
    docblock = f"/-- {doc} -/\n" if doc else (
        f"/-- Borel–Carathéodory ({'f 0 = 0' if form == 'zero' else 'general'}), re-export of "
        f"`{lemma}` (Mathlib). -/\n"
    )
    return (
        f"{docblock}"
        f"theorem {name} {{f : ℂ → ℂ}} {{M R : ℝ}} {{z : ℂ}}\n"
        f"    {hyps} :\n"
        f"    ‖f z‖ ≤ {rhs} :=\n"
        f"  {lemma} {args}"
    )

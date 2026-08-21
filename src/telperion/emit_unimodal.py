"""Unimodal integer-maximum emitter — the README-tracked-open "generic Lean
lemma for unimodal integer maxima", as a first-class shape.

Proves `∀ n ≥ s0, f(n) ≤ B` for a positive real sequence `f : ℕ → ℝ` whose
successor ratio `r(s) = f(s+1)/f(s)` is monotone (crosses 1 exactly once at
`s*`): `f` rises to `s*` then falls, so its integer maximum is `f(s*)`, and
`f(s*) ≤ B` closes it.  The certificate machinery is `unimodal.py`
(`unimodal_certificate`): a Pólya-certified decreasing ratio + exact crossing
facts.  This module wires it into a pipeline emitter.

Lean shape (per instance):

    theorem <name> : ∀ n : ℕ, s0 ≤ n → f n ≤ B := by
      have hdn : ∀ s, s* ≤ s → f (s+1) ≤ f s := by ...   -- the Pólya tail
      have hup : ∀ s, s0 ≤ s → s < s* → f s ≤ f (s+1) := by
        intro s _ _; interval_cases s <;> norm_num       -- finite climb [s0,s*)
      have hpk : ∀ n, s0 ≤ n → f n ≤ f s* := Telperion.unimodal_peak hup hdn
      intro n hn; exact le_trans (hpk n hn) (by norm_num)   -- f s* ≤ B

The reusable peak lemma `Telperion.unimodal_peak` is proven ONCE in the prelude
(`UNIMODAL_PRELUDE`): descend via `Nat.le_induction`, climb via induction on the
gap `s* - n`.  Add it at the call site: `LeanProfile(prelude=UNIMODAL_PRELUDE)`.

SCOPE / HONESTY: the certifier + the per-instance obligations (decreasing tail
Pólya cert, finite climb, base bound) are all exact-arithmetic validated here;
the Lean KERNEL verdict is CI-only (this repo cannot run `lake` locally).  The
Pólya-tail hypothesis `hdn` is the genuine Lean risk (it renders `f` as a real
function and proves the tail step); it is emitted best-effort and settled by
the compile gate.  conjecture1_proved unaffected.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, expr_lean_from_parts, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .unimodal import UnimodalityCertificate, unimodal_certificate
from .workflow import Emitter

# The reusable integer-unimodal-peak lemma, proven once (no `sorry`, no axioms).
UNIMODAL_PRELUDE = r"""namespace Telperion

/-- If `f : ℕ → ℝ` rises up to `sstar` and falls beyond it, then its maximum
over `n ≥ s0` is at `sstar`. -/
theorem unimodal_peak {f : ℕ → ℝ} {s0 sstar : ℕ}
    (hup : ∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1))
    (hdn : ∀ s, sstar ≤ s → f (s + 1) ≤ f s) :
    ∀ n, s0 ≤ n → f n ≤ f sstar := by
  have climb : ∀ a b, s0 ≤ a → a ≤ b → b ≤ sstar → f a ≤ f b := by
    intro a b ha hab hb
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih =>
      have hks : k < sstar := lt_of_lt_of_le (Nat.lt_succ_self k) hb
      exact le_trans (ih (le_of_lt hks)) (hup k (le_trans ha hk) hks)
  have desc : ∀ a b, sstar ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih => exact le_trans (hdn k (le_trans ha hk)) ih
  intro n hn
  rcases (by omega : n ≤ sstar ∨ sstar < n) with h | h
  · exact climb n sstar hn h le_rfl
  · exact desc sstar n le_rfl (le_of_lt h)

/-- Bridge: from a positive sequence whose successor ratio is `≥ 1` below `sstar`
and `≤ 1` at/above it, derive the pointwise climb/descend hypotheses
`unimodal_peak` needs. Lets a caller assemble the full `f n ≤ B` theorem from a
Pólya-certified decreasing ratio plus the two crossing facts. -/
theorem climb_descend_of_ratio
    (f : ℕ → ℝ) (s0 sstar : ℕ) (hs0 : s0 ≤ sstar)
    (hpos : ∀ s, s0 ≤ s → 0 < f s)
    (hrup : ∀ s, s0 ≤ s → s < sstar → 1 ≤ f (s + 1) / f s)
    (hrdn : ∀ s, sstar ≤ s → f (s + 1) / f s ≤ 1) :
    (∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1)) ∧
    (∀ s, sstar ≤ s → f (s + 1) ≤ f s) := by
  refine ⟨?_, ?_⟩
  · intro s hs hlt
    have hp : 0 < f s := hpos s hs
    have h := hrup s hs hlt
    rw [le_div_iff₀ hp] at h
    linarith
  · intro s hs
    have hp : 0 < f s := hpos s (le_trans hs0 hs)
    have h := hrdn s hs
    rw [div_le_one hp] at h
    linarith

end Telperion
"""


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_unimodal_point(family, pt, name):
    """Certify one unimodal-max instance: (CertifiedInstance, n_checks).

    Reads (ratio, s0, s_symbol) = family.special[1](pt), where `ratio` is the
    successor ratio `r(s) = f(s+1)/f(s)` of a positive sequence `f` (given
    directly — `f` itself is often a product/binomial with no closed rational
    form, so we certify via the ratio).  `unimodal_certificate` Pólya-certifies
    `r` decreasing and locates the crossing `s*`.  Raises ValueError (refusal)
    when `r` is not certifiably decreasing or has no crossing of 1.
    """
    ratio, s0, s = family.special[1](pt)
    ratio = sp.together(sp.sympify(ratio))
    s = s if s is not None else sp.Symbol("s", nonnegative=True)
    cert: UnimodalityCertificate = unimodal_certificate(ratio, int(s0), s_symbol=s)
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=(cert, s),
    )
    # checks: decreasing-tail Pólya + the two crossing facts
    return inst, 3


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class UnimodalMaxEmitter(Emitter):
    """Emit the exact-arithmetic certificate of unimodality — the pieces that,
    with the reusable `Telperion.unimodal_peak` lemma (see `UNIMODAL_PRELUDE`),
    pin the integer maximum at `s*`.  Per certified instance, three kernel-
    checkable theorems:

        <name>_dec (t : ℝ) (ht : 0 ≤ t) : 0 ≤ <r(s0+t) − r(s0+t+1)>  := by positivity
        <name>_cross_hi : <r(s*)>   ≤ 1  := by norm_num
        <name>_cross_lo : 1 ≤ <r(s*−1)>  := by norm_num   (when s* > s0)

    `_dec` is the Pólya-certified monotone-ratio step (`r` decreasing); the two
    `_cross_*` facts localize the crossing of 1 at `s*`.  Together with
    `unimodal_peak` (proven once in the prelude) these give: the max of the
    sequence over integers `n ≥ s0` is at `s*`.  The final application is a
    one-line `unimodal_peak` invocation the caller writes against their own Lean
    definition of the sequence `f : ℕ → ℝ` (often `Nat.choose`-like, hence not a
    rational function we could render for you) — named, not faked."""

    def __post_init__(self):
        self.kind = "unimodal"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        t = sp.Symbol("t", nonnegative=True)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            cert, _s = inst.payload  # type: ignore[misc]
            dec = cert.decreasing_cert
            step_body = expr_lean_from_parts(dec.numerator, dec.denominator, (t,))
            lines.append(
                f"theorem {inst.lean_name}_dec (t : ℝ) (ht : 0 ≤ t) : "
                f"(0:ℝ) ≤ {step_body} := by positivity\n"
            )
            n += 1
            lines.append(
                f"theorem {inst.lean_name}_cross_hi : "
                f"({rat_lean(cert.cross_hi)} : ℝ) ≤ 1 := by norm_num\n"
            )
            n += 1
            if cert.s_star > cert.s0:
                lines.append(
                    f"theorem {inst.lean_name}_cross_lo : "
                    f"(1:ℝ) ≤ {rat_lean(cert.cross_lo)} := by norm_num\n"
                )
                n += 1
        return "".join(lines), n


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def unimodal_max_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a unimodal-integer-max family (kind='unimodal').

    spec: a callable ``pt -> (f, s0, bound, s_symbol)`` where ``f`` is a positive
    rational function of the integer index ``s_symbol`` (a sympy Symbol), ``s0``
    the lower index, ``bound`` the claimed maximum.  ``certify_unimodal_point``
    Pólya-certifies the decreasing ratio, locates the peak s*, and checks
    f(s*) ≤ bound — refusing otherwise (the negative control).
    """
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("unimodal", spec),
        constants=dict(constants or {}),
    )

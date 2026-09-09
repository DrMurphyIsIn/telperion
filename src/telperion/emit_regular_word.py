"""RegularWordLinearInvariant emitter — a linear counting invariant over a
forbidden-factor word grammar, distilled from the OpenAI Navier--Stokes blowup
formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/VolterraAnalyticBounds.lean`` ``GoodWord``/``goodWord_losses``,
Apache-2.0).

Telperion's first DISCRETE/word-combinatorics kind: over ``List Bool`` words
avoiding the factor ``true·true`` (no consecutive derivative letters), the
count of ``true`` letters obeys the linear density bound

    2·losses(w) ≤ |w| + 1,      i.e.      losses(w) ≤ (|w|+1)/2,

by structural recursion (``termination_by w.length``) + ``omega``.  Applies to
any density bound on words avoiding a fixed factor; in the source it caps the
loss-letter count feeding the Volterra analytic estimates (the letters-to-zero
half, ``word_eq_zero_of_not_good``, is Field-specific PRELUDE, not emitted).

HONESTY SEAM: none — decidable/finitary facts about lists.
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

REGULAR_WORD_PRELUDE = r"""
-- Forbidden-factor word-grammar counting invariant, ported from OpenAI's
-- Navier-Stokes blowup formalization (github.com/openai/NavierStokesAndEuler,
-- VolterraAnalyticBounds.lean; Apache-2.0).  Telperion's first discrete axis.

/-- The count of `true` (derivative) letters in a word. -/
def wordLosses : List Bool → ℕ
  | [] => 0
  | false :: w => wordLosses w
  | true :: w => wordLosses w + 1

/-- Words without consecutive `true` letters (the forbidden factor `tt`). -/
def GoodWord : List Bool → Prop
  | [] => True
  | false :: w => GoodWord w
  | true :: [] => True
  | true :: false :: w => GoodWord w
  | true :: true :: _ => False

/-- The linear density invariant: a good word is at most half `true` letters. -/
theorem goodWord_losses (w : List Bool) (hw : GoodWord w) :
    2 * wordLosses w ≤ w.length + 1 := by
  match w with
  | [] => simp [wordLosses]
  | false :: w =>
      have ih := goodWord_losses w hw
      simp only [wordLosses, List.length_cons]
      omega
  | [true] => simp [wordLosses]
  | true :: false :: w =>
      have ih := goodWord_losses w hw
      simp only [wordLosses, List.length_cons]
      omega
  | true :: true :: w => exact False.elim hw
termination_by w.length

theorem losses_le_half (w : List Bool) (hw : GoodWord w) :
    wordLosses w ≤ (w.length + 1) / 2 := by
  have := goodWord_losses w hw
  omega
""".strip("\n")


@dataclass(frozen=True)
class RegularWordCert:
    mode: str = "calculus"


def regular_word_certificate() -> RegularWordCert:
    return RegularWordCert()


def certify_regular_word_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=regular_word_certificate())
    return inst, 1


@dataclass
class RegularWordEmitter(Emitter):
    """Emit the fixed word-grammar counting atoms (once per file)."""

    def __post_init__(self):
        self.kind = "regular_word"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return REGULAR_WORD_PRELUDE + "\n", 2


def regular_word_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``regular_word`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("regular_word", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )

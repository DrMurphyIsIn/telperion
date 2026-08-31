"""Preconnectedness-by-convex-cover emitter.

Some domains are not convex but ARE preconnected because they are a finite union
of convex pieces glued along shared points.  The canonical case here is a convex
open set with a single INTERIOR point removed -- e.g. the strip domain of the
zeta fractional-part representation,

    stripDomain = {s : ℂ | 0 < Re s} \\ {1},

an open right half-plane punctured at the interior point 1.  No two-convex cover
exists (a convex set cannot exclude an interior point while covering a
neighbourhood of it), so we use FOUR convex half-plane pieces

    A = {b < re} ∩ {re < c}     B = {b < re} ∩ {0 < im}
    C = {b < re} ∩ {im < 0}     D = {c < re}

for a real puncture point `c` on the real axis with `b < c`, glued in the order
((A ∪ B) ∪ C) ∪ D at ((b+c)/2, 1), ((b+c)/2, -1), (c+1, 1).  A ∪ B ∪ C ∪ D
excludes exactly the point (c, 0).

WHY THIS IS A CERTIFICATE (not a template).  Telperion is the CHECKER; this
generator is UNTRUSTED.  The load-bearing claim is COVER COMPLETENESS

    {b < re} \\ {(c,0)}  =  A ∪ B ∪ C ∪ D,

a set identity over the linear forms (re-b), (re-c), im.  Their signs partition
the plane into finitely many CELLS (a hyperplane arrangement); the identity holds
iff, on every geometrically realizable sign-cell, the target predicate agrees with
the disjunction of the piece predicates.  That is a FINITE, EXACT check (the
`FiniteDecide` shape) -- `verify_cover_complete` enumerates all realizable cells
and REFUSES any cover that misses a cell or overshoots the target (including the
anti-phantom failure of a puncture that is not interior, `c <= b`).  Only after
the finite certificate re-verifies is any Lean written; the emitted proof mirrors
the kernel-checked `StripReprR3.lean` (CI job `strip-repr-r3-compiles`, green).

The Lean uses `convex_halfSpace_re_gt/re_lt/im_gt/im_lt` (capital S, Mathlib
v4.32.0), `Convex.inter`, `Convex.isPreconnected`, and `IsPreconnected.union`
(shared point first).  A gap-filler FEEDING input (R); NOT a proof of RH.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product

import sympy as sp

from .expr import rat_lean


# --------------------------------------------------------------------------- #
# The untrusted construction.                                                 #
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class PuncturedHalfPlaneCover:
    """A 4-convex-piece cover of `{b < Re s} \\ {(c, 0)}` (c real, b < c)."""
    b: sp.Rational
    c: sp.Rational

    @property
    def gluing_points(self) -> list[tuple[sp.Rational, sp.Rational]]:
        mid = sp.Rational(self.b + self.c, 1) / 2
        return [(mid, sp.Integer(1)), (mid, sp.Integer(-1)), (self.c + 1, sp.Integer(1))]


# --------------------------------------------------------------------------- #
# The exact re-verification (the certificate).                                #
# --------------------------------------------------------------------------- #
def _cell_target(s1: int, s2: int, s3: int) -> bool:
    """Target `{b < re} \\ {(c,0)}` on a sign-cell (s1=sgn(re-b), s2=sgn(re-c),
    s3=sgn(im)).  In the domain iff re>b and NOT (re=c and im=0)."""
    in_base = s1 > 0
    is_puncture = (s2 == 0) and (s3 == 0)   # re == c and im == 0
    return in_base and not is_puncture


def _cell_pieces(s1: int, s2: int, s3: int) -> bool:
    """A ∪ B ∪ C ∪ D on a sign-cell."""
    A = (s1 > 0) and (s2 < 0)
    B = (s1 > 0) and (s3 > 0)
    C = (s1 > 0) and (s3 < 0)
    D = (s2 > 0)
    return A or B or C or D


def _realizable(b: sp.Rational, c: sp.Rational, s1: int, s2: int, s3: int) -> bool:
    """Is the sign-cell (s1,s2,s3) geometrically realizable, given b < c?
    s1 = sgn(re-b), s2 = sgn(re-c) are linked because b < c: re < b ⟹ re < c, etc.
    s3 = sgn(im) is free."""
    if not (b < c):
        return False
    # Enumerate the consistent (s1, s2) pairs for a real `re` with b < c.
    #   re < b  -> (s1,s2) = (-,-)
    #   re = b  -> (0,-)
    #   b<re<c  -> (+,-)
    #   re = c  -> (+,0)
    #   re > c  -> (+,+)
    consistent = {(-1, -1), (0, -1), (1, -1), (1, 0), (1, 1)}
    return (s1, s2) in consistent


def verify_cover_complete(cover: PuncturedHalfPlaneCover) -> bool:
    """EXACT finite certificate: the 4-piece union equals the target on EVERY
    realizable sign-cell.  Returns False (REFUSE) if the puncture is not interior
    (c <= b) or any cell disagrees.  This is the anti-phantom gate."""
    b, c = cover.b, cover.c
    if not (b < c):
        return False
    for s1, s2, s3 in product((-1, 0, 1), repeat=3):
        if not _realizable(b, c, s1, s2, s3):
            continue
        if _cell_target(s1, s2, s3) != _cell_pieces(s1, s2, s3):
            return False
    return True


def verify_gluing_points(cover: PuncturedHalfPlaneCover) -> bool:
    """Each gluing point must lie in the two pieces it joins (exact membership)."""
    b, c = cover.b, cover.c
    p_ab, p_ac, p_bd = cover.gluing_points

    def inA(p):  # {b<re} ∩ {re<c}
        return (b < p[0]) and (p[0] < c)

    def inB(p):  # {b<re} ∩ {0<im}
        return (b < p[0]) and (0 < p[1])

    def inC(p):  # {b<re} ∩ {im<0}
        return (b < p[0]) and (p[1] < 0)

    def inD(p):  # {c<re}
        return c < p[0]

    return (inA(p_ab) and inB(p_ab)        # A ∩ B
            and inA(p_ac) and inC(p_ac)    # A ∩ C
            and inB(p_bd) and inD(p_bd))   # B ∩ D  (in (A∪B∪C) via B)


# --------------------------------------------------------------------------- #
# Lean emission (only after the certificate re-verifies).                     #
# --------------------------------------------------------------------------- #
def emit_preconnected_lean(cover: PuncturedHalfPlaneCover, thm_name: str,
                           domain: str = "stripDomain") -> str:
    """Emit a kernel-ready Lean proof of `IsPreconnected <domain>` where
    `<domain> = {s : ℂ | b < s.re} \\ {c}`.  REFUSES to emit unless the exact
    cover-completeness and gluing certificates both pass."""
    if not verify_cover_complete(cover):
        raise ValueError(
            f"cover REFUSED: {{{cover.b} < re}} \\ {{{cover.c}}} is not covered by the "
            f"four pieces (puncture not interior, or a sign-cell disagrees)")
    if not verify_gluing_points(cover):
        raise ValueError("cover REFUSED: a gluing point is not in both its pieces")

    b, c = rat_lean(cover.b), rat_lean(cover.c)
    (mab_x, mab_y), (mac_x, mac_y), (mbd_x, mbd_y) = cover.gluing_points
    mab = (rat_lean(mab_x), rat_lean(mab_y))
    mac = (rat_lean(mac_x), rat_lean(mac_y))
    mbd = (rat_lean(mbd_x), rat_lean(mbd_y))

    return f"""\
/-- Preconnectedness of `{{s : ℂ | {b} < s.re}} \\ {{{c}}}` (open half-plane
    punctured at the interior real point {c}) via a 4-convex-piece cover.
    Cover-completeness re-verified by exact sign-cell enumeration before emission. -/
theorem {thm_name} : IsPreconnected {domain} := by
  have preA : IsPreconnected ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.re < {c}}}) :=
    ((convex_halfSpace_re_gt {b}).inter (convex_halfSpace_re_lt {c})).isPreconnected
  have preB : IsPreconnected ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | 0 < s.im}}) :=
    ((convex_halfSpace_re_gt {b}).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have preC : IsPreconnected ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.im < 0}}) :=
    ((convex_halfSpace_re_gt {b}).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have preD : IsPreconnected {{s : ℂ | {c} < s.re}} := (convex_halfSpace_re_gt {c}).isPreconnected
  have g1 : (⟨{mab[0]}, {mab[1]}⟩ : ℂ) ∈ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.re < {c}}}) := by
    norm_num [Set.mem_inter_iff, Set.mem_setOf_eq]
  have g1' : (⟨{mab[0]}, {mab[1]}⟩ : ℂ) ∈ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | 0 < s.im}}) := by
    norm_num [Set.mem_inter_iff, Set.mem_setOf_eq]
  have preAB := IsPreconnected.union (⟨{mab[0]}, {mab[1]}⟩ : ℂ) g1 g1' preA preB
  have g2 : (⟨{mac[0]}, {mac[1]}⟩ : ℂ) ∈
      (({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.re < {c}}}) ∪ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | 0 < s.im}})) :=
    Or.inl (by norm_num [Set.mem_inter_iff, Set.mem_setOf_eq])
  have g2' : (⟨{mac[0]}, {mac[1]}⟩ : ℂ) ∈ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.im < 0}}) := by
    norm_num [Set.mem_inter_iff, Set.mem_setOf_eq]
  have preABC := IsPreconnected.union (⟨{mac[0]}, {mac[1]}⟩ : ℂ) g2 g2' preAB preC
  have g3 : (⟨{mbd[0]}, {mbd[1]}⟩ : ℂ) ∈
      ((({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.re < {c}}}) ∪ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | 0 < s.im}})) ∪ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.im < 0}})) :=
    Or.inl (Or.inr (by norm_num [Set.mem_inter_iff, Set.mem_setOf_eq]))
  have g3' : (⟨{mbd[0]}, {mbd[1]}⟩ : ℂ) ∈ {{s : ℂ | {c} < s.re}} := by
    norm_num [Set.mem_setOf_eq]
  have preABCD := IsPreconnected.union (⟨{mbd[0]}, {mbd[1]}⟩ : ℂ) g3 g3' preABC preD
  have heq : {domain} =
      ((({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.re < {c}}}) ∪ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | 0 < s.im}}))
        ∪ ({{s : ℂ | {b} < s.re}} ∩ {{s : ℂ | s.im < 0}})) ∪ {{s : ℂ | {c} < s.re}} := by
    ext s
    simp only [{domain}, Set.mem_diff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff, Set.mem_setOf_eq, Complex.ext_iff, Complex.one_re, Complex.one_im]
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy s.re {c} with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · have him : s.im ≠ 0 := by rintro h0; exact hne ⟨h, h0⟩
        rcases lt_or_gt_of_ne him with h2 | h2
        · exact Or.inl (Or.inr ⟨hre, h2⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hre, h2⟩))
      · exact Or.inr h
    · rintro ((( ⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h)
      · exact ⟨h1, by rintro ⟨he, _⟩; linarith⟩
      · exact ⟨h1, by rintro ⟨_, he⟩; linarith⟩
      · exact ⟨h1, by rintro ⟨_, he⟩; linarith⟩
      · exact ⟨by linarith, by rintro ⟨he, _⟩; linarith⟩
  rw [heq]; exact preABCD
"""


def _self_test() -> None:
    # The verified R3 instance: {0 < re} \ {1}.
    r3 = PuncturedHalfPlaneCover(sp.Integer(0), sp.Integer(1))
    assert verify_cover_complete(r3), "R3 cover must re-verify"
    assert verify_gluing_points(r3), "R3 gluing points must check"
    lean = emit_preconnected_lean(r3, "isPreconnected_stripDomain")
    assert "IsPreconnected.union" in lean and "convex_halfSpace_re_gt" in lean

    # Anti-phantom 1: a non-interior puncture (c <= b) is REFUSED.
    bad = PuncturedHalfPlaneCover(sp.Integer(2), sp.Integer(1))  # c=1 < b=2
    assert not verify_cover_complete(bad), "non-interior puncture must be refused"
    try:
        emit_preconnected_lean(bad, "forged")
        raise AssertionError("emission must refuse a non-interior puncture")
    except ValueError:
        pass

    # Anti-phantom 2: tamper the target/pieces disagreement is caught by the cell check.
    # (Directly exercise the cell predicate: at the puncture cell the union is empty
    #  while a *wrong* target that keeps the puncture would disagree.)
    assert _cell_target(1, 0, 0) is False and _cell_pieces(1, 0, 0) is False

    print("emit_preconnected_cover self-test: OK")


if __name__ == "__main__":
    _self_test()

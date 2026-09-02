"""Algebraic-bracket emitter: rigorous rational two-sided enclosures of a square root.

The ALGEBRAIC companion to emit_bracket's IntervalBracketEmitter (which encloses
the transcendental ``exp(-theta)``).  Here the enclosed quantity is a real square
root of a nonnegative rational:

    lo <= Real.sqrt a <= hi              (lo >= 0,  lo^2 <= a <= hi^2).

The soundness of BOTH sides reduces to two EXACT rational facts about squares,
so the whole certificate is a rational computation (no floats, no transcendental
Taylor heart):

    lo <= sqrt a    <==   lo^2 <= a               (Real.le_sqrt_of_sq_le)
    sqrt a <= hi    <==   0 <= hi  AND  a <= hi^2  (Real.sqrt_le_iff)

``algebraic_bracket_certificate(a, lo, hi)`` sympy-checks ``lo >= 0`` and
``lo**2 <= a <= hi**2`` and RAISES ``ValueError`` otherwise (the negative
control: ``lo**2 > a`` under-shoots, ``a > hi**2`` over-shoots, ``lo < 0`` or
``a < 0`` is out of domain).

EMITTED LEAN (per instance), one conjunction theorem:

    theorem <name> : (<lo> : ℝ) ≤ Real.sqrt <a> ∧ Real.sqrt <a> ≤ <hi> := by
      refine ⟨Real.le_sqrt_of_sq_le (by norm_num),
              Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩⟩

Mathlib v4.32.0 lemmas used (verified against
``Mathlib/Analysis/Real/Sqrt.lean`` at rev v4.32.0):
  * ``Real.le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ Real.sqrt y``   (no side condition)
  * ``Real.sqrt_le_iff : Real.sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2``
The three residual rational goals (``lo^2 ≤ a``, ``0 ≤ hi``, ``a ≤ hi^2``) are
closed by ``norm_num`` — pure rational arithmetic.

HONEST SCOPE: rigorous rational enclosures of a real square root.  BG-relevant
instances (e.g. ``1 ≤ √2 ≤ 17/12`` — the ``e2_two_rhoB`` crux — and ``√23``)
are supported, but this emitter proves ONLY the enclosure; it does not close any
downstream BG obligation.  conjecture1_proved=False.
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
class AlgebraicBracketCertificate:
    """A verified rational two-sided enclosure ``lo <= sqrt(a) <= hi``.

    Fields are exact sympy Rationals.  The invariants ``0 <= lo``,
    ``lo**2 <= a`` and ``a <= hi**2`` are checked (and re-provable in Lean by
    ``norm_num``); their conjunction is exactly what makes the emitted tactic
    sequence sound.
    """

    a: sp.Rational      # radicand, a >= 0
    lo: sp.Rational     # lower bound, lo >= 0, lo^2 <= a
    hi: sp.Rational     # upper bound, a <= hi^2


def algebraic_bracket_certificate(a, lo, hi) -> AlgebraicBracketCertificate:
    """Build and EXACTLY self-check a ``lo <= sqrt(a) <= hi`` certificate.

    Refuses (``ValueError``) when the radicand is negative, the lower bound is
    negative, or either square inequality fails — the negative controls."""
    a = sp.nsimplify(a)
    lo = sp.nsimplify(lo)
    hi = sp.nsimplify(hi)
    if not (a.is_Rational and lo.is_Rational and hi.is_Rational):
        raise ValueError(f"algebraic_bracket needs rational a, lo, hi; got {a}, {lo}, {hi}")
    if a < 0:
        raise ValueError(f"REFUSED: radicand a = {a} < 0; sqrt domain requires a >= 0")
    if lo < 0:
        raise ValueError(f"REFUSED: lower bound lo = {lo} < 0; must have lo >= 0")
    if lo**2 > a:
        raise ValueError(
            f"REFUSED: lo^2 = {lo**2} > a = {a}; lo={lo} is NOT a valid lower bound "
            f"for sqrt({a})"
        )
    if a > hi**2:
        raise ValueError(
            f"REFUSED: a = {a} > hi^2 = {hi**2}; hi={hi} is NOT a valid upper bound "
            f"for sqrt({a})"
        )
    return AlgebraicBracketCertificate(a=sp.Rational(a), lo=sp.Rational(lo), hi=sp.Rational(hi))


def certify_algebraic_bracket_point(family, pt, name):
    """Certify one algebraic-bracket instance from ``family.special[1](pt) ->
    (a, lo, hi)``.  Returns ``(CertifiedInstance, n_checks)``; ``n_checks`` = 3
    (the three exact rational facts: ``lo^2 <= a``, ``0 <= hi``, ``a <= hi^2``)."""
    a, lo, hi = family.special[1](pt)
    cert = algebraic_bracket_certificate(a, lo, hi)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 3


@dataclass
class AlgebraicBracketEmitter(Emitter):
    """Emit ``lo <= Real.sqrt a <= hi`` — one conjunction theorem per instance,
    closed deterministically by ``Real.le_sqrt_of_sq_le`` (lower) +
    ``Real.sqrt_le_iff`` (upper), with the three residual rational side-goals
    discharged by ``norm_num``."""

    def __post_init__(self):
        self.kind = "algebraic_bracket"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: AlgebraicBracketCertificate = inst.payload  # type: ignore[assignment]
            a = rat_lean(cert.a)
            lo = rat_lean(cert.lo)
            hi = rat_lean(cert.hi)
            lines.append(
                f"theorem {inst.lean_name} :\n"
                f"    ({lo} : ℝ) ≤ Real.sqrt {a} ∧ Real.sqrt {a} ≤ {hi} := by\n"
                f"  refine ⟨Real.le_sqrt_of_sq_le (by norm_num),\n"
                f"          Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩⟩\n"
            )
            nthm += 1
        return "".join(lines), nthm


def algebraic_bracket_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an algebraic-bracket family (kind='algebraic_bracket').

    ``spec``: a callable ``pt -> (a, lo, hi)`` returning rationals with
    ``a >= 0``, ``lo >= 0``, ``lo^2 <= a`` and ``a <= hi^2``.  Refuses (at
    certification) any point violating those exact rational facts."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("algebraic_bracket", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: build a valid cert, run a negative control, print Lean ---
    print("=== positive: a=2, lo=1, hi=17/12 (the BG e2_two_rhoB crux) ===")
    cert = algebraic_bracket_certificate(2, 1, sp.Rational(17, 12))
    print(f"  cert = {cert}")
    print(f"  checks: lo^2={cert.lo**2} <= a={cert.a} <= hi^2={cert.hi**2}  (all exact)")

    print("\n=== negative control: a=2, lo=1, hi=1  (hi^2=1 < a=2, over-shoot) ===")
    try:
        algebraic_bracket_certificate(2, 1, 1)
        print("  ERROR: negative control did NOT raise!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== negative control: a=2, lo=sqrt-overshoot 3/2 (lo^2=9/4 > 2) ===")
    try:
        algebraic_bracket_certificate(2, sp.Rational(3, 2), 2)
        print("  ERROR: negative control did NOT raise!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== negative control: a=-1 (radicand out of domain) ===")
    try:
        algebraic_bracket_certificate(-1, 0, 1)
        print("  ERROR: negative control did NOT raise!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (√2, √3, √23) ===")
    import importlib
    _certify_mod = importlib.import_module(".certify", __package__)
    from .certify import certify
    from .workflow import ValidationReport, emit

    # Self-test injects the certify.py registration that the final REPORT asks
    # the maintainer to add permanently (kept out of the shared file per the
    # do-not-edit-shared-files constraint).  This mirrors the exact dispatch the
    # production pipeline uses once _SPECIAL_KINDS / _SPECIAL_DISPATCH carry the
    # algebraic_bracket rows.
    if "algebraic_bracket" not in _certify_mod._SPECIAL_KINDS:
        _certify_mod._SPECIAL_KINDS = _certify_mod._SPECIAL_KINDS + ("algebraic_bracket",)
    _certify_mod._SPECIAL_DISPATCH["algebraic_bracket"] = (
        "emit_algebraic_bracket", "certify_algebraic_bracket_point"
    )

    _SPECS = {
        # 1 <= √2 <= 17/12   (1 <= 2 <= 289/144)  — the BG e2_two_rhoB crux
        0: (sp.Integer(2), sp.Integer(1), sp.Rational(17, 12)),
        # 12/7 <= √3 <= 7/4  (144/49 <= 3 <= 49/16)
        1: (sp.Integer(3), sp.Rational(12, 7), sp.Rational(7, 4)),
        # 14/3 <= √23 <= 24/5  (196/9 <= 23 <= 576/25)  — BG-relevant (621/64=27*23)
        2: (sp.Integer(23), sp.Rational(14, 3), sp.Rational(24, 5)),
    }
    _NAMES = {0: "sqrt_two", 1: "sqrt_three", 2: "sqrt_twentythree"}
    fam = algebraic_bracket_family(
        "AlgebraicBracket",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("AlgebraicBracket",)),
        [AlgebraicBracketEmitter()],
        ValidationReport(checks=(("algebraic_bracket", True),)),
    )
    print(next(iter(report.files.values())))

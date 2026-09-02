"""Finite-argmax margin emitter: a designated winner strictly beats a finite list
of competitors, certified by cross-multiplied INTEGER strict inequalities.

The combinatorial companion to the BG competitor-extremality theorems
(examples/bg_extremality/frozen/BGExtremality.lean — the ``bgext_n*_beats_runnerup``
facts).  There, a near-star ``N(0,k)`` maximizes ``Phi^11`` over all trees on ``n``
vertices, i.e. its rational value strictly exceeds each competitor's; each such
"beats" fact is exactly a cross-multiplied integer inequality

    p_i * q_w  <  p_w * q_i          (v_i = p_i/q_i  <  v_w = p_w/q_w,  q_i,q_w > 0).

This emitter certifies *finite extremality with a strict margin*: given a winner
rational ``v_w = p_w/q_w`` (``q_w > 0``) and a finite list of competitor rationals
``v_i = p_i/q_i`` (``q_i > 0``), it sympy-checks the cross-multiplied strict
inequality ``p_w*q_i > p_i*q_w`` for EVERY competitor (no division — the whole
certificate is integer arithmetic).  It RAISES ``ValueError`` (the anti-phantom
negative control) if any competitor ties or beats the winner, or if any
denominator is ``<= 0``.

Optionally it also certifies the value-load / nonvacuity fact ``v_w < 1`` (via the
integer inequality ``p_w < q_w``) — mirroring the ``bgext_n*_value_le1`` companions.

EMITTED LEAN (per instance), one INTEGER strict inequality per competitor:

    theorem <name>_beats_<i> : (<p_i> * <q_w> : ℤ) < <p_w> * <q_i> := by norm_num

and (if the winner<1 check is on)

    theorem <name>_lt_one : (<p_w> : ℤ) < <q_w> := by norm_num

Everything is a strict inequality between concrete integers, ascribed ``: ℤ`` and
closed by pure ``norm_num`` — the lowest-risk tactic there is.  (No ℝ literal is
ever emitted, so the ℝ-ascription hazard does not arise here.)

HONEST SCOPE: this proves ONLY the finite pairwise extremality with margin — the
winner is the strict argmax over the *given finite list*.  It does not prove any
maximality over an infinite / unenumerated competitor set, nor does it close any
downstream BG obligation.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_finite_argmax.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


def _as_ratio(v) -> tuple[sp.Integer, sp.Integer]:
    """Normalize a value to an exact integer numerator/denominator pair (q > 0)."""
    r = sp.nsimplify(v)
    r = sp.Rational(r)  # exact rational; raises if not rational-convertible
    p, q = sp.Integer(r.p), sp.Integer(r.q)  # sympy keeps q > 0 canonically
    return p, q


@dataclass(frozen=True)
class FiniteArgmaxCertificate:
    """A verified finite-argmax strict-margin certificate.

    The winner ``p_w/q_w`` (``q_w > 0``) strictly beats every competitor
    ``p_i/q_i`` (``q_i > 0``); the certified facts are the cross-multiplied
    INTEGER strict inequalities ``p_i*q_w < p_w*q_i`` (re-provable in Lean by
    ``norm_num``).  If ``check_lt_one`` is set, the value-load fact ``p_w < q_w``
    (i.e. ``v_w < 1``) is additionally certified.
    """

    p_w: sp.Integer                                   # winner numerator
    q_w: sp.Integer                                   # winner denominator, > 0
    competitors: tuple[tuple[sp.Integer, sp.Integer], ...]  # (p_i, q_i), each q_i > 0
    check_lt_one: bool                                # also certify v_w < 1


def finite_argmax_certificate(
    winner, competitors, *, check_lt_one: bool = False
) -> FiniteArgmaxCertificate:
    """Build and EXACTLY self-check a finite-argmax strict-margin certificate.

    ``winner`` and each entry of ``competitors`` is a rational (int, Fraction,
    sympy Rational, or ``(p, q)`` pair).  Refuses (``ValueError``) when a
    denominator is ``<= 0``, when the competitor list is empty, when any
    competitor ties or beats the winner (the cross-multiplied margin fails), or
    (when ``check_lt_one``) when ``v_w >= 1``.
    """
    def _pair(x):
        if isinstance(x, (tuple, list)):
            p, q = sp.Integer(x[0]), sp.Integer(x[1])
            if q == 0:
                raise ValueError(f"REFUSED: zero denominator in {x!r}")
            # canonicalize sign so q > 0
            if q < 0:
                p, q = -p, -q
            return p, q
        return _as_ratio(x)

    p_w, q_w = _pair(winner)
    if q_w <= 0:
        raise ValueError(f"REFUSED: winner denominator q_w = {q_w} <= 0")

    comps = [_pair(c) for c in competitors]
    if not comps:
        raise ValueError("REFUSED: competitor list is empty; nothing to beat")

    for i, (p_i, q_i) in enumerate(comps):
        if q_i <= 0:
            raise ValueError(f"REFUSED: competitor {i} denominator q_i = {q_i} <= 0")
        # EXACT cross-multiplied strict-margin self-check (q_w, q_i > 0):
        #   v_i < v_w  <==>  p_i * q_w < p_w * q_i.
        lhs = sp.Integer(p_i * q_w)
        rhs = sp.Integer(p_w * q_i)
        if not (lhs < rhs):
            raise ValueError(
                f"REFUSED: competitor {i} value {p_i}/{q_i} is NOT strictly below "
                f"winner {p_w}/{q_w} (cross-mult: {lhs} </ {rhs}); no strict margin"
            )

    if check_lt_one:
        # value-load / nonvacuity: v_w < 1  <==>  p_w < q_w  (q_w > 0).
        if not (p_w < q_w):
            raise ValueError(
                f"REFUSED: winner value {p_w}/{q_w} is NOT < 1 (p_w={p_w} </ q_w={q_w}); "
                f"value-load check failed"
            )

    return FiniteArgmaxCertificate(
        p_w=p_w,
        q_w=q_w,
        competitors=tuple(comps),
        check_lt_one=bool(check_lt_one),
    )


def certify_finite_argmax_point(family, pt, name):
    """Certify one finite-argmax instance from ``family.special[1](pt) -> spec``.

    ``spec`` is either ``(winner, competitors)`` or
    ``{"winner": ..., "competitors": [...], "lt_one": bool}``.  Returns
    ``(CertifiedInstance, n_checks)`` where ``n_checks`` counts the emitted
    integer inequalities (one per competitor, plus one for the ``v_w < 1``
    value-load fact when enabled)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = finite_argmax_certificate(
            spec["winner"],
            spec["competitors"],
            check_lt_one=bool(spec.get("lt_one", False)),
        )
    else:
        winner, competitors = spec[0], spec[1]
        check_lt_one = bool(spec[2]) if len(spec) > 2 else False
        cert = finite_argmax_certificate(
            winner, competitors, check_lt_one=check_lt_one
        )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    n_checks = len(cert.competitors) + (1 if cert.check_lt_one else 0)
    return inst, n_checks


@dataclass
class FiniteArgmaxMarginEmitter(Emitter):
    """Emit finite extremality with a strict cross-multiplied margin: a winner
    ``p_w/q_w`` strictly beats each competitor ``p_i/q_i``, one INTEGER strict
    inequality ``(p_i*q_w : ℤ) < p_w*q_i`` per competitor closed by ``norm_num``,
    plus an optional ``(p_w : ℤ) < q_w`` value-load fact (``v_w < 1``).

    Models the PROVEN ``bgext_n*_beats_runnerup`` / ``bgext_n*_value_le1`` pattern
    from examples/bg_extremality — pure ``norm_num`` over ℤ, the lowest-risk
    tactic."""

    def __post_init__(self):
        self.kind = "finite_argmax"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: FiniteArgmaxCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            p_w, q_w = int(cert.p_w), int(cert.q_w)
            lines.append(
                f"-- Finite argmax with strict margin: winner {p_w}/{q_w} strictly "
                f"beats {len(cert.competitors)} competitor(s).\n"
                f"-- Each fact is the cross-multiplied integer inequality "
                f"p_i*q_w < p_w*q_i (no division).\n"
            )
            if cert.check_lt_one:
                # value-load / nonvacuity: v_w < 1  <==>  p_w < q_w.
                lines.append(
                    f"theorem {base}_lt_one : ({p_w} : ℤ) < {q_w} := by norm_num\n"
                )
                nthm += 1
            for i, (p_i, q_i) in enumerate(cert.competitors):
                p_i, q_i = int(p_i), int(q_i)
                lines.append(
                    f"theorem {base}_beats_{i} : "
                    f"({p_i} * {q_w} : ℤ) < {p_w} * {q_i} := by norm_num\n"
                )
                nthm += 1
        return "".join(lines), nthm


def finite_argmax_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a finite-argmax strict-margin family (kind='finite_argmax').

    ``spec``: a callable ``pt -> (winner, competitors)`` or
    ``pt -> {"winner": ..., "competitors": [...], "lt_one": bool}``, where
    ``winner`` and each competitor is a rational (``p/q`` with ``q > 0``, given as
    an int/Fraction/sympy Rational or a ``(p, q)`` pair).  Refuses (at
    certification) a non-positive denominator, an empty list, any competitor that
    ties or beats the winner, or (when ``lt_one``) a winner value ``>= 1``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("finite_argmax", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid cert, negative control, print emitted Lean ----------
    print("=== positive: near-star N(0,5) winner Phi^11 = 1/1 beats runner-up ===")
    # The n=11 BG tie: winner value 1 (=1/1), runner-up
    #   25804264053054077850709/46523913960640966796875 < 1.  (from BGExtremality)
    cert = finite_argmax_certificate(
        (1, 1),
        [(25804264053054077850709, 46523913960640966796875)],
        check_lt_one=False,  # winner is exactly 1 here, so v_w < 1 does NOT hold
    )
    print(f"  cert OK: winner={cert.p_w}/{cert.q_w}, "
          f"{len(cert.competitors)} competitor(s), lt_one={cert.check_lt_one}")

    print("\n=== positive: near-star N(0,2) winner < 1, beats runner-up (n=5) ===")
    cert2 = finite_argmax_certificate(
        (73039787676416, 92354487127101),
        [(3123330500020692224, 16360320331104560847)],
        check_lt_one=True,  # winner 73039787676416/92354487127101 < 1
    )
    print(f"  cert OK: winner={cert2.p_w}/{cert2.q_w}, lt_one={cert2.check_lt_one}")

    print("\n=== positive: small multi-competitor argmax  3/4 beats 1/2, 2/3, 5/7 ===")
    cert3 = finite_argmax_certificate(
        sp.Rational(3, 4),
        [sp.Rational(1, 2), sp.Rational(2, 3), sp.Rational(5, 7)],
        check_lt_one=True,
    )
    print(f"  cert OK: winner={cert3.p_w}/{cert3.q_w}, "
          f"{len(cert3.competitors)} competitors, lt_one={cert3.check_lt_one}")

    print("\n=== NEGATIVE CONTROL: a competitor TIES the winner (expect ValueError) ===")
    try:
        finite_argmax_certificate(sp.Rational(3, 4), [sp.Rational(3, 4)])
        raise SystemExit("FAIL: tie was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: a competitor BEATS the winner (expect ValueError) ===")
    try:
        finite_argmax_certificate(sp.Rational(1, 2), [sp.Rational(2, 3)])
        raise SystemExit("FAIL: stronger competitor was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: non-positive denominator (expect ValueError) ===")
    try:
        finite_argmax_certificate((1, 0), [sp.Rational(1, 2)])
        raise SystemExit("FAIL: zero denominator was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: lt_one fails when winner >= 1 (expect ValueError) ===")
    try:
        finite_argmax_certificate(sp.Rational(5, 4), [sp.Rational(1, 2)], check_lt_one=True)
        raise SystemExit("FAIL: winner >= 1 was NOT refused under lt_one")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (three instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="fa_nearstar_n11",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="fa_nearstar_n5",
                          corners=(), payload=cert2),
        CertifiedInstance(point={"case": 2}, lean_name="fa_small_multi",
                          corners=(), payload=cert3),
    ]

    class _View:
        instances = insts

    body, nthm = FiniteArgmaxMarginEmitter().emit_body(
        _View(), LeanProfile(namespace=("FiniteArgmax",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

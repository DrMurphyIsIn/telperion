"""Concave-stationary-max emitter — a stationary point of a strictly concave
objective is its unique maximizer.

Motivating instance (Arda trading, ``src/arda/risk/risk_bounds.py:64``): the
Kelly-fraction objective

    g(f) = wr·ln(1 + f·b) + (1 − wr)·ln(1 − f)          on  f ∈ (0, 1),

with ``b > 0`` (reward:risk) and ``0 < wr < 1`` (win rate).  (A win multiplies
capital by ``1 + f·b``, a loss by ``1 − f``; both log terms enter with a PLUS
sign — the standard Kelly log-growth objective.)  Its unique
maximizer is the Kelly fraction

    f* = (wr·b − (1 − wr)) / b .

Optimality rests on two exact, kernel-checkable facts:

1. FIRST-ORDER CONDITION (rational identity).  The derivative is the rational
   function

       g'(f) = wr·b/(1 + f·b) − (1 − wr)/(1 − f),

   and at ``f = f*`` it clears (both denominators nonzero on the domain) to
   ``g'(f*) = 0`` — a ``field_simp; ring`` / ``norm_num`` identity.

2. STRICT CONCAVITY (SOS-over-denominators positivity).  The second derivative
   is everywhere negative,

       g''(f) = −wr·b²/(1 + f·b)² − (1 − wr)/(1 − f)²  < 0,

   i.e. ``−g''(f) = wr·b²/(1 + f·b)² + (1 − wr)/(1 − f)² > 0`` for every
   ``f ∈ (0, 1)`` — a manifest sum of ``positive · (rational)²`` terms,
   closeable by ``positivity`` once the denominators are known positive.

A stationary point of a strictly concave function on a convex domain is its
UNIQUE maximizer (``g(f) < g(f*)`` for ``f ≠ f*``); that conclusion follows
classically from (1) + (2).  This emitter ships the two LOAD-BEARING certified
facts as separate green theorems (the FALLBACK form): the ``ln``-derivative /
``StrictConcaveOn`` glue that would state the unique-max conclusion directly is
transcendental and heavy, so we certify the exact rational facts that carry the
argument and note the classical conclusion in the docstring.

CERTIFICATE.  ``(wr, b)`` rationals + ``f*``, with the exact sympy verification
that (1) ``g'(f*) = 0`` and (2) ``−g''`` is a positive sum of
squares-over-denominators on the domain (each denominator positive on
``(0, 1)``, each numerator a nonnegative-weighted square).  ``…_certificate``
RAISES (the anti-phantom negative control) if ``f*`` is not the stationary
point, or if the objective is not strictly concave (a convex / non-stationary
instance).

EMITTED LEAN (per instance), with ``wr``, ``b``, ``f*`` concrete rationals:

    -- FOC: g'(f*) = 0.
    theorem <name>_foc :
        (wr * b / (1 + fstar * b) - (1 - wr) / (1 - fstar) : ℝ) = 0 := by norm_num

    -- strict concavity: −g''(f) > 0 for all f in (0, 1).
    theorem <name>_concave :
        ∀ f ∈ Set.Ioo (0:ℝ) 1,
          (0:ℝ) < wr * b ^ 2 / (1 + f * b) ^ 2 + (1 - wr) / (1 - f) ^ 2 := by
      intro f hf
      obtain ⟨hf0, hf1⟩ := hf
      have hden1 : (0:ℝ) < 1 + f * b := by nlinarith
      have hden2 : (0:ℝ) < 1 - f := by linarith
      positivity

HONEST SCOPE: this proves the two load-bearing facts (FOC + strict concavity),
NOT the unique-max conclusion as a single Lean theorem; that follows classically.
conjecture1_proved=False.
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
except ImportError:  # run directly: `python src/telperion/emit_concave_stationary_max.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# ---------------------------------------------------------------------------
# Certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ConcaveStationaryMaxCertificate:
    """A verified concave-stationary-max certificate for the Kelly objective.

    Carries the concrete rationals ``wr`` (``0 < wr < 1``), ``b`` (``b > 0``)
    and the stationary point ``fstar`` (``0 < fstar < 1``).  The certified
    facts are the FOC ``g'(fstar) = 0`` (rational identity) and the strict
    concavity ``−g''(f) > 0`` on ``(0, 1)`` (positive SOS-over-denominators).
    """

    wr: sp.Rational
    b: sp.Rational
    fstar: sp.Rational


def concave_stationary_max_certificate(wr, b, fstar=None) -> ConcaveStationaryMaxCertificate:
    """Build and EXACTLY self-check a concave-stationary-max certificate for the
    Kelly objective ``g(f) = wr·ln(1+f·b) − (1−wr)·ln(1−f)`` on ``(0, 1)``.

    ``wr``, ``b`` are rationals with ``0 < wr < 1``, ``b > 0``.  ``fstar`` is the
    claimed stationary point; if ``None`` it is computed as the Kelly fraction
    ``(wr·b − (1−wr))/b``.  Refuses (``ValueError`` — the negative control) when:
    the parameter ranges are violated; ``fstar`` is not in ``(0, 1)``; ``fstar``
    is NOT the stationary point (``g'(fstar) ≠ 0``); or the objective is not
    strictly concave on the domain (``−g''`` not a positive SOS-over-denominators).
    """
    wr = sp.nsimplify(wr)
    b = sp.nsimplify(b)
    if not (wr.is_rational and b.is_rational):
        raise ValueError(f"REFUSED: wr={wr}, b={b} must be rational")
    if not (0 < wr < 1):
        raise ValueError(f"REFUSED: win rate wr={wr} must satisfy 0 < wr < 1")
    if not (b > 0):
        raise ValueError(f"REFUSED: reward:risk b={b} must satisfy b > 0")

    kelly = sp.Rational(wr * b - (1 - wr), b)
    if fstar is None:
        fstar = kelly
    else:
        fstar = sp.nsimplify(fstar)
    if not fstar.is_rational:
        raise ValueError(f"REFUSED: fstar={fstar} must be rational")
    if not (0 < fstar < 1):
        raise ValueError(
            f"REFUSED: stationary point fstar={fstar} must lie in the open "
            f"domain (0, 1)")

    f = sp.Symbol("f", real=True)
    # Standard Kelly log-growth objective: a win multiplies capital by (1+f·b),
    # a loss by (1−f), so both log terms enter with a PLUS sign.  Its derivative
    # is g'(f) = wr·b/(1+f·b) − (1−wr)/(1−f) (the minus arises from the chain
    # rule d/df ln(1−f) = −1/(1−f)), matching risk_bounds.py:64's f*.
    g = wr * sp.log(1 + f * b) + (1 - wr) * sp.log(1 - f)

    # (1) FIRST-ORDER CONDITION.  g'(f) = wr·b/(1+f·b) − (1−wr)/(1−f).
    gprime = sp.diff(g, f)
    gprime_rational = wr * b / (1 + f * b) - (1 - wr) / (1 - f)
    # sympy self-check: our stated rational derivative matches sympy's diff.
    if sp.simplify(gprime - gprime_rational) != 0:
        raise ValueError(
            "REFUSED: stated g' does not match sympy diff of g (internal error)")
    foc = sp.nsimplify(gprime_rational.subs(f, fstar))
    if sp.simplify(foc) != 0:
        raise ValueError(
            f"REFUSED: fstar={fstar} is NOT the stationary point — "
            f"g'(fstar) = {foc} ≠ 0 (not a first-order-condition root)")

    # (2) STRICT CONCAVITY.  −g''(f) = wr·b²/(1+f·b)² + (1−wr)/(1−f)² > 0.
    neg_gpp = -sp.diff(g, f, 2)
    neg_gpp_rational = wr * b ** 2 / (1 + f * b) ** 2 + (1 - wr) / (1 - f) ** 2
    if sp.simplify(neg_gpp - neg_gpp_rational) != 0:
        raise ValueError(
            "REFUSED: stated −g'' does not match sympy diff (internal error)")
    # Strict-concavity structure check: each term is (positive coeff)·(1/den)²
    # with den > 0 on the open domain (0, 1) and b > 0.  The two coefficients
    # wr·b² and (1−wr) are strictly positive; the objective is strictly concave
    # iff BOTH are > 0 (a convex or affine instance would fail here).
    coeff1 = sp.nsimplify(wr * b ** 2)
    coeff2 = sp.nsimplify(1 - wr)
    if not (coeff1 > 0 and coeff2 > 0):
        raise ValueError(
            f"REFUSED: −g'' is not a positive SOS-over-denominators "
            f"(coeffs {coeff1}, {coeff2}); objective not strictly concave")
    # Spot-check strict concavity numerically at the domain midpoint 1/2 (exact).
    if sp.nsimplify(neg_gpp_rational.subs(f, sp.Rational(1, 2))) <= 0:
        raise ValueError(
            "REFUSED: −g'' non-positive at the domain midpoint — not concave")

    return ConcaveStationaryMaxCertificate(
        wr=sp.Rational(wr), b=sp.Rational(b), fstar=sp.Rational(fstar)
    )


def certify_concave_stationary_max_point(family, pt, name):
    """Certify one concave-stationary-max instance from
    ``family.special[1](pt) -> spec``.

    ``spec`` is either ``(wr, b)`` / ``(wr, b, fstar)`` or
    ``{"wr": ..., "b": ..., "fstar": ...}`` (``fstar`` optional — defaults to the
    Kelly fraction).  Returns ``(CertifiedInstance, n_checks)`` where ``n_checks``
    is the number of load-bearing facts emitted (2: FOC + strict concavity)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = concave_stationary_max_certificate(
            spec["wr"], spec["b"], spec.get("fstar")
        )
    else:
        wr, b = spec[0], spec[1]
        fstar = spec[2] if len(spec) > 2 else None
        cert = concave_stationary_max_certificate(wr, b, fstar)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

def _rat(q) -> str:
    """A rational constant as ℝ-ascribed Lean source: `(11 / 20 : ℝ)` etc.

    Bare integers are ascribed too so the whole expression is unambiguously ℝ.
    """
    q = sp.Rational(q)
    if q.q == 1:
        return str(q.p) if q.p >= 0 else f"(-{-q.p})"
    if q.p >= 0:
        return f"({q.p} / {q.q})"
    return f"(-({-q.p} / {q.q}))"


@dataclass
class ConcaveStationaryMaxEmitter(Emitter):
    """Emit the two load-bearing facts of Kelly-fraction optimality — the FOC
    ``g'(fstar) = 0`` (by ``norm_num`` on concrete rationals) and strict
    concavity ``−g''(f) > 0`` on ``(0, 1)`` (denominators positive by
    ``nlinarith``/``linarith``, then ``positivity``).  The unique-max conclusion
    ``g(f) < g(fstar)`` for ``f ≠ fstar`` follows classically from these."""

    def __post_init__(self):
        self.kind = "concave_stationary_max"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: ConcaveStationaryMaxCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            wr = _rat(cert.wr)
            b = _rat(cert.b)
            fs = _rat(cert.fstar)

            lines.append(
                f"-- Concave-stationary-max (Kelly optimality): "
                f"g(f) = wr·ln(1+f·b) + (1−wr)·ln(1−f) on (0,1), "
                f"wr={cert.wr}, b={cert.b}, f*={cert.fstar}.\n"
                f"-- Two load-bearing facts; the unique-max conclusion "
                f"g(f) < g(f*) (f ≠ f*) follows classically.\n"
                f"-- FOC: g'(f*) = wr·b/(1+f*·b) − (1−wr)/(1−f*) = 0.\n"
                f"theorem {base}_foc : "
                f"({wr} * {b} / (1 + {fs} * {b}) - "
                f"(1 - {wr}) / (1 - {fs}) : ℝ) = 0 := by norm_num\n"
            )
            nthm += 1
            lines.append(
                f"-- strict concavity: −g''(f) = wr·b²/(1+f·b)² + (1−wr)/(1−f)² > 0 "
                f"on (0,1).\n"
                f"theorem {base}_concave : ∀ f ∈ Set.Ioo (0:ℝ) 1, "
                f"(0:ℝ) < {wr} * {b} ^ 2 / (1 + f * {b}) ^ 2 + "
                f"(1 - {wr}) / (1 - f) ^ 2 := by\n"
                f"  intro f hf\n"
                f"  obtain ⟨hf0, hf1⟩ := hf\n"
                f"  have hb : (0:ℝ) < {b} := by norm_num\n"
                f"  have hden1 : (0:ℝ) < 1 + f * {b} := by nlinarith\n"
                f"  have hden2 : (0:ℝ) < 1 - f := by linarith\n"
                f"  positivity\n"
            )
            nthm += 1
        return "".join(lines), nthm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def concave_stationary_max_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a concave-stationary-max family (kind='concave_stationary_max').

    ``spec``: a callable ``pt -> (wr, b)`` / ``pt -> (wr, b, fstar)`` or
    ``pt -> {"wr": ..., "b": ..., "fstar": ...}`` for the Kelly objective
    ``g(f) = wr·ln(1+f·b) − (1−wr)·ln(1−f)`` on ``(0, 1)``, with ``0 < wr < 1``,
    ``b > 0``.  ``fstar`` optional (defaults to the Kelly fraction
    ``(wr·b−(1−wr))/b``).  Refuses (at certification) a non-stationary ``fstar``
    or a non-strictly-concave instance."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("concave_stationary_max", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid Kelly cert, negative controls, print emitted Lean ----
    print("=== positive: Kelly wr=0.55, b=2 => f* = (0.55·2 − 0.45)/2 = 0.325 ===")
    cert = concave_stationary_max_certificate(sp.Rational(55, 100), 2)
    print(f"  cert OK: wr={cert.wr}, b={cert.b}, f*={cert.fstar}")
    assert cert.fstar == sp.Rational(325, 1000), cert.fstar

    print("\n=== positive: Kelly wr=0.6, b=3/2 => f* = (0.6·1.5 − 0.4)/1.5 ===")
    cert2 = concave_stationary_max_certificate(sp.Rational(6, 10), sp.Rational(3, 2))
    print(f"  cert OK: wr={cert2.wr}, b={cert2.b}, f*={cert2.fstar}")

    print("\n=== NEGATIVE CONTROL: non-stationary fstar (expect ValueError) ===")
    try:
        # supply a wrong stationary point (0.5 ≠ Kelly 0.325)
        concave_stationary_max_certificate(sp.Rational(55, 100), 2, sp.Rational(1, 2))
        raise SystemExit("FAIL: non-stationary fstar was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: wr out of (0,1) (expect ValueError) ===")
    try:
        concave_stationary_max_certificate(sp.Rational(3, 2), 2)
        raise SystemExit("FAIL: wr >= 1 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: b <= 0 -> non-concave (expect ValueError) ===")
    try:
        concave_stationary_max_certificate(sp.Rational(55, 100), -1)
        raise SystemExit("FAIL: b <= 0 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: fstar outside (0,1) (expect ValueError) ===")
    try:
        # wr very small makes Kelly negative -> outside domain
        concave_stationary_max_certificate(sp.Rational(1, 100), 2)
        raise SystemExit("FAIL: fstar outside (0,1) was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (two instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="csm_kelly_wr55_b2",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="csm_kelly_wr60_b15",
                          corners=(), payload=cert2),
    ]

    class _View:
        instances = insts

    body, nthm = ConcaveStationaryMaxEmitter().emit_body(
        _View(), LeanProfile(namespace=("ConcaveStationaryMax",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

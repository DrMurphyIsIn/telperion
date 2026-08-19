"""Interlacing / real-rootedness emitter — Newton log-concavity of coefficients.

The SOUNDLY-EMITTABLE core of the real-stability vocabulary
(`bg/interlacing.py`).  A univariate polynomial that is REAL-ROOTED has a
log-concave (in fact ultra-log-concave, by Newton's inequalities) coefficient
sequence.  For a concrete polynomial

    p(x) = Σ_{k=0}^{n} a_k x^k          (a_k exact rationals),

with a real-rootedness witness (all roots real, via `is_real_rooted` from the
source), the coefficient inequalities

    plain log-concavity:   a_k^2 - a_{k-1}·a_{k+1} ≥ 0,
    Newton (ultra-lc):     a_k^2 - a_{k-1}·a_{k+1}·((k+1)/k)·((n-k+1)/(n-k)) ≥ 0,

are EXACT NUMERIC RATIONAL facts once the coefficients are pinned.  That makes
each one robustly kernel-checkable:

    theorem <name>_k : (0:ℝ) ≤ a_k^2 - a_{k-1}*a_{k+1}*w := by norm_num

`norm_num` closes an inequality between two rational literals.  This is distinct
from the general theorem "real-rooted ⇒ log-concave": THAT structural
implication is NOT emitted here (it is the un-formalized mathematical content).
What is emitted is the family of checkable numeric consequences, together with
the real-rootedness witness that (mathematically) explains why they hold.  This
is the honest scope — see the module/emitter docstrings.

NEGATIVE CONTROL: `certify_interlacing_point` verifies real-rootedness of the
polynomial (via the source `is_real_rooted`) AND recomputes each coefficient
inequality exactly; either a non-real-rooted polynomial or a failing inequality
raises ValueError (a refusal).  No Lean is emitted for a refused instance.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile


def is_real_rooted(poly: sp.Expr, x: sp.Symbol) -> bool:
    """A univariate polynomial is real-rooted iff its real roots (with
    multiplicity) exhaust its degree.  Engine-local — the core must not import
    the `telperion.bg` research lab (enforced by tests/test_core_boundary.py);
    this is the same one-liner as `bg.interlacing.is_real_rooted`."""
    P = sp.Poly(poly, x)
    return len(sp.real_roots(poly, x)) == P.degree()
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Payload
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NewtonInequality:
    """One exact coefficient inequality  0 ≤ a_k^2 - a_{k-1}·a_{k+1}·w.

    ``weight`` w is 1 for plain log-concavity, or the Newton factor
    ((k+1)/k)·((n-k+1)/(n-k)) for the ultra-log-concave (Newton) form.  All of
    ``a_{k-1}, a_k, a_{k+1}, weight, slack`` are exact rationals; ``slack`` =
    a_k^2 - a_{k-1}·a_{k+1}·w ≥ 0 is the certified nonnegative quantity."""

    k: int
    a_lo: sp.Rational      # a_{k-1}
    a_mid: sp.Rational     # a_k
    a_hi: sp.Rational      # a_{k+1}
    weight: sp.Rational    # w (1 = plain log-concave; Newton factor otherwise)
    slack: sp.Rational     # a_k^2 - a_{k-1}*a_{k+1}*w  (>= 0)


@dataclass(frozen=True)
class InterlacingPayload:
    """Certificate payload for one real-rooted polynomial: the coefficient
    sequence, the real-rootedness witness flag, and the certified Newton /
    log-concavity inequalities."""

    coeffs: tuple[sp.Rational, ...]     # (a_0, ..., a_n)
    x_name: str
    real_rooted: bool
    newton: bool                        # True = Newton weights; False = plain
    inequalities: tuple[NewtonInequality, ...]


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def _newton_weight(k: int, n: int) -> sp.Rational:
    """Newton ultra-log-concavity weight ((k+1)/k)·((n-k+1)/(n-k)).

    Defined for interior indices 1 <= k <= n-1 with k != 0 and n-k != 0."""
    return (sp.Rational(k + 1, k)
            * sp.Rational(n - k + 1, n - k))


def certify_interlacing_point(family, pt, name):
    """Certify one real-rootedness / log-concavity instance.

    spec(pt) = (coeffs, x_symbol) where ``coeffs`` is the coefficient tuple
    (a_0, ..., a_n) (exact rationals / sympy numbers) and ``x_symbol`` the
    polynomial variable.  Steps:

      1. Reconstruct p(x) = Σ a_k x^k and verify it is REAL-ROOTED via the
         source `is_real_rooted` (the interlacing/real-stability witness).
      2. Compute the exact coefficient inequalities
         a_k^2 - a_{k-1}·a_{k+1}·w ≥ 0 for every interior k, with w the Newton
         weight (``constants['newton']`` truthy, default) or 1 (plain).
      3. Assert every slack is ≥ 0 (exact rational); store on inst.payload.

    Raises ValueError (a refusal — the negative control) when the polynomial is
    not real-rooted, or any coefficient inequality fails.  Returns
    (CertifiedInstance, n_checks)."""
    coeffs_raw, x = family.special[1](pt)
    x = sp.sympify(x)
    coeffs = tuple(sp.nsimplify(sp.sympify(c)) for c in coeffs_raw)
    coeffs = tuple(sp.Rational(c) for c in coeffs)
    n = len(coeffs) - 1
    if n < 2:
        raise ValueError(
            f"interlacing instance '{name}' REFUSED: need degree >= 2 "
            f"(got {n + 1} coefficient(s)); no interior log-concavity index"
        )

    # (1) real-rootedness witness
    p = sum(c * x ** k for k, c in enumerate(coeffs))
    p = sp.expand(p)
    if sp.Poly(p, x).degree() != n:
        raise ValueError(
            f"interlacing instance '{name}' REFUSED: leading coefficient a_{n} "
            f"is zero — declared degree {n} not attained"
        )
    if not is_real_rooted(p, x):
        raise ValueError(
            f"interlacing instance '{name}' REFUSED: p is NOT real-rooted "
            f"(coeffs={coeffs}); the real-stability witness fails"
        )

    # (2)/(3) exact coefficient inequalities
    newton = bool(family.constants.get("newton", True))
    checks = 1  # the real-rootedness check
    ineqs: list[NewtonInequality] = []
    for k in range(1, n):
        a_lo, a_mid, a_hi = coeffs[k - 1], coeffs[k], coeffs[k + 1]
        w = _newton_weight(k, n) if newton else sp.Integer(1)
        slack = sp.Rational(a_mid ** 2 - a_lo * a_hi * w)
        if slack < 0:
            raise ValueError(
                f"interlacing instance '{name}' REFUSED: "
                f"{'Newton' if newton else 'log-concavity'} inequality at k={k} "
                f"fails: a_k^2 - a_(k-1)*a_(k+1)*w = {slack} < 0 "
                f"(a_(k-1)={a_lo}, a_k={a_mid}, a_(k+1)={a_hi}, w={w})"
            )
        ineqs.append(NewtonInequality(k=k, a_lo=a_lo, a_mid=a_mid, a_hi=a_hi,
                                      weight=w, slack=slack))
        checks += 1

    payload = InterlacingPayload(
        coeffs=coeffs,
        x_name=str(x),
        real_rooted=True,
        newton=newton,
        inequalities=tuple(ineqs),
    )
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=payload,
    )
    return inst, checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class InterlacingEmitter(Emitter):
    """Emit the exact coefficient log-concavity / Newton inequalities of a
    real-rooted polynomial as `norm_num`-closable numeric facts.

    Per certified instance, one theorem PER interior coefficient index k:

        theorem <name>_k : (0:ℝ) ≤ a_k^2 - a_{k-1} * a_{k+1} * w := by norm_num

    where a_{k-1}, a_k, a_{k+1}, w are exact rational literals.  `norm_num`
    discharges an inequality between rational literals robustly — no prelude
    lemmas, no `sorry`.

    HONEST SCOPE: these are the checkable numeric CONSEQUENCES of
    real-rootedness (Newton's inequalities), NOT the general theorem
    "real-rooted ⇒ log-concave".  That structural implication — the reason the
    inequalities hold for the whole family rather than instance-by-instance —
    is the un-emitted mathematical content, flagged in the emitted comment.  The
    real-rootedness witness is verified in `certify_interlacing_point` (exact
    root count) but is NOT itself re-proved in Lean here."""

    def __post_init__(self):
        self.kind = "interlacing"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        ntheorems = 0
        for inst in fam.instances:
            payload: InterlacingPayload = inst.payload  # type: ignore[assignment]
            n = len(payload.coeffs) - 1
            kind_word = "Newton (ultra-log-concave)" if payload.newton else "log-concave"
            lines.append(
                f"-- {inst.lean_name}: coefficient sequence of a REAL-ROOTED "
                f"degree-{n} polynomial is {kind_word}.\n"
                f"-- Emitted: the exact numeric coefficient inequalities "
                f"(Newton's inequalities), closed by `norm_num`.\n"
                f"-- NOT emitted (honest scope): the general implication "
                f"`real-rooted => log-concave`; the real-rootedness witness is "
                f"verified symbolically at certification, not re-proved in Lean.\n"
            )
            for ineq in payload.inequalities:
                a_lo = rat_lean(ineq.a_lo)
                a_mid = rat_lean(ineq.a_mid)
                a_hi = rat_lean(ineq.a_hi)
                w = rat_lean(ineq.weight)
                thm = f"{inst.lean_name}_{ineq.k}"
                lines.append(
                    f"theorem {thm} : "
                    f"(0:ℝ) ≤ {a_mid}^2 - {a_lo} * {a_hi} * {w} := by norm_num\n"
                )
                ntheorems += 1
        return "".join(lines), ntheorems


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def interlacing_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a real-rootedness / log-concavity family (kind='interlacing').

    Parameters
    ----------
    name, grid, lean_name
        As for every family: name, the finite parameter grid, and a
        ``pt -> str`` Lean theorem base-name map.
    symbols
        The family's declared symbols (unused by the numeric emission — the
        coefficients are pinned rationals — but recorded for provenance).
    spec
        A callable ``pt -> (coeffs, x_symbol)`` where ``coeffs`` is the
        coefficient tuple ``(a_0, ..., a_n)`` (exact rationals / sympy numbers)
        of a REAL-ROOTED polynomial and ``x_symbol`` the polynomial variable.
        ``certify_interlacing_point`` verifies real-rootedness and computes the
        exact Newton / log-concavity coefficient inequalities, refusing
        (ValueError) a non-real-rooted polynomial or a failing inequality.
    constants
        Optional; ``{'newton': False}`` selects the plain log-concavity weight
        (w = 1) instead of the Newton ultra-log-concave weight (the default).
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("interlacing", spec),
        constants=dict(constants or {}),
    )

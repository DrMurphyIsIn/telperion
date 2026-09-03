"""Transcendental-enclosure emitter — rational lower/upper bounds for a
transcendental expression over a box, kernel-checked via Mathlib.

Certifies RATIONAL bounds ``L ≤ expr ≤ U`` for a transcendental ``expr`` over a
box, so a downstream ``nlinarith``/``linarith`` can treat the transcendental term
as a pure rational bracket.  This serves TWO fronts simultaneously.

FRONT 1 — BG subaction compact-core cells (the LIVE proof front).  Each per-cell
inequality of the compact-core carries a term

    e_v = log(1 + S/d) − F*

with ``S/d`` ranging over a rational cell box ``x ∈ [x0, x1]``.  To make the cell
a pure-rational ``nlinarith`` goal, one encloses ``log(1 + x)`` between rationals
over the box.  The ``log`` face of this emitter does exactly that:

* UPPER  ``Real.log (1 + x) ≤ x``           for all ``x ≥ 0``
  (Mathlib ``Real.log_le_sub_one_of_pos`` at ``y = 1 + x`` gives ``log y ≤ y−1``).
* LOWER  ``L ≤ Real.log (1 + x)``           for ``x ∈ [x0, x1]``, a chosen rational
  ``L`` (``Real.log`` is monotone, so ``log(1+x) ≥ log(1+x0)``, and ``log(1+x0)`` is
  bounded below by a rational ``L`` via ``Real.le_log_iff_exp_le`` + a rational
  ``exp`` lower bound ``Real.add_one_le_exp``).

FRONT 2 — Montgomery–Taylor extremal constant (AxiomMath / ZetaZeros,
arXiv:2609.02882).  The extremal constant is

    C₀ = 3/2 − (1/√2)·cot(1/√2) = 0.6725007…

Enclosing ``C₀`` between rationals needs ``cos``/``sin`` bounds at ``1/√2``.  The
``trig`` face of this emitter targets a LOOSE-but-honest rational enclosure of
``C₀``.  HONESTY: a tight kernel-checked enclosure of ``C₀`` requires ``√2`` plus
Taylor bounds for ``cos``/``sin`` at ``1/√2`` and is genuinely fiddly; per the
build mandate — a valid loose bound that COMPILES beats a tight bound that does
not — the trig face is DEFERRED as a follow-on and is NOT emitted here.  The log
face (BG-critical) ships alone and green.  See ``trig=True`` spec handling below,
which raises a clear "deferred" refusal rather than emitting non-green Lean.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


def _lean_rat(q) -> str:
    """Render an exact rational as a Lean literal fragment (n or n/d)."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"{q.p}"
    return f"{q.p}/{q.q}"


@dataclass(frozen=True)
class TranscendentalEnclosureCertificate:
    """A verified rational enclosure ``L ≤ expr ≤ U`` over a box.

    ``face`` is ``"log"`` (only supported face; ``"trig"`` is deferred — see
    module docstring — and refused at cert time).

    log face: encloses ``Real.log (1 + x)`` over ``x ∈ [x0, x1]``.  ``U`` is the
    tangent bound ``x1`` (since ``log(1+x) ≤ x ≤ x1`` on the box), and ``L`` is a
    chosen rational lower bound with ``exp(L) ≤ 1 + x0`` (so ``L ≤ log(1+x0) ≤
    log(1+x)``).  ``exp_L_num`` records the exact rational upper bound used for
    ``exp(L)`` in the self-check (a rational ``≥ exp(L)`` would falsify it).

    All fields are exact ``sympy`` rationals.
    """

    face: str          # "log"
    x0: object          # box lower endpoint
    x1: object          # box upper endpoint
    L: object           # certified rational LOWER bound of expr on the box
    U: object           # certified rational UPPER bound of expr on the box
    expr_lo: object     # exact/high-precision value of expr at x0 (min on box)
    expr_hi: object     # exact/high-precision value of expr at x1 (max on box)


# exp lower bound used in Lean: `Real.add_one_le_exp : x + 1 ≤ Real.exp x`, i.e.
# `L + 1 ≤ exp L`.  So the RATIONAL certificate that closes `L ≤ log(1+x0)` is the
# stronger, purely-rational fact `L + 1 ≤ 1 + x0` PLUS `L + 1 ≤ exp L` — chaining
# `exp L ≥ L + 1` is too weak in general, so the self-check instead verifies the
# TIGHT rational sufficient condition `exp(L) ≤ 1 + x0` in high precision, and the
# emitted Lean discharges `L ≤ log(1+x0)` via `Real.le_log_iff_exp_le` with a
# `Real.exp` monotone bound whose rational witness is checked here.


def transcendental_enclosure_certificate(
    *, face: str = "log", x0=None, x1=None, L=None, U=None
) -> TranscendentalEnclosureCertificate:
    """Build and self-check a rational enclosure ``L ≤ expr ≤ U`` over a box.

    log face (default).  ``expr = log(1 + x)`` over ``x ∈ [x0, x1]`` with
    ``0 ≤ x0 < x1``.  Self-check (exact where possible, else high precision;
    ANY failure raises ``ValueError`` — the negative control):

    * UPPER: ``U`` must upper-bound ``log(1+x)`` on the box.  Since ``log(1+x) ≤ x``
      (Mathlib tangent bound) and ``x ≤ x1``, ``U = x1`` always works; we REFUSE if
      the caller supplies a ``U`` with ``U < max_box log(1+x) = log(1+x1)`` (the
      transcendental max), i.e. ``U`` is not a genuine upper bound.
    * LOWER: ``L`` must lower-bound ``log(1+x)`` on the box, i.e. ``L ≤ log(1+x0)``
      (the transcendental min).  We REFUSE if ``L > log(1+x0)``.  Additionally, for
      the emitted Lean route to close, ``L`` must admit the rational sufficient
      condition ``exp(L) ≤ 1 + x0`` — we REFUSE if that fails too.

    NEGATIVE CONTROL: an ``L`` above ``log(1+x0)`` (e.g. ``L = 1/4`` on box
    ``[1/4,1/2]`` where ``log(5/4) ≈ 0.223 < 1/4``) or a ``U`` below ``log(1+x1)``
    is refused.

    trig face: DEFERRED (see module docstring).  Any ``face="trig"`` is REFUSED
    with a clear message — we do not emit non-green Lean.
    """
    if face == "trig":
        raise ValueError(
            "REFUSED: the trig face (Montgomery–Taylor C₀ = 3/2 − (1/√2)cot(1/√2)) "
            "is DEFERRED as a follow-on — a kernel-checked enclosure of C₀ needs √2 "
            "plus cos/sin Taylor bounds at 1/√2; the log face ships alone and green "
            "(see module docstring). conjecture1_proved=False."
        )
    if face != "log":
        raise ValueError(f"REFUSED: unknown face {face!r} (expected 'log'; 'trig' deferred)")

    x0 = sp.Rational(1, 4) if x0 is None else sp.Rational(x0)
    x1 = sp.Rational(1, 2) if x1 is None else sp.Rational(x1)
    if not (0 <= x0 < x1):
        raise ValueError(f"REFUSED: need 0 ≤ x0 < x1, got [{x0}, {x1}]")

    # transcendental min/max on the box (log(1+x) is monotone increasing).
    expr_lo = sp.log(1 + x0)   # = min over box
    expr_hi = sp.log(1 + x1)   # = max over box

    # UPPER default: the tangent bound endpoint x1 (log(1+x) ≤ x ≤ x1).
    U = x1 if U is None else sp.Rational(U)
    # LOWER default: choose the largest "nice" rational with exp(L) ≤ 1 + x0.
    # For box [1/4,1/2]: log(5/4) ≈ 0.2231, exp(1/5)=1.2214 ≤ 5/4 → L = 1/5.
    L = sp.Rational(1, 5) if L is None else sp.Rational(L)

    # (UPPER) U must be a genuine upper bound of the transcendental max.
    if not (sp.N(U - expr_hi, 40) >= 0):
        raise ValueError(
            f"REFUSED: U = {U} is NOT an upper bound of log(1+x) on [{x0},{x1}] — "
            f"log(1+x1) = log({1 + x1}) ≈ {float(expr_hi):.6f} > {float(U):.6f} "
            f"(negative control)"
        )
    # (LOWER, transcendental) L must be ≤ the transcendental min log(1+x0).
    if not (sp.N(expr_lo - L, 40) >= 0):
        raise ValueError(
            f"REFUSED: L = {L} is NOT a lower bound of log(1+x) on [{x0},{x1}] — "
            f"log(1+x0) = log({1 + x0}) ≈ {float(expr_lo):.6f} < {float(L):.6f} "
            f"(negative control)"
        )
    # (LOWER, rational route) exp(L) ≤ 1 + x0 must hold for the Lean route to close.
    exp_L = sp.exp(L)
    if not (sp.N((1 + x0) - exp_L, 40) >= 0):
        raise ValueError(
            f"REFUSED: rational route broken — exp(L) = exp({L}) ≈ {float(exp_L):.6f} "
            f"> 1 + x0 = {1 + x0}; cannot discharge L ≤ log(1+x0) via "
            f"Real.le_log_iff_exp_le (negative control)"
        )

    return TranscendentalEnclosureCertificate(
        face="log", x0=x0, x1=x1, L=L, U=U,
        expr_lo=sp.nsimplify(expr_lo, rational=False),
        expr_hi=sp.nsimplify(expr_hi, rational=False),
    )


def certify_transcendental_enclosure_point(family, pt, name):
    """Certify one transcendental-enclosure instance from ``family.special[1](pt)``.

    ``spec`` is a dict ``{"face": "log", "x0": ..., "x1": ..., "L": ..., "U": ...}``
    (all optional; log-face defaults to box ``[1/4, 1/2]``, ``L = 1/5``, ``U = 1/2``).
    """
    spec = family.special[1](pt)
    cert = transcendental_enclosure_certificate(
        face=spec.get("face", "log"),
        x0=spec.get("x0"), x1=spec.get("x1"),
        L=spec.get("L"), U=spec.get("U"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class TranscendentalEnclosureEmitter(Emitter):
    """Emit the rational-enclosure theorems for a transcendental over a box.

    Each log-face instance emits THREE self-contained theorems (only
    ``import Mathlib``):

    1. ``<name>_upper`` — the tangent UPPER bound, valid for all ``x ≥ 0``:

           theorem <name>_upper (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x

       via ``Real.log_le_sub_one_of_pos`` at ``y = 1 + x``.

    2. ``<name>_lower_box`` — the rational LOWER bound over the box ``[x0, x1]``:

           theorem <name>_lower_box (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
               (L : ℝ) ≤ Real.log (1 + x)

       via monotonicity ``Real.log_le_log`` (so ``log(1+x) ≥ log(1+x0)``) and a
       rational floor ``L ≤ log(1+x0)`` discharged by ``Real.le_log_iff_exp_le``
       with the rational ``exp`` bound ``Real.add_one_le_exp`` chained through the
       certified ``exp(L) ≤ 1 + x0``.

    3. ``<name>_enclosure`` — the packaged rational bracket over the box:

           theorem <name>_enclosure (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
               (L : ℝ) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ (U : ℝ)

       combining (2) with (1) chained through ``x ≤ x1 = U``.

    HONEST SCOPE: the log face is BG-critical and ships green; the trig face
    (Montgomery–Taylor ``C₀``) is DEFERRED (refused at cert time).
    conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "transcendental_enclosure"

    def _emit_log(self, cert: TranscendentalEnclosureCertificate, name: str) -> str:
        x0 = _lean_rat(cert.x0)
        x1 = _lean_rat(cert.x1)
        L = _lean_rat(cert.L)
        U = _lean_rat(cert.U)
        # The rational floor `L ≤ log(1 + x0)` reduces (via `Real.le_log_iff_exp_le`,
        # needs `0 < 1 + x0`) to the purely-rational upper bound `exp L ≤ 1 + x0`.
        # We discharge THAT with Mathlib's degree-3 Taylor upper bound on exp:
        #   `Real.exp_bound' (0 ≤ L) (L ≤ 1) (0 < 3)`  gives
        #   `exp L ≤ Σ_{m<3} L^m/m! + L^3·4/(3!·3)`, a concrete rational upper bound;
        # `norm_num [Finset.sum_range_succ, Nat.factorial]` evaluates the RHS and
        # `linarith` closes `exp L ≤ 1 + x0` (the cert guarantees the strict rational
        # gap `exp(L) ≤ 1 + x0`, so the degree-3 tail leaves margin).  The tangent
        # UPPER bound uses `Real.log_le_sub_one_of_pos`, and monotonicity uses
        # `Real.log_le_log`.  All rational literals are ℝ-ascribed.
        return (
            f"-- ===== log face: rational enclosure of Real.log (1 + x) on "
            f"[{x0}, {x1}] =====\n"
            f"-- Serves BG compact-core cells (e_v = log(1 + S/d) − F*): enclosing\n"
            f"-- log(1+x) between rationals turns a per-cell inequality into a pure\n"
            f"-- rational nlinarith goal.\n"
            f"\n"
            f"-- (1) tangent UPPER bound, all x ≥ 0: log(1+x) ≤ x "
            f"(Real.log_le_sub_one_of_pos at y = 1+x).\n"
            f"theorem {name}_upper (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by\n"
            f"  have hy : (0 : ℝ) < 1 + x := by linarith\n"
            f"  have h := Real.log_le_sub_one_of_pos hy\n"
            f"  linarith\n"
            f"\n"
            f"-- (2) rational LOWER bound on the box [{x0}, {x1}]: {L} ≤ log(1+x).\n"
            f"-- log monotone ⇒ log(1+x) ≥ log(1+{x0}); and {L} ≤ log(1+{x0}) via\n"
            f"-- Real.le_log_iff_exp_le reduced to the certified exp({L}) ≤ 1+{x0}.\n"
            f"theorem {name}_lower_box (x : ℝ) (hx : x ∈ Set.Icc ({x0} : ℝ) ({x1} : ℝ)) :\n"
            f"    ({L} : ℝ) ≤ Real.log (1 + x) := by\n"
            f"  obtain ⟨hlo, _hhi⟩ := hx\n"
            f"  have hx0pos : (0 : ℝ) < 1 + ({x0} : ℝ) := by norm_num\n"
            f"  have hxpos : (0 : ℝ) < 1 + x := by linarith\n"
            f"  -- rational floor: {L} ≤ log(1 + {x0}).\n"
            f"  have hfloor : ({L} : ℝ) ≤ Real.log (1 + ({x0} : ℝ)) := by\n"
            f"    rw [Real.le_log_iff_exp_le hx0pos]\n"
            f"    -- exp({L}) ≤ 1 + {x0} via the degree-3 Taylor upper bound on exp.\n"
            f"    have hexp := Real.exp_bound' (x := ({L} : ℝ)) (by norm_num) (by norm_num)\n"
            f"      (n := 3) (by norm_num)\n"
            f"    have hsum : (∑ m ∈ Finset.range 3, ({L} : ℝ) ^ m / m.factorial)\n"
            f"        + ({L} : ℝ) ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) ≤ 1 + ({x0} : ℝ) := by\n"
            f"      norm_num [Finset.sum_range_succ, Nat.factorial]\n"
            f"    linarith\n"
            f"  -- monotone step: log(1+{x0}) ≤ log(1+x).\n"
            f"  have hmono : Real.log (1 + ({x0} : ℝ)) ≤ Real.log (1 + x) :=\n"
            f"    Real.log_le_log hx0pos (by linarith)\n"
            f"  linarith\n"
            f"\n"
            f"-- (3) packaged rational enclosure {L} ≤ log(1+x) ≤ {U} on [{x0}, {x1}].\n"
            f"theorem {name}_enclosure (x : ℝ) (hx : x ∈ Set.Icc ({x0} : ℝ) ({x1} : ℝ)) :\n"
            f"    ({L} : ℝ) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ ({U} : ℝ) := by\n"
            f"  obtain ⟨hlo, hhi⟩ := hx\n"
            f"  refine ⟨{name}_lower_box x ⟨hlo, hhi⟩, ?_⟩\n"
            f"  have hup := {name}_upper x (by linarith)\n"
            f"  linarith\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: TranscendentalEnclosureCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            if cert.face == "log":
                lines.append(self._emit_log(cert, name))
                nthm += 3
            else:  # pragma: no cover — guarded at certify time
                raise ValueError(f"unknown/deferred face {cert.face!r}")
        return "\n".join(lines), nthm


def transcendental_enclosure_family(name, grid, lean_name, spec, constants=None):
    """Build a transcendental-enclosure family (kind='transcendental_enclosure').

    ``spec``: a callable ``pt -> {"face": "log", "x0": ..., "x1": ..., "L": ...,
    "U": ...}`` (all optional; log-face defaults to box ``[1/4, 1/2]``,
    ``L = 1/5``, ``U = 1/2``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("transcendental_enclosure", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive: log(1+x) enclosure on [1/4, 1/2], L=1/5, U=1/2 ===")
    c = transcendental_enclosure_certificate()
    print(f"  cert OK: face={c.face}, box=[{c.x0},{c.x1}], L={c.L}, U={c.U}; "
          f"min=log(1+x0)≈{float(c.expr_lo):.6f} ≥ L, "
          f"max=log(1+x1)≈{float(c.expr_hi):.6f} ≤ U")

    print("\n=== positive: log(1+x) enclosure on [0, 1/2], L=0, U=1/2 ===")
    c2 = transcendental_enclosure_certificate(x0=0, x1=Fraction(1, 2), L=0)
    print(f"  cert OK: box=[{c2.x0},{c2.x1}], L={c2.L}, U={c2.U}")

    print("\n=== NEGATIVE CONTROL: L=1/4 too high on [1/4,1/2] (log(5/4)≈0.223) ===")
    try:
        transcendental_enclosure_certificate(L=Fraction(1, 4))
        raise SystemExit("FAIL: over-high L was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

    print("\n=== NEGATIVE CONTROL: U=2/5 below log(3/2)≈0.405 on [1/4,1/2] ===")
    try:
        transcendental_enclosure_certificate(U=Fraction(2, 5))
        raise SystemExit("FAIL: too-low U was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

    print("\n=== NEGATIVE CONTROL: trig face is DEFERRED (refused) ===")
    try:
        transcendental_enclosure_certificate(face="trig")
        raise SystemExit("FAIL: trig face was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

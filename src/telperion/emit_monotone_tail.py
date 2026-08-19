"""Monotone-ratio family-tail emitter — the ``b(s) <= B for all s >= s0`` shape.

A first-class emitter for the monotone-ratio tail bound (the source is
``bg/near_star_tail.py``'s ``NearStarTailCertificate``): given a POSITIVE
sequence ``b(s)`` defined by an exact rational cavity form, prove

    b(s) <= B    for every integer s >= s0

via three ingredients that between them cover the whole tail:

  (1) the consecutive RATIO ``r(s) = b(s+1)/b(s)`` — a rational function of ``s``
      even when ``b`` itself is not (the transcendental amplitude factors cancel
      in the quotient; this is the near-star's ``(486/529)(1+1/(4s^2+11s+6))^11``);
  (2) the NONINCREASING TAIL: ``r(s) <= 1`` for all ``s >= s0``, i.e. ``b`` is
      nonincreasing on the tail.  Since ``b(s) > 0`` this is equivalent to
      ``1 - r(s) >= 0``; that rational claim is Polya-certified on the tail region
      ``s = s0 + t, t >= 0`` (an all-nonneg-coefficient numerator over an
      all-positive denominator, the ``polya_certify`` shape);
  (3) the BASE value ``b(s0) <= B`` — an exact rational fact (``norm_num``).

Then ``b(s) <= b(s0) <= B`` for every ``s >= s0``: descend from any ``s`` to
``s0`` one nonincreasing step at a time (ingredient 2), landing on the base
(ingredient 3).  That descent is a single clean ``Nat`` induction.

HONEST SCOPE
------------
* The NONINCREASING-STEP certificate (``0 <= 1 - r(s0+t)`` over ``t >= 0``, a
  num/den Polya form closed by ``positivity``) and the BASE fact
  (``b(s0) <= B`` by ``norm_num`` on an exact rational) are STANDARD, robust
  Lean — the same two tactics ``emit_cone`` / ``emit_lattice_box`` rely on.  The
  step numerator is rendered so ``positivity`` closes it as written.
* The step is stated as ``1 - r(s0+t) >= 0`` (equivalently ``r(s0+t) <= 1``).
  This is EXACTLY the ``b`` nonincreasing fact for a positive ``b``, and it is
  what the induction consumes; it is proven rigorously and independently of any
  Lean encoding of ``b`` itself.
* The assembled ``forall s >= s0, b s <= B`` theorem is emitted over an ABSTRACT
  ``b : ℕ → ℝ`` fed the two proven ingredients as hypotheses (``hstep`` : the
  per-step nonincrease, ``hbase`` : ``b s0 <= B``).  That assembly lemma is a
  genuine, ``sorry``-free ``Nat.le_induction`` — it is the mechanical part.  What
  it does NOT do is pin ``b`` to a concrete Lean closed form: encoding an
  arbitrary transcendental cavity ``b`` as a Lean function and re-deriving its
  ratio in-kernel is the remaining piece, and it is documented as such (no
  ``sorry``, no stub) rather than faked.  For the near-star the concrete
  ``r``-step and the concrete rational base ARE emitted and kernel-checkable; the
  outstanding link is instantiating the abstract assembly at the concrete ``b``.

NEGATIVE CONTROL
----------------
``certify_monotone_tail_point`` refuses (ValueError, no Lean) when the tail is
NOT certifiably nonincreasing (``1 - r(s0+t)`` has no nonneg-num / positive-den
Polya form) or when the base is violated (``b(s0) > B``).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance, PolyaCertificate, polya_certify
from .expr import expr_lean, expr_lean_from_parts, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Payload
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MonotoneTailPayload:
    """The certified pieces of one ``b(s) <= B for s >= s0`` instance."""

    b_expr: sp.Expr          # b(s), a (possibly transcendental) exact expr in s
    s_symbol: sp.Symbol      # the integer variable s
    s0: int                  # tail start
    bound: sp.Rational       # B
    ratio: sp.Expr           # r(s) = b(s+1)/b(s), a RATIONAL function of s
    step_cert: PolyaCertificate   # Polya cert for 0 <= 1 - r(s0 + t), t >= 0
    t_symbol: sp.Symbol      # the tail variable t (s = s0 + t)
    base_value: sp.Rational  # b(s0) as an exact rational


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_monotone_tail_point(family, pt, name):
    """Certify one monotone-tail instance: (CertifiedInstance, n_checks).

    Reads ``(b_expr, s0, bound, s_symbol) = family.special[1](pt)``, derives the
    exact consecutive ratio ``r(s) = b(s+1)/b(s)``, Polya-certifies the
    nonincreasing tail ``0 <= 1 - r(s0 + t)`` over the nonnegative tail variable
    ``t``, and checks the base ``b(s0) <= B`` exactly.  Raises ValueError (a
    refusal, no Lean) when the tail is not certifiably nonincreasing or the base
    is violated.
    """
    b_expr, s0, bound, s = family.special[1](pt)
    b_expr = sp.sympify(b_expr)
    bound = sp.Rational(bound)
    s0 = int(s0)

    checks = 0

    # (1) exact consecutive ratio r(s) = b(s+1)/b(s) — must be a rational fn of s.
    ratio = sp.simplify(b_expr.subs(s, s + 1) / b_expr)
    ratio = sp.together(ratio)
    r_num, r_den = sp.fraction(ratio)
    if not (sp.Poly(sp.expand(r_num), s) and sp.Poly(sp.expand(r_den), s)):
        raise ValueError(
            f"monotone-tail instance '{name}' REFUSED: ratio b(s+1)/b(s) is not "
            "a rational function of s"
        )
    checks += 1

    # (2) nonincreasing tail: 0 <= 1 - r(s0 + t) over t >= 0 (Polya).
    t = sp.Symbol("t", nonnegative=True)
    step_expr = sp.together(1 - ratio.subs(s, s0 + t))
    try:
        step_cert = polya_certify(step_expr, (t,))
    except ValueError as e:
        raise ValueError(
            f"monotone-tail instance '{name}' REFUSED: tail is not certifiably "
            f"nonincreasing (1 - r(s0+t) has no Polya form): {e}"
        )
    checks += 1

    # (3) base: b(s0) <= B exactly.
    base_value = sp.nsimplify(b_expr.subs(s, s0))
    base_value = sp.Rational(base_value)
    if base_value > bound:
        raise ValueError(
            f"monotone-tail instance '{name}' REFUSED: base b({s0}) = "
            f"{base_value} > B = {bound}"
        )
    checks += 1

    payload = MonotoneTailPayload(
        b_expr=b_expr,
        s_symbol=s,
        s0=s0,
        bound=bound,
        ratio=ratio,
        step_cert=step_cert,
        t_symbol=t,
        base_value=base_value,
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
class MonotoneRatioTailEmitter(Emitter):
    """Emit ``b(s) <= B for all s >= s0`` as three kernel-checkable pieces.

    Per instance:

      * ``<name>_step`` — the nonincreasing-step certificate
        ``0 <= 1 - r(s0 + t)`` for ``t >= 0`` (equivalently ``r(s0+t) <= 1``),
        a num/den Polya form discharged by ``positivity`` (robust, the
        ``DirectPolya`` idiom).
      * ``<name>_base`` — the base fact ``b(s0) <= B`` on an exact rational,
        by ``norm_num`` (robust).
      * ``<name>_tail`` — the assembled ``forall s, s0 <= s -> b s <= B`` over an
        ABSTRACT ``b : ℕ → ℝ``, via ``Nat.le_induction``, fed the two ingredients
        as hypotheses ``hstep`` (per-step nonincrease) and ``hbase``.  This is a
        genuine ``sorry``-free assembly; instantiating ``b`` at the concrete
        cavity form is documented as the remaining link (see module docstring).

    Deterministic ordering: grid order.
    """

    def __post_init__(self):
        self.kind = "monotone_tail"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            pl: MonotoneTailPayload = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            t = pl.t_symbol

            # --- (a) nonincreasing-step certificate: 0 <= 1 - r(s0 + t) --------
            cert = pl.step_cert
            step_body = expr_lean_from_parts(cert.numerator, cert.denominator, (t,))
            trivial_den = sp.simplify(cert.denominator - 1) == 0
            if trivial_den:
                step_thm = (
                    f"theorem {name}_step ({t} : ℝ) (h{t} : 0 ≤ {t}) :\n"
                    f"    0 ≤ {step_body} := by\n"
                    f"  positivity\n"
                )
            else:
                step_thm = (
                    f"theorem {name}_step ({t} : ℝ) (h{t} : 0 ≤ {t}) :\n"
                    f"    0 ≤ {step_body} := by\n"
                    f"  positivity\n"
                )
            lines.append(step_thm)
            n += 1

            # --- (b) base fact: b(s0) <= B on an exact rational ----------------
            base_s = rat_lean(pl.base_value)
            bound_s = rat_lean(pl.bound)
            lines.append(
                f"theorem {name}_base : ({base_s} : ℝ) ≤ {bound_s} := by norm_num\n"
            )
            n += 1

            # --- (c) assembled monotone-tail theorem (abstract b) --------------
            # Nat.le_induction from the anchor s0: b s0 <= B is the base; the
            # inductive step uses hstep (b (m+1) <= b m for m >= s0) to keep the
            # bound.  A genuine sorry-free assembly over an abstract positive
            # nonincreasing b; instantiating b at the concrete cavity form (whose
            # step is <name>_step and whose base is <name>_base) is the remaining
            # link — documented, not faked.
            lines.append(
                f"-- {name}: assembled monotone-tail bound over an abstract\n"
                f"-- b : ℕ → ℝ.  The two ingredients above ({name}_step : the\n"
                f"-- nonincreasing step r(s0+t) ≤ 1, and {name}_base : b(s0) ≤ B)\n"
                f"-- feed hstep and hbase.  Instantiating b at the concrete cavity\n"
                f"-- form is the remaining link (see module docstring).\n"
                f"theorem {name}_tail (b : ℕ → ℝ) (B : ℝ)\n"
                f"    (hstep : ∀ m, {pl.s0} ≤ m → b (m + 1) ≤ b m)\n"
                f"    (hbase : b {pl.s0} ≤ B) :\n"
                f"    ∀ s, {pl.s0} ≤ s → b s ≤ B := by\n"
                f"  intro s hs\n"
                f"  induction s, hs using Nat.le_induction with\n"
                f"  | base => exact hbase\n"
                f"  | succ m hm ih => exact le_trans (hstep m hm) ih\n"
            )
            n += 1
        return "".join(lines), n


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def monotone_tail_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a monotone-ratio tail family (kind='monotone_tail'), mirroring
    ``cone_family`` / ``lattice_box_family``.

    Parameters
    ----------
    name, grid, lean_name
        As for every family: name, the finite parameter grid, and a
        ``pt -> str`` Lean theorem-name map.
    symbols
        The free variables (typically empty for a pure integer-tail family; the
        tail variable ``s`` is supplied inside ``spec``, not here).
    spec
        A callable ``pt -> (b_expr, s0, bound, s_symbol)`` where ``b_expr`` is a
        sympy expression for the positive sequence ``b(s)`` in the integer symbol
        ``s_symbol``, ``s0`` the integer tail start, and ``bound`` the rational
        ``B``.  ``certify_monotone_tail_point`` derives ``r(s) = b(s+1)/b(s)``,
        Polya-certifies the nonincreasing tail ``0 <= 1 - r(s0 + t)``, checks
        ``b(s0) <= B`` exactly, and refuses (no Lean) otherwise.
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("monotone_tail", spec),
        constants=dict(constants or {}),
    )

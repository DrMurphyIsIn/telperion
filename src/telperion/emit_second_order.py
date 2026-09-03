"""Second-order linear-recurrence closed-form emitter — the three-term
generalization of the first-order forward telescoping emitter
(``emit_fwd_telescope.py``, the W2 prover mechanizing SumEqProd.lean).

Where ``emit_fwd_telescope`` certifies a FIRST-order/affine recurrence
``f(q+1) = f(q)·A(q)/(P−q)`` by the single contiguous identity, this emitter
handles the SECOND-order (three-term) linear recurrence

    A(q)·f(q+2) + B(q)·f(q+1) + C(q)·f(q) = 0        (q ≥ q₀),

with A, B, C polynomial coefficients in q (the forward three-term form, so no
ℕ-subtraction ever appears).  This is the Hahn / Krawtchouk / Jacobi
orthogonal-polynomial recurrence shape flagged as the missing piece for the
Laurent max-cut / full-rank W2 target (see
telperion/examples/knapsack_sos/FULLRANK_W2_SCOPING.md, item (c)).

CERTIFICATE.  Given the recurrence coefficients (A, B, C) and a claimed CLOSED
FORM ``g(q)``, the certificate is:

  (i)   the recurrence coefficients A(q), B(q), C(q);
  (ii)  the closed form g(q) (a sympy expr in q, plus its Lean rendering);
  (iii) the exact RING IDENTITY, denominator-cleared and sympy-verified,

            A(q)·g(q+2) + B(q)·g(q+1) + C(q)·g(q) = 0                  (⋆)

        — i.e. g SATISFIES the recurrence, checked exactly in sympy;
  (iv)  the two base values g(q₀), g(q₀+1).

Because (⋆) holds and A(q) ≠ 0 on the tail, the recurrence determines f(q+2)
from f(q+1), f(q); with the two base cases pinned, ``f(q) = g(q)`` for all
q ≥ q₀ by a two-step induction.  ``second_order_certificate`` sympy-checks (⋆)
and the base evaluations and RAISES ``ValueError`` (the anti-phantom negative
control) if g does NOT satisfy the recurrence.

EMITTED LEAN (per instance).  Over an ABSTRACT ``f : ℕ → ℝ`` fed the recurrence
and the two base equalities as hypotheses (the ``emit_monotone_tail`` idiom),
with g emitted as a concrete Lean closed form ``<name>_g``:

    theorem <name> (f : ℕ → ℝ)
        (hrec : ∀ q, q₀ ≤ q → A q * f (q+2) + B q * f (q+1) + C q * f q = 0)
        (hA   : ∀ q, q₀ ≤ q → A q ≠ 0)
        (hb0  : f q₀ = <name>_g q₀) (hb1 : f (q₀+1) = <name>_g (q₀+1))
        (q : ℕ) (hq : q₀ ≤ q) : f q = <name>_g q := by ...

proved by a single-step ``Nat.le_induction`` on the STRENGTHENED predicate
``f q = g q ∧ f (q+1) = g (q+1)`` (the standard second-order induction trick).
The step consumes the recurrence-satisfaction ``ring`` identity (⋆) emitted as
a ``have`` and cancels A(q) ≠ 0.  The two base facts are separate ``norm_num``
lemmas ``<name>_base0``/``<name>_base1``.

HONEST SCOPE.  This certifies that the given g SATISFIES the recurrence and the
two base cases, hence equals the recurrence-defined f on the tail — an exact,
kernel-checkable identity.  It does not by itself establish positivity /
interlacing of the sequence (the downstream W2 obligation); that is a separate
certificate consuming this closed form.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import expr_lean, rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_second_order.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import expr_lean, rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# ---------------------------------------------------------------------------
# Payload
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SecondOrderCertificate:
    """A verified second-order-recurrence closed-form certificate.

    The closed form ``g`` satisfies ``A·g(q+2) + B·g(q+1) + C·g(q) = 0`` (an
    exact sympy-verified ring identity) and reproduces the two base values
    ``g(q₀)``, ``g(q₀+1)``.  ``g_lean`` is the Lean rendering of ``g(q)`` as a
    function of the ℝ-cast index (rendered by the caller so power/transcendental
    closed forms are emitted faithfully — sympy is used only for the exact
    self-check).
    """

    q0: int                    # tail start q₀
    A: sp.Expr                 # A(q)
    B: sp.Expr                 # B(q)
    C: sp.Expr                 # C(q)
    g: sp.Expr                 # closed form g(q) (sympy, in q)
    g_lean: str                # Lean rendering of g(q); "q" is the ℕ index cast
    base0: sp.Rational         # g(q₀)
    base1: sp.Rational         # g(q₀+1)


def second_order_certificate(
    q0, A, B, C, g, g_lean: str,
) -> SecondOrderCertificate:
    """Build and EXACTLY self-check a second-order-recurrence closed-form cert.

    Verifies the ring identity (⋆) ``A·g(q+2) + B·g(q+1) + C·g(q) = 0`` exactly
    in sympy (denominator-cleared), and evaluates the two base values
    ``g(q₀)``, ``g(q₀+1)`` to exact rationals.  Refuses (``ValueError`` — no
    Lean) when g does NOT satisfy the recurrence, or when the leading
    coefficient A(q) is identically zero (then it is not genuinely
    second-order), or when a base value is not an exact rational.
    """
    q = sp.Symbol("q")
    A, B, C, g = sp.sympify(A), sp.sympify(B), sp.sympify(C), sp.sympify(g)
    q0 = int(q0)

    if sp.simplify(A) == 0:
        raise ValueError(
            "second_order REFUSED: leading coefficient A(q) is identically zero "
            "— the recurrence is not genuinely second-order"
        )

    # (⋆) exact ring identity: A·g(q+2) + B·g(q+1) + C·g(q) = 0, denom-cleared.
    resid = A * g.subs(q, q + 2) + B * g.subs(q, q + 1) + C * g
    resid_num, _ = sp.fraction(sp.together(resid))
    if sp.simplify(resid_num) != 0:
        raise ValueError(
            "second_order REFUSED: closed form g does NOT satisfy the recurrence "
            f"A·g(q+2)+B·g(q+1)+C·g(q)=0 (residual numerator {sp.simplify(resid_num)}) "
            "— g is not a solution"
        )

    # (iv) the two base values as exact rationals.
    try:
        base0 = sp.Rational(sp.nsimplify(g.subs(q, q0)))
        base1 = sp.Rational(sp.nsimplify(g.subs(q, q0 + 1)))
    except (TypeError, ValueError) as e:
        raise ValueError(
            f"second_order REFUSED: base value g(q₀) or g(q₀+1) is not an exact "
            f"rational: {e}"
        )

    return SecondOrderCertificate(
        q0=q0, A=A, B=B, C=C, g=g, g_lean=str(g_lean), base0=base0, base1=base1,
    )


def certify_second_order_point(family, pt, name):
    """Certify one second-order instance from ``family.special[1](pt) -> spec``.

    ``spec`` is a dict ``{"q0", "A", "B", "C", "g", "g_lean"}`` (A/B/C/g sympy
    exprs in q; ``g_lean`` a Lean string for g(q) with the ℕ-index cast written
    ``q``).  Returns ``(CertifiedInstance, n_checks)``: one check for the ring
    identity plus two for the base evaluations."""
    spec = family.special[1](pt)
    cert = second_order_certificate(
        spec["q0"], spec["A"], spec["B"], spec["C"], spec["g"], spec["g_lean"],
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 3


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

_TEMPLATE = '''-- {name}: closed form for the second-order recurrence
--   ({A_str})*f(q+2) + ({B_str})*f(q+1) + ({C_str})*f(q) = 0   (q >= {q0}),
-- certificate = the ring identity A*g(q+2)+B*g(q+1)+C*g(q)=0 (verified exactly
-- at certification) + the two base values, assembled by a two-step induction.

def {name}_g (q : ℕ) : ℝ := {g_lean}

theorem {name}_base0 : {name}_g {q0} = {base0} := by norm_num [{name}_g]

theorem {name}_base1 : {name}_g ({q0} + 1) = {base1} := by norm_num [{name}_g]

theorem {name} (f : ℕ → ℝ)
    (hrec : ∀ q, {q0} ≤ q →
      ({A_q}) * f (q + 2) + ({B_q}) * f (q + 1) + ({C_q}) * f q = 0)
    (hA : ∀ q, {q0} ≤ q → ({A_q}) ≠ 0)
    (hb0 : f {q0} = {name}_g {q0}) (hb1 : f ({q0} + 1) = {name}_g ({q0} + 1)) :
    ∀ q, {q0} ≤ q → f q = {name}_g q := by
  -- Strengthened predicate P q := (f q = g q) ∧ (f (q+1) = g (q+1)); a single
  -- Nat.le_induction carries the two-back dependence of the recurrence.
  have key : ∀ q, {q0} ≤ q → f q = {name}_g q ∧ f (q + 1) = {name}_g (q + 1) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => exact ⟨hb0, hb1⟩
    | succ m hm ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      -- recurrence-satisfaction of the closed form g (the (⋆) ring identity):
      have hgid : ({A_m}) * {name}_g (m + 2) + ({B_m}) * {name}_g (m + 1)
          + ({C_m}) * {name}_g m = 0 := by
        simp only [{name}_g]; push_cast; ring
      have hrecm := hrec m hm
      have hAm := hA m hm
      -- subtract the two relations, substitute the two inductive equalities,
      -- and cancel the (nonzero) leading coefficient A(m).
      have hcancel : ({A_m}) * f (m + 2) = ({A_m}) * {name}_g (m + 2) := by
        rw [ih0, ih1] at hrecm
        linear_combination hrecm - hgid
      exact mul_left_cancel₀ hAm hcancel
  intro q hq
  exact (key q hq).1
'''


@dataclass
class SecondOrderRecurrenceEmitter(Emitter):
    """Emit the second-order closed-form theorem: a claimed g satisfies the
    three-term recurrence + two base cases, hence equals the recurrence-defined
    f on the tail.

    Per instance: ``<name>_base0``/``<name>_base1`` (concrete base values by
    ``norm_num``) and ``<name>`` (the assembled closed-form theorem via a
    two-step ``Nat.le_induction`` on the strengthened predicate; the ⋆ ring
    identity is a ``ring``-closed ``have``, the leading coefficient is cancelled
    by ``mul_left_cancel₀``).  Deterministic grid ordering."""

    def __post_init__(self):
        self.kind = "second_order"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        q, m = sp.symbols("q m")
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: SecondOrderCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            A, B, C = cert.A, cert.B, cert.C
            lines.append(_TEMPLATE.format(
                name=name,
                q0=cert.q0,
                g_lean=cert.g_lean,
                base0=rat_lean(cert.base0),
                base1=rat_lean(cert.base1),
                A_str=expr_lean(A, (q,)),
                B_str=expr_lean(B, (q,)),
                C_str=expr_lean(C, (q,)),
                A_q=_coeff_lean(A, q),
                B_q=_coeff_lean(B, q),
                C_q=_coeff_lean(C, q),
                A_m=_coeff_lean(A.subs(q, m), m),
                B_m=_coeff_lean(B.subs(q, m), m),
                C_m=_coeff_lean(C.subs(q, m), m),
            ))
            nthm += 3
        return "\n".join(lines), nthm


def _coeff_lean(e: sp.Expr, sym: sp.Symbol) -> str:
    """Render a coefficient polynomial over ℝ with the ℕ index cast to ℝ.

    The index symbol appears in Lean as ``(sym : ℝ)`` (via push_cast in the
    proof); a constant coefficient renders as a bare ℝ literal.
    """
    body = expr_lean(sp.expand(e), (sym,))
    if e.free_symbols & {sym}:
        # index occurs — wrap the cast so the arithmetic is over ℝ.
        return body.replace(str(sym), f"({sym} : ℝ)")
    return f"({body} : ℝ)"


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def second_order_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a second-order-recurrence family (kind='second_order').

    ``spec``: a callable ``pt -> {"q0", "A", "B", "C", "g", "g_lean"}`` where
    A, B, C, g are sympy expressions in the symbol ``q`` (the recurrence
    ``A·f(q+2)+B·f(q+1)+C·f(q)=0`` and the claimed closed form g), and
    ``g_lean`` is the Lean rendering of ``g(q)`` (the ℕ index written ``q`` and
    cast to ℝ inside).  Refuses (at certification) a g that does not satisfy the
    recurrence, an identically-zero leading coefficient, or a non-rational base.
    """
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("second_order", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid cert, negative control, print emitted Lean ----------
    q = sp.Symbol("q")

    print("=== positive: geometric g(q) = 2^q + 3^q, recurrence roots 2,3 ===")
    # f(q+2) - 5 f(q+1) + 6 f(q) = 0; characteristic (x-2)(x-3), g = 2^q + 3^q.
    cert = second_order_certificate(
        q0=0,
        A=sp.Integer(1), B=sp.Integer(-5), C=sp.Integer(6),
        g=2 ** q + 3 ** q,
        g_lean="(2 : ℝ) ^ q + (3 : ℝ) ^ q",
    )
    print(f"  cert OK: q0={cert.q0}, g(0)={cert.base0}, g(1)={cert.base1}")

    print("\n=== positive: linear g(q) = q, recurrence = second difference 0 ===")
    # f(q+2) - 2 f(q+1) + f(q) = 0; closed form g(q) = q (base 3, 4).
    cert2 = second_order_certificate(
        q0=3,
        A=sp.Integer(1), B=sp.Integer(-2), C=sp.Integer(1),
        g=q,
        g_lean="(q : ℝ)",
    )
    print(f"  cert OK: q0={cert2.q0}, g(3)={cert2.base0}, g(4)={cert2.base1}")

    print("\n=== NEGATIVE CONTROL: wrong g (does NOT satisfy recurrence) ===")
    try:
        second_order_certificate(
            q0=0,
            A=sp.Integer(1), B=sp.Integer(-5), C=sp.Integer(6),
            g=2 ** q + 5 ** q,   # 5 is not a root of (x-2)(x-3)
            g_lean="(2 : ℝ) ^ q + (5 : ℝ) ^ q",
        )
        raise SystemExit("FAIL: wrong closed form was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: zero leading coefficient (expect ValueError) ===")
    try:
        second_order_certificate(
            q0=0, A=sp.Integer(0), B=sp.Integer(1), C=sp.Integer(-1),
            g=q, g_lean="(q : ℝ)",
        )
        raise SystemExit("FAIL: zero leading coefficient was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (two instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="so_geom_2_3",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="so_linear",
                          corners=(), payload=cert2),
    ]

    class _View:
        instances = insts

    body, nthm = SecondOrderRecurrenceEmitter().emit_body(
        _View(), LeanProfile(namespace=("SecondOrder",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

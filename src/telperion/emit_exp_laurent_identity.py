"""ExpLaurentIdentity emitter -- identities in ``Real.exp d`` and ``Real.exp (-d)``
certified as an exact reduction modulo the SINGLE relation ``e^d * e^(-d) = 1``.

THE SHAPE.  A great many "exp bookkeeping" rows in the RH-adjacent corpus are
Laurent polynomials in the one transcendental ``y = exp d``, with ``z = exp (-d)``
its formal inverse: amplitude sums ``y + z`` (a ``2 cosh`` channel), one-sided
clearances ``y - 1`` and ``1 - z``, their products and squares.  Every TRUE
identity among them is exactly a polynomial identity in ``Q[y, z]`` modulo the one
relation ``y*z - 1``; every FALSE one leaves a nonzero remainder.  This emitter
makes that the certificate:

    claim      lhs = rhs                       (Laurent polynomials in y, z)
    certify    lhs - rhs = cofactor * (y*z - 1) in Q[y, z]   (exact, sympy)
    emit       have hrel : Real.exp d * Real.exp (-d) = 1 := by
                 rw [<- Real.exp_add]; norm_num
               linear_combination (cofactor) * hrel

The COFACTOR is the load-bearing certificate: `linear_combination` re-derives the
goal from it by `ring`, so a corrupted cofactor -- or a corrupted side -- leaves a
nonzero residue and the Lean KERNEL rejects the theorem.  That is the emitter's
negative control (``negctrl_adapters/adapter_exp_laurent_identity.py``).

TWO REFUSALS (Layer-1 self-check, both exercised in the tests):

  * NON-IDENTITY -- the remainder of ``lhs - rhs`` modulo ``y*z - 1`` is nonzero.
    The motivating instance is the mistake QC_RECURRENCE section 6 caught in
    itself: the SUM of the two clearances, ``(y - 1) + (1 - z) = 2d + O(d^3)``, is
    NOT the amplitude excess ``y + z - 2``; only the PRODUCT is.  Certifying the
    sum is refused with a nonzero remainder ``2 - 2z``.
  * RELATION NOT LOAD-BEARING -- the cofactor is 0, i.e. ``lhs - rhs`` vanishes as
    a polynomial and the claim never uses ``e^d * e^(-d) = 1``.  That is an
    ordinary ring identity; it belongs to ``IdentityEmitter``, and emitting it here
    would advertise a certificate that carries no information.  Refused.

HONESTY SEAM: none.  Every emitted theorem is an unconditional statement about
``Real.exp`` at a universally quantified real ``d`` -- no enclosure, no Arb input,
no analytic hypothesis.  What the emitter does NOT do is supply the meaning: an
exp-Laurent row is dictionary bookkeeping between two instruments, never evidence
about zeta.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# The two formal generators: y = exp(d), z = exp(-d).  A family's `spec` returns
# its claimed (lhs, rhs) as sympy expressions in exactly these symbols.
Y = sp.Symbol("expPos")
Z = sp.Symbol("expNeg")

#: The single relation the certificate reduces against.
RELATION = Y * Z - 1


@dataclass(frozen=True)
class ExpLaurentCert:
    """A certified exp-Laurent identity.

    ``lhs``/``rhs`` are the claimed sides, kept UNEXPANDED (the emitted statement
    must read like the mathematics, not like sympy's canonical form); ``cofactor``
    is the exact quotient with ``lhs - rhs = cofactor * (y*z - 1)``; ``var`` is the
    Lean binder name for the real displacement.
    """

    lhs: sp.Expr
    rhs: sp.Expr
    cofactor: sp.Expr
    var: str = "d"


def _assert_exp_laurent(expr: sp.Expr, name: str) -> None:
    """Refuse anything that is not a polynomial in the two generators."""
    extra = expr.free_symbols - {Y, Z}
    if extra:
        raise ValueError(
            f"exp_laurent_identity instance '{name}' REFUSED: side {expr} carries "
            f"symbols {sorted(map(str, extra))} outside the exp generators "
            f"(expPos = e^d, expNeg = e^(-d))")
    try:
        sp.Poly(sp.expand(expr), Y, Z)
    except sp.PolynomialError as exc:
        raise ValueError(
            f"exp_laurent_identity instance '{name}' REFUSED: side {expr} is not a "
            f"polynomial in the exp generators ({exc})") from exc


def exp_laurent_certificate(lhs, rhs, *, var: str = "d",
                            name: str = "<anon>") -> ExpLaurentCert:
    """Certify ``lhs = rhs`` modulo ``e^d * e^(-d) = 1`` and return the cofactor.

    EXACT: the quotient/remainder are computed in ``Q[y, z]`` and the cofactor is
    re-multiplied and compared against ``lhs - rhs`` before it is returned.
    """
    lhs, rhs = sp.sympify(lhs), sp.sympify(rhs)
    _assert_exp_laurent(lhs, name)
    _assert_exp_laurent(rhs, name)

    diff = sp.expand(lhs - rhs)
    if diff == 0:
        raise ValueError(
            f"exp_laurent_identity instance '{name}' REFUSED: the cofactor is 0, "
            f"so the relation e^{var} * e^(-{var}) = 1 is NOT load-bearing -- this "
            "is a plain ring identity and belongs to IdentityEmitter")
    quotients, remainder = sp.reduced(diff, [RELATION], Y, Z)
    cofactor = sp.expand(quotients[0])
    remainder = sp.expand(remainder)

    if remainder != 0:
        raise ValueError(
            f"exp_laurent_identity instance '{name}' REFUSED: lhs - rhs does not "
            f"reduce to 0 modulo e^{var} * e^(-{var}) = 1 (remainder "
            f"{remainder}) -- not an identity")
    if cofactor == 0:
        raise ValueError(
            f"exp_laurent_identity instance '{name}' REFUSED: the cofactor is 0, "
            f"so the relation e^{var} * e^(-{var}) = 1 is NOT load-bearing -- this "
            "is a plain ring identity and belongs to IdentityEmitter")
    # exact re-validation of the returned certificate
    if sp.expand(cofactor * RELATION - diff) != 0:  # pragma: no cover
        raise ValueError(
            f"exp_laurent_identity instance '{name}' REFUSED: cofactor "
            f"re-multiplication failed the exact re-check")
    return ExpLaurentCert(lhs=lhs, rhs=rhs, cofactor=cofactor, var=var)


def certify_exp_laurent_identity_point(family, pt, name):
    """``spec(pt) -> (lhs, rhs)`` or ``(lhs, rhs, var)``.

    n_checks = 3: the two-sided generator audit, the exact reduction to remainder
    0, and the cofactor re-multiplication.
    """
    spec = family.special[1](pt)
    if len(spec) == 3:
        lhs, rhs, var = spec
    else:
        lhs, rhs = spec
        var = family.constants.get("var", "d")
    cert = exp_laurent_certificate(lhs, rhs, var=var, name=name)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                             payload=cert)
    return inst, 3


# ---------------------------------------------------------------------------
# Lean rendering: structure-preserving (the STATEMENT must read as written).
# ---------------------------------------------------------------------------

def _order_key(term: sp.Expr):
    """Deterministic, READABLE ordering: the e^d channel before the e^(-d) channel
    before the constants.

    sympy discards the order the author wrote (`Mul`/`Add` args are canonicalized),
    and Lean multiplication is not definitionally commutative, so the emitted
    statement must be reassembled in a FIXED order -- the one the corpus writes
    these rows in: ``(e^d - 1) * (1 - e^(-d))``, ``e^d + e^(-d) - 2``.
    """
    free = term.free_symbols
    channel = 0 if Y in free else (1 if Z in free else 2)
    return (channel, sp.default_sort_key(term))


def _render(expr: sp.Expr, var: str) -> str:
    """Render a polynomial in the exp generators as Lean, preserving structure.

    Canonicalization is the PROOF's job (`linear_combination`/`ring`); the emitted
    statement keeps the shape the mathematics was written in -- so
    ``(expPos - 1) * (1 - expNeg)`` emits as ``(Real.exp d - 1) * (1 - Real.exp (-d))``
    and NOT as an expanded sum.
    """
    if expr is Y or expr == Y:
        return f"Real.exp {var}"
    if expr is Z or expr == Z:
        return f"Real.exp (-{var})"
    if isinstance(expr, sp.Integer):
        return str(expr) if expr >= 0 else f"(-{-expr})"
    if isinstance(expr, sp.Rational):
        return f"({expr.p} / {expr.q})" if expr >= 0 else f"(-({-expr.p} / {expr.q}))"
    if isinstance(expr, sp.Add):
        terms = sorted(expr.args, key=_order_key)
        pos = [t for t in terms if not t.could_extract_minus_sign()]
        neg = [t for t in terms if t.could_extract_minus_sign()]
        if not pos:  # all-negative sum: lead with the first negated term
            head, rest = f"-{_render(-neg[0], var)}", neg[1:]
        else:
            head, rest = _render(pos[0], var), neg
            for t in pos[1:]:
                head = f"{head} + {_render(t, var)}"
        for t in rest:
            head = f"{head} - {_render(-t, var)}"
        return f"({head})"
    if isinstance(expr, sp.Mul):
        factors = sorted(expr.args, key=_order_key)
        return "(" + " * ".join(_render(a, var) for a in factors) + ")"
    if isinstance(expr, sp.Pow):
        base, exponent = expr.args
        if not (isinstance(exponent, sp.Integer) and exponent > 0):
            raise ValueError(f"unsupported exponent {exponent} in {expr}")
        return f"{_render(base, var)} ^ {int(exponent)}"
    raise ValueError(f"unsupported node {type(expr).__name__} in {expr}")


def _strip_outer(text: str) -> str:
    """Drop one redundant outer parenthesis pair (readability only)."""
    if not (text.startswith("(") and text.endswith(")")):
        return text
    depth = 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and i != len(text) - 1:
                return text
    return text[1:-1]


@dataclass
class ExpLaurentIdentityEmitter(Emitter):
    """Emit ``forall d : R, lhs = rhs`` via the one relation ``e^d * e^(-d) = 1``
    and the certified cofactor, discharged by ``linear_combination``."""

    def __post_init__(self):
        self.kind = "exp_laurent_identity"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: ExpLaurentCert = inst.payload  # type: ignore[assignment]
            var = cert.var
            lhs_s = _strip_outer(_render(cert.lhs, var))
            rhs_s = _strip_outer(_render(cert.rhs, var))
            cof_s = _strip_outer(_render(sp.sympify(cert.cofactor), var))
            lines.append(
                f"-- {inst.lean_name}: exp-Laurent identity in e^{var}, e^(-{var}), "
                f"certified as an exact\n"
                f"-- reduction modulo the single relation e^{var} * e^(-{var}) = 1 "
                f"with cofactor {cert.cofactor}.\n"
                f"-- Unconditional; no enclosure, no analytic hypothesis.  "
                f"conjecture1_proved = False.\n"
                f"theorem {inst.lean_name} ({var} : ℝ) :\n"
                f"    {lhs_s} = {rhs_s} := by\n"
                f"  have hrel : Real.exp {var} * Real.exp (-{var}) = 1 := by\n"
                f"    rw [← Real.exp_add]; norm_num\n"
                f"  linear_combination ({cof_s} : ℝ) * hrel\n")
            n_thm += 1
        return "\n".join(lines), n_thm


def exp_laurent_identity_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
    symbols: Sequence[sp.Symbol] = (Y, Z),
) -> InequalityFamily:
    """Kind ``exp_laurent_identity``; ``spec: pt -> (lhs, rhs[, var])`` in the
    generators ``Y = expPos`` (= ``e^d``) and ``Z = expNeg`` (= ``e^(-d)``)."""
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("exp_laurent_identity", spec),
        constants=dict(constants or {}),
    )

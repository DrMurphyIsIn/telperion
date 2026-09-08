"""AffineLedger emitter family — distilled from the OpenAI Navier--Stokes / Euler
formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/ExponentLedger.lean``, manuscript Proposition 10.3).

The finite-time-blowup construction is an iterative correction scheme whose
bookkeeping assigns REAL EXPONENTS -- affine in a scale parameter ``σ`` and a
fixed accuracy ``κ`` -- to each analytic estimate, then repeatedly checks that a
per-stage GAIN dominates the per-stage INCREMENT.  ``ExponentLedger.lean`` isolates
that bookkeeping as ~40 self-contained real-arithmetic facts over the region
``{σ ≥ 1/5, 0 ≤ κ ≤ 1e-5}``, every one closed by ``linarith`` / ``ring`` /
``min``-lemmas.

This emitter ships that shape as a first-class kind.  Given affine forms in
rational variables over a BOX region (each variable a closed or half-open
interval), it certifies one of two claims and emits the ``linarith``-discharged
theorem:

  * ``margin``    : ``threshold ≤`` (or ``<``) an affine form, on the region;
  * ``min_lower`` : ``threshold <`` (or ``≤``) ``min(f_1, …, f_m)`` -- i.e. the
    threshold is below every listed gain (the "gain dominates increment" step),
    closed by ``lt_min_iff`` / ``le_min_iff`` + one ``linarith`` per branch.

Certification is EXACT: an affine form over a box attains its extremum at a
vertex, so the worst-corner value is a rational computed in closed form (no LP,
no float).  A missing bound in the binding direction ⟹ the form is unbounded
there ⟹ the instance is REFUSED (the negative control).

HONESTY SEAM (identical to the zeta-23 / RH-in-a-box discipline): this certifies
the LEDGER ARITHMETIC only -- "IF the analytic estimates carry these exponents
THEN the gains dominate the increments".  That a correction of the stated order
actually exists, that any PDE estimate holds, is NOT established here; those are
the analytic hypotheses of a full theorem.  ``conjecture1_proved = False``.  This
is exponent bookkeeping, not a proof of finite-time blowup.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# --------------------------------------------------------------------------- #
# Certificate payload + exact box-extremum                                    #
# --------------------------------------------------------------------------- #

Box = dict  # var-name -> (lo | None, hi | None), rational bounds; None = ∓∞


@dataclass(frozen=True)
class AffineLedgerCert:
    """A certified affine-ledger claim.

    ``variables``  ordered tuple of sympy Symbols (the ledger parameters).
    ``box``        var-name -> (lo, hi) rational interval; None means unbounded.
    ``mode``       ``"margin"`` or ``"min_lower"``.
    ``threshold``  the rational left-hand side.
    ``forms``      the affine right-hand form(s); one for margin, ≥ 1 for min_lower.
    ``strict``     True for ``<``, False for ``≤``.
    ``worst``      the exact worst-corner value(s) that were checked (provenance).
    """

    variables: tuple[sp.Symbol, ...]
    box: tuple[tuple[str, object, object], ...]
    mode: str
    threshold: sp.Rational
    forms: tuple[sp.Expr, ...]
    strict: bool
    worst: tuple[sp.Rational, ...]


def _affine_coeffs(form: sp.Expr, variables: Sequence[sp.Symbol]) -> tuple[sp.Rational, dict]:
    """Return (constant, {var: coeff}) for an AFFINE ``form``; raise on nonlinear."""
    form = sp.expand(form)
    const = sp.Rational(form.subs({v: 0 for v in variables}))
    coeffs = {}
    for v in variables:
        c = form.coeff(v, 1)
        if c.free_symbols & set(variables):
            raise ValueError(f"affine_ledger REFUSED: form {form} is not affine in {v}")
        coeffs[v] = sp.Rational(c)
    # residual must be exactly the constant (no cross terms / higher powers)
    residual = sp.expand(form - const - sum(coeffs[v] * v for v in variables))
    if sp.simplify(residual) != 0:
        raise ValueError(f"affine_ledger REFUSED: form {form} is not affine")
    return const, coeffs


def _box_min(form: sp.Expr, variables, box_map) -> sp.Rational | None:
    """Exact minimum of an affine ``form`` over the box; None if unbounded below."""
    const, coeffs = _affine_coeffs(form, variables)
    total = const
    for v in variables:
        c = coeffs[v]
        lo, hi = box_map[v.name]
        if c > 0:
            if lo is None:
                return None  # +coeff, no floor ⟹ ↓ to -∞
            total += c * sp.Rational(lo)
        elif c < 0:
            if hi is None:
                return None  # -coeff, no ceiling ⟹ ↓ to -∞
            total += c * sp.Rational(hi)
    return sp.Rational(total)


def affine_ledger_certificate(
    variables, box, mode, threshold, forms, strict=True
) -> AffineLedgerCert:
    """Build and EXACTLY re-check an affine-ledger claim.  Refuses (ValueError)
    when the claim fails at the worst corner or a form is unbounded below."""
    variables = tuple(variables)
    box_map = {name: (lo, hi) for name, lo, hi in box}
    if set(box_map) != {v.name for v in variables}:
        raise ValueError("affine_ledger REFUSED: box must name exactly the variables")
    if mode not in ("margin", "min_lower"):
        raise ValueError(f"affine_ledger REFUSED: mode ∈ {{margin, min_lower}}; got {mode}")
    forms = tuple(sp.nsimplify(f) if not isinstance(f, sp.Expr) else f for f in forms)
    if mode == "margin" and len(forms) != 1:
        raise ValueError("affine_ledger REFUSED: margin takes exactly one form")
    if mode == "min_lower" and len(forms) < 1:
        raise ValueError("affine_ledger REFUSED: min_lower needs ≥ 1 form")
    thr = sp.Rational(sp.nsimplify(threshold))
    worst = []
    for f in forms:
        m = _box_min(f, variables, box_map)
        if m is None:
            raise ValueError(f"affine_ledger REFUSED: form {f} unbounded below on the box")
        ok = (m > thr) if strict else (m >= thr)
        if not ok:
            raise ValueError(
                f"affine_ledger REFUSED: worst-corner value {m} of {f} violates "
                f"{'>' if strict else '≥'} {thr} (overclaim / false margin)")
        worst.append(m)
    box_t = tuple((name, box_map[name][0], box_map[name][1]) for name in (v.name for v in variables))
    return AffineLedgerCert(
        variables=variables, box=box_t, mode=mode, threshold=thr,
        forms=forms, strict=strict, worst=tuple(worst),
    )


def certify_affine_ledger_point(family, pt, name):
    """Certify one affine-ledger instance: ``(CertifiedInstance, n_checks)``.

    ``spec(pt) -> (variables, box, mode, threshold, forms, strict)``.
    ``n_checks`` = one worst-corner check per form."""
    spec = family.special[1](pt)
    variables, box, mode, threshold, forms, strict = spec
    cert = affine_ledger_certificate(variables, box, mode, threshold, forms, strict)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.forms)


# --------------------------------------------------------------------------- #
# Emitter                                                                     #
# --------------------------------------------------------------------------- #


@dataclass
class AffineLedgerEmitter(Emitter):
    """Emit the affine-ledger arithmetic fact (``margin`` / ``min_lower``),
    discharged by ``linarith`` off the box interval hypotheses (plus
    ``lt_min_iff`` / ``le_min_iff`` for ``min_lower``).  Self-contained over ℝ."""

    def __post_init__(self):
        self.kind = "affine_ledger"

    @staticmethod
    def _hyps(cert: AffineLedgerCert) -> tuple[str, str]:
        """Return (binder_reals, hypotheses) Lean fragments for the box."""
        names = " ".join(v.name for v in cert.variables)
        hyps = []
        i = 0
        for name, lo, hi in cert.box:
            if lo is not None:
                hyps.append(f"(hlo{i} : {rat_lean(sp.Rational(lo))} ≤ {name})")
                i += 1
            if hi is not None:
                hyps.append(f"(hhi{i} : {name} ≤ {rat_lean(sp.Rational(hi))})")
                i += 1
        return names, " ".join(hyps)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: AffineLedgerCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            names, hyps = self._hyps(cert)
            binder = f"({names} : ℝ)" if names else ""
            rel = "<" if cert.strict else "≤"
            thr = rat_lean(cert.threshold)
            svars = cert.variables
            if cert.mode == "margin":
                rhs = expr_lean(cert.forms[0], svars)
                lines.append(
                    f"-- {nm}: affine-ledger margin (NS/Euler ExponentLedger shape).\n"
                    f"-- Honesty seam: the exponents are HYPOTHESES from the analytic side;\n"
                    f"-- this certifies only that the margin holds on the parameter box.\n"
                    f"-- (All box hypotheses are kept for statement fidelity; a given\n"
                    f"-- margin may not consume every bound, hence the linter suppression.)\n"
                    f"set_option linter.unusedVariables false in\n"
                    f"theorem {nm} {binder} {hyps} :\n"
                    f"    {thr} {rel} {rhs} := by\n"
                    f"  linarith\n"
                )
                n_thm += 1
            else:  # min_lower
                # right-nested `min f1 (min f2 (... fm))`
                rendered = [expr_lean(f, svars) for f in cert.forms]
                min_expr = rendered[-1]
                for r in reversed(rendered[:-1]):
                    min_expr = f"min ({r}) ({min_expr})"
                iff_lemma = "lt_min_iff" if cert.strict else "le_min_iff"
                tuple_terms = ", ".join("by linarith" for _ in rendered)
                proof = (
                    "  linarith\n" if len(rendered) == 1
                    else f"  simp only [{iff_lemma}]\n  exact ⟨{tuple_terms}⟩\n"
                )
                lines.append(
                    f"-- {nm}: affine-ledger min-lower bound (NS/Euler gain-dominates-increment).\n"
                    f"-- Honesty seam: exponents are analytic-side HYPOTHESES; certifies the\n"
                    f"-- threshold lies below every listed gain on the parameter box.\n"
                    f"-- (All box hypotheses are kept for statement fidelity; a given\n"
                    f"-- branch may not consume every bound, hence the linter suppression.)\n"
                    f"set_option linter.unusedVariables false in\n"
                    f"theorem {nm} {binder} {hyps} :\n"
                    f"    {thr} {rel} {min_expr} := by\n"
                    f"{proof}"
                )
                n_thm += 1
        return "\n".join(lines), n_thm


def affine_ledger_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an affine-ledger family (kind ``affine_ledger``).

    ``spec: pt -> (variables, box, mode, threshold, forms, strict)`` where
    ``variables`` is a tuple of sympy Symbols, ``box`` a sequence of
    ``(var_name, lo, hi)`` (rational or None), ``mode`` ∈ {"margin", "min_lower"},
    ``forms`` a sequence of affine sympy expressions.  The theorem quantifies its
    own reals, so a single dummy grid symbol carries the family."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("affine_ledger", spec),
        constants=dict(constants or {}),
    )

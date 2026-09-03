"""Scale-invariance / objective-degeneracy emitter — a homogeneity certificate.

Proves that a rational objective ``f`` is INVARIANT under an exact algebraic
transformation of its arguments — either

  * PARAMETER CANCELLATION: a parameter ``p`` drops out of ``f`` entirely
    (``∂f/∂p ≡ 0`` as a rational function), so ``f(p₁, x…) = f(p₂, x…)`` for all
    ``p₁, p₂``; or
  * DEGREE-0 HOMOGENEITY: scaling a designated subset of arguments by a common
    factor ``λ`` leaves ``f`` unchanged (``f(λ•args) − f(args) ≡ 0`` as a
    rational function), so ``f(λ•args) = f(args)`` for all ``λ > 0``.

The certificate is EXACT sympy verification of the vanishing rational function;
the emitted Lean is the ``field_simp; ring`` spine over ℝ with the nonzero side
conditions that keep every denominator well-defined:

    theorem <name> (…vars…) (hpos : 0 < scale) (…nonzero side conds…) :
        f (scale • args) = f args := by
      field_simp
      ring

MOTIVATING STRUCTURE — the Arda trading system's leverage↔position_size
degeneracy in the Sharpe objective.  In
``src/arda/acceleration/rust_core.py`` (~L1250–1318) and its Rust twin
``arda_rust/src/backtesting.rs`` (``compute_weighted_sharpe``, ~L317–330):

    pnl_i          = Δprice_i · direction_i · pos_size,   pos_size = capital·s·L/price
    fee_i          ∝ notional = capital · s · L
    trade_return_i = (pnl_i − fee_i) / (capital · s · L)

Two exact algebraic facts fall out and are the shipped examples:
  1. ``position_size`` (``s``) CANCELS entirely from ``trade_return`` — it sits in
     both the ``pnl``/``fee`` numerator and the denominator ⟹ ``trade_return`` is
     independent of ``s`` (pure ``field_simp; ring`` cancellation).
  2. ``leverage`` (``L``) scales ``trade_return`` by ``1/L`` ⟹ the Sharpe ratio
     ``mean/std·√n`` — equivalently ``Sharpe² = mean²·n/variance`` — is INVARIANT
     under scaling ``L`` (numerator and denominator scale identically).  We ship
     the ``Sharpe²`` (rational, degree-0-homogeneous) form for a fixed small
     ``n``, which is pure ``field_simp; ring``.

This is why CLAUDE.md forbids ``leverage`` as an evolvable gene: it is
mathematically degenerate with ``position_size`` in the Sharpe objective.

NEGATIVE CONTROL: ``<name>_certificate`` RAISES ``ValueError`` when the objective
GENUINELY depends on the parameter / is not degree-0 homogeneous (the difference
does not cancel to 0) — the anti-phantom guard.

HONEST SCOPE: this proves ONLY the exact algebraic invariance of the given
rational objective under the given transformation.  It says nothing about the
statistical content of the Sharpe estimator, nor does it close any trading or
downstream obligation.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Mapping, Sequence

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_scale_invariance.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# --------------------------------------------------------------------------- #
# Lean rendering (ℝ-ascribed; canonicalization is field_simp/ring's job, the
# STATEMENT keeps lhs/rhs shapes distinct so the nonvacuity gate does not see a
# collapsed X = X).
# --------------------------------------------------------------------------- #
def _render(expr) -> str:
    """Structure-preserving Lean renderer over ℝ.  Bare rational literals are
    ℝ-ascribed at the fraction so they do not default to ℤ."""
    if isinstance(expr, sp.Symbol):
        return str(expr)
    if isinstance(expr, sp.Integer):
        return str(int(expr)) if expr >= 0 else f"(-{-int(expr)})"
    if isinstance(expr, sp.Rational):
        return f"(({_render(sp.Integer(expr.p))} : ℝ) / {_render(sp.Integer(expr.q))})"
    if isinstance(expr, sp.Add):
        return "(" + " + ".join(_render(a) for a in expr.args) + ")"
    if isinstance(expr, sp.Pow):
        base, exp = expr.args
        if exp == -1:
            return f"(1 / {_render(base)})"
        if isinstance(exp, sp.Integer) and exp < -1:
            return f"(1 / {_render(base)} ^ {-int(exp)})"
        if isinstance(exp, sp.Integer) and exp > 0:
            return f"{_render(base)} ^ {int(exp)}"
        raise ValueError(f"unsupported exponent {exp} in {expr}")
    if isinstance(expr, sp.Mul):
        num, den = [], []
        for a in expr.args:
            if isinstance(a, sp.Pow) and isinstance(a.args[1], sp.Integer) \
                    and a.args[1] < 0:
                den.append(a.args[0] if a.args[1] == -1
                           else sp.Pow(a.args[0], -a.args[1]))
            elif isinstance(a, sp.Rational) and not isinstance(a, sp.Integer):
                num.append(sp.Integer(a.p))
                den.append(sp.Integer(a.q))
            else:
                num.append(a)
        num_s = " * ".join(_render(a) for a in num) if num else "1"
        if not den:
            return f"({num_s})"
        den_s = " * ".join(_render(a) for a in den)
        return f"(({num_s}) / ({den_s}))"
    raise ValueError(f"unsupported node {type(expr).__name__} in {expr}")


def _collect_var_denominators(expr, out: list) -> None:
    """Collect distinct denominator sub-expressions carrying free symbols — the
    exact objects whose ≠ 0 side conditions field_simp needs."""
    if isinstance(expr, sp.Pow) and isinstance(expr.args[1], sp.Integer) \
            and expr.args[1] < 0:
        base = expr.args[0]
        if base.free_symbols and base not in out:
            out.append(base)
        _collect_var_denominators(base, out)
        return
    if isinstance(expr, (sp.Add, sp.Mul, sp.Pow)):
        for a in expr.args:
            _collect_var_denominators(a, out)


# --------------------------------------------------------------------------- #
# Certificate
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class ScaleInvarianceCertificate:
    """A verified scale-invariance / objective-degeneracy certificate.

    ``mode`` is ``"cancellation"`` (a parameter drops out) or ``"homogeneity"``
    (degree-0 under a common scaling).  ``f_lhs`` and ``f_rhs`` are the two
    rational-function SHAPES of the emitted equation ``f_lhs = f_rhs`` (kept
    distinct for nonvacuity); ``variables`` are the free ℝ variables in scope;
    ``scale`` is the scaling / distinguished parameter symbol; ``side_conditions``
    are the denominators required ≠ 0.  The exact sympy check is that
    ``f_lhs − f_rhs`` cancels to 0 as a rational function.
    """

    mode: str                                     # "cancellation" | "homogeneity"
    f_lhs: sp.Expr                                # emitted-equation left  shape
    f_rhs: sp.Expr                                # emitted-equation right shape
    variables: tuple[sp.Symbol, ...]             # free ℝ vars in the statement
    scale: sp.Symbol                             # scale param λ (homog) / p1 (cancel)
    scale_pos: bool                              # emit 0 < scale hypothesis
    side_conditions: tuple[sp.Expr, ...]         # denominators required ≠ 0


def scale_invariance_certificate(
    objective: sp.Expr,
    *,
    mode: str,
    scale: sp.Symbol,
    args: Sequence[sp.Symbol] | None = None,
    second: sp.Symbol | None = None,
    scale_pos: bool = True,
) -> ScaleInvarianceCertificate:
    """Build and EXACTLY self-check a scale-invariance certificate over ℝ.

    ``objective``: a rational expression ``f`` (the objective) in some symbols.

    ``mode="homogeneity"``: ``scale`` = the scaling factor ``λ``; ``args`` = the
    subset of symbols scaled by ``λ``.  Certifies ``f(λ•args) − f(args) ≡ 0`` as a
    rational function ⟹ emit ``f(λ•args) = f(args)``.  (``λ`` must NOT already
    appear in ``objective``.)

    ``mode="cancellation"``: ``scale`` = the distinguished parameter ``p`` claimed
    to drop out; ``second`` = a fresh symbol ``p'`` for the RHS.  Certifies
    ``∂f/∂p ≡ 0`` (equivalently ``f(p) − f(p→p') ≡ 0``) ⟹ emit ``f(p) = f(p')``.

    RAISES ``ValueError`` (the anti-phantom negative control) when the invariance
    FAILS: the objective genuinely depends on the parameter / is not degree-0
    homogeneous (the difference does not cancel to 0).
    """
    objective = sp.sympify(objective)
    if mode not in ("homogeneity", "cancellation"):
        raise ValueError(f"unknown mode {mode!r} (expected homogeneity|cancellation)")

    if mode == "homogeneity":
        if args is None or len(tuple(args)) == 0:
            raise ValueError("homogeneity mode requires a non-empty `args` to scale")
        scaled = tuple(sp.sympify(a) for a in args)
        if scale in objective.free_symbols:
            raise ValueError(
                f"REFUSED: scale symbol {scale} already appears in the objective")
        missing = [a for a in scaled if a not in objective.free_symbols]
        if missing:
            raise ValueError(
                f"REFUSED: scaled arg(s) {missing} do not appear in the objective")
        subs = {a: scale * a for a in scaled}
        f_lhs = objective.subs(subs, simultaneous=True)
        f_rhs = objective
        # EXACT self-check: the two rational functions coincide.
        diff = sp.cancel(sp.together(f_lhs - f_rhs))
        if diff != 0:
            raise ValueError(
                f"REFUSED: objective is NOT degree-0 homogeneous under scaling "
                f"{list(scaled)} by {scale}: f(λ•args) − f(args) = {diff} ≢ 0")
        variables = tuple(sorted(objective.free_symbols, key=str))
    else:  # cancellation
        if scale not in objective.free_symbols:
            raise ValueError(
                f"REFUSED: parameter {scale} does not even appear in the objective; "
                "cancellation is vacuous")
        if second is None:
            second = sp.Symbol(str(scale) + "2")
        if second in objective.free_symbols:
            raise ValueError(f"REFUSED: fresh symbol {second} already in objective")
        # EXACT self-check: ∂f/∂p ≡ 0 (as a rational function).
        deriv = sp.cancel(sp.together(sp.diff(objective, scale)))
        if deriv != 0:
            raise ValueError(
                f"REFUSED: objective genuinely DEPENDS on {scale}: "
                f"∂f/∂{scale} = {deriv} ≢ 0 (no cancellation)")
        f_lhs = objective
        f_rhs = objective.subs({scale: second}, simultaneous=True)
        # sanity: as rational functions f(p) and f(p') coincide.
        if sp.cancel(sp.together(f_lhs - f_rhs)) != 0:
            raise ValueError("REFUSED: cancellation self-check failed (f(p) ≠ f(p'))")
        variables = tuple(
            sorted((objective.free_symbols | {second}), key=str))

    # Denominators requiring ≠ 0 side conditions (across both shapes).  Collect
    # from the RAW (un-`together`'d) shapes so each denominator FACTOR surfaces
    # as its own side condition — `field_simp` needs each factor nonzero, not
    # just the combined product.
    dens: list = []
    _collect_var_denominators(f_lhs, dens)
    _collect_var_denominators(f_rhs, dens)
    # de-dup preserving order
    seen: list = []
    for d in dens:
        if d not in seen:
            seen.append(d)

    return ScaleInvarianceCertificate(
        mode=mode,
        f_lhs=f_lhs,
        f_rhs=f_rhs,
        variables=tuple(variables),
        scale=scale,
        scale_pos=bool(scale_pos),
        side_conditions=tuple(seen),
    )


def certify_scale_invariance_point(family, pt, name):
    """Certify one scale-invariance instance from ``family.special[1](pt)``.

    ``spec`` is a dict:
      ``{"objective": expr, "mode": "homogeneity"|"cancellation",
         "scale": Symbol, "args": [Symbol…] (homogeneity),
         "second": Symbol (cancellation, optional), "scale_pos": bool (optional)}``.

    Returns ``(CertifiedInstance, n_checks)``.
    """
    spec = family.special[1](pt)
    cert = scale_invariance_certificate(
        spec["objective"],
        mode=spec["mode"],
        scale=spec["scale"],
        args=spec.get("args"),
        second=spec.get("second"),
        scale_pos=bool(spec.get("scale_pos", True)),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    # checks: the vanishing-difference identity + one per side condition.
    n_checks = 1 + len(cert.side_conditions)
    return inst, n_checks


@dataclass
class ScaleInvarianceEmitter(Emitter):
    """Emit ``f(scale•args) = f(args)`` (homogeneity) or ``f(p) = f(p')``
    (parameter cancellation) over ℝ via ``field_simp; ring`` under the nonzero
    denominator side conditions.  Models the Arda leverage↔position_size Sharpe
    degeneracy (``rust_core.py`` / ``backtesting.rs``)."""

    def __post_init__(self):
        self.kind = "scale_invariance"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: ScaleInvarianceCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name

            # binder variables: all free ℝ vars, plus the scale symbol.
            binder_syms = list(cert.variables)
            if cert.scale not in binder_syms:
                binder_syms.append(cert.scale)
            binders = " ".join(f"({s} : ℝ)" for s in binder_syms)

            hyps = []
            if cert.mode == "homogeneity" and cert.scale_pos:
                hyps.append(f"(hpos : (0 : ℝ) < {cert.scale})")
            for j, d in enumerate(cert.side_conditions):
                hyps.append(f"(hd{j} : ({_render(d)} : ℝ) ≠ 0)")
            hyp_s = (" " + " ".join(hyps)) if hyps else ""

            lhs_s = _render(cert.f_lhs)
            rhs_s = _render(cert.f_rhs)

            if cert.mode == "homogeneity":
                comment = (
                    f"-- {base}: degree-0 homogeneity — scaling the arguments by "
                    f"{cert.scale} > 0 leaves the objective invariant "
                    f"(field_simp; ring)."
                )
            else:
                comment = (
                    f"-- {base}: parameter cancellation — the objective does not "
                    f"depend on {cert.scale} (∂f/∂{cert.scale} ≡ 0), so any two "
                    f"values agree (field_simp; ring)."
                )

            lines.append(
                f"{comment}\n"
                f"theorem {base} {binders}{hyp_s} :\n"
                f"    {lhs_s} = {rhs_s} := by\n"
                f"  field_simp\n"
                f"  all_goals ring\n"
            )
            nthm += 1
        return "\n".join(lines), nthm


def scale_invariance_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable[[Mapping], dict],
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a scale-invariance family (kind='scale_invariance').

    ``spec``: ``pt -> {"objective", "mode", "scale", "args"?, "second"?,
    "scale_pos"?}`` (see ``scale_invariance_certificate``).  The listed
    ``symbols`` are only informational (the certificate reads free symbols off the
    objective itself); pass ``()`` if unused.
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("scale_invariance", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid certs, negative control, print emitted Lean --------- #
    capital, s, s2, L, dprice, direction, fee, price = sp.symbols(
        "capital s s2 L dprice direction fee price", positive=True
    )

    print("=== positive [cancellation]: trade_return is INDEPENDENT of "
          "position_size s ===")
    # trade_return = (pnl - fee_amt) / (capital*s*L), with
    #   pnl      = dprice*direction*pos_size,  pos_size = capital*s*L/price
    #   fee_amt  = notional*fee = capital*s*L*fee
    # => the capital*s*L factor is common to pnl, fee_amt AND the denominator,
    #    so s cancels entirely.
    pos_size = capital * s * L / price
    pnl = dprice * direction * pos_size
    fee_amt = capital * s * L * fee
    trade_return = (pnl - fee_amt) / (capital * s * L)
    cert_cancel = scale_invariance_certificate(
        trade_return, mode="cancellation", scale=s, second=s2
    )
    print(f"  cert OK: mode={cert_cancel.mode}, scale={cert_cancel.scale}, "
          f"side_conditions={[str(d) for d in cert_cancel.side_conditions]}")

    print("\n=== positive [homogeneity]: squared Sharpe is INVARIANT under "
          "scaling returns by L (fixed n=3) ===")
    # Sharpe^2 = mean^2 * n / variance, with population mean/variance over n=3
    # per-trade returns r1,r2,r3.  Scaling every r_i by lam scales mean by lam and
    # variance by lam^2, so Sharpe^2 is degree-0 homogeneous.
    r1, r2, r3, lam = sp.symbols("r1 r2 r3 lam", real=True)
    n = 3
    mean = (r1 + r2 + r3) / n
    variance = ((r1 - mean) ** 2 + (r2 - mean) ** 2 + (r3 - mean) ** 2) / n
    sharpe_sq = mean ** 2 * n / variance
    cert_homog = scale_invariance_certificate(
        sharpe_sq, mode="homogeneity", scale=lam, args=[r1, r2, r3]
    )
    print(f"  cert OK: mode={cert_homog.mode}, scale={cert_homog.scale}, "
          f"vars={[str(v) for v in cert_homog.variables]}, "
          f"side_conditions={[str(d) for d in cert_homog.side_conditions]}")

    print("\n=== NEGATIVE CONTROL: an objective that GENUINELY depends on the "
          "parameter (expect ValueError) ===")
    # f = a*p + b  really depends on p -> cancellation must be refused.
    a, b, p = sp.symbols("a b p", real=True)
    try:
        scale_invariance_certificate(a * p + b, mode="cancellation", scale=p)
        raise SystemExit("FAIL: parameter-dependent objective was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: an objective that is NOT degree-0 homogeneous "
          "(expect ValueError) ===")
    # g = r1 + r2 scales by lam (degree 1, not 0) -> homogeneity must be refused.
    try:
        scale_invariance_certificate(
            r1 + r2, mode="homogeneity", scale=lam, args=[r1, r2]
        )
        raise SystemExit("FAIL: degree-1 objective was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (both instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="si_return_indep_position_size",
                          corners=(), payload=cert_cancel),
        CertifiedInstance(point={"case": 1}, lean_name="si_sharpe_sq_leverage_invariant",
                          corners=(), payload=cert_homog),
    ]

    class _View:
        instances = insts

    body, nthm = ScaleInvarianceEmitter().emit_body(
        _View(), LeanProfile(namespace=("ScaleInvariance",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

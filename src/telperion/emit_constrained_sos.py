"""Constrained SOS / Putinar-Positivstellensatz emitter — nonnegativity of a
polynomial ON a basic closed semialgebraic set `{g_1 ≥ 0, …, g_m ≥ 0}`.

Where the unconstrained `SOSEmitter` proves `0 ≤ p` over ALL reals, this emitter
proves `0 ≤ p` only where the constraints hold, via a Putinar (a.k.a. constrained
Positivstellensatz) certificate:

    p ≡ σ_0 + Σ_i σ_i · g_i        (exact identity),   each σ_j a sum of squares.

Since every `σ_j ≥ 0` (a sum of squares) and every `g_i ≥ 0` (by hypothesis on
the set), the right-hand side is a sum of nonnegative terms, so `0 ≤ p` on the
set.  Telperion is the CERTIFICATE CHECKER here: the SOS multipliers `σ_j` are
supplied (the finite witness an SDP/SOSTOOLS run produces); certification
verifies the identity EXACTLY in rational arithmetic and that every square
coefficient is nonnegative — a decomposition that does not reconstruct `p`, or
that smuggles in a negative coefficient, is REFUSED and no Lean is emitted.

The emitted Lean is robust — `ring` for the exact identity, `positivity` for each
sum-of-squares multiplier, `mul_nonneg` to pair it with the constraint
hypothesis, and `linarith` to add the nonnegative pieces:

    theorem <name> : ∀ x y : ℝ, 0 ≤ g_1 → … → 0 ≤ g_m → (0:ℝ) ≤ p := by
      intro x y hg_1 … hg_m
      have t0 : (0:ℝ) ≤ <σ_0> := by positivity
      have t1 : (0:ℝ) ≤ (<σ_1>) * (<g_1>) := mul_nonneg (by positivity) hg_1
      …
      have hid : (p : ℝ) = <σ_0> + (<σ_1>)*(<g_1>) + … := by ring
      rw [hid]; linarith

Each SOS multiplier `σ_j = Σ_t c_t · b_t²` is rendered with `expr_lean_raw` so the
squares survive to the Lean text and `positivity` recognizes them (an EXPANDED
square `x² - 2xy + y²` defeats `positivity`; `ring` closes the identity
regardless).  This realizes the constrained arm of real-algebraic-geometry
positivity that the unconstrained SOS layer could not reach.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, expr_lean_raw, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _sos_expr(sos_terms, syms) -> sp.Expr:
    """Σ c_t · b_t²  from a list of (coef, base) sum-of-squares terms."""
    acc = sp.Integer(0)
    for c, b in sos_terms:
        acc += sp.nsimplify(c) * sp.sympify(b) ** 2
    return acc


def _check_nonneg_coeffs(sos_terms, where: str, name: str) -> int:
    """Every square coefficient must be a nonnegative rational; else refuse."""
    n = 0
    for c, _b in sos_terms:
        cr = sp.nsimplify(c)
        if not cr.is_rational:
            raise ValueError(
                f"putinar instance '{name}' REFUSED: {where} coefficient {c} is "
                "not rational (an SOS multiplier must be exact)"
            )
        if cr < 0:
            raise ValueError(
                f"putinar instance '{name}' REFUSED: {where} carries a NEGATIVE "
                f"coefficient {c} — not a sum of squares"
            )
        n += 1
    return n


def certify_putinar_point(family, pt, name):
    """Certify one Putinar instance: (CertifiedInstance, n_checks).

    Reads ``family.special[1](pt)``, either the 3-tuple ``(p, sigma0,
    constraints)`` or the 4-tuple ``(p, sigma0, constraints, equalities)``, where
    ``sigma0`` is a list of ``(coef, base)`` sum-of-squares terms for σ_0,
    ``constraints`` a list of ``(g_i, sigma_i, hyp_name)`` — the constraint
    ``g_i ≥ 0``, its SOS multiplier σ_i, and the Lean binder name — and
    ``equalities`` (optional) a list of ``(h_j, lambda_j, hyp_name)`` — the
    equality ``h_j = 0``, its FREE polynomial multiplier λ_j (arbitrary sign,
    NOT SOS), and the Lean binder.  Verifies
    ``p = σ_0 + Σ σ_i g_i + Σ λ_j h_j`` exactly, every SOS coefficient
    nonnegative; raises ValueError (a refusal) otherwise.  On the variety every
    ``h_j = 0``, so the certificate proves ``0 ≤ p`` on ``{g_i ≥ 0} ∩ {h_j = 0}``
    — the recursion-constrained (reachable) field set.
    """
    spec = family.special[1](pt)
    if len(spec) == 4:
        p, sigma0, constraints, equalities = spec
    else:
        p, sigma0, constraints = spec
        equalities = []
    p = sp.expand(sp.sympify(p))
    syms = tuple(family.symbols)
    if not constraints and not equalities:
        raise ValueError(
            f"putinar instance '{name}' REFUSED: no constraints — an "
            "unconstrained claim belongs to the SOS emitter, not Putinar"
        )

    # FINDER mode: when σ_0 is None (and the constraints carry no supplied
    # multipliers), SEARCH for the certificate via the SDP finder, then fall
    # through to the SAME exact verification below.  The finder is untrusted —
    # a bad search cannot pass the reconstruction check.
    _need_find = sigma0 is None or (
        constraints and all(sigma_i is None for _g, sigma_i, _h in constraints))
    if _need_find:
        from .sos_sdp import find_putinar_certificate
        half_deg = family.constants.get("putinar_half_deg")
        gens = [(g, hyp) for g, _sigma_i, hyp in constraints]
        eqs = [(h, hyp) for h, _lam, hyp in equalities]
        found = find_putinar_certificate(
            p, gens, syms,
            half_deg=int(half_deg) if half_deg is not None else None,
            equalities=eqs)
        if found is None:
            raise ValueError(
                f"putinar instance '{name}' REFUSED: no certificate "
                f"(p = σ_0 + Σ σ_i·g_i + Σ λ_j·h_j) found by the SDP finder — p "
                "may not be nonnegative on the set, or needs a higher relaxation "
                "order (raise 'putinar_half_deg')")
        if len(found) == 3:
            sigma0, constraints, equalities = found
        else:
            sigma0, constraints = found
            equalities = []

    checks = _check_nonneg_coeffs(sigma0, "σ_0", name)
    recon = _sos_expr(sigma0, syms)
    for g, sigma_i, _hyp in constraints:
        checks += _check_nonneg_coeffs(sigma_i, "an SOS multiplier", name)
        recon += sp.sympify(g) * _sos_expr(sigma_i, syms)
    # Equality (ideal) multipliers λ_j are FREE — no nonnegativity check; they
    # vanish on the variety.  Each adds λ_j·h_j to the reconstruction.
    for h, lam, _hyp in equalities:
        recon += sp.sympify(lam) * sp.sympify(h)
        checks += 1  # counts the multiplier's exact contribution

    if sp.expand(p - recon) != 0:
        raise ValueError(
            f"putinar instance '{name}' REFUSED: certificate does not reconstruct "
            f"the target — p - (σ_0 + Σ σ_i g_i + Σ λ_j h_j) = "
            f"{sp.expand(p - recon)}"
        )
    checks += 1  # the exact identity

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, list(sigma0), list(constraints), list(equalities)),
    )
    return inst, checks


@dataclass
class ConstrainedSOSEmitter(Emitter):
    """Emit `0 ≤ p` on `{g_i ≥ 0}` from a Putinar certificate `p = σ_0 + Σ σ_i g_i`.

    One theorem per instance; the constraint hypotheses become binders, the SOS
    multipliers are discharged by `positivity`, paired with the constraint
    hypotheses by `mul_nonneg`, and summed by `linarith`.  Deterministic
    ordering: grid order, then constraints as supplied."""

    def __post_init__(self):
        self.kind = "putinar"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            payload = inst.payload  # type: ignore[misc]
            if len(payload) == 4:
                p, sigma0, constraints, equalities = payload
            else:
                p, sigma0, constraints = payload
                equalities = []
            p_s = expr_lean(sp.expand(p), syms)

            def _render_sos(terms):
                parts = [f"{rat_lean(sp.nsimplify(c))} * ({expr_lean_raw(sp.sympify(b), syms)})^2"
                         for c, b in terms]
                return " + ".join(parts) if parts else "0"

            sigma0_s = _render_sos(sigma0)
            # inequality hypotheses: (name, g_rendered, sigma_rendered)
            cons = []
            for g, sigma_i, hyp in constraints:
                cons.append((hyp, expr_lean(sp.expand(sp.sympify(g)), syms),
                             _render_sos(sigma_i)))
            # equality hypotheses: (name, h_rendered, lambda_rendered) — λ is a
            # free polynomial (any sign), rendered with expr_lean, and its
            # product with h vanishes because h = 0 on the variety.
            eqs = []
            for h, lam, hyp in equalities:
                eqs.append((hyp, expr_lean(sp.expand(sp.sympify(h)), syms),
                            expr_lean(sp.expand(sp.sympify(lam)), syms)))

            hyp_arrows = ("".join(f" (0:ℝ) ≤ {gs} →" for _h, gs, _s in cons)
                          + "".join(f" {hs} = 0 →" for _h, hs, _l in eqs))
            intro_hyps = " ".join([h for h, _g, _s in cons] + [h for h, _hs, _l in eqs])

            haves = []
            summands = []
            if sigma0:
                haves.append(f"  have t0 : (0:ℝ) ≤ {sigma0_s} := by positivity")
                summands.append(sigma0_s)
            for i, (h, gs, ss) in enumerate(cons, start=1):
                term = f"({ss}) * ({gs})"
                haves.append(
                    f"  have t{i} : (0:ℝ) ≤ {term} := mul_nonneg (by positivity) {h}")
                summands.append(term)
            for j, (h, hs, ls) in enumerate(eqs, start=1):
                term = f"({ls}) * ({hs})"
                haves.append(
                    f"  have e{j} : {term} = 0 := by rw [{h}]; ring")
                summands.append(term)
            rhs = " + ".join(summands) if summands else "0"

            eqnote = " + Σ λ_j·h_j (free multipliers on the equality variety)" if eqs else ""
            lines.append(
                f"-- {inst.lean_name}: Putinar certificate  p = σ_0 + Σ σ_i·g_i"
                f"{eqnote} on the constraint set.\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{hyp_arrows} "
                f"(0:ℝ) ≤ {p_s} := by\n"
                f"  intro {binder} {intro_hyps}\n"
                + "\n".join(haves) + "\n"
                f"  have hid : ({p_s} : ℝ) = {rhs} := by ring\n"
                f"  rw [hid]; linarith\n"
            )
            n += 1
        return "\n".join(lines), n


def putinar_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a constrained-SOS / Putinar family (kind='putinar').

    Parameters
    ----------
    symbols
        The free real variables `p` and the constraints are polynomials in.
    spec
        A callable ``pt -> (p, sigma0, constraints)`` where ``p`` is the target
        polynomial (claim ``0 ≤ p`` on the set), ``sigma0`` a list of
        ``(coef, base)`` sum-of-squares terms for σ_0, and ``constraints`` a list
        of ``(g_i, sigma_i, hyp_name)`` giving each constraint ``g_i ≥ 0``, its
        SOS multiplier σ_i (same ``(coef, base)`` shape), and the Lean hypothesis
        name.  ``certify_putinar_point`` verifies ``p = σ_0 + Σ σ_i g_i`` exactly
        with all coefficients nonnegative, and refuses otherwise — no Lean is
        emitted for a certificate that fails to reconstruct the target.

        FINDER mode: return ``sigma0 = None`` (with each constraint's ``sigma_i``
        also ``None``) and Telperion SEARCHES for the SOS multipliers itself
        (`find_putinar_certificate`, a numeric SDP rounded to EXACT rationals) —
        upgrading the emitter from "you supply the multipliers" to "you supply
        the constraint set."  The relaxation order is taken from
        ``constants['putinar_half_deg']`` when set (default: ⌈deg p / 2⌉).
        Either way ``certify_putinar_point`` re-verifies the identity exactly.
    """
    if not tuple(symbols):
        raise ValueError("Putinar families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("putinar", spec),
        constants=dict(constants or {}),
    )

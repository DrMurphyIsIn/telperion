"""Rational domination-ratio emitter — a template dominates a competitor via an
all-nonneg-coefficient rational ratio ``r(params) = P/Q ≥ 1`` on a parameter box.

The MULTIVARIATE-ENVELOPE generalization of the shipped finite-argmax margin
(``emit_finite_argmax`` — the finite, constant, one-cross-multiplication case).
There a designated winner rational ``p_w/q_w`` strictly beats a finite list of
CONSTANT competitor rationals ``p_i/q_i`` via the single integer cross-mult
``p_i·q_w < p_w·q_i``.  Here the winner-vs-competitor margin is itself a
FUNCTION of a multivariate parameter family: a template ``T_tmpl`` dominates a
competitor ``T`` — ``Φ(T) ≤ Φ(T_tmpl)`` — via a rational ratio

    r(params) = P(params) / Q(params) ≥ 1                       (Q > 0)

with ``P, Q`` polynomials carrying ALL-NONNEGATIVE coefficients over a box
``∏_i [l_i, u_i]``.  Cross-multiplying (no division, ``Q > 0``) reduces the
claim to the polynomial box-positivity fact

    P(params) − Q(params) ≥ 0     on the box                    (⇒ r ≥ 1).

This emitter certifies exactly that.  It handles the tractable case the roadmap
calls out — ``D := P − Q`` MULTI-AFFINE (degree ≤ 1 in each parameter) — via the
corner principle generalizing ``emit_bilinear_corner`` to ``k`` variables: a
multi-affine ``D`` on a box attains its minimum at one of the ``2^k`` corners, so

    D(corner) ≥ 0  for every corner   ⟹   D(params) ≥ 0  on the box.

The exact witness is the convex-combination identity (``multilinear_corner``)

    D(g)·∏_i(u_i−l_i) = Σ_corner (∏_i wnum_i^{corner_i})·D(corner),

``wnum_i^{lo}=u_i−g_i ≥ 0``, ``wnum_i^{hi}=g_i−l_i ≥ 0`` on the box; every
weight-product times its (nonneg) corner value is nonneg, and ``∏(u_i−l_i)>0``
gives ``D ≥ 0``.  ``domination_ratio_certificate`` sympy-checks (i) ``Q > 0`` on
the box (all-nonneg coeffs + a positive constant term, or every corner ``Q``
value ``> 0``), (ii) ``D = P − Q`` multi-affine, and (iii) every corner value of
``D`` is ``≥ 0``; it RAISES ``ValueError`` (the anti-phantom negative control)
if the ratio is NOT ``≥ 1`` somewhere on the box (a negative ``D`` corner) or the
box is degenerate.

EMITTED LEAN (per instance): denominators cleared up front, then the
``k``-variable corner-principle bridge (``nlinarith`` on the sign-cased
``mul_nonneg`` corner products, exactly as ``multilinear_corner`` / the h_floors
``bilinear_corner_nonneg`` pattern do):

    theorem <name> (x_1 … x_k : ℝ)
        (hl_i : l_i ≤ x_i) (hu_i : x_i ≤ u_i) … :
        Q params ≤ P params := by
      … (corner products, convex-combination identity, nlinarith) …

``Q ≤ P`` is the cross-multiplied ``r ≥ 1``; with ``Q > 0`` it is the ratio.
Bare rational literals are ℝ-ascribed.  ``import Mathlib``; namespaced.

HONEST SCOPE: this proves ONLY ``P − Q ≥ 0`` on the given box for a multi-affine
``P − Q`` with the supplied all-nonneg-coeff ``P, Q`` — i.e. the rational ratio
``r = P/Q ≥ 1`` there.  It does not prove ``Φ(T) ≤ Φ(T_tmpl)`` for any specific
``Φ`` (the caller supplies ``P, Q`` as the already-extracted ratio numerator and
denominator), nor does it close any downstream BG/RH obligation.
conjecture1_proved=False.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_domination_ratio.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


def _is_multi_affine(P: sp.Expr, gens: Sequence[sp.Symbol]) -> bool:
    """True iff ``P`` has degree ≤ 1 in each generator (affine-in-each)."""
    poly = sp.Poly(sp.expand(P), *gens)
    return all(all(e <= 1 for e in monom) for monom in poly.monoms())


def _all_coeffs_nonneg(P: sp.Expr, gens: Sequence[sp.Symbol]) -> bool:
    """True iff every monomial coefficient of ``P`` (in ``gens``) is ≥ 0."""
    poly = sp.Poly(sp.expand(P), *gens)
    return all(sp.Rational(c) >= 0 for c in poly.coeffs())


@dataclass(frozen=True)
class DominationRatioCertificate:
    """A verified rational domination-ratio certificate ``r = P/Q ≥ 1`` on a box.

    ``P``, ``Q`` are all-nonneg-coefficient polynomials in ``gens`` over the box
    ``∏_i [l_i, u_i]`` (``box[g] = (l, u)``), ``Q > 0`` on the box, and
    ``D := P − Q`` is multi-affine with every corner value ≥ 0 — so ``P ≥ Q``,
    i.e. ``r ≥ 1``, on the box.  The certified data are the corner values of
    ``D`` and the convex-combination identity witness."""

    P: sp.Expr
    Q: sp.Expr
    gens: tuple                       # (x_1, …, x_k)
    box: tuple                        # ((l_1, u_1), …, (l_k, u_k)), rationals
    corners: tuple                    # ((corner_key, D_value), …) over {lo,hi}^k
    q_corners: tuple                  # ((corner_key, Q_value), …) — all > 0


def domination_ratio_certificate(
    P, Q, gens: Sequence[sp.Symbol], box: Sequence[Sequence]
) -> DominationRatioCertificate:
    """Build and EXACTLY self-check a domination-ratio certificate ``P/Q ≥ 1``.

    ``P``, ``Q``: sympy polynomials in ``gens`` with all-nonnegative coefficients.
    ``box``: a sequence of ``(l_i, u_i)`` rational endpoints, one per generator.

    Verifies (all exact, in sympy): ``P, Q`` all-nonneg-coeff; the box
    non-degenerate (``l_i < u_i``); ``Q`` strictly positive at every corner (⇒
    ``Q > 0`` on the box, since a nonneg-coeff multilinear-or-higher poly is
    corner-minimized only downward — we require positivity at all corners for a
    rigorous, tactic-checkable ``Q > 0``); ``D = P − Q`` MULTI-AFFINE; and every
    corner value of ``D`` is ``≥ 0``.  RAISES ``ValueError`` (the negative
    control) if the ratio dips below 1 anywhere on the box (some ``D`` corner
    ``< 0``), if ``Q`` is not corner-positive, or if the box is degenerate."""
    P = sp.expand(sp.sympify(P))
    Q = sp.expand(sp.sympify(Q))
    gens = tuple(gens)
    box = tuple((sp.nsimplify(l), sp.nsimplify(u)) for (l, u) in box)
    if len(box) != len(gens):
        raise ValueError(
            f"REFUSED: box has {len(box)} intervals but {len(gens)} generators"
        )
    for i, (l, u) in enumerate(box):
        if u <= l:
            raise ValueError(
                f"REFUSED: degenerate box interval {i}: l={l} </ u={u}"
            )
    if not _all_coeffs_nonneg(P, gens):
        raise ValueError("REFUSED: P has a negative coefficient (not all-nonneg)")
    if not _all_coeffs_nonneg(Q, gens):
        raise ValueError("REFUSED: Q has a negative coefficient (not all-nonneg)")

    D = sp.expand(P - Q)
    if not _is_multi_affine(D, gens):
        raise ValueError(
            "REFUSED: P - Q is not multi-affine (degree > 1 in some parameter); "
            "outside the tractable corner-dispatch case"
        )

    # Q > 0 on the box: check every corner value of Q is strictly positive.
    q_corners = []
    for corner in itertools.product(*[("lo", "hi")] * len(gens)):
        subs = {g: box[i][0 if c == "lo" else 1] for i, (g, c) in enumerate(zip(gens, corner))}
        qv = sp.nsimplify(sp.expand(Q.subs(subs)))
        if not (qv > 0):
            raise ValueError(
                f"REFUSED: Q corner {corner} value = {qv} is not > 0; "
                f"denominator not certifiably positive on the box"
            )
        q_corners.append((corner, qv))

    # D = P - Q >= 0 on the box <=> every corner value of D >= 0 (multi-affine).
    corners = []
    for corner in itertools.product(*[("lo", "hi")] * len(gens)):
        subs = {g: box[i][0 if c == "lo" else 1] for i, (g, c) in enumerate(zip(gens, corner))}
        dv = sp.nsimplify(sp.expand(D.subs(subs)))
        if not (dv >= 0):
            raise ValueError(
                f"REFUSED: D = P - Q corner {corner} value = {dv} < 0; "
                f"ratio P/Q < 1 there — NOT a domination ratio"
            )
        corners.append((corner, dv))

    # Exact convex-combination identity self-check:
    #   D(g)*prod(u_i - l_i) = sum_corner (prod wnum_i^{corner_i}) * D(corner).
    los = [box[i][0] for i in range(len(gens))]
    his = [box[i][1] for i in range(len(gens))]
    Dfac = sp.prod([his[i] - los[i] for i in range(len(gens))])
    rhs = 0
    for corner, dv in corners:
        wnum = sp.prod([
            (his[i] - gens[i]) if corner[i] == "lo" else (gens[i] - los[i])
            for i in range(len(gens))
        ])
        rhs += sp.expand(wnum) * dv
    if sp.expand(D * Dfac - rhs) != 0:
        raise ValueError(
            "REFUSED: convex-combination identity self-check failed "
            "(D*prod != sum of weighted corners)"
        )

    return DominationRatioCertificate(
        P=P, Q=Q, gens=gens, box=box,
        corners=tuple(corners), q_corners=tuple(q_corners),
    )


def certify_domination_ratio_point(family, pt, name):
    """Certify one domination-ratio instance from
    ``family.special[1](pt) -> (P, Q, box)`` (``gens`` from ``family.symbols``).

    ``box`` is a sequence of ``(l_i, u_i)`` endpoints, one per symbol.  Returns
    ``(CertifiedInstance, n_checks)`` — one check (the box-positivity theorem)."""
    spec = family.special[1](pt)
    P, Q, box = spec[0], spec[1], spec[2]
    cert = domination_ratio_certificate(P, Q, family.symbols, box)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def _lean_poly(e: sp.Expr, gens: Sequence[sp.Symbol]) -> str:
    """Render a polynomial as Lean source (``**`` -> ``^``), gens as bare names."""
    return str(sp.expand(e)).replace("**", "^")


@dataclass
class RecursiveDominationRatioEmitter(Emitter):
    """Emit ``Q params ≤ P params`` (the cross-multiplied ``r = P/Q ≥ 1``) on a
    parameter box, for a multi-affine ``D = P − Q``, via the ``k``-variable
    corner principle: corner products (``mul_nonneg``), the convex-combination
    identity (``ring``), and ``nlinarith`` — the generalization of the proven
    ``emit_bilinear_corner`` ``bilinear_corner_nonneg`` pattern to ``k`` vars.

    One self-contained theorem per instance (no shared prelude lemma — the box
    endpoints are concrete rationals, so each corner value closes by ``ring``/
    ``nlinarith`` directly)."""

    def __post_init__(self):
        self.kind = "domination_ratio"

    def _instance_text(self, cert: DominationRatioCertificate, lean_name: str) -> str:
        gens = cert.gens
        k = len(gens)
        gnames = [str(g) for g in gens]
        los = [cert.box[i][0] for i in range(k)]
        his = [cert.box[i][1] for i in range(k)]
        los_l = [rat_lean(l) for l in los]
        his_l = [rat_lean(u) for u in his]

        P_l = _lean_poly(cert.P, gens)
        Q_l = _lean_poly(cert.Q, gens)
        D_l = _lean_poly(sp.expand(cert.P - cert.Q), gens)

        binders = " ".join(gnames)
        # box hypotheses  hl_i : l_i ≤ x_i,  hu_i : x_i ≤ u_i
        hyps = "".join(
            f"    (hl{i} : {los_l[i]} ≤ {gnames[i]}) (hu{i} : {gnames[i]} ≤ {his_l[i]})\n"
            for i in range(k)
        )

        lines: list[str] = []
        lines.append(
            f"theorem {lean_name} ({binders} : ℝ)\n"
            f"{hyps}"
            f"    : {Q_l} ≤ {P_l} := by\n"
        )
        # per-generator nonneg brackets from the box
        for i in range(k):
            lines.append(
                f"  have hg{i} : (0:ℝ) ≤ {gnames[i]} - {los_l[i]} := by linarith\n"
            )
            lines.append(
                f"  have hh{i} : (0:ℝ) ≤ {his_l[i]} - {gnames[i]} := by linarith\n"
            )
        # corner products: weight-numerator * corner-value, each nonneg
        corners = list(itertools.product(*[("lo", "hi")] * k))
        # map corner -> D value from cert
        dvals = {c: dv for c, dv in cert.corners}
        prod_names: list[str] = []
        for j, corner in enumerate(corners):
            fac_names = [f"hh{i}" if corner[i] == "lo" else f"hg{i}" for i in range(k)]
            nested = fac_names[0]
            for nm in fac_names[1:]:
                nested = f"(mul_nonneg {nested} {nm})"
            wnum_fac = "*".join(
                f"({his_l[i]} - {gnames[i]})" if corner[i] == "lo"
                else f"({gnames[i]} - {los_l[i]})"
                for i in range(k)
            )
            dv = dvals[corner]
            lines.append(
                f"  have hw{j} : (0:ℝ) ≤ {wnum_fac} := {nested}\n"
            )
            lines.append(
                f"  have hq{j} : (0:ℝ) ≤ ({wnum_fac}) * ({rat_lean(dv)}) := "
                f"mul_nonneg hw{j} (by norm_num)\n"
            )
            prod_names.append(f"hq{j}")
        # convex-combination identity D * prod(u-l) = sum weighted corners
        Dfac = "*".join(f"({his_l[i]} - {los_l[i]})" for i in range(k))
        rhs_terms = []
        for corner in corners:
            wnum_fac = "*".join(
                f"({his_l[i]} - {gnames[i]})" if corner[i] == "lo"
                else f"({gnames[i]} - {los_l[i]})"
                for i in range(k)
            )
            rhs_terms.append(f"({wnum_fac}) * ({rat_lean(dvals[corner])})")
        rhs = " + ".join(rhs_terms)
        lines.append(
            f"  have hid : ({D_l}) * ({Dfac}) = {rhs} := by ring\n"
        )
        # D > 0 factor positivity: prod(u_i - l_i) > 0
        dpos = [f"(by norm_num : (0:ℝ) < {his_l[i]} - {los_l[i]})" for i in range(k)]
        dnested = dpos[0]
        for dp in dpos[1:]:
            dnested = f"(mul_pos {dnested} {dp})"
        lines.append(f"  have hd : (0:ℝ) < {Dfac} := {dnested}\n")
        lines.append(
            f"  nlinarith [hid, hd, {', '.join(prod_names)}]\n"
        )
        return "".join(lines)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: DominationRatioCertificate = inst.payload  # type: ignore[assignment]
            k = len(cert.gens)
            lines.append(
                f"-- Domination ratio r = P/Q ≥ 1 on a {k}-parameter box "
                f"(cross-multiplied to Q ≤ P; D = P - Q multi-affine, "
                f"corner-dispatched).\n"
            )
            lines.append(self._instance_text(cert, inst.lean_name))
            nthm += 1
        return "".join(lines), nthm


def domination_ratio_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a domination-ratio family (kind='domination_ratio').

    Parameters
    ----------
    symbols
        The free (real) parameters ``P, Q`` are polynomials in.
    spec
        A callable ``pt -> (P, Q, box)`` where ``P, Q`` are sympy polynomials
        with all-nonnegative coefficients, ``box`` is a sequence of ``(l_i,u_i)``
        rational endpoints (one per symbol), ``Q > 0`` at every corner, and
        ``P − Q`` is multi-affine with every corner value ≥ 0.  Refuses (at
        certification) otherwise — in particular a ratio that dips below 1
        anywhere on the box (a negative ``P − Q`` corner).
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("domination_ratio", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid certs, negative control, print emitted Lean ----------
    x, y = sp.symbols("x y")

    print("=== positive: 2-param multi-affine ratio, r = P/Q ≥ 1 on [0,1]^2 ===")
    # Q = 1 + x + y + x*y = (1+x)(1+y);  P = Q + (x + y + x*y)  (extra nonneg mass)
    #   D = P - Q = x + y + x*y, multi-affine, corners {0,1,3,...} all ≥ 0.
    Q = 1 + x + y + x * y
    P = 2 + 2 * x + 2 * y + 2 * x * y
    cert = domination_ratio_certificate(P, Q, (x, y), ((0, 1), (0, 1)))
    print(f"  cert OK: P={cert.P}, Q={cert.Q}, "
          f"corners(D)={[str(v) for _, v in cert.corners]}")

    print("\n=== positive: genuine mixed-slope multi-affine D (1 template beats) ===")
    # D = P - Q = 3 - x - 2y + x*y on [0,1]^2: corners 3,1,2,1 (all ≥ 0), NOT monotone.
    # Build P, Q both nonneg-coeff with that difference:
    Q2 = 2 + x + 2 * y            # nonneg coeffs
    P2 = 5 + x * y                # P2 - Q2 = 3 - x - 2y + x*y ; P2 nonneg coeffs
    assert sp.expand(P2 - Q2) == sp.expand(3 - x - 2 * y + x * y)
    cert2 = domination_ratio_certificate(P2, Q2, (x, y), ((0, 1), (0, 1)))
    print(f"  cert OK: P={cert2.P}, Q={cert2.Q}, "
          f"corners(D)={[str(v) for _, v in cert2.corners]}")

    print("\n=== positive: 1-param linear ratio r = P/Q ≥ 1 on [1,2] ===")
    # Q = x, P = 2*x  =>  D = x ≥ 0 on [1,2]; r = 2 ≥ 1.
    cert3 = domination_ratio_certificate(2 * x, x, (x,), ((1, 2),))
    print(f"  cert OK: P={cert3.P}, Q={cert3.Q}, "
          f"corners(D)={[str(v) for _, v in cert3.corners]}")

    print("\n=== NEGATIVE CONTROL: ratio < 1 somewhere on the box (expect ValueError) ===")
    try:
        # D = P - Q = x - 1 on [0,1]: at x=0, D=-1 < 0  => r = P/Q < 1 there.
        domination_ratio_certificate(1 + x, 2, (x,), ((0, 1),))
        raise SystemExit("FAIL: sub-1 ratio was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: negative coefficient in P (expect ValueError) ===")
    try:
        domination_ratio_certificate(3 - x, 1, (x,), ((0, 1),))
        raise SystemExit("FAIL: negative coefficient was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: degenerate box (expect ValueError) ===")
    try:
        domination_ratio_certificate(2 * x, x, (x,), ((1, 1),))
        raise SystemExit("FAIL: degenerate box was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: Q not corner-positive (expect ValueError) ===")
    try:
        # Q = x, box [0,1]: at x=0, Q=0, not > 0.
        domination_ratio_certificate(2 * x, x, (x,), ((0, 1),))
        raise SystemExit("FAIL: non-positive Q corner was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (three instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="dr_two_param",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="dr_mixed_slope",
                          corners=(), payload=cert2),
        CertifiedInstance(point={"case": 2}, lean_name="dr_one_param",
                          corners=(), payload=cert3),
    ]

    class _View:
        instances = insts

    body, nthm = RecursiveDominationRatioEmitter().emit_body(
        _View(), LeanProfile(namespace=("DominationRatio",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)

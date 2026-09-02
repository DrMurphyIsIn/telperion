"""Order-balance boundary-contradiction emitter (the integer zero/pole-order hinge
at the 1-line, `ζ(1+it) ≠ 0`).

The finite INTEGER/LINEAR hinge at the heart of the classical de la Vallee Poussin
boundary argument, isolated exactly as `zeta_boundary_contradiction`
(examples/zero_free_bridge/lean/ZeroFreeBridge.lean) isolates its own `3·1 − 4k − k'
≥ 0 ⟹ False` step.  There the residue limits at `1, 1+it, 1+2it` are HYPOTHESES
(`hpole/hz1/hz2`); the kernel-checked content is the tiny linear-arithmetic
collapse `3 − 4k − k' ≤ -1 < 0`.  This emitter GENERALIZES that hinge to any
nonnegative-cosine weight vector and any integer zero-orders.

THE MATH.  A pointwise-nonnegative cosine polynomial `P(φ) = Σ_{j<N} a_j cos(jφ)`
with weights `a_j ≥ 0` (rationals) feeds, for `Re s > 1`, the positivity
`0 ≤ Σ_j a_j · Re(-ζ'/ζ)(σ + i j t)` (the `cosine_comb_zeta_nonneg` layer).
Multiply by `(σ-1) > 0`, take `σ → 1⁺`; each residue limit is:

  * the pole at `s = 1`  contributes the fixed  `+a₀·1`   (simple pole, residue +1);
  * a zero of order `k_j ≥ 1` at `1 + i j t`  contributes  `-a_j·k_j`;
  * points with no forced zero/pole contribute `≤ 0` (order `≥ 0`, sign `-`).

`ge_of_tendsto` on the nonnegative pre-limit forces

    0  ≤  a₀·1  −  Σ_{j≥1} a_j·k_j        i.e.        a₀  ≥  Σ_{j≥1} a_j·k_j.

The certificate is the finite integer/linear FACT that this order balance is
STRICTLY VIOLATED:  with the supplied weights and orders (`a_j ≥ 0`, `k_j ≥ 1`),

    a₀  <  Σ_{j≥1} a_j·k_j                                 [order_balance hinge]

so `0 ≤ a₀ − Σ a_j k_j < 0` — a contradiction — and no such zero can exist on
`Re = 1`.  (The classical dVP case is `(a₀,a₁,a₂) = (3,4,1)`, `k₁ ≥ 1`, `k₂ ≥ 0`:
`3 < 4·1 = 4`, exactly `zeta_boundary_contradiction`.)

WHY THIS IS A CERTIFICATE (not a template).  Telperion is the CHECKER; the
generator is UNTRUSTED.  `order_balance_certificate` re-derives, EXACTLY in sympy
over the rationals, that `a₀ < Σ_{j≥1} a_j·k_j`, and RAISES `ValueError` (the
anti-phantom negative control) when the balance is NOT violated (`a₀ ≥ Σ a_j k_j`
— no contradiction), when any weight is `< 0`, or when any zero order is `< 1`.
No Lean is written for a non-certificate.

EMITTED LEAN (per instance) mirrors `zeta_boundary_contradiction`'s proof
skeleton: the residue LIMITS `P_j` are abstract-real HYPOTHESES (their zeta
meaning — the real-line restriction of `residue_logDeriv`, i.e. `(z-z0)·logDeriv
ζ → order` — is supplied elsewhere), plus the positivity hypothesis
`0 ≤ Σ a_j·P_j`, the pole limit `P₀ = 1`, and the polar bounds `P_j ≤ -k_j`
(`j ≥ 1`, an order-`k_j` zero).  The conclusion is `False`, closed by `linarith`.
Bare rational literals are ascribed `: ℝ` (the ℤ-default pitfall that cost a build
round in a sibling emitter); the integer-order facts `k_j ≥ 1` ride in as ℝ
inequalities via `exact_mod_cast`, exactly as in the model.

HONEST SCOPE.  This is the `c = 0` BOUNDARY hinge (`ζ(1+it) ≠ 0`, already in
Mathlib) — it FEEDS the classical zero-free region, does NOT improve the
Vinogradov-Korobov rate, and is NOT a proof of RH.  The analysis (residue limits
from `residue_logDeriv`, the cosine positivity) is kept as HYPOTHESES; the emitter
certifies ONLY the finite integer/linear order-balance hinge.  conjecture1_proved
= False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_order_balance.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class OrderBalanceCertificate:
    """A verified order-balance boundary-contradiction certificate.

    ``weights`` are the nonnegative cosine coefficients ``(a₀, a₁, …, a_m)``
    (rationals ``≥ 0``); ``a₀`` is the pole (residue ``+a₀·1``) term.  ``orders``
    are the integer zero orders ``(k₁, …, k_m)`` at the shifted points ``1 + i j t``
    (each ``k_j ≥ 1``).  The certified fact is the strict order-balance violation

        a₀  <  Σ_{j≥1} a_j·k_j

    — the finite linear hinge that forces the ``ζ(1+it) ≠ 0`` contradiction (the
    Lean re-checks it by ``linarith`` off abstract residue-limit hypotheses).
    """

    weights: tuple[sp.Rational, ...]       # (a0, a1, …, a_m), each ≥ 0; a0 = pole term
    orders: tuple[sp.Integer, ...]         # (k1, …, k_m), each ≥ 1
    balance_deficit: sp.Rational           # (Σ_{j≥1} a_j·k_j) − a0  > 0  (strict margin)


def order_balance_certificate(weights, orders) -> OrderBalanceCertificate:
    """Build and EXACTLY self-check an order-balance certificate.

    ``weights`` is ``(a₀, a₁, …, a_m)`` (rationals ``≥ 0``, ``a₀`` the pole term);
    ``orders`` is ``(k₁, …, k_m)`` (integers ``≥ 1``), one per non-pole weight.
    Refuses (``ValueError``) when the lengths mismatch, when any weight is ``< 0``,
    when any order is ``< 1`` (not a genuine zero), or when the order balance is NOT
    strictly violated (``a₀ ≥ Σ_{j≥1} a_j·k_j`` — no contradiction; the anti-phantom
    negative control)."""
    ws = tuple(sp.nsimplify(w) for w in weights)
    for w in ws:
        if not w.is_rational:
            raise ValueError(f"order_balance needs rational weights; got {w!r}")
    ws = tuple(sp.Rational(w) for w in ws)
    if len(ws) < 2:
        raise ValueError(
            "REFUSED: need a pole weight a0 plus at least one non-pole weight "
            f"(got {len(ws)} weight(s))"
        )
    ks = tuple(sp.nsimplify(k) for k in orders)
    for k in ks:
        if k != int(k):
            raise ValueError(f"REFUSED: zero order {k} is not an integer")
    ks = tuple(sp.Integer(int(k)) for k in ks)

    if len(ks) != len(ws) - 1:
        raise ValueError(
            f"REFUSED: got {len(ws)} weights (a0 + {len(ws) - 1} non-pole) but "
            f"{len(ks)} orders; need one order per non-pole weight"
        )

    a0 = ws[0]
    if a0 < 0:
        raise ValueError(f"REFUSED: pole weight a0 = {a0} < 0")
    for j, aj in enumerate(ws[1:], start=1):
        if aj < 0:
            raise ValueError(f"REFUSED: weight a{j} = {aj} < 0 (nonneg-cosine required)")
    for j, kj in enumerate(ks, start=1):
        if kj < 1:
            raise ValueError(
                f"REFUSED: zero order k{j} = {kj} < 1 (not a genuine zero; no residue drop)"
            )

    # EXACT order-balance self-check: the contradiction needs a0 < Σ_{j≥1} a_j·k_j.
    rhs = sp.Rational(0)
    for aj, kj in zip(ws[1:], ks):
        rhs += aj * kj
    deficit = sp.Rational(rhs - a0)
    if not (deficit > 0):
        raise ValueError(
            f"REFUSED: order balance is NOT violated — a0 = {a0} ≥ Σ a_j·k_j = {rhs}; "
            f"no boundary contradiction (deficit {deficit} </ 0). Certificate rejected."
        )

    return OrderBalanceCertificate(weights=ws, orders=ks, balance_deficit=deficit)


def certify_order_balance_point(family, pt, name):
    """Certify one order-balance instance from ``family.special[1](pt) -> spec``.

    ``spec`` is either ``(weights, orders)`` or a dict
    ``{"weights": (...), "orders": (...)}``.  Returns
    ``(CertifiedInstance, n_checks)`` with ``n_checks = 1`` (the single exact
    order-balance strict-violation self-check)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = order_balance_certificate(spec["weights"], spec["orders"])
    else:
        cert = order_balance_certificate(spec[0], spec[1])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class OrderBalanceEmitter(Emitter):
    """Emit the order-balance boundary contradiction: from abstract residue-limit
    hypotheses ``P_j`` (their zeta meaning supplied elsewhere), the positivity
    ``0 ≤ Σ a_j·P_j``, the pole limit ``P₀ = 1``, and the polar bounds
    ``P_j ≤ -k_j`` (order-``k_j`` zero, ``j ≥ 1``), derive ``False`` by ``linarith``.

    Mirrors the PROVEN ``zeta_boundary_contradiction`` hinge
    (examples/zero_free_bridge): the `3·1 − 4k − k' ≥ 0 ⟹ False` step, generalized
    to any nonnegative-cosine weights and integer zero orders.  ℝ ascribed on bare
    rational literals; integer orders enter as ℝ inequalities."""

    def __post_init__(self):
        self.kind = "order_balance"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: OrderBalanceCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            ws = cert.weights
            ks = cert.orders
            m = len(ks)  # number of non-pole shifts (j = 1..m)
            a0 = rat_lean(ws[0])

            # binders: the abstract residue limits P0..Pm (reals) and integer orders k1..km.
            p_binders = " ".join(f"P{j}" for j in range(m + 1))
            k_binders = " ".join(f"k{j}" for j in range(1, m + 1))
            # positivity hypothesis: 0 ≤ Σ_j a_j·P_j.
            pos_terms = " + ".join(f"{rat_lean(ws[j])} * P{j}" for j in range(m + 1))
            # per-order hypotheses: k_j ≥ 1 (as ℤ) and the polar bound P_j ≤ -(k_j : ℝ).
            k_ge_hyps = " ".join(f"(hk{j} : 1 ≤ k{j})" for j in range(1, m + 1))
            bound_hyps = " ".join(
                f"(hb{j} : P{j} ≤ -(k{j} : ℝ))" for j in range(1, m + 1)
            )

            # weights / orders summary comment.
            wsum = ", ".join(str(w) for w in ws)
            ksum = ", ".join(str(k) for k in ks)
            rhs_val = ", ".join(f"a{j}·k{j}" for j in range(1, m + 1))

            lines.append(
                f"/-- ORDER-BALANCE BOUNDARY CONTRADICTION (weights a = ({wsum}); "
                f"orders k = ({ksum})),\n"
                f"    the finite integer/linear hinge of the classical dVP boundary "
                f"`ζ(1+it) ≠ 0`, generalized\n"
                f"    from `zeta_boundary_contradiction` (examples/zero_free_bridge).  "
                f"The residue LIMITS `P_j`\n"
                f"    are abstract reals (real-line `residue_logDeriv`: "
                f"`(z-z₀)·logDeriv ζ → order`, supplied\n"
                f"    elsewhere); from the cosine positivity `0 ≤ Σ a_j·P_j`, the pole "
                f"`P₀ = 1`, and the\n"
                f"    order-`k_j` polar bounds `P_j ≤ -k_j` (j ≥ 1), the order balance "
                f"`a₀ ≥ Σ {rhs_val}` is\n"
                f"    forced — but the certificate has `a₀ < Σ a_j·k_j` "
                f"(deficit {cert.balance_deficit} > 0), so `False`.\n"
                f"    Boundary (c=0) hinge only; FEEDS the classical region, NOT a "
                f"proof of RH. -/\n"
            )
            # theorem signature
            lines.append(
                f"theorem {base} ({p_binders} : ℝ) "
                f"({' '.join(f'k{j}' for j in range(1, m + 1))} : ℤ)\n"
                f"    {k_ge_hyps}\n"
                f"    (hpos : (0 : ℝ) ≤ {pos_terms})\n"
                f"    (hpole : P0 = 1)\n"
                f"    {bound_hyps} :\n"
                f"    False := by\n"
            )
            # proof body: cast each k_j ≥ 1 to ℝ, substitute pole, close by linarith.
            for j in range(1, m + 1):
                lines.append(
                    f"  have hk{j}r : (1 : ℝ) ≤ (k{j} : ℝ) := by exact_mod_cast hk{j}\n"
                )
            # linarith gets: hpos, hpole, all hb_j, all hk_jr.
            lin_facts = ", ".join(
                ["hpos", "hpole"]
                + [f"hb{j}" for j in range(1, m + 1)]
                + [f"hk{j}r" for j in range(1, m + 1)]
            )
            lines.append(f"  linarith [{lin_facts}]\n")
            nthm += 1
        return "".join(lines), nthm


def order_balance_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an order-balance boundary-contradiction family (kind='order_balance').

    ``spec``: a callable ``pt -> (weights, orders)`` (or
    ``pt -> {"weights": (...), "orders": (...)}``), where ``weights`` is
    ``(a₀, a₁, …, a_m)`` (rationals ``≥ 0``, ``a₀`` the pole term) and ``orders`` is
    ``(k₁, …, k_m)`` (integers ``≥ 1``).  Refuses (at certification) a length
    mismatch, a negative weight, an order ``< 1``, or a non-violated order balance
    (``a₀ ≥ Σ a_j·k_j``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("order_balance", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- positive: the classical dVP 3-4-1 boundary case -------------------------
    print("=== positive: classical dVP (a=(3,4,1); orders k=(1,1)) — 3 < 4·1+1·1=5 ===")
    cert = order_balance_certificate((3, 4, 1), (1, 1))
    print(
        f"  cert OK: weights={tuple(str(w) for w in cert.weights)}, "
        f"orders={tuple(int(k) for k in cert.orders)}, deficit={cert.balance_deficit}"
    )

    print("\n=== positive: minimal dVP hinge (a=(3,4); single order k=(1,)) — 3 < 4 ===")
    cert_min = order_balance_certificate((3, 4), (1,))
    print(
        f"  cert OK: weights={tuple(str(w) for w in cert_min.weights)}, "
        f"orders={tuple(int(k) for k in cert_min.orders)}, deficit={cert_min.balance_deficit}"
    )

    print("\n=== positive: degree-3 Fejer (a=(20,30,12,2); orders k=(1,1,1)) — 20 < 44 ===")
    cert3 = order_balance_certificate((20, 30, 12, 2), (1, 1, 1))
    print(
        f"  cert OK: weights={tuple(str(w) for w in cert3.weights)}, "
        f"deficit={cert3.balance_deficit}"
    )

    print("\n=== NEGATIVE CONTROL: balance NOT violated (a=(5,4,1); k=(1,1)) expect ValueError ===")
    try:
        order_balance_certificate((5, 4, 1), (1, 1))  # 5 ≥ 4·1 + 1·1 = 5, tie → no contradiction
        raise SystemExit("FAIL: non-violated balance was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: a zero order k < 1 (a=(3,4); k=(0,)) expect ValueError ===")
    try:
        order_balance_certificate((3, 4), (0,))
        raise SystemExit("FAIL: order k=0 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: a negative weight (a=(3,-4); k=(1,)) expect ValueError ===")
    try:
        order_balance_certificate((3, -4), (1,))
        raise SystemExit("FAIL: negative weight was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    # --- build instances + emit Lean directly ------------------------------------
    _SPECS = {0: ((3, 4, 1), (1, 1)), 1: ((3, 4), (1,)), 2: ((20, 30, 12, 2), (1, 1, 1))}
    _NAMES = {0: "ob_dvp_341", 1: "ob_dvp_min", 2: "ob_fejer_deg3"}
    fam = order_balance_family(
        "OrderBalanceSelfTest",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1, 2):
        inst, n = certify_order_balance_point(fam, {"case": case}, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = OrderBalanceEmitter().emit_body(_View(), LeanProfile(namespace=("OrderBalance",)))
    print("\n" + "=" * 72)
    print(f"EMITTED LEAN ({nthm} theorems):")
    print("=" * 72)
    print(body)

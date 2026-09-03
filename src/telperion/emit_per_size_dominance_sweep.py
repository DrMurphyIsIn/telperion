"""BG per-size domination sweep emitter (Hdom) — a FINITE per-n sweep of configs.

This EVOLVES the ``tight_cap_enclosure`` (fixed-named-config) emitter into a
per-size FINITE SWEEP.  For a fixed size ``n`` we enumerate a finite SET of named
child-message configs (each a list of exactly ``n`` rational cavity messages μ)
and certify the Brualdi–Goldwasser g-step closure

    (baseOf l)¹¹ · prodBcap l / (W · (5/3)¹¹)  ≤  1

for EACH config in the set, then AGGREGATE the per-config faces into one theorem

    sweep_n<N> : ∀ l ∈ ([l₁, l₂, …] : List (List ℚ)), (baseOf l)¹¹·prodBcap l/(W(5/3)¹¹) ≤ 1

with the EXACT rational definitions of ``proof/formalization/R3Cert/`` (same as
tight_cap_enclosure):

    W          = 64/621
    glemma μ   = W²·(5/3)¹¹ / (1 + μ/3)¹¹
    master_ub μ= W·(3/(2+μ))¹¹
    Bcap μ     = min(master_ub μ, min(glemma μ, 1))          (three-way min)
    baseOf l   = (3(|l|+1) + 3·Σl + 1) / (3(|l|+1))          (boostR at j=|l|)
    prodBcap l = ∏_{μ∈l} Bcap μ

Each per-config face is the SAME concrete-``norm_num`` face that
``tight_cap_enclosure`` already emits and certifies; this emitter reuses that
per-config certificate (``tight_cap_enclosure_certificate`` in concrete mode) and
adds a per-size aggregation theorem dispatching to the per-config theorems via
``List.forall_mem_cons`` + ``simp``/``decide``.

HONEST SCOPE.  This closes each LISTED config at size ``n`` — a FINITE SWEEP.
It does NOT prove the enumeration is EXHAUSTIVE over all Balanced+Capped
merge-normal states of size ``n`` (that is the structural normal-form
characterization, still open); and it is PER-``n``, NOT uniform in ``n``
(uniform-in-``n`` is the arm-rate unimodality, partly in ``R47ArmRate``).  It
reuses/aggregates the ``tight_cap_enclosure`` per-config certificate — it does NOT
touch the general-arity g-lemma open core (``gV_le`` / ``gstep_lt_gamma``).  The
emitted file is self-contained (only ``import Mathlib``; the
W/glemma/master_ub/Bcap/baseOf/prodBcap defs are inlined via the reused
``_INLINE_DEFS`` prelude — it does NOT import the R3Cert project).

conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
    from .emit_tight_cap_enclosure import (
        _INLINE_DEFS,
        _lean_list,
        _lhs,
        tight_cap_enclosure_certificate,
    )
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter
    from telperion.emit_tight_cap_enclosure import (  # noqa: F401 (re-export for reuse)
        _INLINE_DEFS,
        _lean_list,
        _lhs,
        tight_cap_enclosure_certificate,
    )


def _lean_list_of_lists(cfgs: list[list[sp.Rational]]) -> str:
    return "[" + ", ".join(_lean_list(list(l)) for l in cfgs) + "]"


@dataclass(frozen=True)
class PerSizeDominanceSweepCertificate:
    """A verified BG per-size g-step domination sweep certificate.

    ``size`` is the fixed config length ``n`` (every enumerated config has exactly
    ``n`` children).  ``configs`` is the tuple of enumerated configs — each a tuple
    of exact rational child messages μ.  ``lhs_values`` is the tuple of EXACT
    rational LHS values ``(baseOf l)¹¹·prodBcap l/(W(5/3)¹¹)``, one per config, each
    checked ``≤ 1``.  ``per_config`` is the tuple of the reused
    ``tight_cap_enclosure`` concrete certificates (one per config), so this cert is
    literally an AGGREGATION of tight_cap_enclosure per-config certificates.

    NEGATIVE CONTROL: if ANY enumerated config has exact LHS ``> 1`` the builder
    REFUSES with ``ValueError`` (a false sweep is never certified).
    """

    size: int
    configs: tuple
    lhs_values: tuple
    per_config: tuple


def per_size_dominance_sweep_certificate(
    *, size: int, configs=None
) -> PerSizeDominanceSweepCertificate:
    """Build and EXACTLY self-check (over ℚ) a per-size g-step domination sweep.

    ``size`` is the fixed config length ``n``; ``configs`` is a non-empty list of
    configs, each a list of exactly ``size`` exact rational cavity messages μ.  For
    EVERY config the EXACT rational LHS ``(baseOf l)¹¹·prodBcap l/(W(5/3)¹¹)`` is
    computed in sympy and asserted ``≤ 1`` (delegating each per-config check to
    ``tight_cap_enclosure_certificate`` in concrete mode, so the per-config face is
    the very same certificate).

    NEGATIVE CONTROL: refuse (``ValueError``) if ANY enumerated config has exact
    LHS ``> 1``.  In particular a config containing a single child ``μ = 13/16 ∈
    (1/2, 1)`` — where the g-step arm peaks ≈ 1.076 — is REFUSED, guaranteeing a
    wrong sweep can never be certified.
    """
    if not configs:
        raise ValueError("REFUSED: per_size_dominance_sweep needs a non-empty config set")
    n = int(size)
    parsed: list[list[sp.Rational]] = []
    lhs_values: list[sp.Rational] = []
    per_config: list[object] = []
    for cfg in configs:
        l = [sp.nsimplify(sp.Rational(m)) for m in cfg]
        if len(l) != n:
            raise ValueError(
                f"REFUSED: config {[str(m) for m in l]} has length {len(l)} != size {n} "
                f"(a per-size sweep requires every config to have exactly n children)"
            )
        # Reuse the tight_cap_enclosure concrete per-config certificate: it computes
        # the EXACT rational LHS and RAISES ValueError if that LHS > 1.
        cert = tight_cap_enclosure_certificate(mode="concrete", children=l)
        lhs = sp.nsimplify(_lhs(l))
        if not (lhs.is_number and lhs <= 1):  # defensive: mirror the per-config gate
            raise ValueError(
                f"REFUSED: config {[str(m) for m in l]} VIOLATES the g-step "
                f"domination sweep — exact LHS = {lhs} > 1 (negative control)"
            )
        parsed.append(l)
        lhs_values.append(lhs)
        per_config.append(cert)
    return PerSizeDominanceSweepCertificate(
        size=n,
        configs=tuple(tuple(l) for l in parsed),
        lhs_values=tuple(lhs_values),
        per_config=tuple(per_config),
    )


def certify_per_size_dominance_sweep_point(family, pt, name):
    """Certify one per-size-domination-sweep instance from ``family.special[1](pt)``.

    ``spec`` is a dict: ``{"size": n, "configs": [[μ, …], …]}``."""
    spec = family.special[1](pt)
    cert = per_size_dominance_sweep_certificate(
        size=spec["size"], configs=spec.get("configs")
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class PerSizeDominanceSweepEmitter(Emitter):
    """Emit the BG per-size g-step domination sweep theorems for a fixed size ``n``.

    For each enumerated config ``l`` a CONCRETE per-config face

        theorem <name>_cfg<k> :
            (baseOf L)¹¹ * prodBcap L / (W * (5/3)¹¹) ≤ 1 := by
          norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, …]

    (the whole LHS is a concrete rational; ``norm_num`` over the unfolded defs
    closes it — this is exactly the tight_cap_enclosure concrete face), then the
    AGGREGATE theorem over the enumerated set

        theorem <name> :
            ∀ l ∈ ([L₁, L₂, …] : List (List ℚ)),
              (baseOf l)¹¹ * prodBcap l / (W * (5/3)¹¹) ≤ 1 := by
          simp only [List.forall_mem_cons, List.forall_mem_nil, …]
          exact ⟨<name>_cfg0, <name>_cfg1, …⟩

    The self-contained W/glemma/master_ub/Bcap/baseOf/prodBcap defs are supplied
    once via the reused ``LeanProfile.prelude`` (``_INLINE_DEFS``); this emitter
    emits ONLY the theorems.  HONEST SCOPE: finite per-``n`` sweep of the LISTED
    configs, aggregating the tight_cap_enclosure per-config certificate — NOT an
    exhaustiveness/normal-form claim and NOT uniform in ``n``.
    conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "per_size_dominance_sweep"

    def _emit_cfg(self, L: str, name: str) -> str:
        return (
            f"-- CONCRETE per-config g-step domination face for {L}\n"
            f"-- (same face as tight_cap_enclosure concrete: whole LHS is a rational;\n"
            f"--  norm_num over the unfolded defs closes it).\n"
            f"theorem {name} :\n"
            f"    (baseOf {L}) ^ 11 * prodBcap {L}\n"
            f"      / (W * (5 / 3) ^ 11) ≤ 1 := by\n"
            f"  norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, List.map,\n"
            f"    List.prod, List.sum, List.length, List.foldr]\n"
        )

    def _emit_aggregate(
        self, cfgs: list[list[sp.Rational]], name: str, cfg_names: list[str]
    ) -> str:
        set_lit = _lean_list_of_lists(cfgs)
        # anonymous-constructor witness: one per-config face, then the trailing
        # `∀ x ∈ [], …` nil obligation left by repeated List.forall_mem_cons.
        witnesses = ", ".join(cfg_names + ["List.forall_mem_nil _"])
        return (
            f"-- AGGREGATE per-size sweep over the enumerated config set (size n).\n"
            f"-- Dispatches each membership to its per-config face via List.forall_mem_cons.\n"
            f"-- HONEST SCOPE: finite sweep of the LISTED configs — NOT exhaustive over\n"
            f"-- all size-n normal-form states, and NOT uniform in n.\n"
            f"theorem {name} :\n"
            f"    ∀ l ∈ ({set_lit} : List (List ℚ)),\n"
            f"      (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1 := by\n"
            f"  simp only [List.forall_mem_cons]\n"
            f"  exact ⟨{witnesses}⟩\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: PerSizeDominanceSweepCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            cfgs = [list(l) for l in cert.configs]
            cfg_names = [f"{base}_cfg{k}" for k in range(len(cfgs))]
            for l, cname in zip(cfgs, cfg_names):
                lines.append(self._emit_cfg(_lean_list(list(l)), cname))
                nthm += 1
            lines.append(self._emit_aggregate(cfgs, base, cfg_names))
            nthm += 1
        return "\n".join(lines), nthm


def per_size_dominance_sweep_family(name, grid, lean_name, spec, constants=None):
    """Build a BG per-size domination sweep family (kind='per_size_dominance_sweep').

    ``spec``: a callable ``pt -> {"size": n, "configs": [[μ, …], …]}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("per_size_dominance_sweep", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive: per-size sweep at n=3 (cherry / mixed / arm-mixed) ===")
    c = per_size_dominance_sweep_certificate(
        size=3,
        configs=[
            [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)],
            [Fraction(1, 3), Fraction(1, 2), Fraction(1, 3)],
            [Fraction(1, 2), Fraction(1, 2), Fraction(1, 3)],
        ],
    )
    print(f"  cert OK: size={c.size}, {len(c.configs)} configs, all LHS ≤ 1")
    for l, v in zip(c.configs, c.lhs_values):
        print(f"    {[str(m) for m in l]} -> LHS ≈ {float(v):.6f}")

    print("\n=== NEGATIVE CONTROL: a size-1 sweep containing μ = 13/16 (LHS > 1) ===")
    try:
        per_size_dominance_sweep_certificate(size=1, configs=[[Fraction(13, 16)]])
        raise SystemExit("FAIL: violating sweep config was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

    print("\n=== NEGATIVE CONTROL: a config of the wrong length for the sweep size ===")
    try:
        per_size_dominance_sweep_certificate(
            size=3, configs=[[Fraction(1, 3), Fraction(1, 3)]]
        )
        raise SystemExit("FAIL: wrong-length config was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

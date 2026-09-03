"""BG per-hub SCL node-decouple "recursion closure" emitter.

This packages the ASSEMBLY step of the Brualdi–Goldwasser SCL (single-child-
lift) induction at a FIXED price μ*: from the PROVEN tangent-majorant
(`bell_node_tangent` of ``proof/formalization/R3Cert/BGSCLInduction.lean``)
plus a per-hub CEILING, conclude the node ceiling.  Concretely, writing
``bV μ* b = bell b + μ*·bY b`` (the fixed-price value), the assembly is:

    nodeVal ≤ childBellSum + tangentBracket + μ*·nodeY          (htan)
    childBellSum + tangentBracket + μ*·nodeY ≤ cherryVal        (hceil)
    ─────────────────────────────────────────────────────────
    nodeVal ≤ cherryVal

where (mirroring the exact shapes of the proven in-repo lemmas)

    tangentBracket = log(1 + s0/d) + (S − s0)/(d + s0) − F*,    d = |cs|+1,
                     S = Σ_c bY c,   reference field-sum s0 ≥ 0,
    bY (node cs)   = 1/(d + S)                       (`bY_node`, PROVEN),
    bV μ* b        = bell b + μ*·bY b                 (fixed-price value).

The reusable deliverable is the abstract-real assembly lemma
``recursion_closure_assembly`` (proof: ``linarith``).  Its two hypotheses are
EXACTLY the tangent-majorant face (``htan``, the proven ``bell_node_tangent``
instantiated at ``s0`` with the price term ``μ*·nodeY`` added on both sides)
and the per-hub ceiling face (``hceil``).

HONEST SCOPE.  This emitter packages the tangent+ceiling → node-ceiling
ASSEMBLY at a fixed price.  It does NOT re-derive the concave-log tangent
majorant — that is the already-PROVEN ``bell_node_tangent`` (fed in as
``htan``) — and it does NOT prove the arity-unbounded "worst config =
all-cherry" exchange argument, which is structural and remains open.  The
emitted file is self-contained (only ``import Mathlib``; no R3Cert import).

conjecture1_proved=False.
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


# ---- the fixed I = [456/3703, 3/7] price interval (BGSCLInduction) -----------
_I_LO = sp.Rational(456, 3703)
_I_HI = sp.Rational(3, 7)


def _lean_rat(q) -> str:
    """Render an exact rational as a Lean ℚ literal (n or n/d)."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"{q.p}"
    return f"{q.p}/{q.q}"


@dataclass(frozen=True)
class RecursionClosureCertificate:
    """A verified BG per-hub SCL node-decouple assembly certificate.

    All quantities are exact rationals grounding the abstract-real assembly
    lemma at a fixed price ``mu_star`` in ``I = [456/3703, 3/7]``:

        nodeVal      — the hub `bell(node cs)`   (abstract-but-rational here)
        child_bell   — Σ_c bell(c)               (childBellSum)
        tangent      — tangentBracket at reference s0
        node_y       — bY(node cs) = 1/(d + S)   (from `bY_node`)
        cherry_val   — the per-child ceiling `bV μ* cherry`

    The self-check verifies the CHAIN is consistent, i.e. the middle quantity
    ``child_bell + tangent + mu_star*node_y ≤ cherry_val`` (so the assembly is
    SOUND).  NEGATIVE CONTROL: if that ceiling is violated, the cert is REFUSED
    (ValueError) — an unsound assembly.  ``mid_value`` records the exact middle
    quantity; ``tie`` flags the all-cherry equality case (mid == cherry_val).
    """

    mu_star: object
    node_val: object
    child_bell: object
    tangent: object
    node_y: object
    cherry_val: object
    mid_value: object = None
    tie: bool = False


def recursion_closure_certificate(
    *, mu_star, node_val, child_bell, tangent, node_y, cherry_val
) -> RecursionClosureCertificate:
    """Build and EXACTLY self-check (over ℚ) a recursion-closure assembly cert.

    Verifies the assembly is SOUND: the middle quantity of the chain

        mid := child_bell + tangent + mu_star*node_y

    satisfies ``mid ≤ cherry_val`` (the per-hub ceiling ``hceil``).  Given the
    tangent-majorant ``htan`` (``node_val ≤ mid``, the proven
    ``bell_node_tangent`` + price), ``linarith`` then closes ``node_val ≤
    cherry_val``.

    NEGATIVE CONTROL: if ``mid > cherry_val`` the supplied ceiling is VIOLATED —
    the assembly would be unsound (it would let a node exceed the cherry
    ceiling), so the cert is REFUSED with ``ValueError``.  Also refuses a price
    ``mu_star`` outside the invariant interval ``I = [456/3703, 3/7]``.
    """
    mu = sp.nsimplify(sp.Rational(mu_star))
    nv = sp.nsimplify(sp.Rational(node_val))
    cb = sp.nsimplify(sp.Rational(child_bell))
    tb = sp.nsimplify(sp.Rational(tangent))
    ny = sp.nsimplify(sp.Rational(node_y))
    cv = sp.nsimplify(sp.Rational(cherry_val))

    if not (_I_LO <= mu <= _I_HI):
        raise ValueError(
            f"REFUSED: price μ* = {mu} is outside the invariant interval "
            f"I = [456/3703, 3/7] (negative control)"
        )

    mid = sp.nsimplify(cb + tb + mu * ny)
    if not (mid.is_number and mid <= cv):
        raise ValueError(
            f"REFUSED: per-hub ceiling VIOLATED — "
            f"child_bell + tangent + μ*·node_y = {mid} > cherry_val = {cv}; "
            f"the tangent+ceiling assembly would be UNSOUND (negative control)"
        )
    return RecursionClosureCertificate(
        mu_star=mu, node_val=nv, child_bell=cb, tangent=tb, node_y=ny,
        cherry_val=cv, mid_value=mid, tie=bool(mid == cv),
    )


def certify_recursion_closure_point(family, pt, name):
    """Certify one recursion-closure instance from ``family.special[1](pt)``.

    ``spec`` is a dict with the exact rational keys ``mu_star``, ``node_val``,
    ``child_bell``, ``tangent``, ``node_y``, ``cherry_val``."""
    spec = family.special[1](pt)
    cert = recursion_closure_certificate(
        mu_star=spec["mu_star"],
        node_val=spec["node_val"],
        child_bell=spec["child_bell"],
        tangent=spec["tangent"],
        node_y=spec["node_y"],
        cherry_val=spec["cherry_val"],
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# the inline self-contained assembly lemma emitted once at the top of the file.
# (only `import Mathlib`; abstract reals — this is the REUSABLE deliverable.)
_INLINE_DEFS = """\
/-- **The BG per-hub SCL node-decouple assembly** (reusable, abstract reals).

    At a fixed price `muStar`, with `bV μ b = bell b + μ·bY b`, this packages
    the proven tangent-majorant (`bell_node_tangent`) + a per-hub ceiling into
    the node ceiling:

      * `htan`  : nodeVal ≤ childBellSum + tangentBracket + muStar·nodeY
                  (the proven `bell_node_tangent` at reference `s0`, plus the
                   price term `muStar·nodeY` added to both sides — here
                   `nodeVal = bell (node cs)`, `nodeY = bY (node cs)`);
      * `hceil` : childBellSum + tangentBracket + muStar·nodeY ≤ cherryVal
                  (the per-hub ceiling, `cherryVal = bV muStar cherry`);
      * ⟹ nodeVal ≤ cherryVal.

    HONEST SCOPE: packages the tangent+ceiling → node-ceiling ASSEMBLY at a
    fixed price.  Does NOT re-derive the log-tangent (that is `bell_node_tangent`)
    nor prove the all-cherry exchange (structural).  conjecture1_proved=False. -/
theorem recursion_closure_assembly
    (nodeVal childBellSum tangentBracket muStar nodeY cherryVal : ℝ)
    (htan : nodeVal ≤ childBellSum + tangentBracket + muStar * nodeY)
    (hceil : childBellSum + tangentBracket + muStar * nodeY ≤ cherryVal) :
    nodeVal ≤ cherryVal := by
  linarith"""


@dataclass
class RecursionClosureEmitter(Emitter):
    """Emit the BG per-hub SCL node-decouple closure theorem(s).

    The reusable abstract-real assembly lemma ``recursion_closure_assembly`` is
    supplied once via the ``LeanProfile.prelude`` (module constant
    ``_INLINE_DEFS``).  This emitter emits, per instance, a CONCRETE grounding
    ``example`` that instantiates the assembly at a fixed rational price
    ``muStar`` ∈ ``I = [456/3703, 3/7]`` with concrete rational values for
    ``childBellSum``/``tangentBracket``/``nodeY``/``cherryVal`` and abstract-but-
    hypothesized bounds ``htan``/``hceil`` (the two ``≤`` facts).  Because the
    tangent bracket carries a `log`, we keep theorem 2 HONEST as an instance of
    theorem 1 over ABSTRACT hypotheses rather than faking a numeric log — the
    assembly lemma is the real deliverable.

    A ``tie`` instance additionally records the all-cherry EQUALITY (nodeVal =
    cherryVal) as an ``example`` composing with the tie of the
    ``tight_cap_enclosure`` emitter.

    HONEST SCOPE: packages the tangent+ceiling → node-ceiling assembly at a
    fixed price; does NOT derive the log-tangent (`bell_node_tangent`) nor prove
    the all-cherry exchange (structural).  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "recursion_closure"

    def _emit_instance(self, cert: RecursionClosureCertificate, name: str) -> str:
        mu = _lean_rat(cert.mu_star)
        cb = _lean_rat(cert.child_bell)
        tb = _lean_rat(cert.tangent)
        ny = _lean_rat(cert.node_y)
        cv = _lean_rat(cert.cherry_val)
        mid = _lean_rat(cert.mid_value)
        header = (
            f"-- CONCRETE per-hub SCL node-decouple at fixed price "
            f"μ* = {mu} ∈ I = [456/3703, 3/7].\n"
            f"-- Grounds `recursion_closure_assembly` with concrete rational "
            f"childBellSum/tangentBracket/nodeY/cherryVal;\n"
            f"-- htan (the proven `bell_node_tangent` + price) and hceil "
            f"(the per-hub ceiling) are the ABSTRACT hypotheses.\n"
            f"-- Middle quantity childBellSum+tangentBracket+μ*·nodeY = {mid} "
            f"≤ cherryVal = {cv} (the certified ceiling).\n"
        )
        body = (
            f"theorem {name} (nodeVal : ℝ)\n"
            f"    (htan : nodeVal\n"
            f"      ≤ ({cb} : ℝ) + ({tb}) + ({mu}) * ({ny}))\n"
            f"    (hceil : ({cb} : ℝ) + ({tb}) + ({mu}) * ({ny}) ≤ ({cv})) :\n"
            f"    nodeVal ≤ ({cv} : ℝ) := by\n"
            f"  exact recursion_closure_assembly nodeVal ({cb}) ({tb}) ({mu}) "
            f"({ny}) ({cv}) htan hceil\n"
        )
        tie = ""
        if cert.tie:
            tie = (
                f"\n-- TIE: the all-cherry config gives EQUALITY of the middle "
                f"quantity with the\n"
                f"-- cherry ceiling ({mid} = {cv}), composing with the tie of "
                f"`tight_cap_enclosure`.\n"
                f"example : (({cb} : ℝ) + ({tb}) + ({mu}) * ({ny})) = ({cv}) := "
                f"by norm_num\n"
            )
        return header + body + tie

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: RecursionClosureCertificate = inst.payload  # type: ignore[assignment]
            lines.append(self._emit_instance(cert, inst.lean_name))
            nthm += 1
        return "\n".join(lines), nthm


def recursion_closure_family(name, grid, lean_name, spec, constants=None):
    """Build a BG per-hub SCL recursion-closure family (kind='recursion_closure').

    ``spec``: a callable ``pt -> {"mu_star": ..., "node_val": ..., "child_bell":
    ..., "tangent": ..., "node_y": ..., "cherry_val": ...}`` (all exact
    rationals)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("recursion_closure", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # A concrete all-cherry-flavoured instance at the interval midpoint-ish
    # price.  Numbers chosen so the ceiling holds with slack; the TIE variant
    # picks cherry_val exactly equal to the middle quantity.
    print("=== positive: per-hub SCL node-decouple, price μ* = 1/4 ∈ I ===")
    c = recursion_closure_certificate(
        mu_star=Fraction(1, 4),
        node_val=Fraction(1, 10),   # abstract nodeVal placeholder (rational)
        child_bell=Fraction(1, 5),
        tangent=Fraction(-1, 20),
        node_y=Fraction(1, 8),
        cherry_val=Fraction(1, 5),
    )
    print(f"  cert OK: μ*={c.mu_star}, mid = {c.mid_value} ≤ cherry_val = "
          f"{c.cherry_val} (tie={c.tie})")

    print("\n=== positive: all-cherry TIE (mid == cherry_val) ===")
    ct = recursion_closure_certificate(
        mu_star=Fraction(1, 4),
        node_val=Fraction(1, 10),
        child_bell=Fraction(1, 5),
        tangent=Fraction(-1, 20),
        node_y=Fraction(1, 8),
        cherry_val=Fraction(1, 5) + Fraction(-1, 20) + Fraction(1, 4) * Fraction(1, 8),
    )
    print(f"  cert OK: mid = {ct.mid_value} = cherry_val = {ct.cherry_val} "
          f"(tie={ct.tie})")

    print("\n=== NEGATIVE CONTROL: ceiling violated (mid > cherry_val) ===")
    try:
        recursion_closure_certificate(
            mu_star=Fraction(1, 4),
            node_val=Fraction(1, 10),
            child_bell=Fraction(1, 2),
            tangent=Fraction(1, 10),
            node_y=Fraction(1, 8),
            cherry_val=Fraction(1, 5),   # far below the middle quantity
        )
        raise SystemExit("FAIL: violating ceiling was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

    print("\n=== NEGATIVE CONTROL: price outside I = [456/3703, 3/7] ===")
    try:
        recursion_closure_certificate(
            mu_star=Fraction(9, 10),
            node_val=Fraction(1, 10),
            child_bell=Fraction(1, 5),
            tangent=Fraction(-1, 20),
            node_y=Fraction(1, 8),
            cherry_val=Fraction(1, 5),
        )
        raise SystemExit("FAIL: out-of-interval price was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

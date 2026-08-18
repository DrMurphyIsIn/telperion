"""First-class SOS/SDP emitter — the LP -> SDP upgrade of the certifier.

Pólya certificates are the LP-feasibility special case (a nonnegative
combination of known-nonnegative forms).  The SDP layer certifies `0 <= p` by a
POSITIVE-SEMIDEFINITE Gram matrix `p = mᵀ Q m`, reaching polynomials that vanish
at INTERIOR points (tie shapes Pólya lifting provably cannot handle) and reading
the equality variety off the dual (`ker Q`) for free.

This module promotes `sos_sdp.py`'s standalone `lean_certificate()` string
builder to a pipeline-enforced Emitter + `family.kind == "sos"` path + convenience
constructor, so an SOS family flows through the single certify() -> emit() ->
freeze() API and its honesty machinery (declared ties are cross-checked against
the SDP dual's tight variety — an over-claiming certificate is refused).

Rendering uses the tool's canonical graded-lex ordering (`expr._poly_any_lean`),
NOT sympy print order — emitted Lean is byte-stable across the sympy CI matrix.

HONEST SCOPE: this is the certificate LAYER the occupancy / SOS-for-trees method
runs on.  Aiming it at the ∏deg-normalized matching functional's recursive tree
profile so the dual lands on the integer tie s=5 is the named research program
(unbounded degree + arithmetic tie), NOT delivered here.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .certify import CertifiedInstance, _dual_engine_check
from .expr import _poly_any_lean, rat_lean
from .family import InequalityFamily
from .lean import LeanProfile
from .sos_sdp import sos_sdp_certificate
from .workflow import Emitter


def _sos_pin_checks(family, pt, p: sp.Expr, cert, tight) -> int:
    """The honesty declarations for an SOS certificate, enforced.

    A declared tie (a substitution where `0 <= p` MUST be exactly tight) is
    checked two ways: the target vanishes there (the tie is real), and every
    square base vanishes there (complementary slackness: `p = Σ dᵢℓᵢ² = 0` iff
    every `ℓᵢ = 0`, so a certificate with a non-vanishing base at a declared tie
    carries positive slack — an OVERCLAIM, refused).  Returns the check count."""
    checks = 0
    if family.ties is not None:
        for tie in family.ties(pt):
            tval = sp.expand(p.subs(tie))
            if tval != 0:
                raise ValueError(
                    f"declared tie {tie} is not tight: p = {tval}"
                )
            for _, base in cert.terms:
                bval = sp.expand(base.subs(tie))
                if bval != 0:
                    raise ValueError(
                        f"OVERCLAIM: square base ({base}) = {bval} != 0 at "
                        f"declared tie {tie} — the certificate has positive "
                        f"slack there and does not achieve the tie"
                    )
            checks += 1 + len(cert.terms)
    if family.anchors is not None:
        for subs, val in family.anchors(pt):
            got = sp.expand(p.subs(subs) - val)
            if got != 0:
                raise ValueError(
                    f"anchor mismatch at {subs}: off by {got} from declared {val}"
                )
            checks += 1
    return checks


def certify_sos_point(family, pt, name):
    """Certify one SOS instance: (CertifiedInstance, n_checks).

    Runs the SDP, rationalizes and EXACTLY verifies the Gram (inside
    sos_sdp_certificate; a numerically-inexact rationalization is a refusal, not
    a lie), then the honesty pins.  Raises ValueError on any refusal."""
    syms = family.symbols
    if not syms:
        raise ValueError("SOS families require at least one symbol")
    p = sp.expand(family.target(pt))
    res = sos_sdp_certificate(p, syms, family.sos_half_deg)
    if res is None:
        raise ValueError(
            f"no exact rational SOS certificate at half_deg={family.sos_half_deg} "
            f"(SDP infeasible or Gram not exactly rationalizable)"
        )
    cert, tight = res
    # exact identity self-check (belt-and-suspenders over sos_sdp_certificate's own)
    if sp.expand(cert.as_expr() - p) != 0:
        raise ValueError("SOS identity self-check failed: Σ dᵢℓᵢ² != p")
    checks = 1
    checks += _sos_pin_checks(family, pt, p, cert, tight)
    checks += _dual_engine_check(family, pt)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        sos=cert, tight=tuple(tight),
    )
    return inst, checks


@dataclass
class SOSEmitter(Emitter):
    """One `0 ≤ p` theorem per instance from its exact rational SOS certificate:
    `have hsos : p = Σ dᵢ·(ℓᵢ)² := by ring; rw [hsos]; positivity`.

    The tight variety (the SDP dual's `ker Q`) is documented above each theorem —
    the equality case, read off the certificate for free."""

    def __post_init__(self):
        self.kind = "sos_sdp"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = fam.family.symbols
        binder = " ".join(str(s) for s in syms)
        out: list[str] = []
        for inst in fam.instances:
            cert = inst.sos
            p = sp.expand(fam.family.target(inst.point))
            p_l = _poly_any_lean(p, syms)
            sos_terms = " + ".join(
                f"{rat_lean(c)} * ({_poly_any_lean(sp.expand(base), syms)})^2"
                for c, base in cert.terms
            )
            tightdoc = " ∧ ".join(
                f"{_poly_any_lean(sp.expand(b), syms)} = 0" for b in inst.tight
            ) or "(none — strictly positive)"
            out.append(
                f"-- {inst.lean_name}: SDP-SOS certificate (PSD Gram, "
                f"off-diagonal coupling).\n"
                f"-- Tight variety (0 ≤ p is tight iff): {tightdoc}\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ, (0:ℝ) ≤ {p_l} := by\n"
                f"  intro {binder}\n"
                f"  have hsos : ({p_l} : ℝ) = {sos_terms} := by ring\n"
                f"  rw [hsos]; positivity\n"
            )
        return "\n".join(out), len(fam.instances)


def sos_family(
    name,
    symbols,
    grid,
    lean_name,
    target,
    half_deg: int = 1,
    ties=None,
    anchors=None,
    independent_target=None,
    constants=None,
) -> InequalityFamily:
    """Convenience constructor for an SOS/SDP family (kind='sos').

    `target(pt)` is the polynomial `p` (claim `0 <= p` over all reals); `half_deg`
    is the monomial half-degree of the Gram basis.  `ties(pt)` declares interior
    tie points the certificate MUST achieve (cross-checked against the SDP dual)."""
    if not tuple(symbols):
        raise ValueError("SOS families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        target=target,
        sos_half_deg=half_deg,
        ties=ties,
        anchors=anchors,
        independent_target=independent_target,
        constants=constants or {},
    )

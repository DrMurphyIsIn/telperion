"""Signature / statement-match gate — the POSITIVE half of the trust boundary.

`negative_control` proves a forged FALSE instance is kernel-REJECTED (the generator
cannot forge a compiling proof of a false claim).  It does NOT prove the dual: that
a TRUE-compiling instance states the INTENDED proposition rather than a weaker or
merely-different one that also compiles axiom-clean.  A buggy emitter can emit

    theorem foo : 0 ≤ x^2 + 1 := …            -- compiles, clean axioms

when the certificate TARGET was ``0 ≤ x^2 + x + 1``.  Both are true; the emitted one
is the wrong (weaker) claim.  The RH thread hit exactly this class by hand: a
``∃ C, ‖ζ‖ ≤ C·(1+log|t|)`` restatement gives NO region constant, versus the intended
explicit ``‖ζ‖ ≤ 6·(1+log|t|)``.

This is AXLE `verify_proof`'s signature match (``use_def_eq=False``): compare the
candidate declaration's type to the CLAIMED formal statement — an independent
spec-side source — not merely that it compiles.

MECHANISM (kernel-checked, no metaprogramming).  Given emitted ``content`` defining
theorems and an ``expected`` map ``{decl_name -> intended full type}``, append for
each a guard

    theorem <name>__sig_guard : <intended> := <name>

The guard elaborates IFF ``<name>``'s type is defeq to ``<intended>`` — the Lean
kernel checks ``<name> : <intended>``.  A weaker/different claim (``≤ x+1`` vs
``≤ x``, ``∃ C`` vs explicit ``6``) is NOT defeq to the intended type, so the guard
fails to elaborate → MISMATCH.  Because the body is the bare ``<name>`` (no
application), ``<intended>`` must be the decl's FULL type with the SAME binder info
(implicit ``{…}`` stays implicit); :func:`forall_type` builds it from the binder and
statement text the emitter already has.

Trust note: defeq-level match is SOUND for the property that matters — it NEVER
accepts a logically-weaker theorem (those are not defeq to the intended).  It may
accept a defeq-equivalent restatement, which is the SAME proposition, so no trust
leak.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field

try:  # normal package import
    from .negative_control import _splice_prelude
    from .verify import VerifyResult, verify_lean
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.negative_control import _splice_prelude
    from telperion.verify import VerifyResult, verify_lean


def forall_type(binders: str, statement: str) -> str:
    """Build the full ∀-type ``∀ <binders>, <statement>`` (statement alone if no
    binders).  Pass the binder text VERBATIM as it appears in the theorem signature
    (``{s : ℂ} (hs : 1 ≤ s.re) {N : ℕ}``) so the guard's ``:= <name>`` body matches
    the decl's binder info exactly.  A hypothesis binder may equivalently appear as
    ``H →`` inside ``statement`` (``∀ {σ : ℝ}, 1 ≤ σ → …``) — both are defeq."""
    binders = binders.strip()
    return f"∀ {binders}, {statement}" if binders else statement


def sig_guard_name(name: str) -> str:
    return f"{name}__sig_guard"


def build_sig_guards(expected: dict) -> str:
    """The guard block: one ``theorem <name>__sig_guard : <intended> := <name>`` per
    entry.  Pure text — unit-testable offline, no Lean needed."""
    return "\n".join(
        f"theorem {sig_guard_name(n)} : {t} := {n}" for n, t in expected.items()
    )


@dataclass
class SignatureMatch:
    """Per-declaration signature verdict."""

    name: str
    intended: str
    matches: object          # bool | None (None = not reached: base proof failed)
    detail: str = ""


@dataclass
class SignatureResult:
    """Outcome of the signature/statement-match gate.

    * ``base``       — the underlying proof verification of ``content`` (compile +
      axiom check of the named decls).
    * ``matches``    — per-decl :class:`SignatureMatch`.
    * ``all_match``  — every named decl's type is defeq to its intended proposition.
    * ``okay``       — ``base.okay and base.axioms_clean and all_match``: the proofs
      compile axiom-clean AND every decl states exactly the intended claim.
    """

    okay: bool
    base: VerifyResult
    matches: dict = field(default_factory=dict)
    all_match: bool = False
    detail: str = ""


def check_signatures(
    content: str,
    *,
    env_dir,
    expected: dict,
    prelude: str = "",
    allow_axioms=(),
    timeout: int = 600,
    server=None,
) -> SignatureResult:
    """Assert each named decl in ``content`` states its intended proposition.

    ``expected``: ``{decl_name -> intended full type}`` (use :func:`forall_type`).
    First verifies ``content`` (proof + axioms of the named decls); if the proof
    itself does not compile, returns early (signatures moot).  Then appends the
    guard block and verifies: a clean pass means every guard elaborated, i.e. every
    decl's type matches.  On failure, re-checks each guard alone to attribute the
    mismatch to specific decls.
    """
    names = list(expected)
    spliced = _splice_prelude(content, prelude)

    # ---- proof-level verification of the real decls (compile + axioms). --------
    base = verify_lean(
        spliced, env_dir=env_dir, decls=names,
        allow_axioms=allow_axioms, timeout=timeout, server=server,
    )
    if not base.okay:
        return SignatureResult(
            okay=False, base=base,
            matches={n: SignatureMatch(n, expected[n], None,
                                       "base content did not compile") for n in names},
            all_match=False,
            detail="base content did not compile; signatures not checked",
        )

    # ---- fast path: all guards in one file. ------------------------------------
    guards = build_sig_guards(expected)
    full = spliced.rstrip() + "\n\n" + guards + "\n"
    guard_names = [sig_guard_name(n) for n in names]
    g = verify_lean(
        full, env_dir=env_dir, decls=guard_names,
        allow_axioms=allow_axioms, timeout=timeout, server=server,
    )
    if g.okay:
        matches = {
            n: SignatureMatch(n, expected[n], True, "type matches intended proposition")
            for n in names
        }
        return SignatureResult(
            okay=bool(base.axioms_clean), base=base, matches=matches,
            all_match=True,
            detail=("all signatures match"
                    + ("" if base.axioms_clean else "; but base axioms DIRTY")),
        )

    # ---- attribution: re-check each guard alone. -------------------------------
    matches = {}
    for n in names:
        one = spliced.rstrip() + "\n\n" + f"theorem {sig_guard_name(n)} : {expected[n]} := {n}\n"
        gg = verify_lean(
            one, env_dir=env_dir, decls=[sig_guard_name(n)],
            allow_axioms=allow_axioms, timeout=timeout, server=server,
        )
        if gg.okay:
            matches[n] = SignatureMatch(n, expected[n], True,
                                        "type matches intended proposition")
        else:
            err = gg.errors[0][:160] if gg.errors else "guard failed to elaborate"
            matches[n] = SignatureMatch(n, expected[n], False, f"MISMATCH: {err}")
    all_match = all(m.matches for m in matches.values())
    return SignatureResult(
        okay=bool(all_match and base.axioms_clean), base=base, matches=matches,
        all_match=all_match,
        detail=("all signatures match" if all_match
                else "signature MISMATCH on: "
                     + ", ".join(n for n, m in matches.items() if not m.matches)),
    )

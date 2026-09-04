"""Signature / statement-match gate — the POSITIVE half of the trust boundary.

`verify_lean` certifies a proof COMPILES and is axiom-clean (no `sorryAx`); the
`negative_control` certifies a FALSE instance is kernel-rejected. Neither certifies
the TRUE instance states the *intended* proposition — a buggy emitter (or a
hand-weakened cell) can emit a theorem that compiles, has clean axioms, and is still
the WRONG (weaker) claim, e.g. `0 ≤ x²+1` where `0 ≤ x²+x+1` was meant. AXLE's
`verify_proof` catches this with a signature match (`use_def_eq=False`); this is the
Telperion analog.

Mechanism (no metaprogram): for a declaration `foo` and an INTENDED type `T`, emit
`theorem __sigmatch_foo : T := @foo`.  Lean accepts it iff `@foo`'s type is defeq to
`T`.  A weaker/different `foo` fails with a type mismatch — the exact positive-half
check.  This composes on top of `telperion.verify.verify_lean` (it does NOT modify the
verify core), so it is collision-free with the hardened verify path.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class StatementMatchResult:
    """Outcome of checking each named decl against its intended type."""

    all_match: bool
    matched: list = field(default_factory=list)          # decl names whose type = intended
    mismatched: dict = field(default_factory=dict)       # name -> the Lean type-mismatch error
    elapsed_s: float = 0.0

    def summary(self) -> str:
        tag = "OK" if self.all_match else "MISMATCH"
        m = f"; {len(self.mismatched)} mismatch(es): {sorted(self.mismatched)}" if self.mismatched else ""
        return f"[{tag}] {len(self.matched)}/{len(self.matched)+len(self.mismatched)} statements match{m}"


def statement_match_check(intended, *, env_dir, imports=("import Mathlib",),
                          prelude="", allow_axioms=()):
    """Check each declaration states its INTENDED proposition.

    ``intended``: ``{fully_qualified_decl_name -> intended_type_str}``.  For each, emit
    ``theorem __sigmatch_… : <intended> := @<name>`` on top of ``imports``/``prelude``
    (which must bring ``<name>`` into scope) and elaborate.  A decl whose type is defeq
    to its intended type passes; otherwise the type mismatch is recorded.  Returns a
    :class:`StatementMatchResult`.

    Checks are run one-per-decl so a mismatch is attributable to the exact declaration.
    """
    import time
    from .verify import verify_lean

    head = "\n".join(imports) + ("\n" + prelude if prelude else "") + "\n"
    matched, mismatched = [], {}
    t0 = time.time()
    for i, (name, typ) in enumerate(intended.items()):
        safe = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in name)
        check = head + f"theorem __sigmatch_{i}_{safe} : {typ} := @{name}\n"
        r = verify_lean(check, env_dir=env_dir, allow_axioms=allow_axioms)
        if r.okay:
            matched.append(name)
        else:
            mismatched[name] = (r.errors[0] if r.errors else "elaboration failed")
    return StatementMatchResult(
        all_match=(len(mismatched) == 0), matched=matched, mismatched=mismatched,
        elapsed_s=time.time() - t0,
    )


def def_identity_check(name, binder, intended_body, *, env_dir,
                       imports=("import Mathlib",), prelude=""):
    """Check a Prop-valued DEFINITION unfolds to its intended body (via ``Iff.rfl``).

    For ``def foo (x) : Prop := <body>``, emit ``example (x) : foo x ↔ <intended_body>
    := Iff.rfl`` — passes iff the def IS the intended body definitionally.  ``binder``
    is the argument list (e.g. ``"(ρ : Branch → ℝ)"``) and the application ``foo <args>``
    is formed from it.  Returns ``(ok: bool, error: str|None)``.
    """
    from .verify import verify_lean

    args = " ".join(b.strip("() ").split(" ")[0] for b in binder.split(")(")) if binder else ""
    head = "\n".join(imports) + ("\n" + prelude if prelude else "") + "\n"
    check = head + f"example {binder} : {name} {args} ↔ ({intended_body}) := Iff.rfl\n"
    r = verify_lean(check, env_dir=env_dir)
    return r.okay, (r.errors[0] if r.errors else None)

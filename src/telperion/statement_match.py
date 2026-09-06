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
                          prelude="", allow_axioms=(), batch=True):
    """Check each declaration states its INTENDED proposition.

    ``intended``: ``{fully_qualified_decl_name -> intended_type_str}``.  For each, emit
    ``theorem __sigmatch_… : <intended> := @<name>`` on top of ``imports``/``prelude``
    (which must bring ``<name>`` into scope) and elaborate.  A decl whose type is defeq
    to its intended type passes; otherwise the type mismatch is recorded.  Returns a
    :class:`StatementMatchResult`.

    ``batch`` (default) runs ALL checks in ONE ``lake env lean`` invocation — a single
    ``import Mathlib`` load instead of one per decl.  Measured ~N× faster (3 checks:
    4.3s batched vs 14.4s separate), the practical warm-tier win for an audit of many
    statements (`lean --stdin` is single-shot, so a persistent server is the only way
    to amortise the load across *separate* calls — that is the LSP path, deferred).  On
    an all-match batch this returns immediately; on ANY failure it re-runs per-decl to
    ATTRIBUTE the mismatch to the exact declaration.  ``batch=False`` forces per-decl.
    """
    import time
    from .verify import verify_lean

    head = "\n".join(imports) + ("\n" + prelude if prelude else "") + "\n"
    items = list(intended.items())
    t0 = time.time()

    if batch and len(items) > 1:
        body = head + "".join(
            f"theorem __sigmatch_{i}_{_safe(name)} : {typ} := @{name}\n"
            for i, (name, typ) in enumerate(items))
        r = verify_lean(body, env_dir=env_dir, allow_axioms=allow_axioms)
        if r.okay:
            return StatementMatchResult(
                all_match=True, matched=[n for n, _ in items], mismatched={},
                elapsed_s=time.time() - t0)
        # a mismatch is present but not attributable from the batch — fall through
        # to the per-decl pass (correctness over speed once something is wrong).

    matched, mismatched = [], {}
    for i, (name, typ) in enumerate(items):
        check = head + f"theorem __sigmatch_{i}_{_safe(name)} : {typ} := @{name}\n"
        r = verify_lean(check, env_dir=env_dir, allow_axioms=allow_axioms)
        if r.okay:
            matched.append(name)
        else:
            mismatched[name] = (r.errors[0] if r.errors else "elaboration failed")
    return StatementMatchResult(
        all_match=(len(mismatched) == 0), matched=matched, mismatched=mismatched,
        elapsed_s=time.time() - t0,
    )


def statement_match_example(theorem_name: str, explicit_type: str) -> str:
    """Return a Lean `example` line that kernel-enforces the theorem's statement.

    Emits exactly::

        example : <explicit_type> := <theorem_name>\\n

    When this line is compiled alongside the theorem, Lean's kernel checks that
    ``theorem_name``'s type is definitionally equal to ``explicit_type``.  Any
    statement drift -- a weakening, a different type, a wrong arity -- is a
    compile error rather than a silent divergence.

    The caller is responsible for passing the SAME type string used in the
    theorem's own signature (single-sourced); that identity is what makes this
    a drift net, not just a comment.

    conjecture1_proved = False.
    """
    return f"example : {explicit_type} := {theorem_name}\n"


def _safe(name: str) -> str:
    return "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in name)


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

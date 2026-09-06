"""Re-export emitter — wrap an already-proven / upstream Lean theorem as a named lemma.

A recurring Telperion shape is NOT a computed certificate but a PACKAGING: take a theorem that
is already proven (in the corpus, e.g. `residue_logDeriv`) or already upstream (in Mathlib, e.g.
`Complex.borelCaratheodory`) and emit a named re-export at a chosen instantiation, so downstream
code has a uniform entry point and a kernel-checkable dogfood that the packaging is well-typed.

`emit_order_residue` and `emit_borel_caratheodory` are both this pattern, hand-written. This
module factors it: `reexport_cert` emits

    theorem <name> <binders> <hyps> :
        <conclusion> :=
      <target_lemma> <args>

which type-checks exactly when `target_lemma <args>` has type `conclusion` — i.e. it re-exports,
proving nothing new. UNTRUSTED like every emitter: the kernel re-checks the term.

The value is uniformity: any "package theorem `L` at instantiation `I`" becomes one call, and the
two existing wrappers are recovered exactly (see the tests). conjecture1_proved = False.
"""
from __future__ import annotations

__all__ = ["reexport_cert"]


def reexport_cert(
    name: str,
    target_lemma: str,
    *,
    binders: str = "",
    hyps: str = "",
    conclusion: str,
    args: str = "",
    doc: str | None = None,
) -> str:
    """Emit `theorem <name> <binders> <hyps> : <conclusion> := <target_lemma> <args>`.

    * ``binders``    — implicit/instance binders, e.g. ``{f : ℂ → ℂ} {z₀ : ℂ}`` ('' for none).
    * ``hyps``       — explicit hypothesis binders, e.g. ``(hf : MeromorphicAt f z₀)`` (may span
                       lines; the caller controls indentation of continuation lines).
    * ``conclusion`` — the goal proposition (REQUIRED).
    * ``args``       — the argument string applied to ``target_lemma`` (e.g. ``hf hord``); ''
                       re-exports the lemma itself with no arguments.
    * ``doc``        — docstring; a default cites ``target_lemma``.

    Raises on an empty ``name``, ``target_lemma``, or ``conclusion`` (a re-export with nothing to
    conclude is a caller bug, caught here rather than as a Lean error).
    """
    if not name or not target_lemma or not conclusion:
        raise ValueError("reexport_cert: name, target_lemma, and conclusion are all required")
    head = f"theorem {name}"
    if binders:
        head += f" {binders}"
    if hyps:
        head += f" {hyps}"
    rhs = f"{target_lemma} {args}".rstrip()
    docblock = f"/-- {doc} -/\n" if doc else f"/-- Re-export of `{target_lemma}`. -/\n"
    return f"{docblock}{head} :\n    {conclusion} :=\n  {rhs}"

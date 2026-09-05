"""Order = residue of the logarithmic derivative — packaging the proven `residue_logDeriv`.

`residue_logDeriv` (PROVEN, `ZeroFreeBridge.lean`) says: for `f` meromorphic at `z₀` with
`meromorphicOrderAt f z₀ = n`,

    Tendsto (fun z => (z - z₀) · logDeriv f z) (𝓝[≠] z₀) (𝓝 (n : ℂ))  —

i.e. the residue of `f'/f` at `z₀` equals the (integer) meromorphic order.  Nothing here is
proved anew; this emitter is the reusable PACKAGING the zero-free plan calls for: given a
concrete integer order `n` (a pole `n<0`, a zero `n>0`), it emits a ready-to-use
SPECIALIZATION of `residue_logDeriv` at that order — the lemma downstream residue/order
balance arguments (`OrderBalance`) actually consume, and the shape upstreamable to Mathlib.

The emitted theorem is a direct re-export (`:= residue_logDeriv hf hord`), so it type-checks
exactly when `residue_logDeriv` has the stated type — a kernel-checkable dogfood that the
packaging is well-typed.  A specialization at a FIXED `n` is the useful unit because callers
typically know the order (the pole of `ζ` is `n=-1`; a simple zero is `n=1`).

UNTRUSTED like every emitter: the kernel re-checks the emitted term.  conjecture1_proved = False.
"""
from __future__ import annotations

__all__ = ["emit_order_residue_cert", "ORDER_NAMES"]

#: human labels for the common orders (for auto-docs).
ORDER_NAMES = {-1: "simple pole", -2: "double pole", 1: "simple zero", 2: "double zero"}


def _int_lit(n: int) -> str:
    """Lean integer literal, parenthesizing negatives for use inside casts."""
    return f"({n})" if n < 0 else f"{n}"


def emit_order_residue_cert(
    name: str,
    n: int,
    *,
    residue_lemma: str = "residue_logDeriv",
    doc: str | None = None,
) -> str:
    """Emit a Lean specialization of `residue_logDeriv` at integer order `n`.

    The emitted theorem takes the two `residue_logDeriv` hypotheses (`MeromorphicAt f z₀`
    and `meromorphicOrderAt f z₀ = n`) and concludes the residue limit equals `n`, proved by
    the direct application `:= <residue_lemma> hf hord`.  `residue_lemma` lets the caller
    point at a namespaced copy.  A non-integer `n` is a type error caught here.
    """
    if not isinstance(n, int):
        raise TypeError(f"{name}: order n must be an int, got {type(n).__name__}")
    nlit = _int_lit(n)
    label = ORDER_NAMES.get(n, f"order {n}")
    docblock = f"/-- {doc} -/\n" if doc else (
        f"/-- Residue of `f'/f` at a {label} equals its order `{n}`: the `n = {n}` "
        f"specialization of `{residue_lemma}`. -/\n"
    )
    return (
        f"{docblock}"
        f"theorem {name} {{f : ℂ → ℂ}} {{z₀ : ℂ}}\n"
        f"    (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (({nlit} : ℤ) : WithTop ℤ)) :\n"
        f"    Filter.Tendsto (fun z => (z - z₀) * logDeriv f z) (nhdsWithin z₀ {{z₀}}ᶜ)\n"
        f"      (nhds ((({nlit} : ℤ)) : ℂ)) :=\n"
        f"  {residue_lemma} hf hord"
    )

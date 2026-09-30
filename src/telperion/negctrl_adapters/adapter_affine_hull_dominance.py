"""Negative-control adapter for AffineHullDominanceEmitter (exact tree maxima by hull pruning).

The instance is the dogfood recursion, the Randic-weighted matching sum
`pi(T) = sum over matchings M of prod_{uv in M} 1/(deg u deg v)`, on trees with at most
`N = 6` vertices.  The honest certificate proves `M_6 = 29/8` (attained by one tree).

FALSE forgery: the maximizing root bundle of class `(5, k)` is REMOVED from the kept list, the
candidate that produced it is given a forged convex-combination witness (all weight on the
best remaining kept point of that class, which does NOT dominate it), and the claimed maximum
is lowered to the best remaining root value.  The claim `M_6 = <second-best value>` is then
FALSE, not merely unproved: the true maximizer attains 29/8, more than the claim.  Everything
else in the file is the honest certificate, and the forged value IS attained by a tree, so the
listed-maximizer check passes; the only wrong object is the dominance witness, and the
kernel-decided checker `Cert.Valid` evaluates to false on it.

TRUE twin: the honest certificate at `N = 6`.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from functools import lru_cache

from telperion.emit_affine_hull_dominance import (
    MATCHING_SUM_RECURSION,
    AffineHullDominanceEmitter,
    HullDominanceCert,
    cand_bundle,
    eval_pi,
    hull_dominance_certificate,
    witness_for,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

#: tree size of the control instance
N_CONTROL = 6


def make_true_cert() -> HullDominanceCert:
    """The honest matching-sum certificate for trees on at most 6 vertices."""
    return hull_dominance_certificate(recursion=MATCHING_SUM_RECURSION, N=N_CONTROL,
                                      label="matching sum, negative-control twin")


@lru_cache(maxsize=None)
def _forests(total: int) -> frozenset:
    """Every multiset of rooted trees with `total` vertices in all, as sorted tuples."""
    if total == 0:
        return frozenset({()})
    out = set()
    for a in range(1, total + 1):
        for t in rooted_trees(a):
            for rest in _forests(total - a):
                out.add(tuple(sorted((t,) + rest)))
    return frozenset(out)


@lru_cache(maxsize=None)
def rooted_trees(n: int) -> tuple:
    """Every rooted tree on n vertices, as sorted tuples of children (leaf = ())."""
    return tuple(sorted(_forests(n - 1)))


def forge_wrong_maximum(cert: HullDominanceCert) -> HullDominanceCert:
    """Remove every maximizing root bundle at n = N (one per root vertex of each maximizer),
    forge the witnesses of the candidates that produced them, and lower the claim."""
    rec, N = cert.rec, cert.N
    KB = dict(cert.KB)
    WB = dict(cert.WB)
    KH = dict(cert.KH)
    best = cert.value(N)
    for k in range(1, N):
        K_old = KB.get((N - 1, k), ())
        drop = [p for p in K_old if rec.root(k, p) == best]
        if not drop:
            continue
        K_new = tuple(q for q in K_old if q not in drop)
        runner = (K_new.index(max(K_new, key=lambda q: rec.root(k, q))) if K_new else None)
        wits = []
        for x, _prov in cand_bundle(rec, KB, KH, N - 1, k):
            if runner is None:
                # the class is emptied: no convex weights over an empty list sum to 1
                wits.append(("dom", ()))
            elif x in drop:
                wits.append(("dom", tuple(Fraction(1) if t == runner else Fraction(0)
                                          for t in range(len(K_new)))))
            else:
                wits.append(witness_for(K_new, x))
        KB[(N - 1, k)] = K_new
        WB[(N - 1, k)] = tuple(wits)
    forged = max(rec.root(kk, q) for kk in range(1, N) for q in KB.get((N - 1, kk), ()))
    trees = tuple(t for t in rooted_trees(N) if eval_pi(rec, t) == forged)[:1]
    values = tuple((n, forged if n == N else v) for n, v in cert.values)
    maxs = tuple((n, trees if n == N else ts) for n, ts in cert.maximizers)
    return replace(cert, KB=tuple(sorted(KB.items())), WB=tuple(sorted(WB.items())),
                   values=values, maximizers=maxs, checked=False,
                   label="FORGED: maximizing root bundles removed")


def make_false_cert() -> HullDominanceCert:
    """Hand-forged FALSE cert: M_6 claimed to be the second-best value."""
    return forge_wrong_maximum(make_true_cert())


def _emit(cert: HullDominanceCert, name: str) -> str:
    return emit_via_single_instance_family(
        AffineHullDominanceEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="AffineHullDominanceEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged maximum of the Randic-weighted matching sum on 6 vertices (the maximizing "
            "root bundle dropped from the kept list and replaced by a convex-combination "
            "witness that does not dominate it, so the second-best value is claimed as M_6; "
            "false, since the true maximizer attains 29/8): the decided checker Cert.Valid "
            "is false and the kernel rejects it; the true twin compiles"
        ),
        imports_line="import Mathlib",
    )
)

"""3-XOR moment-matrix PSD emitter — GF(2) closure → block-rank-one SOS.

A degree-d SoS lower bound for an UNSATISFIABLE 3-XOR (Tseitin) instance, in the
Schoenebeck/Grigoriev ±1 semantics.  An instance is a list of clauses `(A, e)`
(`A` a subset of variables, `e ∈ {±1}`) asserting `∏_{i∈A} xᵢ = e`.  The width-w
CLOSURE of ∅ propagates signs `sgn(S ⊕ A) = e·sgn(S)`; a sign CONFLICT is a
width-w refutation.  When the width-2d closure is CONFLICT-FREE, the degree-d
moment matrix `M[S,T] = sgn(S ⊕ T)` (over index sets `|S|,|T| ≤ d`) is
**block-rank-one**: partitioning the index sets into classes `S ∼ T ⟺ (S⊕T) ∈
closure`, `M` is block-diagonal and each block is `σσᵀ` for the ±1 vector
`σ_S = sgn(S ⊕ rep(S))`.  Hence

    xᵀ M x = Σ_classes ( Σ_{S ∈ class} σ_S · x_S )²

— a compact sum of squares (one square per class), so `0 ≤ xᵀMx` is the robust,
search-free `ring` (the SOS identity) + `positivity`.  This is the CORRECT
structural picture for 3-XOR (GF(2) combinatorial consistency, NOT
scheme-eigenvalue positivity).

Everything on the verdict path is EXACT (integers / GF(2)): certification refuses
a SATISFIABLE instance, a width-w conflict (a refutation exists), or a moment
matrix that is not block-rank-one (a corrupted-sign negative control) — no Lean
is emitted for a non-member.  The emitted PSD claim is self-contained (no
external prelude); the full refutation-form duality layer is a separate follow-up.
"""
from __future__ import annotations

import itertools
from collections import deque
from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# --------------------------------------------------------------------------
# Exact GF(2) / closure core (vendored, self-contained — no cross-example dep)
# --------------------------------------------------------------------------

def _unsat_gf2(instance, n: int) -> bool:
    """Exact GF(2) Gaussian elimination: True iff the ±1 system is UNSAT."""
    pivots: dict[int, tuple[int, int]] = {}
    for aset, e in instance:
        vec = 0
        for i in aset:
            vec |= 1 << i
        rhs = 0 if e == 1 else 1
        while vec:
            p = vec.bit_length() - 1
            if p in pivots:
                pv, pr = pivots[p]
                vec ^= pv
                rhs ^= pr
            else:
                pivots[p] = (vec, rhs)
                break
        else:
            if rhs == 1:
                return True
    return False


def _closure(instance, w: int):
    """Width-w BFS sign closure of ∅.  Returns (sgn: dict[frozenset,int], conflict)."""
    sgn = {frozenset(): 1}
    queue = deque([frozenset()])
    while queue:
        S = queue.popleft()
        for aset, e in instance:
            T = S ^ aset
            if len(T) > w:
                continue
            val = e * sgn[S]
            if T in sgn:
                if sgn[T] != val:
                    return sgn, True
            else:
                sgn[T] = val
                queue.append(T)
    return sgn, False


def _index_sets(n: int, d: int):
    out = []
    for i in range(d + 1):
        out.extend(frozenset(S) for S in itertools.combinations(range(n), i))
    return out


def _class_partition(sgn, idx):
    """Partition index sets into derivability classes; (reps, assign, sigma) or
    (None, None, None) if the relation is not transitive (not block-rank-one)."""
    reps: list = []
    assign: dict = {}
    for S in idx:
        for r, R in enumerate(reps):
            if (S ^ R) in sgn:
                assign[S] = r
                break
        else:
            assign[S] = len(reps)
            reps.append(S)
    for S in idx:
        for T in idx:
            if (assign[S] == assign[T]) != ((S ^ T) in sgn):
                return None, None, None
    sigma = {S: sgn[S ^ reps[assign[S]]] for S in idx}
    return reps, assign, sigma


# --------------------------------------------------------------------------
# Certificate
# --------------------------------------------------------------------------

def _var(S) -> sp.Symbol:
    """A distinct real variable per index set S (∅ -> x_e; {i} -> x_i; {i,j} -> x_i_j)."""
    name = "x_e" if not S else "x_" + "_".join(str(i) for i in sorted(S))
    return sp.Symbol(name)


@dataclass(frozen=True)
class Xor3Certificate:
    """A verified 3-XOR degree-d moment-matrix-PSD certificate."""

    n: int
    degree: int
    idx: tuple                    # ordered index sets (frozensets)
    n_classes: int
    moment_quad: object           # the moment-matrix quadratic xᵀMx (sympy expr)
    sos_terms: tuple              # (linear_form, ...): xᵀMx = Σ (linear_form)²


def xor3_certificate(instance, n: int, degree: int = 2) -> Xor3Certificate:
    """Build and EXACTLY self-check a degree-`degree` moment-matrix-PSD certificate
    for an UNSAT 3-XOR instance whose width-2·degree closure is conflict-free.

    ``instance`` is a sequence of ``(A, e)`` with ``A`` an iterable of variable
    indices and ``e ∈ {±1}``.  Refuses a satisfiable instance, a closure conflict
    (a refutation exists), or a non-block-rank-one moment matrix."""
    inst = [(frozenset(A), int(e)) for A, e in instance]
    for _, e in inst:
        if e not in (1, -1):
            raise ValueError("3-XOR clause signs must be ±1")
    if not _unsat_gf2(inst, n):
        raise ValueError("instance is SATISFIABLE — no SoS lower bound to certify (refused)")
    w = 2 * degree
    sgn, conflict = _closure(inst, w)
    if conflict:
        raise ValueError(
            f"width-{w} closure has a SIGN CONFLICT — a degree-{degree} refutation "
            "exists, so the moment matrix is not PSD (refused, negative control)"
        )
    idx = _index_sets(n, degree)
    reps, assign, sigma = _class_partition(sgn, idx)
    if reps is None:
        raise ValueError(
            "moment matrix is not block-rank-one (closure not transitive on the "
            "index sets) — refused (negative control)"
        )
    # block-rank-one SOS: xᵀMx = Σ_class ( Σ_{S∈class} σ_S x_S )²
    sos_forms = []
    for c in range(len(reps)):
        form = sum(sigma[S] * _var(S) for S in idx if assign[S] == c)
        sos_forms.append(sp.expand(form))
    # exact self-check: xᵀMx − Σ forms² == 0, with M[S,T] = sgn(S⊕T) (0 if absent)
    xs = {S: _var(S) for S in idx}
    quad = sp.expand(sum(
        sgn.get(S ^ T, 0) * xs[S] * xs[T] for S in idx for T in idx
    ))
    if sp.expand(quad - sum(f**2 for f in sos_forms)) != 0:
        raise ValueError("moment-PSD SOS self-check failed — certificate rejected")
    return Xor3Certificate(
        n=n, degree=degree, idx=tuple(idx), n_classes=len(reps),
        moment_quad=quad, sos_terms=tuple(sos_forms),
    )


def certify_xor3_point(family, pt, name):
    """Certify one 3-XOR instance from ``family.special[1](pt) -> (instance, n, degree)``."""
    spec = family.special[1](pt)
    instance, n = spec[0], spec[1]
    degree = spec[2] if len(spec) > 2 else 2
    cert = xor3_certificate(instance, n, degree)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# --------------------------------------------------------------------------
# Emitter
# --------------------------------------------------------------------------

@dataclass
class Xor3MomentPSDEmitter(Emitter):
    """Emit `0 ≤ xᵀMx` for the degree-d 3-XOR moment matrix via the block-rank-one
    SOS, discharged deterministically by `ring` (the SOS identity) + `positivity`."""

    def __post_init__(self):
        self.kind = "xor3_moment"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        from .expr import expr_lean
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: Xor3Certificate = inst.payload  # type: ignore[assignment]
            xsyms = [_var(S) for S in cert.idx]
            binders = " ".join(str(s) for s in xsyms)
            # the goal is the MOMENT-matrix quadratic xᵀMx; hid rewrites it to the
            # block-rank-one SOS (a ring identity, guaranteed by the self-check).
            quad_s = expr_lean(sp.expand(cert.moment_quad), tuple(xsyms))
            sos_s = " + ".join(f"({expr_lean(f, tuple(xsyms))})^2" for f in cert.sos_terms)
            lines.append(
                f"theorem {inst.lean_name} ({binders} : ℝ) :\n"
                f"    (0:ℝ) ≤ {quad_s} := by\n"
                f"  have hid : {quad_s} = {sos_s} := by ring\n"
                f"  rw [hid]; positivity\n"
            )
            nthm += 1
        return "".join(lines), nthm


def xor3_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a 3-XOR moment-PSD family (kind='xor3_moment').

    ``spec``: a callable ``pt -> (instance, n[, degree])`` where ``instance`` is a
    sequence of ``(A, e)`` clauses (``A`` variable indices, ``e ∈ {±1}``), ``n``
    the number of variables, ``degree`` the SoS degree (default 2).  Refuses a
    satisfiable instance, a closure conflict, or a non-block-rank-one matrix."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("xor3_moment", spec),
        constants=dict(constants or {}),
    )

"""Range-completeness emitter -- "every m < N satisfying P is in the explicit
list L", decided by the Lean kernel, with the surrogate-predicate bridge.

The shape (CN-1 emitter survey, phase 2, item N6; the kernel-checked template is
`mem_nonHeegner190` in the tenth-discriminant formalization, `CN1/Finite/Witnesses.lean`,
with `SqfBelow` and `sqfBelow_of_squarefree` in `CN1/Finite/SplitPrime.lean`):

    theorem <nm> : ∀ m ∈ Finset.range N, P' m → G₁ m → … → m ∉ <nm>_excl → m ∈ <nm>_list := by
      decide +kernel

where `P'` is a KERNEL-FRIENDLY SURROGATE for the property `P` one actually cares
about.  `Squarefree m` is the worked case: Mathlib's `Decidable (Squarefree n)`
goes through `Nat.minFac` (well-founded recursion), which does not reduce under
`decide`, so the coverage is decided against

    SqfBelow K m := ∀ k ∈ Finset.Icc 2 K, ¬ k * k ∣ m

and a once-proved bridge lemma `Squarefree m → SqfBelow K m` (a four-line tactic
proof from `Nat.isUnit_iff` and `omega`) turns the kernel fact into the theorem
about `P`:

    theorem <nm>_of_squarefree : ∀ m < N, Squarefree m → G₁ m → … → m ∉ excl → m ∈ list

The bridge is sound for EVERY K (it is the direction P → P').  The bound
K² > N is what makes P' AGREE with P on the range: a non-squarefree m < N has a
square factor p² ≤ m < N, so p < √N ≤ K and `SqfBelow K` rejects it.  Without the
bound the coverage theorem would force L to contain non-squarefree numbers, so
the emitter REFUSES K² ≤ N (the certificate would be sound but the list would
not mean "the squarefree numbers").

Optionally the emitter also states the list's length (`<nm>_length`), its
duplicate-freedom (`<nm>_nodup`, `List.Nodup` by `decide +kernel`) and its
SOUNDNESS (`<nm>_sound : ∀ m ∈ list, m < N ∧ P' m ∧ G m ∧ m ∉ excl`); together
with the coverage theorem these say "L is EXACTLY the guarded set, of size |L|",
which is the list-completeness claim (idoneal numbers, class-number tables).

Everything decided by the kernel is first evaluated EXACTLY in Python through the
SAME AST (`emit_finite_decide`'s evaluator: this kind is a face of
`finite_decide`), so a false coverage, a list with a duplicate when `nodup` is
requested, a list element outside the guarded set when `soundness` is requested,
or a guard no element of the range satisfies (a VACUOUS coverage: any list would
do) is refused before any Lean is written.  The kernel is the final gate.

conjecture1_proved = False.  A finite decidability fact about an explicit list;
nothing here concerns zeta.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .emit_finite_decide import (
    And, Cmp, ForallIcc, ForallIn, ForallRange, Imp, Lit, Mul, NatTable, Not,
    NotMem, Mem, Var, _eval_prop, _lean_prop,
)
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

KIND = "range_completeness_decide"

#: `decide +kernel` on `∀ m ∈ Finset.range N, …` nests the `Finset.decidableDforallFinset`
#: instance N deep.  The CN-1 template at N = 653 set `maxRecDepth 8192`; the probe on
#: v4.32.0 (docs/EMITTER_RANGE_COMPLETENESS_DECIDE_DESIGN_2026-10-22.md) found the
#: default depth sufficient up to N = 2000.  Emitted per theorem as `set_option … in`
#: anyway (free, and the template set it); `max_rec_depth` overrides it.
DEFAULT_MAX_REC_DEPTH = 8192


# ------------------------------------------------------------ the surrogate

def _is_squarefree(m: int) -> bool:
    """Exact `Squarefree m` on ℕ (0 is not squarefree; 1 is)."""
    if m == 0:
        return False
    k = 2
    while k * k <= m:
        if m % (k * k) == 0:
            return False
        k += 1
    return True


@dataclass(frozen=True)
class SquarefreeSurrogate:
    """P = `Squarefree m` with surrogate P' = `SqfBelow K m := ∀ k ∈ Icc 2 K, ¬ k*k ∣ m`.

    `k` is the surrogate's bound K.  `guard(var)` is P' as a `finite_decide` AST
    node (what the kernel decides); `bridge_lean(nm, var)` is the once-proved
    `P → P'` lemma; `real_lean(var)` is the hypothesis of the consumer theorem.
    """

    k: int

    def check_bound(self, n: int) -> None:
        if self.k < 2:
            raise ValueError(
                f"{KIND} REFUSED: the squarefree surrogate needs K >= 2, got K = {self.k}")
        if self.k * self.k <= n:
            raise ValueError(
                f"{KIND} REFUSED: surrogate bound K^2 > N fails ({self.k}^2 = "
                f"{self.k * self.k} <= {n}); SqfBelow {self.k} would be weaker than "
                f"Squarefree on the range")

    def guard(self, var: str):
        return ForallIcc("k", 2, self.k,
                         Not(Cmp("dvd", Mul(Var("k"), Var("k")), Var(var))))

    def holds_exact(self, m: int) -> bool:
        """P' evaluated exactly (used only to cross-check the bound against P)."""
        return all(m % (k * k) != 0 for k in range(2, self.k + 1))

    @staticmethod
    def real_holds_exact(m: int) -> bool:
        return _is_squarefree(m)

    @staticmethod
    def real_lean(var: str) -> str:
        return f"Squarefree {var}"

    @staticmethod
    def bridge_name(nm: str) -> str:
        return f"{nm}_sqfBelow_of_squarefree"

    @staticmethod
    def consumer_suffix() -> str:
        return "_of_squarefree"

    def bridge_lean(self, nm: str, var: str) -> str:
        """`Squarefree m → ∀ k ∈ Finset.Icc 2 K, ¬ (k * k) ∣ m`: `hm k h : IsUnit k`,
        `Nat.isUnit_iff` gives `k = 1`, and `2 ≤ k` from `Finset.mem_Icc` closes by `omega`."""
        guard = _lean_prop(self.guard(var), nm)
        return (
            f"/-- Bridge: Mathlib's `Squarefree` implies the kernel-friendly surrogate "
            f"`SqfBelow {self.k}` (sound for every bound K). -/\n"
            f"theorem {self.bridge_name(nm)} {{{var} : ℕ}} (hm : Squarefree {var}) :\n"
            f"    {guard} := by\n"
            f"  intro k hk h\n"
            f"  have := Nat.isUnit_iff.mp (hm k h)\n"
            f"  rw [Finset.mem_Icc] at hk\n"
            f"  omega\n"
        )


# ------------------------------------------------------------- certificate

def _nat(v, what: str) -> int:
    """A natural-number literal; floats and negatives are refused (exact arithmetic only)."""
    if isinstance(v, bool) or isinstance(v, float) or isinstance(v, sp.Float):
        raise ValueError(f"{KIND} REFUSED: {what} must be an exact natural number, got {v!r}")
    iv = int(v)
    if iv != v or iv < 0:
        raise ValueError(f"{KIND} REFUSED: {what} must be an exact natural number, got {v!r}")
    return iv


@dataclass(frozen=True)
class RangeCompletenessCert:
    """The certified data of one instance; `emit_body` renders it verbatim.

    `members` IS the statement (the list L); `exclude` the optional exclusion list;
    `guards` extra decidable guards over `var` as `finite_decide` AST props;
    `surrogate` the P/P' pair (None for a purely decidable P); the three flags
    select the optional companion theorems.
    """

    n: int
    members: tuple
    exclude: tuple = ()
    guards: tuple = ()
    surrogate: SquarefreeSurrogate | None = None
    var: str = "m"
    emit_length: bool = False
    emit_nodup: bool = False
    emit_soundness: bool = False
    max_rec_depth: int = DEFAULT_MAX_REC_DEPTH

    # -- the two decided propositions, as finite_decide AST ------------------

    def _hyps(self) -> list:
        hyps = []
        if self.surrogate is not None:
            hyps.append(self.surrogate.guard(self.var))
        hyps.extend(self.guards)
        if self.exclude:
            hyps.append(NotMem(Var(self.var), "excl"))
        return hyps

    def coverage_prop(self):
        body = Mem(Var(self.var), "list")
        for h in reversed(self._hyps()):
            body = Imp(h, body)
        return ForallRange(self.var, self.n, body)

    def soundness_prop(self):
        parts = [Cmp("lt", Var(self.var), Lit(self.n))] + self._hyps()
        body = parts[-1]
        for p in reversed(parts[:-1]):
            body = And(p, body)
        return ForallIn(self.var, "list", body)

    def tables(self) -> dict:
        t = {"list": NatTable("list", self.members)}
        if self.exclude:
            t["excl"] = NatTable("excl", self.exclude)
        return t


def range_completeness_certificate(
    n, members, *, exclude=(), guards=(), surrogate=None, var: str = "m",
    emit_length: bool = False, emit_nodup: bool = False, emit_soundness: bool = False,
    max_rec_depth: int = DEFAULT_MAX_REC_DEPTH,
) -> tuple[RangeCompletenessCert, int]:
    """Build and EXACTLY check the certificate; returns `(cert, n_atomic_checks)`.

    Refuses: a float or negative anywhere; N = 0; a surrogate bound with K² ≤ N;
    a coverage that is FALSE (names the first uncovered element); a VACUOUS
    coverage (no element of the range satisfies the guards); a duplicate in L
    when `emit_nodup`; an element of L outside the guarded set when
    `emit_soundness`; a guard that mentions a variable other than `var`.
    """
    n = _nat(n, "N")
    if n == 0:
        raise ValueError(f"{KIND} REFUSED: N = 0 -- an empty range covers nothing")
    if not var.isidentifier():
        raise ValueError(f"{KIND} REFUSED: bad bound variable {var!r}")
    members = tuple(_nat(v, "a list element") for v in members)
    exclude = tuple(_nat(v, "an excluded element") for v in exclude)
    guards = tuple(guards)
    if surrogate is not None:
        if not isinstance(surrogate, SquarefreeSurrogate):
            raise ValueError(f"{KIND} REFUSED: unknown surrogate {surrogate!r}")
        surrogate.check_bound(n)
        # With K^2 > N the surrogate agrees with Squarefree on the whole range; a
        # disagreement here would be a bug in one of the two exact evaluators.
        for m in range(n):
            if surrogate.holds_exact(m) != surrogate.real_holds_exact(m):
                raise ValueError(
                    f"{KIND} REFUSED: surrogate disagrees with Squarefree at m = {m}")
    max_rec_depth = _nat(max_rec_depth, "max_rec_depth")
    cert = RangeCompletenessCert(
        n=n, members=members, exclude=exclude, guards=guards, surrogate=surrogate,
        var=var, emit_length=emit_length, emit_nodup=emit_nodup,
        emit_soundness=emit_soundness, max_rec_depth=max_rec_depth,
    )
    tables = cert.tables()
    counter = [0]

    # Vacuity: at least one element of the range must satisfy every guard.
    hyps = cert._hyps()
    survivors = [m for m in range(n)
                 if all(_eval_prop(h, {var: m}, tables, [0]) for h in hyps)]
    if not survivors:
        raise ValueError(
            f"{KIND} REFUSED: vacuous coverage -- no m < {n} satisfies the guards, "
            "so any list would do")

    # Coverage, evaluated through the SAME AST the kernel will decide.
    if not _eval_prop(cert.coverage_prop(), {}, tables, counter):
        missing = [m for m in survivors if m not in members]
        raise ValueError(
            f"{KIND} REFUSED: coverage is FALSE -- m = {missing[0]} satisfies the "
            f"guards but is not in the list ({len(missing)} uncovered)")

    if emit_nodup and len(set(members)) != len(members):
        dup = sorted(v for v in set(members) if members.count(v) > 1)
        raise ValueError(f"{KIND} REFUSED: nodup requested but the list repeats {dup}")
    if emit_soundness and not _eval_prop(cert.soundness_prop(), {}, tables, counter):
        bad = [v for v in members if v not in survivors]
        raise ValueError(
            f"{KIND} REFUSED: soundness requested but {bad[0]} is in the list and "
            f"outside the guarded set ({len(bad)} such)")
    if emit_length:
        counter[0] += 1
    if emit_nodup:
        counter[0] += 1
    return cert, counter[0]


def certify_range_completeness_point(family, pt, name):
    """`spec = family.special[1](pt)` is a dict of :func:`range_completeness_certificate`
    keyword arguments (`n`, `members`, and the optional ones)."""
    spec = dict(family.special[1](pt))
    n = spec.pop("n")
    members = spec.pop("members")
    cert, n_checks = range_completeness_certificate(n, members, **spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


# ------------------------------------------------------------------ Lean

def _list_def(name: str, values, doc: str) -> str:
    body = ", ".join(str(v) for v in values)
    return f"/-- {doc} -/\ndef {name} : List ℕ := [{body}]\n"


def render_instance(cert: RangeCompletenessCert, nm: str) -> str:
    """The Lean text of one instance (list defs, coverage, bridge, companions)."""
    var = cert.var
    lines = [_list_def(f"{nm}_list", cert.members, f"{nm}: the explicit list L.")]
    if cert.exclude:
        lines.append(_list_def(f"{nm}_excl", cert.exclude, f"{nm}: the excluded elements."))
    n_guards = len(cert._hyps())
    lines.append(
        f"-- {nm}: coverage of the guarded range by the list, exact-evaluated in Python\n"
        f"-- pre-emission through the same AST; kernel `decide` is the final gate.\n"
        f"set_option maxRecDepth {cert.max_rec_depth} in\n"
        f"theorem {nm} : {_lean_prop(cert.coverage_prop(), nm)} := by\n"
        f"  decide +kernel\n")
    if cert.surrogate is not None:
        s = cert.surrogate
        lines.append(s.bridge_lean(nm, var))
        hyp_names = ["hsq"] + [f"hg{i}" for i in range(1, n_guards)]
        extra = (" → ".join(_hyp_text(h, nm) for h in cert._hyps()[1:]) + " → "
                 if n_guards > 1 else "")
        consumer = f"{nm}{s.consumer_suffix()}"
        lines.append(
            f"/-- {nm}: the consumer-facing theorem about `{s.real_lean(var)}`, from the "
            f"kernel coverage through the bridge. -/\n"
            f"theorem {consumer} : ∀ {var} < {cert.n}, {s.real_lean(var)} → {extra}"
            f"{var} ∈ {nm}_list :=\n"
            f"  fun {var} hm {' '.join(hyp_names)} => {nm} {var} (Finset.mem_range.mpr hm) "
            f"({s.bridge_name(nm)} hsq) {' '.join(hyp_names[1:])}".rstrip() + "\n")
    if cert.emit_length:
        lines.append(
            f"theorem {nm}_length : {nm}_list.length = {len(cert.members)} := by\n"
            f"  decide +kernel\n")
    if cert.emit_nodup:
        lines.append(
            f"theorem {nm}_nodup : {nm}_list.Nodup := by\n"
            f"  decide +kernel\n")
    if cert.emit_soundness:
        lines.append(
            f"-- {nm}: soundness, every list element is in the guarded range (with the\n"
            f"-- coverage theorem: the list is EXACTLY the guarded set).\n"
            f"set_option maxRecDepth {cert.max_rec_depth} in\n"
            f"theorem {nm}_sound : {_lean_prop(cert.soundness_prop(), nm)} := by\n"
            f"  decide +kernel\n")
    return "\n".join(lines)


def _hyp_text(node, nm: str) -> str:
    text = _lean_prop(node, nm)
    return text if isinstance(node, (Cmp, Mem, NotMem, Not)) else f"({text})"


@dataclass
class RangeCompletenessEmitter(Emitter):
    """Emit list defs + `theorem <nm> : ∀ m ∈ Finset.range N, … → m ∈ <nm>_list := by
    decide +kernel`, the surrogate bridge and consumer theorem, and the optional
    length / nodup / soundness companions (ℕ only)."""

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        bodies: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: RangeCompletenessCert = inst.payload  # type: ignore[assignment]
            bodies.append(render_instance(cert, inst.lean_name))
            n_thm += 1 + (2 if cert.surrogate is not None else 0)
            n_thm += int(cert.emit_length) + int(cert.emit_nodup) + int(cert.emit_soundness)
        return "\n".join(bodies), n_thm

    def __post_init__(self):
        self.kind = KIND


def range_completeness_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a range-completeness family (kind ``range_completeness_decide``).

    ``spec: pt -> dict(n=N, members=L, exclude=…, guards=…, surrogate=…, var=…,
    emit_length=…, emit_nodup=…, emit_soundness=…, max_rec_depth=…)``.  The
    claim is evaluated exactly in Python at certification; the kernel re-decides it.
    """
    return InequalityFamily(
        name=name,
        symbols=(sp.symbols("n"),),
        grid=grid,
        lean_name=lean_name,
        special=(KIND, spec),
        constants=dict(constants or {}),
    )

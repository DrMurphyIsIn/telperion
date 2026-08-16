"""Symbolic certification: the gate between a family definition and emission.

certify() proves, in sympy over exact rationals, that every instance of the
family carries a Polya certificate (all-nonnegative-coefficient numerator over
a factored positive denominator), and — for bilinear families — that the
declared before/after difference IS the bilinear form of its four corner
certificates.  Nothing can be emitted without the CertifiedFamily witness this
function returns; a failure raises CertificationError naming every failing
(grid point, corner).

Trust note: none of this is trusted.  The Lean kernel re-proves every emitted
claim from scratch; these checks exist to catch errors before a CI round-trip,
not to establish truth.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

import sympy as sp

from .family import BoxAxis, GridPoint, InequalityFamily


class CertificationError(Exception):
    """One or more instances failed certification; .failures lists them all."""

    def __init__(self, failures: list[tuple[dict, str]]):
        self.failures = failures
        lines = "\n".join(f"  {pt}: {msg}" for pt, msg in failures)
        super().__init__(f"{len(failures)} instance(s) failed certification:\n{lines}")


@dataclass(frozen=True)
class PolyaCertificate:
    """num/den for one nonnegativity claim: num has all-nonnegative integer
    coefficients; den factors positively (sign pre-normalized)."""

    expr: sp.Expr           # the certified expression (0 <= expr)
    numerator: sp.Expr      # expanded, all-nonneg coefficients
    denominator: sp.Expr    # positive by factored structure
    lift_n: int = 0         # Polya lift exponent (0 = direct certificate)


@dataclass(frozen=True)
class BilinearDecomposition:
    """after - before = c1 + c2*q + c3*r + c4*(q*r) with q, r the box symbols."""

    c1: sp.Expr
    c2: sp.Expr
    c3: sp.Expr
    c4: sp.Expr
    q_axis: BoxAxis
    r_axis: BoxAxis


@dataclass(frozen=True)
class CertifiedInstance:
    point: dict
    lean_name: str
    corners: tuple[PolyaCertificate, ...]          # direct: 1; bilinear: 4 (00,01,10,11)
    decomposition: BilinearDecomposition | None = None
    den_atoms: tuple[sp.Expr, ...] = ()


@dataclass(frozen=True)
class CertifiedFamily:
    """The witness that certification ran green.  Only certify() constructs this."""

    family: InequalityFamily
    instances: tuple[CertifiedInstance, ...]
    checks_passed: int
    subdivisions: tuple = ()   # subdivision trees (see certify's bilinear path)

    def __post_init__(self):
        if not getattr(_construction_guard, "open", False):
            raise RuntimeError(
                "CertifiedFamily may only be constructed by certify()"
            )


class _Guard:
    open = False


_construction_guard = _Guard()


def polya_certify(
    expr: sp.Expr, syms: Sequence[sp.Symbol], lift_max: int = 0
) -> PolyaCertificate:
    """Certify 0 <= expr for nonnegative syms via nonneg-num / positive-den form.

    With lift_max > 0, a numerator refusal triggers Pólya lifting: multiply
    num AND den by (1 + Σsyms)^N (N ≤ lift_max) — the lifted pair is again a
    Polya certificate.  Lifting certifies strict positivity only; claims
    touching an equality case never lift (see lift.py).

    Raises ValueError (with a reason) if the expression has no such form —
    that is a refusal, not a soundness event.
    """
    # exactly the origin generator's normal form: together -> fraction -> expand
    # (no simplify() — it can re-split the fraction and wreck the sign structure)
    num, den = sp.fraction(sp.together(expr))
    num, den = sp.expand(num), sp.expand(den)
    if syms:
        pd = sp.Poly(den, *syms)
        if all(c < 0 for c in pd.coeffs()):
            num, den = sp.expand(-num), sp.expand(-den)
        pn = sp.Poly(num, *syms)
        bad = [
            (m, c)
            for m, c in zip(pn.monoms(), pn.coeffs())
            if c < 0 or sp.Integer(c) != c
        ]
        lift_n = 0
        if bad and lift_max > 0:
            from .lift import polya_lift

            lifted = polya_lift(num, syms, lift_max)
            if lifted is not None:
                lift_n, num = lifted
                lifter = sp.expand((1 + sp.Add(*syms)) ** lift_n)
                den = sp.expand(den * lifter)
                bad = []
        if bad:
            raise ValueError(f"numerator not all-nonneg-integer: {bad[:3]}")
        const, factors = sp.factor_list(den)
        if const <= 0:
            raise ValueError(f"denominator constant {const} <= 0")
        for base, _ in factors:
            pb = sp.Poly(base, *syms)
            if not all(c > 0 for c in pb.coeffs()):
                raise ValueError(f"denominator factor {base} not all-positive")
    else:
        lift_n = 0
        if den < 0:
            num, den = -num, -den
        if num < 0:
            raise ValueError(f"negative constant {num}/{den}")
    return PolyaCertificate(expr=expr, numerator=num, denominator=den, lift_n=lift_n)


def restrict_instances(cf: CertifiedFamily, indices) -> CertifiedFamily:
    """A CertifiedFamily view holding a subset of instances (for per-unit
    rendering and sharding).  Internal: preserves the construction guard."""
    _construction_guard.open = True
    try:
        return CertifiedFamily(
            family=cf.family,
            instances=tuple(cf.instances[i] for i in indices),
            checks_passed=cf.checks_passed,
        )
    finally:
        _construction_guard.open = False


def _certify_box(family, pt, name, qa, ra, checks_box, depth, force_depth):
    """Certify one (possibly subdivided) box.  Returns (instances, tree, checks).

    tree: {"name", "q_axis", "r_axis"} for a leaf, plus {"axis", "mid",
    "children"} for an internal split node."""
    from .family import BoxAxis

    q, r = qa.symbol, ra.symbol
    diff = sp.expand(sp.together(family.after(pt) - family.before(pt)))
    pdiff = sp.Poly(diff, q, r)
    if pdiff.total_degree() > 2 or any(m[0] > 1 or m[1] > 1 for m in pdiff.monoms()):
        raise ValueError("difference is not bilinear in the box symbols")
    c1 = pdiff.coeff_monomial(1)
    c2 = pdiff.coeff_monomial(q)
    c3 = pdiff.coeff_monomial(r)
    c4 = pdiff.coeff_monomial(q * r)
    if sp.simplify(diff - (c1 + c2 * q + c3 * r + c4 * q * r)) != 0:
        raise ValueError("bilinear decomposition self-check failed")
    checks = 1
    corner_vals = [(qa.lo, ra.lo), (qa.lo, ra.hi), (qa.hi, ra.lo), (qa.hi, ra.hi)]
    certs, failed = [], []
    for idx, (qv, rv) in enumerate(corner_vals):
        try:
            certs.append(
                polya_certify(
                    c1 + c2 * qv + c3 * rv + c4 * qv * rv,
                    family.symbols,
                    lift_max=family.auto_lift,
                )
            )
            checks += 1
        except ValueError as e:
            failed.append((idx, str(e)))
    must_split = force_depth > 0
    if failed and depth <= 0 and not must_split:
        raise ValueError(f"corner {failed[0][0]:02b}: {failed[0][1]}")
    if failed or must_split:
        # split axis: prefer the axis whose hi-corner failed; alternate under force
        if failed:
            axis = "q" if any(idx >= 2 for idx, _ in failed) else "r"
        else:
            axis = "q" if force_depth % 2 == 1 else "r"
        if axis == "q":
            mid = (qa.lo + qa.hi) / 2
            subs = [
                (f"{name}_qL", BoxAxis(q, qa.lo, mid, qa.lo_is_floor), ra),
                (f"{name}_qR", BoxAxis(q, mid, qa.hi, True), ra),
            ]
        else:
            mid = (ra.lo + ra.hi) / 2
            subs = [
                (f"{name}_rL", qa, BoxAxis(r, ra.lo, mid, ra.lo_is_floor)),
                (f"{name}_rR", qa, BoxAxis(r, mid, ra.hi, True)),
            ]
        instances, children = [], []
        for sub_name, sqa, sra in subs:
            sub_inst, sub_tree, sub_checks = _certify_box(
                family, pt, sub_name, sqa, sra, checks_box,
                depth - 1, max(force_depth - 1, 0),
            )
            instances.extend(sub_inst)
            children.append(sub_tree)
            checks += sub_checks
        tree = {
            "name": name, "point": dict(pt), "q_axis": qa, "r_axis": ra,
            "axis": axis, "mid": mid, "children": children,
        }
        return instances, tree, checks
    decomp = BilinearDecomposition(c1, c2, c3, c4, qa, ra)
    atoms = tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=tuple(certs),
        decomposition=decomp, den_atoms=atoms,
    )
    return [inst], {"name": name, "point": dict(pt), "q_axis": qa, "r_axis": ra}, checks


def certify(family: InequalityFamily, progress=None, force_subdivide: int = 0) -> CertifiedFamily:
    """Run every self-check for every grid point; return the emission witness.

    progress: optional callable (i, total, point) invoked before each instance
    — long certifications (the R47 table runs ~6 min) should not be silent."""
    instances: list[CertifiedInstance] = []
    failures: list[tuple[dict, str]] = []
    subdivision_trees: list[dict] = []
    checks = 0
    seen_names: set[str] = set()
    total = family.grid.size()

    for i, pt in enumerate(family.grid.points(), 1):
        if progress is not None:
            progress(i, total, dict(pt))
        name = family.lean_name(pt)
        if name in seen_names:
            failures.append((dict(pt), f"duplicate lean_name {name!r}"))
            continue
        seen_names.add(name)
        try:
            if family.kind == "direct":
                cert = polya_certify(
                    family.target(pt), family.symbols, lift_max=family.auto_lift
                )
                checks += 1
                atoms = (
                    tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
                )
                instances.append(
                    CertifiedInstance(
                        point=dict(pt), lean_name=name, corners=(cert,),
                        decomposition=None, den_atoms=atoms,
                    )
                )
            else:
                qa, ra = family.box(pt)
                sub_inst, tree, box_checks = _certify_box(
                    family, pt, name, qa, ra, 0,
                    family.auto_subdivide, force_subdivide,
                )
                checks += box_checks
                instances.extend(sub_inst)
                if "children" in tree:
                    subdivision_trees.append(tree)
        except (ValueError, sp.PolynomialError) as e:
            failures.append((dict(pt), str(e)))

    if failures:
        raise CertificationError(failures)

    _construction_guard.open = True
    try:
        return CertifiedFamily(
            family=family,
            instances=tuple(instances),
            checks_passed=checks,
            subdivisions=tuple(subdivision_trees),
        )
    finally:
        _construction_guard.open = False

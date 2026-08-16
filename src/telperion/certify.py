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
    equation: tuple[sp.Expr, sp.Expr] | None = None   # identity claims: (lhs, rhs)
    witness: str | None = None                        # winning candidate label


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

    def witness_table(self) -> dict[str, str]:
        """lean_name -> winning witness label (the deloading_winner_table
        pattern), for export beside the frozen output."""
        return {
            i.lean_name: i.witness for i in self.instances if i.witness is not None
        }


class _Guard:
    open = False


_construction_guard = _Guard()


_ACTIVE_CACHE = None


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
    if _ACTIVE_CACHE is not None:
        from .cache import cert_key

        key = cert_key(expr, lift_max)
        got = _ACTIVE_CACHE.get(key)
        if got is not None:
            if not got.get("ok"):
                raise ValueError(got["reason"])
            return PolyaCertificate(
                expr=expr,
                numerator=sp.sympify(got["num"]),
                denominator=sp.sympify(got["den"]),
                lift_n=got["lift_n"],
            )
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
            reason = f"numerator not all-nonneg-integer: {bad[:3]}"
            if _ACTIVE_CACHE is not None:
                from .cache import cert_key

                _ACTIVE_CACHE.put(cert_key(expr, lift_max), {"ok": False, "reason": reason})
            raise ValueError(reason)
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
    if _ACTIVE_CACHE is not None:
        from .cache import cert_key

        _ACTIVE_CACHE.put(
            cert_key(expr, lift_max),
            {"ok": True, "num": sp.srepr(num), "den": sp.srepr(den), "lift_n": lift_n},
        )
    return PolyaCertificate(expr=expr, numerator=num, denominator=den, lift_n=lift_n)


def _dual_engine_check(family, pt, trials: int = 3) -> int:
    """Cross-check the sympy target against the family's independent
    (pure-Fraction) implementation at seeded exact points."""
    import random
    from fractions import Fraction

    if family.independent_target is None or family.target is None:
        return 0
    rng = random.Random(hash(str(sorted(pt.items()))) & 0xFFFF)
    target = family.target(pt)
    for _ in range(trials):
        point = {
            str(s): Fraction(rng.randint(0, 60), rng.randint(1, 6))
            for s in family.symbols
        }
        sym_val = target.subs({s: sp.Rational(point[str(s)]) for s in family.symbols})
        ind_val = family.independent_target(pt, point)
        if sym_val != sp.Rational(ind_val):
            raise ValueError(
                f"DUAL-ENGINE DISAGREEMENT at {point}: sympy={sym_val}, "
                f"independent={ind_val} — one implementation is wrong"
            )
    return trials


def _pin_checks(family, pt, cert) -> int:
    """The honesty declarations, enforced.  Returns the number of checks run;
    raises ValueError on a wrong tie declaration, an OVERCLAIMING certificate
    (positive slack at a declared tie), or an anchor mismatch."""
    checks = 0
    target = family.target(pt) if family.target is not None else None
    if family.ties is not None and target is not None:
        for tie in family.ties(pt):
            tval = sp.simplify(target.subs(tie))
            if tval != 0:
                raise ValueError(
                    f"declared tie {tie} is not tight: target = {tval}"
                )
            nval = sp.simplify(cert.numerator.subs(tie))
            if nval != 0:
                raise ValueError(
                    f"OVERCLAIM: certificate has slack {nval} at declared tie "
                    f"{tie} — the certificate does not achieve the tie"
                )
            checks += 2
    if family.anchors is not None and target is not None:
        for subs, val in family.anchors(pt):
            got = sp.simplify(target.subs(subs) - val)
            if got != 0:
                raise ValueError(
                    f"anchor mismatch at {subs}: off by {got} from declared {val}"
                )
            checks += 1
    return checks


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


_FORK_STATE: dict = {}


def _certify_point(args):
    """Per-point worker (fork-inherited family via _FORK_STATE in parallel mode)."""
    pt, force_subdivide = args
    family = _FORK_STATE["family"]
    name = family.lean_name(pt)
    try:
        if family.kind == "equation":
            lhs, rhs = family.equation(pt)
            if sp.simplify(sp.together(lhs - rhs)) != 0:
                raise ValueError("identity self-check failed: lhs - rhs != 0")
            atoms = tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
            inst = CertifiedInstance(
                point=dict(pt), lean_name=name, corners=(),
                decomposition=None, den_atoms=atoms, equation=(lhs, rhs),
            )
            return ("ok", [inst], None, 1)
        if family.kind == "witness":
            cands = list(family.witnesses(pt))
            cert, win, reasons = None, None, []
            for label, cand in cands:
                try:
                    cert = polya_certify(cand, family.symbols, lift_max=family.auto_lift)
                    win = label
                    break
                except ValueError as we:
                    reasons.append(f"{label}: {we}")
            if cert is None:
                tag = (
                    "PROVEN IMPOSSIBLE: the declared-COMPLETE candidate "
                    "space is exhausted"
                    if family.witnesses_complete
                    else "no certifiable witness"
                )
                raise ValueError(
                    f"{tag} among {len(cands)} candidate(s); "
                    + " | ".join(reasons[:3])
                )
            atoms = tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
            inst = CertifiedInstance(
                point=dict(pt), lean_name=name, corners=(cert,),
                decomposition=None, den_atoms=atoms, witness=win,
            )
            return ("ok", [inst], None, 1)
        if family.kind == "direct":
            cert = polya_certify(
                family.target(pt), family.symbols, lift_max=family.auto_lift
            )
            n_pin = _pin_checks(family, pt, cert) + _dual_engine_check(family, pt)
            atoms = tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
            inst = CertifiedInstance(
                point=dict(pt), lean_name=name, corners=(cert,),
                decomposition=None, den_atoms=atoms,
            )
            return ("ok", [inst], None, 1 + n_pin)
        qa, ra = family.box(pt)
        sub_inst, tree, box_checks = _certify_box(
            family, pt, name, qa, ra, 0, family.auto_subdivide, force_subdivide
        )
        return ("ok", sub_inst, tree if "children" in tree else None, box_checks)
    except (ValueError, sp.PolynomialError) as e:
        return ("fail", dict(pt), str(e), 0)


def certify(
    family: InequalityFamily,
    progress=None,
    force_subdivide: int = 0,
    workers: int = 1,
    cache_dir=None,
) -> CertifiedFamily:
    """Run every self-check for every grid point; return the emission witness.

    progress: optional callable (i, total, point) invoked before each instance
    — long certifications (the R47 table runs ~6 min) should not be silent.

    workers > 1 certifies grid points in parallel via fork-context
    multiprocessing (fork inherits the family's closures; unavailable on
    platforms without fork — falls back to serial).

    cache_dir enables the persistent certification cache (a performance
    layer only — the drift net and the kernel remain the arbiters)."""
    global _ACTIVE_CACHE
    if cache_dir is not None:
        from .cache import DiskCache

        _ACTIVE_CACHE = DiskCache(cache_dir)
    if workers > 1:
        import multiprocessing as mp

        try:
            ctx = mp.get_context("fork")
        except ValueError:
            ctx = None
        if ctx is not None:
            pts = list(family.grid.points())
            names = [family.lean_name(pt) for pt in pts]
            dupes = {n for n in names if names.count(n) > 1}
            if dupes:
                raise CertificationError(
                    [({}, f"duplicate lean_name {n!r}") for n in sorted(dupes)]
                )
            _FORK_STATE["family"] = family
            try:
                with ctx.Pool(workers) as pool:
                    results = pool.map(
                        _certify_point, [(pt, force_subdivide) for pt in pts]
                    )
            finally:
                _FORK_STATE.pop("family", None)
            instances, failures, trees, checks = [], [], [], 0
            for status, a, b, c in results:
                if status == "ok":
                    instances.extend(a)
                    if b is not None:
                        trees.append(b)
                    checks += c
                else:
                    failures.append((a, b))
            if failures:
                raise CertificationError(failures)
            _construction_guard.open = True
            try:
                return CertifiedFamily(
                    family=family,
                    instances=tuple(instances),
                    checks_passed=checks,
                    subdivisions=tuple(trees),
                )
            finally:
                _construction_guard.open = False
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
            if family.kind == "equation":
                lhs, rhs = family.equation(pt)
                if sp.simplify(sp.together(lhs - rhs)) != 0:
                    raise ValueError("identity self-check failed: lhs - rhs != 0")
                checks += 1
                atoms = (
                    tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
                )
                instances.append(
                    CertifiedInstance(
                        point=dict(pt), lean_name=name, corners=(),
                        decomposition=None, den_atoms=atoms, equation=(lhs, rhs),
                    )
                )
            elif family.kind == "witness":
                cands = list(family.witnesses(pt))
                cert = None
                reasons = []
                for label, cand in cands:
                    try:
                        cert = polya_certify(
                            cand, family.symbols, lift_max=family.auto_lift
                        )
                        win = label
                        break
                    except ValueError as we:
                        reasons.append(f"{label}: {we}")
                if cert is None:
                    tag = (
                        "PROVEN IMPOSSIBLE: the declared-COMPLETE candidate "
                        "space is exhausted"
                        if family.witnesses_complete
                        else "no certifiable witness"
                    )
                    raise ValueError(
                        f"{tag} among {len(cands)} candidate(s); "
                        + " | ".join(reasons[:3])
                    )
                checks += 1
                atoms = (
                    tuple(family.den_atoms(pt)) if family.den_atoms is not None else ()
                )
                instances.append(
                    CertifiedInstance(
                        point=dict(pt), lean_name=name, corners=(cert,),
                        decomposition=None, den_atoms=atoms, witness=win,
                    )
                )
            elif family.kind == "direct":
                cert = polya_certify(
                    family.target(pt), family.symbols, lift_max=family.auto_lift
                )
                checks += 1 + _pin_checks(family, pt, cert) + _dual_engine_check(family, pt)
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

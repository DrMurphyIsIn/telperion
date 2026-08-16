"""The telperion CLI: certify | emit | diff | probe.

Families live in ordinary Python modules; the CLI addresses them as
``path/to/family.py:attr`` where ``attr`` is a zero-arg function returning an
InequalityFamily (and similarly for profiles, emitter lists, and validation).

The enforced workflow holds on the command line too: ``emit`` requires a
validation source (``--validation`` or a ``validation()`` function in the
family module) — there is no flag to skip it.
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

from .certify import CertificationError, certify
from .emit import BilinearBoxEmitter, DirectPolyaEmitter
from .lean import LeanProfile
from .provenance import diff_frozen, freeze
from .workflow import ValidationReport, emit


def _load(spec: str):
    """Load ``path.py:attr`` and return the attribute (called if callable).

    The module is registered under a path-hashed name so a family file called
    family.py can never shadow (or be shadowed by) an installed module."""
    import hashlib as _hl

    path, _, attr = spec.partition(":")
    if not attr:
        raise SystemExit(f"expected path.py:attr, got {spec!r}")
    p = Path(path).resolve()
    modname = f"_telperion_family_{_hl.sha256(str(p).encode()).hexdigest()[:12]}"
    modspec = importlib.util.spec_from_file_location(modname, p)
    mod = importlib.util.module_from_spec(modspec)
    sys.path.insert(0, str(p.parent))
    try:
        modspec.loader.exec_module(mod)
    finally:
        sys.path.pop(0)
    obj = getattr(mod, attr)
    return obj() if callable(obj) else obj, mod


def _default_emitters(fam):
    return [DirectPolyaEmitter()] if fam.kind == "direct" else [BilinearBoxEmitter()]


def cmd_init(args) -> int:
    from .scaffold import init_project

    created = init_project(Path(args.directory), args.namespace)
    for f in created:
        print(f"created {f}")
    print("next: edit family.py, then `telperion certify family.py:family -v`")
    return 0


def cmd_certify(args) -> int:
    fam, _ = _load(args.family)
    progress = None
    if args.verbose:
        def progress(i, total, pt):
            print(f"  [{i}/{total}] {pt}", flush=True)
    try:
        cf = certify(fam, progress=progress, workers=args.workers)
    except CertificationError as e:
        print(f"REFUSED: {e}")
        return 1
    print(
        f"certified: {fam.name} — {len(cf.instances)} instance(s), "
        f"{cf.checks_passed} self-checks green"
    )
    return 0


def _resolve_emit(args):
    fam, mod = _load(args.family)
    cf = certify(fam)
    profile = _load(args.profile)[0] if args.profile else LeanProfile()
    if args.validation:
        validation = _load(args.validation)[0]
    elif hasattr(mod, "validation"):
        validation = mod.validation()
    else:
        raise SystemExit(
            "emit requires exact-numeric validation: pass --validation path.py:fn "
            "or define validation() in the family module (see METHODOLOGY.md)"
        )
    if not isinstance(validation, ValidationReport):
        raise SystemExit("validation source must return a ValidationReport")
    emitters = _load(args.emitters)[0] if args.emitters else _default_emitters(fam)
    return emit(cf, profile, emitters, validation, file_name=args.file_name)


def cmd_emit(args) -> int:
    res = _resolve_emit(args)
    out = Path(args.out)
    freeze(res, out)
    for fname in res.files:
        print(f"wrote {out / fname}  ({res.n_theorems} theorems, hash {res.input_hash[:16]})")
    return 0


def cmd_diff(args) -> int:
    res = _resolve_emit(args)
    rep = diff_frozen(res, Path(args.frozen))
    if not rep.ok:
        print("DRIFT:", *rep.details, sep="\n  ")
        return 1
    print("check: OK (regeneration matches frozen output byte-for-byte)")
    return 0


def cmd_verify(args) -> int:
    """Run every manifest check (regeneration diffs for all frozen families).

    Also fails if an examples/*/generate.py exists that the manifest does not
    list — a family cannot silently fall out of the drift-check net."""
    import subprocess
    import tomllib

    root = Path(args.manifest).resolve().parent
    with open(args.manifest, "rb") as f:
        manifest = tomllib.load(f)
    checks = manifest.get("check", [])
    listed = {str((root / c["script"]).resolve()) for c in checks}
    unlisted = [
        str(p)
        for p in sorted(root.glob("examples/*/generate.py"))
        if str(p.resolve()) not in listed
    ]
    if unlisted:
        print("MANIFEST INCOMPLETE — unlisted generate scripts:")
        for p in unlisted:
            print(f"  {p}")
        return 1
    failed = []
    for c in checks:
        if args.group != "all" and c.get("group", "quick") != args.group:
            continue
        name = c["name"]
        print(f"=== {name} ===", flush=True)
        r = subprocess.run(
            [sys.executable, str(root / c["script"]), "--check"],
            cwd=root,
            capture_output=True,
            text=True,
        )
        tail = (r.stdout + r.stderr).strip().splitlines()
        print("\n".join(tail[-3:]) if tail else "(no output)")
        if r.returncode != 0:
            failed.append(name)
    if failed:
        print(f"VERIFY FAILED: {failed}")
        return 1
    print("verify: all manifest checks green")
    return 0


def cmd_diagnose(args) -> int:
    """Triage: certifiable / provably false (witness) / non-Polya with hints."""
    import sympy as sp

    from .diagnose import diagnose_expr, diagnose_family

    if ":" in args.target and Path(args.target.partition(":")[0]).exists():
        fam, _ = _load(args.target)
        results = diagnose_family(fam, trials=args.trials)
        if not results:
            print(f"all instances of {fam.name} are certifiable")
            return 0
        for pt, d in results:
            print(f"[{pt}]")
            print(d.render())
        return 1
    syms = tuple(sp.Symbol(s.strip(), nonnegative=True) for s in args.symbols.split(","))
    from .parsing import safe_parse_expr

    expr = safe_parse_expr(args.target, syms)
    d = diagnose_expr(expr, syms, trials=args.trials)
    print(d.render())
    return 0 if d.verdict == "CERTIFIABLE" else 1


def cmd_margins(args) -> int:
    """Tightness analysis: where is the family tight, by how much elsewhere."""
    from .margins import margin_report

    fam, _ = _load(args.family)
    cf = certify(fam, force_subdivide=0)
    reports = margin_report(cf, samples=args.samples)
    tight = [r for r in reports if r.is_tight]
    print(f"{fam.name}: {len(reports)} certificates, {len(tight)} tight/marginal")
    shown = reports if args.all else reports[: max(len(tight), 10)]
    for r in shown:
        print("  " + r.render())
    if not args.all and len(shown) < len(reports):
        print(f"  ... {len(reports) - len(shown)} more (use --all)")
    return 0


def cmd_ties(args) -> int:
    """Exact tie points/faces of a single 0 <= expr claim."""
    import sympy as sp

    from .margins import tie_faces, tie_points
    from .parsing import safe_parse_expr

    syms = tuple(sp.Symbol(s.strip(), nonnegative=True) for s in args.symbols.split(","))
    expr = safe_parse_expr(args.expression, syms)
    num = sp.expand(sp.fraction(sp.together(expr))[0])
    try:
        faces = tie_faces(num, syms)
        if not faces:
            print("no ties on the orthant (positive constant term)")
        else:
            for face in faces:
                print("tie face: {" + ", ".join(f"{s} = 0" for s in face) + "}")
        return 0
    except ValueError:
        pts = tie_points(num, syms)
        if not pts:
            print("no exact ties found (mixed-sign numerator; absence NOT proven)")
            return 0
        for p in pts:
            print("tie point: " + ", ".join(f"{k} = {v}" for k, v in p.items()))
        return 0


def cmd_latex(args) -> int:
    """Paper-ready appendix, stamped with the same input hash as the Lean."""
    from .latex import latex_appendix
    from .provenance import family_hash
    from .lean import LeanProfile as _LP

    fam, mod = _load(args.family)
    profile = _load(args.profile)[0] if args.profile else (
        mod.profile() if hasattr(mod, "profile") else _LP()
    )
    cf = certify(fam)
    ihash = family_hash(fam, profile)
    text = latex_appendix(cf, ihash, blueprint=args.blueprint)
    if args.out:
        Path(args.out).write_text(text)
        print(f"wrote {args.out} (input-hash {ihash[:16]})")
    else:
        print(text)
    return 0


def cmd_export_certs(args) -> int:
    """CAS-neutral certificate JSON for independent rechecking."""
    from .interchange import write_certificates
    from .provenance import family_hash
    from .lean import LeanProfile as _LP

    fam, mod = _load(args.family)
    profile = mod.profile() if hasattr(mod, "profile") else _LP()
    cf = certify(fam)
    write_certificates(cf, family_hash(fam, profile), args.out)
    print(f"wrote {args.out}")
    return 0


def cmd_recheck(args) -> int:
    """Independent stdlib-only recheck of exported certificates."""
    from . import recheck as rc

    return rc.main([args.certificates])


def cmd_package(args) -> int:
    """Self-contained reviewer bundle: family, frozen Lean, certificates JSON,
    the standalone rechecker, and REVIEWING.md with the independent checks."""
    import shutil

    from .interchange import write_certificates
    from .provenance import family_hash
    from .lean import LeanProfile as _LP

    fam, mod = _load(args.family)
    profile = mod.profile() if hasattr(mod, "profile") else _LP()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    fam_path = Path(args.family.partition(":")[0]).resolve()
    shutil.copy(fam_path, out / fam_path.name)
    if args.frozen:
        shutil.copytree(args.frozen, out / "frozen", dirs_exist_ok=True)
    cf = certify(fam)
    ihash = family_hash(fam, profile)
    write_certificates(cf, ihash, out / "certificates.json")
    shutil.copy(Path(__file__).parent / "recheck.py", out / "recheck.py")
    (out / "REVIEWING.md").write_text(f"""# Reviewing {fam.name}

Input hash `{ihash[:16]}` — appears in the Lean file headers, the certificate
JSON, and any generated LaTeX; matching hashes = same mathematics.

Three INDEPENDENT one-command checks (each suffices to catch a false claim;
together they leave no single trusted component except the Lean kernel):

1. `python3 recheck.py certificates.json` — stdlib-only rational arithmetic:
   coefficient signs + factor positivity + identity spot-checks (no sympy).
2. Regenerate and diff: `telperion diff {fam_path.name}:<factory> --frozen frozen/`
   (requires telperion + sympy; detects any drift byte-for-byte).
3. `lake build` in the consuming Lean project — the kernel re-proves
   every theorem from first principles.
""")
    print(f"bundle at {out} ({len(cf.instances)} instance(s), hash {ihash[:16]})")
    return 0


def cmd_hunt(args) -> int:
    """Adversarially minimize a claim, exactly. A negative result is a disproof."""
    import sympy as sp

    from .hunt import hunt_diverse, hunt_evolve, hunt_minimum
    from .parsing import safe_parse_expr

    syms = tuple(sp.Symbol(s.strip(), nonnegative=True) for s in args.symbols.split(","))
    expr = safe_parse_expr(args.expression, syms)
    if args.mode == "diverse":
        results = hunt_diverse(expr, syms, iters=max(args.iters, 400))
        for r in results:
            print(r.render())
        return 1 if any(r.is_disproof for r in results) else 0
    res = (
        hunt_evolve(expr, syms, seed=0)
        if args.mode == "evolve"
        else hunt_minimum(expr, syms, iters=args.iters, restarts=args.restarts)
    )
    print(res.render() + f"  [{res.evaluations} exact evaluations]")
    return 1 if res.is_disproof else 0


def cmd_relax(args) -> int:
    """Smooth or arithmetic? Hunt the continuous interpolation of an integer axis."""
    from .relax import relax_probe

    fam, _ = _load(args.family)
    verdict = relax_probe(fam, args.axis, iters=args.iters)
    print(verdict.render())
    return 1 if verdict.verdict == "ARITHMETIC" else 0


def cmd_probe(args) -> int:
    """Quick answer to: does this expression have a Polya certificate?"""
    import sympy as sp

    from .certify import polya_certify

    syms = tuple(sp.Symbol(s.strip(), nonnegative=True) for s in args.symbols.split(","))
    from .parsing import safe_parse_expr

    expr = safe_parse_expr(args.expression, syms)
    try:
        cert = polya_certify(expr, syms)
    except ValueError as e:
        print(f"NOT CERTIFIABLE in this form: {e}")
        return 1
    print(f"certifiable: 0 <= ({cert.numerator}) / ({cert.denominator})")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="telperion")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("certify", help="run the symbolic self-checks for a family")
    p.add_argument("family", help="path/to/family.py:factory")
    p.add_argument("-v", "--verbose", action="store_true", help="per-instance progress")
    p.add_argument("--workers", type=int, default=1, help="parallel certification (fork)")
    p.set_defaults(fn=cmd_certify)

    p = sub.add_parser("init", help="scaffold a new Telperion proof project")
    p.add_argument("directory")
    p.add_argument("--namespace", default="MyProof")
    p.set_defaults(fn=cmd_init)

    for name, fn, extra in (
        ("emit", cmd_emit, True),
        ("diff", cmd_diff, True),
    ):
        p = sub.add_parser(name)
        p.add_argument("family")
        p.add_argument("--profile", help="path.py:factory for the LeanProfile")
        p.add_argument("--emitters", help="path.py:factory returning the emitter list")
        p.add_argument("--validation", help="path.py:fn returning a ValidationReport")
        p.add_argument("--file-name", default=None)
        if name == "emit":
            p.add_argument("-o", "--out", required=True)
            p.set_defaults(fn=cmd_emit)
        else:
            p.add_argument("--frozen", required=True)
            p.set_defaults(fn=cmd_diff)

    p = sub.add_parser("verify", help="run every manifest check (drift net for all frozen families)")
    p.add_argument("--manifest", default="telperion.toml")
    p.add_argument("--group", default="all", help="quick | heavy | all")
    p.set_defaults(fn=cmd_verify)

    p = sub.add_parser("diagnose", help="triage a refusal: false vs non-Polya vs misuse")
    p.add_argument("target", help="path.py:factory OR a raw sympy expression")
    p.add_argument("--symbols", default="u", help="symbols when target is an expression")
    p.add_argument("--trials", type=int, default=400)
    p.set_defaults(fn=cmd_diagnose)

    p = sub.add_parser("margins", help="tightness analysis: ties + margins per certificate")
    p.add_argument("family")
    p.add_argument("--samples", type=int, default=60)
    p.add_argument("--all", action="store_true")
    p.set_defaults(fn=cmd_margins)

    p = sub.add_parser("ties", help="exact tie points/faces of one expression")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u")
    p.set_defaults(fn=cmd_ties)

    p = sub.add_parser("latex", help="paper appendix in sync with the Lean (same input hash)")
    p.add_argument("family")
    p.add_argument("--profile")
    p.add_argument("-o", "--out")
    p.add_argument("--blueprint", action="store_true", help="leanblueprint node mode")
    p.set_defaults(fn=cmd_latex)

    p = sub.add_parser("export-certs", help="CAS-neutral certificate JSON")
    p.add_argument("family")
    p.add_argument("-o", "--out", required=True)
    p.set_defaults(fn=cmd_export_certs)

    p = sub.add_parser("recheck", help="stdlib-only independent recheck of exported certificates")
    p.add_argument("certificates")
    p.set_defaults(fn=cmd_recheck)

    p = sub.add_parser("package", help="self-contained reviewer bundle")
    p.add_argument("family")
    p.add_argument("-o", "--out", required=True)
    p.add_argument("--frozen")
    p.set_defaults(fn=cmd_package)

    p = sub.add_parser("hunt", help="adversarial exact minimization (negative = disproof)")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u")
    p.add_argument("--iters", type=int, default=400)
    p.add_argument("--restarts", type=int, default=6)
    p.add_argument("--mode", default="descent", choices=["descent", "evolve", "diverse"],
                   help="descent = coordinate descent; evolve = GA + memetic refinement; "
                        "diverse = MAP-Elites archive of distinct near-tight points")
    p.set_defaults(fn=cmd_hunt)

    p = sub.add_parser("relax", help="smooth-vs-arithmetic verdict for an integer grid axis")
    p.add_argument("family")
    p.add_argument("--axis", required=True)
    p.add_argument("--iters", type=int, default=200)
    p.set_defaults(fn=cmd_relax)

    p = sub.add_parser("probe", help="check one expression for a Polya certificate")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u", help="comma-separated nonneg symbols")
    p.set_defaults(fn=cmd_probe)

    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())

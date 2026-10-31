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
    if fam.kind == "direct":
        return [DirectPolyaEmitter()]
    if fam.kind == "equation":
        from .emit_facts import IdentityEmitter

        return [IdentityEmitter()]
    return [BilinearBoxEmitter()]


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
        cf = certify(fam, progress=progress, workers=args.workers,
                     profile=args.profile, budget_seconds=args.budget)
    except CertificationError as e:
        print(f"REFUSED: {e}")
        return 1
    print(
        f"certified: {fam.name} — {len(cf.instances)} instance(s), "
        f"{cf.checks_passed} self-checks green"
    )
    if args.profile:
        from .certify import profile_report

        print(profile_report(cf))
    return 0


def _resolve_emit(args):
    from .certify import restrict_instances

    fam, mod = _load(args.family)
    cf = certify(fam)
    if getattr(args, "pilot", 0):
        cf = restrict_instances(cf, range(min(args.pilot, len(cf.instances))))
        print(f"[pilot] restricted to {len(cf.instances)} instance(s) — "
              "validate the template in CI before the full batch")
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


def _ledger_record(args, target: str, fingerprint: str, route: str,
                   verdict: str, detail: str) -> None:
    if not getattr(args, "ledger", None):
        return
    from .ledger import RouteLedger

    led = RouteLedger(args.ledger)
    if led.record(target, fingerprint, route, verdict, detail):
        led.save()
        print(f"[ledger] recorded {route} -> {verdict}")


def cmd_diagnose(args) -> int:
    """Triage: certifiable / provably false (witness) / non-Polya with hints."""
    import sympy as sp

    from .diagnose import diagnose_expr, diagnose_family
    from .ledger import fingerprint_text

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
    if d.verdict != "CERTIFIABLE":
        detail = d.detail
        if d.counterexample:
            detail += " witness: " + ", ".join(
                f"{k}={v}" for k, v in d.counterexample.items()
            )
        else:
            detail += " | " + " | ".join(d.hints[:2])
        _ledger_record(args, args.target, fingerprint_text(args.target),
                       "diagnose", d.verdict, detail)
    return 0 if d.verdict == "CERTIFIABLE" else 1


def cmd_margins(args) -> int:
    """Tightness analysis: where is the family tight, by how much elsewhere."""
    from .margins import margin_report

    fam, _ = _load(args.family)
    cf = certify(fam, force_subdivide=0)
    if args.adequacy:
        from .margins import bracket_adequacy

        rows = bracket_adequacy(cf)
        fragile = [r for r in rows if r.slack_ratio < 1]
        print(f"{fam.name}: {len(rows)} interval certificate(s), "
              f"{len(fragile)} FRAGILE (margin < bracket width)")
        for r in rows[: max(len(fragile), 10)]:
            print("  " + r.render())
        return 0
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


def cmd_lint_lean(args) -> int:
    """Static soundness pre-check of an emitted Lean file — the "green build !=
    proved" classes (sorry/admit, axiom, empty `:= by` block, missing type
    ascription, `Prop := True` trivial stub) that the kernel would accept or
    that CI would pass while nothing was proved.  Complements `verify` (the
    structural drift net) and the in-`emit()` gate; use it on any hand-touched
    or externally supplied .lean before trusting a green build."""
    from .lean_lint import lint_lean_file

    issues = lint_lean_file(args.file)
    if not issues:
        print(f"lint-lean {args.file}: OK (no soundness issues)")
        return 0
    for i in issues:
        print(f"{args.file}:{i.line}: [{i.code}/{i.severity}] {i.message}")
    fatal = any(i.severity == "error" for i in issues) or (args.strict and issues)
    return 1 if fatal else 0


def cmd_lint_provenance(args) -> int:
    """Provenance-header lint for ported files (spec 7.4): every file this counts as
    "ported" -- a `ported`/`adapted`/`copied from` mention in its own first 30 lines, or
    a name in `<dir>/PORTED.toml` -- must carry a `-- Provenance: repo=... file=...
    commit=<40-hex>` line in that same window. Exits 1 and prints every problem
    `missions.process.provenance_problems` reports; 0 and a single OK line otherwise.

    Fix round 1 (Minor): a *dir* that does not exist, or that exists but is not a
    directory, used to print a silent "OK" (`os.walk` on a missing path yields
    nothing, and `_load_ported_toml_safe`'s FileNotFoundError branch reports no
    problem either) -- a typo'd path would pass as cleanly as a real, clean campaign,
    exactly the kind of thing that could mask a CI misconfiguration. That now exits 2
    with a one-line message naming the path, before `provenance_problems` is ever
    called."""
    from .missions.process import provenance_problems

    root = Path(args.dir)
    if not root.is_dir():
        print(f"lint-provenance {root}: not a directory")
        return 2
    problems = provenance_problems(root)
    if not problems:
        print(f"lint-provenance {root}: OK (no provenance problems)")
        return 0
    for p in problems:
        print(f"{root}: {p}")
    return 1


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
    if res.is_disproof:
        from .ledger import fingerprint_text

        _ledger_record(
            args, args.expression, fingerprint_text(args.expression),
            "hunt", "DISPROOF",
            f"exact minimum {res.minimum} at "
            + ", ".join(f"{k}={v}" for k, v in res.argmin.items()),
        )
    return 1 if res.is_disproof else 0


def cmd_relax(args) -> int:
    """Smooth or arithmetic? Hunt the continuous interpolation of an integer axis."""
    from .relax import relax_probe

    from .ledger import fingerprint_text

    fam, _ = _load(args.family)
    verdict = relax_probe(fam, args.axis, iters=args.iters)
    print(verdict.render())
    if verdict.verdict == "ARITHMETIC":
        _ledger_record(
            args, fam.name, fingerprint_text(fam.name + args.axis),
            "relax", "ARITHMETIC",
            f"axis {args.axis}: relaxation fails at "
            + ", ".join(f"{k}={v}" for k, v in verdict.witness.items())
            + " — smooth certificates cannot close this family",
        )
    return 1 if verdict.verdict == "ARITHMETIC" else 0


def cmd_sharpen(args) -> int:
    """Certificate boundary vs truth boundary for a cap-parametrized family."""
    import sympy as sp

    from .probe_sharp import sharpness

    builder, _ = _load(args.builder)
    rep = sharpness(
        lambda cap: builder(cap),
        sp.Rational(args.lo),
        sp.Rational(args.hi),
        steps=args.steps,
    )
    print(rep.render())
    return 0


def cmd_cilog(args) -> int:
    """Parse a lake/CI log: error COUNT first, then known-failure-class matches."""
    from .cilog import parse_log

    text = Path(args.log).read_text()
    diag = parse_log(text)
    print(diag.render())
    return 1 if diag.total_errors else 0


def cmd_status(args) -> int:
    """STATUS.md generated by EXECUTING every manifest check — never asserted."""
    from .status import generate_status

    text, all_green = generate_status(Path(args.manifest), group=args.group)
    Path(args.out).write_text(text)
    print(f"wrote {args.out} — {'ALL GREEN' if all_green else 'FAILURES PRESENT'}")
    return 0 if all_green else 1


def cmd_review_brief(args) -> int:
    """Adversarial review checklist filled with the family's facts."""
    from .provenance import family_hash
    from .status import review_brief
    from .lean import LeanProfile as _LP

    fam, mod = _load(args.family)
    profile = mod.profile() if hasattr(mod, "profile") else _LP()
    text = review_brief(fam, args.family, family_hash(fam, profile))
    if args.out:
        Path(args.out).write_text(text)
        print(f"wrote {args.out}")
    else:
        print(text)
    return 0


def cmd_ledger(args) -> int:
    """Render the route ledger as ROUTES.md."""
    from .ledger import RouteLedger

    led = RouteLedger(args.ledger)
    text = led.render_md()
    if args.out:
        Path(args.out).write_text(text + "\n")
        print(f"wrote {args.out} ({len(led.entries)} entr(ies))")
    else:
        print(text)
    return 0


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


def cmd_prove(args) -> int:
    """Single-goal backend: emit Lean for 0 <= <expr>, or triage the refusal.

    Lean goes to stdout on success; the triage goes to stderr.  Exit code:
    0 = proved, 2 = FALSE (rational counterexample), 3 = NOT_POLYA (hints),
    4 = CERTIFIABLE-but-unemitted (coverage gap).
    """
    import sympy as sp

    from .parsing import safe_parse_expr
    from .prove import prove_goal

    syms = tuple(sp.Symbol(s.strip(), nonnegative=True) for s in args.symbols.split(","))
    expr = safe_parse_expr(args.expression, syms)

    if getattr(args, "json", False):
        # the backend-bridge wire form: the full discharge contract on stdout,
        # for a Lean tactic frontend / LLM-prover tool call to consume.
        import json as _json

        from .tactic import discharge

        resp = discharge(expr, syms, aux_name=args.name)
        print(_json.dumps(resp))
        return 0 if resp["proved"] else {"FALSE": 2, "NOT_POLYA_IN_THIS_FORM": 3}.get(resp["verdict"], 4)

    res = prove_goal(expr, syms, name=args.name,
                     namespace=tuple(args.namespace.split(".")) if args.namespace else None,
                     trials=args.trials)
    if res.proved:
        print(res.lean)
        return 0
    print(res.render(), file=sys.stderr)
    return {"FALSE": 2, "NOT_POLYA_IN_THIS_FORM": 3}.get(res.verdict, 4)


def cmd_sonc(args) -> int:
    """Find + verify a SONC circuit-polynomial nonnegativity certificate. Exit 1 if none."""
    import sympy as sp

    from .parsing import safe_parse_expr
    from .sonc import find_circuit_certificate, verify_circuit_certificate

    syms = tuple(sp.Symbol(s.strip(), real=True) for s in args.symbols.split(","))
    p = safe_parse_expr(args.expression, syms)
    cert = find_circuit_certificate(p, syms)
    if cert is None:
        print("not a nonnegative circuit polynomial (not a single circuit, or |c_β| > Θ)")
        return 1
    if not verify_circuit_certificate(cert):
        print("certificate FAILED independent verification (bug)")
        return 2
    tight = "tight (=)" if cert.lhs_pow == cert.rhs_pow else "strict (<)"
    print(f"nonnegative circuit: exact AM-GM {cert.lhs_pow} <= {cert.rhs_pow} [{tight}], "
          f"λ={list(cert.lambdas)}, q={cert.q}")
    return 0


def cmd_psd(args) -> int:
    """Find + verify an exact LDLᵀ PSD certificate for a rational matrix.

    Matrix is a Python-literal list of rows, e.g. '[[2,1],[1,2]]'. Exit 1 if not
    PSD (indefinite / needs pivoting).
    """
    import ast

    import sympy as sp

    from .psd import find_psd_certificate, verify_psd_certificate

    rows = ast.literal_eval(args.matrix)
    A = sp.Matrix([[sp.Rational(x) for x in row] for row in rows])
    cert = find_psd_certificate(A)
    if cert is None:
        print("NOT PSD (indefinite, non-symmetric, or needs symmetric pivoting)")
        return 1
    if not verify_psd_certificate(cert):
        print("certificate FAILED independent verification (bug)")
        return 2
    kind = "positive definite" if cert.positive_definite else "positive semidefinite (singular)"
    print(f"{kind}: A = L D Lᵀ with D = diag({[cert.D[i, i] for i in range(A.rows)]})")
    return 0


def cmd_prime(args) -> int:
    """Find + verify a Pratt/Lucas primality certificate for n. Exit 1 if composite."""
    from .pratt import find_pratt_certificate, verify_pratt_certificate

    n = args.n
    cert = find_pratt_certificate(n)
    if cert is None:
        print(f"{n}: NOT PRIME (no Pratt certificate)")
        return 1
    if not verify_pratt_certificate(cert):
        print(f"{n}: certificate FAILED independent verification (bug)")
        return 2

    def _render(c, depth=0):
        pad = "  " * depth
        fac = " * ".join(f"{q}^{e}" if e > 1 else f"{q}" for q, e in c.factorization) or "1"
        print(f"{pad}{c.n}: prime — witness a={c.witness}, {c.n}-1 = {fac}")
        for q, _e in c.factorization:
            if q > 2 and q in c.sub_certificates:
                _render(c.sub_certificates[q], depth + 1)

    print(f"{n}: PRIME (Pratt certificate verified in exact arithmetic)")
    _render(cert)
    return 0


def cmd_audit(args) -> int:
    """Audit external Lean for sorry/axiom/stub/vacuity. Exit 1 if any error finding."""
    from .audit import audit_lean_file

    report = audit_lean_file(args.file)
    print(report.render())
    return 0 if report.ok else 1


def cmd_audit_closure(args) -> int:
    """Kernel-level closure audit of named theorems in a built Lake project.

    By default the audit runs as a KERNEL-REPLAY callback (closure_audit.run_closure_audit_replayed, step 5 Task 7):
    the project's modules are read as data and kernel-replayed into the pinned trusted env (--trusted-env, default
    $TELPERION_LEAN_ENV, checked against its trusted manifest), never imported, and no lake runs. The JSON carries
    `isolated: true` and the replay's `olean_sha256`/`olean_closure`, which `mission checks-record` requires to equal
    the probe's and the fingerprint's. `--legacy-import` runs the old script that IMPORTS the submission with
    `lake env lean` (NOT ISOLATED: the submission's lakefile, initializers and elaborators run in the audit and can
    forge it); its JSON says `isolated: false`, and `mission checks-record` refuses it for nodes created on or after
    the cutoff.

    Exit 0 PASS, 1 FAIL (a forbidden constant/module in the closure, a non-allowed axiom, a missing target, an
    untrusted axiom or a kernel rejection refused by the replay, or a scan hit with --fail-on-scan-hit), 2 when the
    audit could not run or Lean died before a verdict.  The JSON (--json) is the record; the terminal gets a summary.
    """
    import json as _json
    import shlex

    from . import closure_audit
    from .closure_audit import (AuditSpec, ClosureAuditError, DEFAULT_ABSENT_CONSTANTS,
                                DEFAULT_LIBRARY_ROOTS, PLACEHOLDER_NONCE, render_audit_callback,
                                render_audit_script)
    from .comparator import CLEAN_AXIOMS

    if args.spec:
        try:
            raw = _json.loads(Path(args.spec).read_text(encoding="utf-8"))
            spec = AuditSpec(**{k: (tuple(v) if isinstance(v, list) else v) for k, v in raw.items()})
        except (OSError, ValueError, TypeError) as exc:
            print(f"audit-closure: cannot read spec {args.spec}: {exc}")
            return 2
    else:
        if not args.imports or not args.target:
            print("audit-closure: pass --spec FILE, or --import MODULE... and --target NAME...")
            return 2
        try:
            spec = AuditSpec(
                imports=tuple(args.imports), targets=tuple(args.target),
                library_roots=tuple(args.library_root) if args.library_root else DEFAULT_LIBRARY_ROOTS,
                scan_patterns=tuple(args.scan or ()),
                absent_constants=tuple(args.absent_const) if args.absent_const else DEFAULT_ABSENT_CONSTANTS,
                absent_module_prefixes=tuple(args.absent_module or ()),
                allowed_axioms=tuple(args.allow_axiom) if args.allow_axiom else CLEAN_AXIOMS,
                include_recursors=not args.no_recursors,
                closure_out=args.closure_out,
            )
        except ValueError as exc:
            print(f"audit-closure: {exc}")
            return 2
    if args.script_path and not args.legacy_import:
        print("audit-closure: --script-path is for --legacy-import only (the replayed audit's script lives in a "
              "private temp dir)")
        return 2
    if args.render_only:
        try:
            text = (render_audit_script(spec) if args.legacy_import
                    else render_audit_callback(spec, PLACEHOLDER_NONCE))
        except ValueError as exc:
            print(f"audit-closure: {exc}")
            return 2
        Path(args.render_only).write_text(text, encoding="utf-8")
        what = "audit script" if args.legacy_import else "replay callback"
        print(f"rendered {what} to {args.render_only} (not run)")
        return 0
    try:
        if args.legacy_import:
            print("audit-closure: WARNING: --legacy-import IMPORTS the submission with `lake env lean`: NOT ISOLATED. "
                  "Its lakefile, initializers and elaborators run in the audit process and can forge the verdict. "
                  "`mission checks-record` refuses this output for nodes created on or after the cutoff; drop "
                  "--legacy-import for the kernel-replayed audit.", file=sys.stderr)
            res = closure_audit.run_closure_audit(spec, args.project, wrapper=args.wrapper, timeout=args.timeout,
                                                  script_path=args.script_path,
                                                  keep_script=bool(args.script_path))
        else:
            res = closure_audit.run_closure_audit_replayed(
                spec, Path(args.project), wrapper=None if args.wrapper is None else shlex.split(args.wrapper),
                timeout=args.timeout, **_trust_kwargs(args))
    except ClosureAuditError as exc:
        print(f"audit-closure: {exc}")
        return 2
    if args.fail_on_scan_hit and (res.scan_hits or res.scan_module_hits):
        res.failures.append(f"{len(res.scan_hits)} scan hit(s) and {len(res.scan_module_hits)} "
                            "module-name hit(s) with --fail-on-scan-hit")
        res.verdict = "FAIL"
    if args.json:
        Path(args.json).write_text(res.to_json() + "\n", encoding="utf-8")
    print(res.render())
    if not res.verdict:
        print(res.raw_tail)
        return 2
    return 0 if res.ok else 1


def _manifest_options_from_args(args):
    from .freeze_manifest import DEFAULT_INCLUDE_GLOBS, ManifestOptions, parse_kv_pairs

    return ManifestOptions(
        include_globs=tuple(args.include) if args.include else DEFAULT_INCLUDE_GLOBS,
        packages_dir=args.packages_dir,
        tools=parse_kv_pairs(args.tool or (), "tool"),
        extras=parse_kv_pairs(args.extra or (), "extra"),
        patches=parse_kv_pairs(args.patch or (), "patch"),
        include_ignored=bool(args.include_ignored),
        hash_toolchain_binary=not args.no_toolchain_binary,
    )


def cmd_freeze_manifest(args) -> int:
    """Pin a Lake project's source state (sources, lake files, toolchain + binary, dependency
    git state, tool binaries, extra files) as JSON, before a verdict-of-record run."""
    from .freeze_manifest import ManifestError, dumps_manifest, freeze_manifest, render_text

    try:
        doc = freeze_manifest(args.project, _manifest_options_from_args(args),
                              timestamp=not args.no_timestamp)
    except ManifestError as exc:
        print(f"freeze-manifest: {exc}")
        return 2
    Path(args.out).write_text(dumps_manifest(doc), encoding="utf-8")
    if args.text:
        Path(args.text).write_text(render_text(doc), encoding="utf-8")
    missing = [k for sec in ("lake_files", "files", "tools", "extras") for k, v in doc[sec].items()
               if v.get("missing")]
    print(f"manifest written: {args.out}  digest {doc['digest']}  "
          f"({len(doc['files'])} source files, {len(doc['dependencies'])} dependencies, "
          f"{len(doc['tools'])} tools, {len(doc['extras'])} extras)")
    for k in missing:
        print(f"  MISSING: {k}")
    return 1 if missing else 0


def cmd_verify_manifest(args) -> int:
    """Re-freeze and diff against a recorded manifest.  Exit 0 unchanged, 1 changed."""
    from .freeze_manifest import ManifestError, dumps_manifest, parse_kv_pairs, verify_manifest

    try:
        overrides = dict(parse_kv_pairs(args.tool or (), "tool")) or None
        diff, new = verify_manifest(args.manifest, args.project, tool_overrides=overrides)
    except ManifestError as exc:
        print(f"verify-manifest: {exc}")
        return 2
    if args.out:
        Path(args.out).write_text(dumps_manifest(new), encoding="utf-8")
    if args.json:
        import json as _json
        Path(args.json).write_text(_json.dumps(diff.to_dict(), indent=2) + "\n", encoding="utf-8")
    print(diff.render())
    return 0 if diff.unchanged else 1


def cmd_benchmark(args) -> int:
    """Run the certifiable-fragment benchmark; print the deterministic table."""
    from .benchmark import certifiable_seed_corpus, run_benchmark

    report = run_benchmark(certifiable_seed_corpus())
    print(report.render())
    return 0


def cmd_evolve(args) -> int:
    """Island MAP-Elites evolution toward a certifying unimodal genome."""
    from .evolve.cli import run_evolve

    argv = []
    argv += ["--islands", str(args.islands)]
    argv += ["--gens", str(args.gens)]
    argv += ["--seed", str(args.seed)]
    argv += ["--model", args.model]
    if args.no_llm:
        argv.append("--no-llm")
    return run_evolve(argv)


def cmd_palomar_mine(args) -> int:
    """Mine the Palomar registry for candidate Telperion emitter shapes.

    Default: fetch the live registry, classify by topic, print the mining report.
    `--poll` runs the incremental subroutine against a seen-state file (only NEW
    entries are surfaced) — the shape a scheduler calls on an interval.
    `--file` reads a local registry JSON instead of the network (offline)."""
    import json as _json

    from .palomar_mine import fetch_feed, fetch_registry, mine, mining_report, parse_feed, poll

    topics = args.topic.split(",") if args.topic else None
    fetch = fetch_feed if args.source == "feed" else fetch_registry
    if args.poll:
        cands = poll(args.state, topics=topics, fetch=fetch, min_score=args.min_score)
    else:
        if args.file:
            raw = Path(args.file).read_text()
            if args.source == "feed":
                entries = parse_feed(raw)
            else:
                data = _json.loads(raw)
                entries = data.get("entries", data) if isinstance(data, dict) else data
        else:
            entries = fetch()
        cands = mine(entries, topics=topics, min_score=args.min_score)
    if args.json:
        from dataclasses import asdict
        print(_json.dumps([asdict(c) for c in cands], indent=2))
    else:
        print(mining_report(cands))
    return 0


def cmd_source_mine(args) -> int:
    """Mine a math source (or all) for candidate Telperion emitter/skill leads.

    Generalizes `palomar-mine` across pluggable sources (palomar, arxiv, github,
    zulip), tagging each lead by lead_type (formalized-certificate → port, vs
    raw-math → formalize-first).  `--poll` is the recurring per-source form
    (one seen-state file per source under `--state-dir`)."""
    import json as _json

    from .source_mining import ALL_SOURCES, build_source, mine_source, poll_source, source_report

    names = list(ALL_SOURCES) if args.source == "all" else [args.source]
    topics = args.topic.split(",") if args.topic else None
    all_cands = []
    for name in names:
        try:
            src = build_source(name)
        except Exception as exc:
            print(f"# source {name!r} unavailable: {type(exc).__name__}: {exc}")
            continue
        if args.poll:
            sdir = Path(args.state_dir).expanduser()
            sdir.mkdir(parents=True, exist_ok=True)
            state = sdir / f"{name}-seen.json"
            all_cands += poll_source(src, state, topics=topics, min_score=args.min_score)
        else:
            all_cands += mine_source(src, src.fetch(), topics=topics, min_score=args.min_score)
    all_cands.sort(key=lambda c: (-c.score, c.source_name, c.entry_id))
    if args.json:
        from dataclasses import asdict
        print(_json.dumps([asdict(c) for c in all_cands], indent=2))
    else:
        print(source_report(all_cands))
    return 0


def _p2m_workspace(args):
    from pathlib import Path as _P
    from .prove2me.workspace import Workspace
    ws = Workspace(root=_P(args.workspace) if args.workspace else None)
    ws.ensure_layout()
    return ws


def cmd_p2m_login(args) -> int:
    """Establish the auth chain: credentials -> 30-day key -> hourly token."""
    import getpass
    from .prove2me.api import Prove2MeClient
    ws = _p2m_workspace(args)
    c = Prove2MeClient(workspace=ws.root)
    email = args.email or input("prove2.me email: ")
    c.login(email, getpass.getpass("password: "))
    c.mint_api_key()
    c.refresh()
    print(f"authenticated; tokens in {c._tokens_path}")
    return 0


def cmd_p2m_missions(args) -> int:
    """List platform missions."""
    from .prove2me.api import Prove2MeClient
    ws = _p2m_workspace(args)
    c = Prove2MeClient(workspace=ws.root)
    c.ensure_auth()
    for m in c.missions():
        print(f"{m.get('id')}  {m.get('status', '?'):<10} {m.get('title', '')[:70]}")
    return 0


def cmd_p2m_triage(args) -> int:
    """Rank open milestones vs emitter registry."""
    from .prove2me.api import Prove2MeClient
    from .prove2me.ledger import AttemptLedger
    from .prove2me.triage import save_queue, triage
    ws = _p2m_workspace(args)
    c = Prove2MeClient(workspace=ws.root)
    c.ensure_auth()
    # LIVE-API adapter (2026-09-11): missions carry no status; milestones are
    # {completed, theorem:{id, theorem_name, status}}; the formal_statement and
    # preamble live on GET /theorems/:id. The triage target id is the THEOREM
    # id (what POST /verify wants).
    milestones = []
    for m in c.missions():
        for mil in c.milestones(str(m["id"])):
            if mil.get("completed"):
                continue
            thm_ref = mil.get("theorem") or {}
            thm_id = str(thm_ref.get("id", ""))
            if not thm_id or thm_ref.get("status") in ("Proved", "Disproved"):
                continue
            thm = c.theorem(thm_id)
            milestones.append({
                "id": thm_id,
                "mission_id": str(m["id"]),
                "status": "open",
                "formal_statement": thm.get("formal_statement", ""),
                "theorem_name": thm.get("theorem_name",
                                        thm_ref.get("theorem_name", "")),
                "preamble": thm.get("preamble", ""),
            })
    led = AttemptLedger(ws.root / "telperion_ledger.jsonl")
    q = triage(milestones, ledger=led)
    save_queue(q, ws.root / "queue.json")
    for item in q[:20]:
        print(f"{item.score:5.2f}  {item.milestone_id:<16} "
              f"{','.join(item.emitter_classes[:3])}")
    print(f"{len(q)} certificate-shaped milestones -> {ws.root / 'queue.json'}")
    return 0


def cmd_p2m_lift(args) -> int:
    """Scaffold a lift family for one milestone (statement fetched or passed)."""
    ws = _p2m_workspace(args)
    stmt = args.statement
    if not stmt:
        from .prove2me.api import Prove2MeClient
        c = Prove2MeClient(workspace=ws.root)
        c.ensure_auth()
        stmt = c.theorem(args.milestone_id).get("formal_statement", "")
        if not stmt:
            print("no formal_statement on that milestone")
            return 1
    name = args.name or f"M{args.milestone_id}"
    try:
        fam = ws.scaffold_lift(args.milestone_id, stmt, name=name)
    except FileExistsError as e:
        print(str(e))
        return 1
    print(f"lift stub: {fam}\nedit family()/validation(), then: "
          f"telperion p2m attempt {args.milestone_id} --name {name}")
    return 0


def cmd_p2m_attempt(args) -> int:
    """Certify+emit the lift, run invariants, build locally, submit (unless --no-submit)."""
    import hashlib
    import importlib.util
    from .prove2me.api import Prove2MeClient
    from .prove2me.attempt import run_attempt
    from .prove2me.ledger import AttemptLedger
    from .prove2me.triage import load_queue
    ws = _p2m_workspace(args)
    name = args.name or f"M{args.milestone_id}"
    fam_path = ws.root / "attempts" / name / "family.py"
    if not fam_path.exists():
        print(f"no lift at {fam_path}: run `telperion p2m lift` first")
        return 1
    spec = importlib.util.spec_from_file_location(f"p2m_lift_{name}", fam_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    from .certify import certify
    from .emit_facts import IdentityEmitter
    from .lean import LeanProfile
    from .workflow import emit
    emitters = getattr(mod, "EMITTERS", None) or [IdentityEmitter()]
    res = emit(certify(mod.family()), LeanProfile(), emitters, mod.validation(),
               file_name=f"{name}.lean")
    # res.files is a dict of filename -> Lean source text; guard against multi-file emit.
    files = list(res.files.values())
    if len(files) != 1:
        print(f"expected 1 emitted Lean file, got {len(files)}: {list(res.files)}")
        return 1
    lean_source = files[0]

    # F5: if the lift defines PROOF_BODY, compose the final submission as the
    # emitted file followed by a `theorem solution` block that closes the proof.
    # This is required for I3: the submitted source must contain formal_statement
    # verbatim and be named `solution`.  render_solution(imports=()) avoids a
    # duplicate `import Mathlib` header since the emitted file already has one.
    items = [i for i in load_queue(ws.root / "queue.json")
             if i.milestone_id == args.milestone_id] \
        if (ws.root / "queue.json").exists() else []
    if not items:
        from .prove2me.triage import QueueItem
        formal_stmt = getattr(mod, "FORMAL_STATEMENT", "")
        if not formal_stmt:
            print("family.py must define FORMAL_STATEMENT or run "
                  "`telperion p2m triage` first")
            return 1
        items = [QueueItem(args.milestone_id, "", formal_stmt,
                           tuple(type(e).__name__ for e in emitters), 0.0)]

    proof_body = getattr(mod, "PROOF_BODY", None)
    formal_stmt_for_composition = items[0].statement or getattr(mod, "FORMAL_STATEMENT", "")
    if proof_body and formal_stmt_for_composition:
        # Live contract: imports must be merged FIRST (theorem preamble +
        # emitted header), then preamble opens, emitted bodies, and the
        # verbatim `theorem solution` closing block (I3).
        from .prove2me.attempt import compose_submission
        lean_source = compose_submission(items[0].preamble, lean_source,
                                         formal_stmt_for_composition, proof_body)
    elif not proof_body:
        print("hint: lift defines no PROOF_BODY; submitting raw emitted file "
              "(will refuse unless it contains the formal statement verbatim)")

    c = Prove2MeClient(workspace=ws.root)
    if not args.no_submit:
        c.ensure_auth()
    led = AttemptLedger(ws.root / "telperion_ledger.jsonl")
    # Naming per vendored platform docs (Theorems.Thm_<id>); confirm/adjust
    # in live acceptance against the actual module path the server expects.
    rec = run_attempt(
        c, ws, items[0], lean_source,
        tuple(type(e).__name__ for e in emitters),
        hashlib.sha256(fam_path.read_bytes()).hexdigest()[:16],
        led, no_submit=args.no_submit, explanation=args.explanation or "",
        # Live contract: module slug is the theorem_name with '.' -> '_'
        # (references/prove.md); fall back to the id form if name unknown.
        target_module=("Theorems.Thm_" + items[0].theorem_name.replace(".", "_"))
        if items[0].theorem_name else f"Theorems.Thm_{args.milestone_id}",
    )
    print(f"{rec.verdict}  milestone={rec.milestone_id} "
          f"submission={rec.submission_id or '-'}")
    return 0 if rec.verdict in ("Proved", "Disproved", "DryRun") else 1


def cmd_p2m_status(args) -> int:
    """Print attempt ledger summary."""
    from .prove2me.ledger import AttemptLedger
    ws = _p2m_workspace(args)
    print(AttemptLedger(ws.root / "telperion_ledger.jsonl").render_status())
    return 0


def cmd_p2m_coverage(args) -> int:
    """Shape-rule vs registry coverage report."""
    import json as _json
    from .prove2me.triage import coverage_report
    rep = coverage_report()
    print(_json.dumps(rep, indent=1))
    return 0 if not rep["unknown_rule_classes"] else 1


def cmd_p2m_sync(args) -> int:
    """Clone or pull the official platform workspace repo.

    NOTE: do NOT route through _p2m_workspace here — that helper calls
    ensure_layout() unconditionally, which would create the directory structure
    before sync_official clones into it.  sync_official calls ensure_layout
    itself after a successful clone/pull.
    """
    from pathlib import Path as _P
    from .prove2me.workspace import Workspace
    root = _P(args.workspace) if args.workspace else None
    ws = Workspace(root=root)
    ws.sync_official(args.repo_url)
    print(f"workspace synced: {ws.root}")
    return 0



# ---------------------------------------------------------------------------
# mission sub-commands (Task M7)
# ---------------------------------------------------------------------------

def _missions_root(args) -> "Path":
    """Resolve the missions root from --missions-root or a sane per-repo default.

    Resolution order (first that exists wins):
    1. args.missions_root if explicitly set (passed as --missions-root)
    2. Path.cwd() / "missions"
    3. Path.cwd() / "telperion" / "missions"
    4. Walk cwd.parents upward; for each ancestor check ancestor/"missions"
       and ancestor/"telperion"/"missions"
    5. Fall through to Path.cwd() / "missions" (callers can mkdir as needed)
    """
    explicit = getattr(args, "missions_root", None)
    if explicit is not None:
        return Path(explicit)
    cwd = Path.cwd()
    search_dirs = [cwd] + list(cwd.parents)
    for d in search_dirs:
        for candidate in (d / "missions", d / "telperion" / "missions"):
            if candidate.is_dir():
                return candidate
    return cwd / "missions"


def _resolve_campaign(root: "Path", slug: str, campaign: "str | None") -> "Path | None":
    """Return the campaign root that owns *slug*, or None on error (already printed).

    If *campaign* is given: return root/campaign unconditionally (the caller
    must handle a missing campaign dir themselves, as usual).

    Otherwise: scan all campaign subdirs for nodes/<slug>.toml.
    - Exactly one hit   -> return that campaign root.
    - Zero hits         -> print message, return None.
    - Multiple hits     -> print message listing them with --campaign hint, return None.
    """
    if campaign:
        return Path(root) / campaign
    root = Path(root)
    if not root.is_dir():
        print(f"Missions root {root} does not exist; pass --missions-root or --campaign")
        return None
    hits = [
        d for d in sorted(root.iterdir())
        if d.is_dir() and (d / "mission.toml").exists()
        and (d / "nodes" / f"{slug}.toml").exists()
    ]
    if len(hits) == 1:
        return hits[0]
    if len(hits) == 0:
        print(f"No campaign contains node {slug!r}. Pass --campaign or check the slug.")
        return None
    names = ", ".join(h.name for h in hits)
    print(
        f"Node {slug!r} found in multiple campaigns: {names}. "
        "Pass --campaign to disambiguate."
    )
    return None


def _campaign_roots(root: "Path", campaign: "str | None") -> "list[Path]":
    """Return list of campaign roots under *root*.

    If *campaign* is given, return [root/campaign].
    Otherwise discover all subdirectories containing mission.toml, sorted.
    """
    root = Path(root)
    if campaign:
        return [root / campaign]
    return sorted(
        d for d in root.iterdir()
        if d.is_dir() and (d / "mission.toml").exists()
    )


def cmd_mission_status(args) -> int:
    from .missions.registry import load_campaign, render_status
    from .missions.claims import load_fresh_claims

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    for camp_root in roots:
        try:
            camp = load_campaign(camp_root)
        except Exception as exc:
            print(f"Error loading {camp_root.name}: {exc}")
            continue
        claims = load_fresh_claims(camp_root)
        print(render_status(camp, claims))
    return 0


def cmd_mission_open_leaves(args) -> int:
    from .missions.registry import load_campaign, open_leaves
    from .missions.claims import load_fresh_claims

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    for camp_root in roots:
        try:
            camp = load_campaign(camp_root)
        except Exception as exc:
            print(f"Error loading {camp_root.name}: {exc}")
            continue
        claims = load_fresh_claims(camp_root)
        include_claimed = getattr(args, "all", False)
        leaves = open_leaves(camp, claims=claims, include_claimed=include_claimed)
        for node in leaves:
            print(f"{node.name}  {node.title}")
    return 0


def cmd_mission_claim(args) -> int:
    from .missions.claims import claim
    from .missions.schema import ClaimError

    camp_root = _resolve_campaign(_missions_root(args), args.slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    ttl = getattr(args, "ttl", 24) or 24
    note = getattr(args, "note", "") or ""
    try:
        claim(camp_root, args.slug, args.session, ttl_hours=ttl, note=note)
    except ClaimError as exc:
        print(str(exc))
        return 1
    print(f"claimed {args.slug} for session {args.session}")
    return 0


def cmd_mission_release(args) -> int:
    from .missions.claims import release
    from .missions.schema import ClaimError

    camp_root = _resolve_campaign(_missions_root(args), args.slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        release(camp_root, args.slug, args.session)
    except ClaimError as exc:
        print(str(exc))
        return 1
    print(f"released {args.slug}")
    return 0


def cmd_mission_add(args) -> int:
    import dataclasses as _dc
    from datetime import date as _date

    from .missions.provenance import ProvenanceError, git_identity, require_identity, session_id
    from .missions.registry import load_campaign
    from .missions.schema import Author, Node, SchemaError, load_manifest, save_node, slug_of
    from .missions.statements import write_statement

    root = _missions_root(args) / args.campaign
    manifest = load_manifest(root / "mission.toml")

    # Statement authorship (2026-09-23): recorded so `mission audit` can refuse a read-back
    # from the same session or identity. Both are required; an anonymous statement has no
    # author to be independent of.
    identity = (getattr(args, "identity", None) or "").strip() or git_identity(root)
    session = session_id(getattr(args, "session", None))
    try:
        require_identity(identity, session, "add")
    except ProvenanceError as exc:
        print(str(exc))
        return 1

    # Load campaign to check for duplicate slugs
    try:
        camp = load_campaign(root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1

    new_slug = slug_of(args.name)
    if new_slug in camp.nodes:
        print(f"Node {new_slug!r} already exists in campaign {args.campaign!r}")
        return 1

    # Build statement text
    if args.statement:
        stmt_text = args.statement
    elif args.statement_file:
        try:
            stmt_text = Path(args.statement_file).read_text()
        except OSError as exc:
            print(f"Cannot read statement file {args.statement_file!r}: {exc}")
            return 1
    else:
        print("--statement or --statement-file required")
        return 1

    # Parse deps
    deps: tuple = ()
    if args.deps:
        deps = tuple(d.strip() for d in args.deps.split(",") if d.strip())

    today = _date.today().isoformat()
    node = Node(
        name=args.name,
        title=args.title,
        kind=args.kind,
        status="draft",
        depends_on=deps,
        statement_module=f"Statements.{new_slug}",
        created=today,
        updated=today,
        author=Author(identity=identity, session=session, date=today),
    )

    node_path = root / "nodes" / f"{new_slug}.toml"
    save_node(node, node_path)
    stmt_path = write_statement(root, node, stmt_text, manifest)
    print(f"node: {node_path}")
    print(f"statement: {stmt_path}")
    print(f"author: {identity} (session {session})")
    return 0


def cmd_mission_audit(args) -> int:
    import dataclasses as _dc
    from datetime import date as _date

    from .missions.provenance import (
        ProvenanceError, SelfAuditError, git_identity, independence_of,
        readback_text_problem, require_identity, session_id,
    )
    from .missions.registry import load_campaign, promote_to_open
    from .missions.schema import Readback, SchemaError, save_node, slug_of

    if not (args.text or "").strip():
        print("audit: --text must be non-empty. A read-back is the only thing standing "
              "between a wrong statement and the registry; an empty one promotes a draft "
              "while recording nothing.")
        return 1

    # The auditor is a structured identity (2026-09-23): git identity + session id, both
    # required, compared against the node's [author] block below. `--auditor` survives only
    # as a display label and defaults to the identity.
    identity = (getattr(args, "identity", None) or "").strip()
    session = session_id(getattr(args, "session", None))

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1

    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1

    if slug not in camp.nodes:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1

    node = camp.nodes[slug]
    identity = identity or git_identity(camp_root)
    try:
        require_identity(identity, session, "audit")
    except ProvenanceError as exc:
        print(str(exc))
        return 1

    # Content: a label is not a read-back.
    problem = readback_text_problem(args.text, node.title)
    if problem:
        print(f"audit: refused. {problem}")
        return 1

    # Independence: refuse the author's own session or identity. Nothing is written on
    # refusal, so a self-audit leaves no trace that could later pass for testimony.
    try:
        independence = independence_of(node.author, identity, session)
    except SelfAuditError as exc:
        print(f"audit: refused. {exc}")
        return 1
    if independence == "unverified":
        print(f"audit: WARNING: {slug} has no [author] block (registered before provenance "
              "was recorded), so the auditor cannot be checked against the author; the "
              "read-back is recorded as independence = \"unverified\".")

    today = _date.today().isoformat()
    label = (getattr(args, "auditor", None) or "").strip() or identity
    rb = Readback(
        text=args.text, auditor=label, date=today,
        auditor_identity=identity, auditor_session=session, independence=independence,
    )
    new_node = _dc.replace(node, readback=rb, updated=today)
    node_path = camp_root / "nodes" / f"{slug}.toml"
    save_node(new_node, node_path)
    camp.nodes[slug] = new_node

    # Promote draft -> open. promote_to_open is the authority on valid transitions:
    # it raises SchemaError for any non-draft status (proved, refuted, open,
    # deprecated) and for missing readback. Readback is always durably written
    # above before this call, so it survives a promote failure.
    try:
        promoted = promote_to_open(camp, slug)
        print(f"{slug}: status -> {promoted.status}")
        return 0
    except SchemaError as exc:
        print(f"{slug}: readback recorded; promote failed: {exc}")
        return 1


def cmd_mission_link(args) -> int:
    from .missions.registry import load_campaign, set_proof
    from .missions.schema import Proof, SchemaError, slug_of

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1

    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1

    # The artifact must actually be there. `link` validated only the two enums, so a
    # session could record a path that does not exist and see "proof link recorded"; because
    # the battery skips coherence checks for nodes that are not proved or refuted, the bogus
    # link stayed invisible to CI until someone ran `grant` (audit 2026-09-19).
    artifact_path = (camp_root / args.artifact).resolve()
    if not artifact_path.exists():
        print(f"{slug}: artifact {args.artifact!r} does not exist "
              f"(resolved to {artifact_path}); refusing to record the link.")
        return 1

    # Repointing a node that is already proved or refuted silently invalidates the evidence
    # its status rests on, while leaving the status in place.
    existing = camp.nodes.get(slug)
    if existing is not None and existing.status in ("proved", "refuted") \
            and not getattr(args, "force", False):
        print(f"{slug}: status is {existing.status!r}; repointing its artifact would leave "
              "the status resting on evidence nobody checked. Re-run with --force if that "
              "is genuinely intended.")
        return 1

    proof = Proof(
        artifact=args.artifact,
        artifact_kind=args.kind,
        via=args.via,
        closure_clean=False,
    )
    try:
        set_proof(camp, slug, proof)
    except (SchemaError, KeyError) as exc:
        print(str(exc))
        return 1
    print(f"{slug}: proof link recorded (status unchanged; use `grant` to flip)")
    return 0


def cmd_mission_attempt(args) -> int:
    from datetime import date as _date

    from .missions.attempts import Attempt, AttemptLog
    from .missions.schema import slug_of

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    ledger = AttemptLog(camp_root / "attempts.jsonl")
    attempt = Attempt(
        node=slug,          # store normalised slug, not raw args.slug
        session=args.session,
        route=args.route,
        verdict=args.verdict,
        detail=args.detail,
        date=_date.today().isoformat(),
    )
    ledger.append(attempt)
    print(f"attempt recorded: {slug} [{args.verdict}]")
    return 0


def cmd_mission_grant(args) -> int:
    from .missions.provenance import git_identity, session_id
    from .missions.registry import load_campaign
    from .missions.schema import SchemaError, slug_of
    from .missions.verify import GateError, grant_status

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1

    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1

    identity = (getattr(args, "identity", None) or "").strip() or git_identity(camp_root)
    session = session_id(getattr(args, "session", None))
    try:
        node = grant_status(camp, slug, identity=identity, session=session)
    except GateError as exc:
        print(str(exc))
        return 1
    except Exception as exc:
        # The gate's readers report an unreadable record as a refusal (process.
        # _load_freeze_safe); anything that still raises is a refusal too, never a traceback.
        print(f"Node {slug!r}: grant refused: {type(exc).__name__}: {exc}")
        return 1

    note = ""
    if node.proof is not None and node.proof.via == "reduction":
        note = f" (closure_clean={node.proof.closure_clean})"
    print(f"{slug}: status -> {node.status}{note}")
    if node.grant is not None:
        print(f"grant: artifact sha256 {node.grant.artifact_sha256[:16]}..., gate "
              f"{node.grant.gate_version}, by {node.grant.identity} (session {node.grant.session})")
    return 0


def cmd_mission_freeze(args) -> int:
    from datetime import date as _date

    from .missions.process import freeze, write_deviations_template_if_missing
    from .missions.provenance import ProvenanceError, git_identity, session_id
    from .missions.schema import SchemaError

    camp_root = _missions_root(args) / args.campaign
    if not camp_root.is_dir():
        print(f"Campaign {args.campaign!r} not found at {camp_root}")
        return 1

    identity = (getattr(args, "identity", None) or "").strip() or git_identity(camp_root)
    session = session_id(getattr(args, "session", None))
    try:
        doc = freeze(camp_root, identity=identity, session=session,
                    date=_date.today().isoformat())
    except (ProvenanceError, SchemaError, ValueError) as exc:
        print(str(exc))
        return 1

    print(f"{args.campaign}: frozen {doc['frozen']} by {doc['identity']} "
          f"(session {doc['session']}); {len(doc['statements'])} statement(s) recorded")
    print(f"commit {args.campaign}/FREEZE.toml now: an uncommitted freeze has no git "
          "history to verify version bumps and unfreeze entries against, and "
          "`mission verify` reports that as a problem once this campaign is post-cutoff.")

    # Step 5 Task 3: a freshly frozen campaign otherwise has no DEVIATIONS.md at all, and
    # every post-cutoff grant afterwards would be refused on "no DEVIATIONS.md" until
    # someone writes one by hand.
    if write_deviations_template_if_missing(camp_root):
        print(f"{args.campaign}/DEVIATIONS.md: wrote the template (no deviations recorded "
              "yet; edit it, or leave it as `none`).")
    return 0


def cmd_mission_deviations_readback(args) -> int:
    from datetime import date as _date

    from .missions.process import write_deviations_readback
    from .missions.provenance import git_identity, session_id

    camp_root = _missions_root(args) / args.campaign
    if not camp_root.is_dir():
        print(f"Campaign {args.campaign!r} not found at {camp_root}")
        return 1

    identity = (getattr(args, "identity", None) or "").strip() or git_identity(camp_root)
    session = session_id(getattr(args, "session", None))
    date = (getattr(args, "date", None) or "").strip() or _date.today().isoformat()
    try:
        doc = write_deviations_readback(camp_root, identity=identity, session=session, date=date)
    except ValueError as exc:
        print(str(exc))
        return 1

    print(f"{args.campaign}/DEVIATIONS.md read back by {doc['auditor_identity']} "
          f"(session {doc['auditor_session']}) on {doc['date']}; ledger sha256 "
          f"{doc['ledger_sha256'][:16]}...")
    return 0


def cmd_mission_unfreeze(args) -> int:
    from datetime import date as _date

    from .missions.process import unfreeze
    from .missions.schema import SchemaError

    camp_root = _missions_root(args) / args.campaign
    if not camp_root.is_dir():
        print(f"Campaign {args.campaign!r} not found at {camp_root}")
        return 1

    try:
        doc = unfreeze(camp_root, author=args.author, reason=args.reason,
                       readback_identity=args.readback_identity,
                       date=_date.today().isoformat())
    except (SchemaError, ValueError) as exc:
        print(str(exc))
        return 1

    print(f"{args.campaign}: unfrozen to version {doc['version']} by {args.author} "
          f"(read back by {args.readback_identity}); {len(doc['statements'])} statement(s) "
          "re-recorded")
    return 0


def cmd_mission_audit_file(args) -> int:
    from .missions.process import render_audit_file
    from .missions.schema import SchemaError

    camp_root = _missions_root(args) / args.campaign
    if not camp_root.is_dir():
        print(f"Campaign {args.campaign!r} not found at {camp_root}")
        return 1

    try:
        text = render_audit_file(camp_root)
    except (SchemaError, ValueError, OSError) as exc:
        print(str(exc))
        return 1

    out_path = camp_root / "lean" / "Audit.lean"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    print(f"{args.campaign}: wrote {out_path}")
    return 0


#: Upper bound on a `--print-axioms-out`/`--closure-json` file (fix round 1, Ruling 10,
#: minor finding): generous for either a `#print axioms` transcript or a closure audit
#: JSON, small enough that a bogus or truncated path cannot read gigabytes into memory
#: before `audit-crosscheck` can report a clean error.
_AUDIT_CROSSCHECK_INPUT_MAX_BYTES = 1 << 24


def _read_audit_crosscheck_input(path: Path, *, what: str) -> Optional[str]:
    """`path.read_text(encoding="utf-8")`, guarded (fix round 1, Ruling 10, minor
    finding): a size cap before reading, and a clean message -- never a traceback -- on a
    missing file, an unreadable one, or one that is not valid UTF-8. Returns None (having
    already printed why) on any problem."""
    try:
        size = path.stat().st_size
    except OSError as exc:
        print(f"cannot read {what} {path}: {exc}")
        return None
    if size > _AUDIT_CROSSCHECK_INPUT_MAX_BYTES:
        print(f"cannot read {what} {path}: larger than "
              f"{_AUDIT_CROSSCHECK_INPUT_MAX_BYTES} bytes")
        return None
    try:
        return path.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"cannot read {what} {path}: {exc}")
        return None
    except UnicodeDecodeError as exc:
        print(f"cannot read {what} {path}: not valid UTF-8 ({exc})")
        return None


def cmd_mission_audit_crosscheck(args) -> int:
    import json as _json

    from .missions.process import crosscheck_axioms, parse_print_axioms

    output = _read_audit_crosscheck_input(args.print_axioms_out, what="--print-axioms-out")
    if output is None:
        return 2
    try:
        print_axioms = parse_print_axioms(output)
    except ValueError as exc:
        print(f"cannot parse {args.print_axioms_out}'s #print axioms output: {exc}")
        return 2

    closure_text = _read_audit_crosscheck_input(args.closure_json, what="--closure-json")
    if closure_text is None:
        return 2
    try:
        closure = _json.loads(closure_text)
    except _json.JSONDecodeError as exc:
        print(f"cannot read {args.closure_json}: {exc}")
        return 2
    targets = closure.get("targets") if isinstance(closure, dict) else None
    if not isinstance(targets, list):
        print(f"{args.closure_json}: not `audit-closure --json` output (no \"targets\" list)")
        return 2
    closure_axioms = {
        t["name"]: t.get("axioms", [])
        for t in targets if isinstance(t, dict) and isinstance(t.get("name"), str)
    }

    try:
        problems = crosscheck_axioms(print_axioms, closure_axioms)
    except ValueError as exc:
        print(f"{args.closure_json}: malformed closure audit data: {exc}")
        return 2
    if problems:
        for p in problems:
            print(f"MISMATCH: {p}")
        return 1
    print(f"OK: {len(print_axioms)} theorem(s) agree between #print axioms and the closure "
          "audit")
    return 0


def cmd_mission_provenance_report(args) -> int:
    from .missions.provenance import render_provenance_report
    from .missions.registry import load_campaign

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    any_flagged = False
    for camp_root in roots:
        try:
            camp = load_campaign(camp_root)
        except Exception as exc:
            print(f"Error loading {camp_root.name}: {exc}")
            any_flagged = True
            continue
        text = render_provenance_report(camp)
        print(text, end="")
        if "\n  " in text:
            any_flagged = True
    return 1 if (any_flagged and getattr(args, "strict", False)) else 0


def cmd_mission_provenance_migrate(args) -> int:
    from .missions.provenance import migrate_unverified

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    total = 0
    for camp_root in roots:
        changed = migrate_unverified(camp_root)
        total += len(changed)
        print(f"{camp_root.name}: {len(changed)} read-back(s) marked independence = \"unverified\"")
    print(f"total: {total}")
    return 0


def cmd_mission_ci_record(args) -> int:
    """Record a run of a named CI job on a node's CURRENT artifact (owner ruling 2026-09-24).

    head_sha and conclusion come from `gh run view` unless given explicitly; the run must
    contain the named job. The record is a sidecar and never changes status; the gate and
    `verify` consult it when the node declares `requires_ci_job`.
    """
    import dataclasses as _dc
    import json as _json
    import subprocess as _sp
    from datetime import date as _date

    from .missions.provenance import sha256_file
    from .missions.registry import load_campaign
    from .missions.schema import CIRecord, SchemaError, save_node, slug_of

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1
    node = camp.nodes.get(slug)
    if node is None:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1
    if node.proof is None:
        print(f"{slug}: no artifact linked; a CI record is about an artifact.")
        return 1
    art = camp_root / node.proof.artifact
    if not art.exists():
        print(f"{slug}: artifact {node.proof.artifact!r} does not exist")
        return 1
    head_sha = (getattr(args, "head_sha", None) or "").strip()
    conclusion = (getattr(args, "conclusion", None) or "").strip()
    if not head_sha or not conclusion:
        try:
            out = _sp.run(["gh", "run", "view", str(args.run_id), "--json", "headSha,conclusion,jobs"],
                          capture_output=True, text=True, timeout=60, check=True).stdout
            info = _json.loads(out)
        except Exception as exc:  # gh missing, offline, bad id
            print(f"{slug}: could not read run {args.run_id} via gh ({exc}); pass --head-sha "
                  "and --conclusion explicitly.")
            return 1
        jobs = {j.get("name"): j.get("conclusion") for j in info.get("jobs", [])}
        if args.job not in jobs:
            print(f"{slug}: run {args.run_id} has no job named {args.job!r} "
                  f"(jobs: {', '.join(sorted(k for k in jobs if k))})")
            return 1
        head_sha = head_sha or str(info.get("headSha", ""))
        conclusion = conclusion or str(jobs[args.job] or info.get("conclusion") or "")
    try:
        rec = CIRecord(
            workflow=args.workflow.strip(), job=args.job.strip(), run_id=str(args.run_id).strip(),
            head_sha=head_sha, artifact_sha256=sha256_file(art), conclusion=conclusion,
            date=_date.today().isoformat(), run_url=(getattr(args, "run_url", None) or "").strip(),
        )
    except SchemaError as exc:
        print(f"{slug}: {exc}")
        return 1
    save_node(_dc.replace(node, ci_record=rec, updated=rec.date), camp_root / "nodes" / f"{slug}.toml")
    print(f"{slug}: CI record {rec.key} run {rec.run_id} ({rec.conclusion}) on artifact sha256 "
          f"{rec.artifact_sha256[:16]}... head {rec.head_sha[:9]}")
    return 0 if rec.conclusion == "success" else 1


def cmd_mission_rejudge_record(args) -> int:
    """Record a local Comparator run with nanoda ON for a `heavy_certificates` node.

    Hosted CI judges a heavy node Lean-kernel-only (its certificates exhaust a 16 GB
    runner under nanoda). The owner's rule: such a node stays proved only with a passing
    LOCAL re-judge -- Comparator, nanoda ON -- on its CURRENT artifact, run on a large
    machine at the pinned telperion/NANODA_REV. The verdict comes from the log text
    (`rejudge_log_verdict`: one passing REJUDGE-PART block per part the node's bundle renders,
    nanoda forced on), never from a flag: there is no `--pass`/`--fail` option. Refuses (exit 2,
    no record) when that bundle cannot be rendered.

    Owner ruling (fix round 1, 2026-10-27): a log must bind itself to ONE node and ONE
    artifact digest via a `REJUDGE-HEADER node=<slug> artifact_sha256=<64-hex>` line the
    re-judge runner writes before Comparator starts -- otherwise a passing log for a
    different node, or for an older artifact, could be recorded as THIS node's re-judge.
    Refuses (exit 2, no record written) when that header is missing, names a different
    node, or names an artifact digest that is not the one currently on disk. Also refuses
    (exit 2, no record) when the node is neither `heavy_certificates = true` nor carries a
    `[comparator]` record whose second kernel was off (`provenance.needs_rejudge`).

    Controller ruling 6 (2026-10-27): a node's status may be `proved`, OR `draft`/`open`
    with a proof link whose artifact exists on disk -- pre-grant judging, so a fresh heavy
    node can be re-judged locally BEFORE `mission grant` ever runs, closing the loop Task 5's
    `grant_status` check otherwise leaves shut (that check refuses to grant a heavy node with
    no passing re-judge, and a `proved`-only `rejudge-record` could never produce one for a
    node that isn't proved yet). Still refused (exit 2, no record): no proof link, a missing
    artifact, and status `deprecated` or `refuted` -- neither is a node a re-judge is ever
    meaningful for.

    Step 0b Task 3 (2026-10-28): a log carrying `REJUDGE-ROUTE nanoda-direct`
    (`nanoda_direct.run_direct`'s own route, for the 7 nodes no Comparator bundle can
    consume) is accepted for ANY proved node, heavy or not -- the `needs_rejudge` gate above
    is for routes Comparator judges; a nanoda-direct node was never a Comparator candidate to
    begin with. Its verdict comes from `rejudge_log_verdict`'s own route branch
    (`nanoda_direct.verdict_of_log`), never from rendering a bundle. The record's `route`
    field is set from the log, so `render_provenance_report` labels it distinctly from a
    Comparator re-judge.

    Controller Ruling 0b-9 (2026-10-28): a nanoda-direct log is REFUSED (exit 2, no
    record) for a node that `needs_rejudge` (Ruling 0b-4 at record time), and must bind
    itself to the node's own registered theorem and module (`_nanoda_direct_binding_problem`).
    """
    import dataclasses as _dc
    import hashlib as _hashlib
    import platform as _platform
    from datetime import date as _date

    from .missions.provenance import sha256_file
    from .missions.registry import load_campaign
    from .missions import rejudge as _rejudge
    from .missions.rejudge import parse_rejudge_header
    from .missions.schema import RejudgeRecord, SchemaError, save_node, slug_of

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1
    node = camp.nodes.get(slug)
    if node is None:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1
    if node.proof is None:
        print(f"{slug}: no artifact linked; a re-judge is about an artifact.", file=sys.stderr)
        return 2
    art = camp_root / node.proof.artifact
    if not art.exists():
        print(f"{slug}: artifact {node.proof.artifact!r} does not exist", file=sys.stderr)
        return 2
    if node.status != "proved" and node.status not in ("draft", "open"):
        print(f"{slug}: status is {node.status!r}; a re-judge may only be recorded for a "
              "'proved' node, or a 'draft'/'open' heavy node whose artifact is already on "
              "disk (pre-grant judging).", file=sys.stderr)
        return 2
    raw = args.log.read_bytes()
    text = raw.decode(errors="replace")
    # Step 0b Task 3 (2026-10-28): a nanoda-direct log (one of the 7 nodes no Comparator
    # bundle can consume) is accepted for a proved node that does NOT need_rejudge -- there is no
    # `[comparator]`-driven "this node is judged Lean-kernel-only" signal to gate on, because
    # these nodes were never judged by Comparator at all. The needs_rejudge gate below stays
    # exactly as it was for every other route.
    route = _rejudge.parse_rejudge_route(text)
    from .missions.provenance import needs_rejudge
    if route == "nanoda-direct" and needs_rejudge(node):
        # Controller Ruling 0b-9 (2026-10-28), Minor 2: Ruling 0b-4 at RECORD time. A node
        # that needs a Comparator re-judge (heavy, judge_via = "heavy", or judged
        # Lean-kernel-only) cannot be satisfied by nanoda-direct, so its record is refused
        # outright instead of being written and then flagged by `mission verify`.
        print(f"{slug}: needs a Comparator re-judge (heavy_certificates, judge_via = "
              "\"heavy\", or judged Lean-kernel-only); a nanoda-direct log cannot satisfy it "
              "(Ruling 0b-4). Refusing to record.", file=sys.stderr)
        return 2
    if route != "nanoda-direct":
        if not needs_rejudge(node):
            # Final-fix 1: the same predicate `rejudge_problem` uses -- the flag, OR a
            # `[comparator]` record saying nanoda was off -- so a node verify demands a re-judge
            # for can always get one recorded.
            print(f"{slug}: heavy_certificates is not set and its [comparator] record does not "
                  "say nanoda was off; a re-judge is only meaningful for a node hosted CI judges "
                  "Lean-kernel-only.", file=sys.stderr)
            return 2
    header = parse_rejudge_header(text)
    if header is None:
        print(f"{slug}: log has no 'REJUDGE-HEADER node=<slug> artifact_sha256=<64-hex>' "
              "line; the re-judge runner must write it before Comparator starts. Refusing "
              "to bind this log to any node.", file=sys.stderr)
        return 2
    header_node, header_sha = header
    if slug_of(header_node) != slug:
        print(f"{slug}: log's REJUDGE-HEADER names node {header_node!r}, not {slug!r}; "
              "refusing a log from a different node.", file=sys.stderr)
        return 2
    cur_sha = sha256_file(art)
    if header_sha != cur_sha:
        print(f"{slug}: log's REJUDGE-HEADER names artifact sha256 {header_sha[:12]}..., but "
              f"the artifact on disk is {cur_sha[:12]}...; re-run the re-judge on the "
              "CURRENT artifact.", file=sys.stderr)
        return 2
    if route == "nanoda-direct":
        # No Comparator bundle to render for these nodes; the verdict comes straight from
        # the log's own REJUDGE-EXPORT/REJUDGE-NANODA sections (nanoda_direct.verdict_of_log).
        parts: list = []
    else:
        # Final-fix 2: the verdict covers EVERY part of the node. Render its bundle the way the
        # queue does (nanoda forced on) to learn the parts; a log must hold exactly one passing
        # REJUDGE-PART block per part. No render, no expected count -> refuse, write nothing.
        try:
            parts = _rejudge.expected_part_slugs(camp_root, node, slug)
        except _rejudge.RejudgeSetupError as exc:
            print(f"{slug}: cannot render the node's bundle to learn its re-judge parts ({exc}); "
                  "refusing to record a verdict whose part count is unknown.", file=sys.stderr)
            return 2
    verdict = _rejudge.rejudge_log_verdict(text, parts)
    if route == "nanoda-direct":
        rc = _nanoda_direct_binding_problem(camp_root, node, slug, art, text, verdict)
        if rc:
            return rc
    rev = _nanoda_rev_path().read_text().strip()
    # Step 0b Task 1 (2026-10-28): bind the record to the artifact's WHOLE import closure,
    # not only the top-level file. The queue's header may already carry `closure_sha256=`
    # (computed by the same function, `provenance.closure_digest`); if so it must match the
    # CURRENT closure, or this is refused exactly like a stale artifact_sha256. If the header
    # predates closure binding (no such field), compute it now and say so in the note.
    from .missions.provenance import ClosureError, closure_digest, closure_files as _closure_files
    try:
        cur_closure_files = _closure_files(camp_root, node)
        cur_closure = closure_digest(camp_root, node)
    except ClosureError as exc:
        print(f"{slug}: cannot resolve its import closure ({exc}); refusing to record.",
              file=sys.stderr)
        return 2
    header_closure = _rejudge.parse_rejudge_header_closure(text)
    note = args.note
    if header_closure is not None:
        if header_closure != cur_closure:
            print(f"{slug}: log's REJUDGE-HEADER names closure_sha256 "
                  f"{header_closure[:12]}..., but the current import closure digests to "
                  f"{cur_closure[:12]}...; re-run the re-judge on the CURRENT closure.",
                  file=sys.stderr)
            return 2
    else:
        extra = "closure_sha256 computed at record time (log predates closure binding)"
        note = f"{note}; {extra}" if note else extra
    try:
        rec = RejudgeRecord(
            date=_date.today().isoformat(), machine=_platform.node(), nanoda_rev=rev,
            comparator_tag=args.comparator_tag, artifact_sha256=cur_sha,
            verdict=verdict, log_sha256=_hashlib.sha256(raw).hexdigest(),
            peak_rss_kb=args.peak_rss_kb, note=note,
            closure_sha256=cur_closure, closure_files=len(cur_closure_files),
            route=route,
        )
    except SchemaError as exc:
        print(f"{slug}: {exc}")
        return 1
    save_node(_dc.replace(node, rejudge=rec, updated=rec.date), camp_root / "nodes" / f"{slug}.toml")
    if verdict != "pass":
        print(f"REJUDGE FAIL {slug}: nanoda/Comparator did not accept -- REPORT TO OWNER",
              file=sys.stderr)
        return 1
    print(f"REJUDGE PASS {slug} nanoda={rev[:8]} artifact={rec.artifact_sha256[:12]}")
    return 0


def cmd_mission_checks_record(args) -> int:
    """Record the spec 5.2 checks (negation probe, closure audit, statement fingerprint) for a node.

    Every verdict is read from the checks' own JSON output, never from a flag:
    - `--probe-json`: `telperion probe-negation --json` stdout, {"verdict", "detail",
      "olean_sha256", "olean_closure"};
    - `--fingerprint-json`: `telperion fingerprint --json` stdout, {"fingerprints",
      "olean_sha256", "olean_closure"} (or {"error"}, refused);
    - `--closure-json`: the file `telperion audit-closure --json FILE` writes
      (closure_audit.AuditResult.to_json). PASS only when its "verdict" is "PASS" AND "ok" is
      true (a clean Lean exit); anything else, including no verdict, is recorded as FAIL.

    Ruling 9: the probe and the fingerprint must have run on the SAME replayed olean closure,
    so both JSONs must carry the same `olean_sha256`; it is stored next to the artifact's
    source sha256. Step 5 Task 7: so must the closure audit, which now runs as a kernel-replay
    callback: its JSON must say `isolated: true` and carry that same `olean_sha256`, so all
    three checks ran on ONE replayed closure (recorded as `closure_isolated`). For a node that
    needs checks (`provenance.checks_required`: created on or after the cutoff), a closure JSON
    that is not isolated (`audit-closure --legacy-import`, which imports the submission, or a
    JSON from before step 5) is refused; for an older node it is recorded with
    `closure_isolated` false. The fingerprinted theorem (`--target`, or the only one in the
    JSON) must also be one of the closure audit's targets. A `signoff:` in --note is free text:
    nothing checks the reviewer is independent of the author (see `provenance.checks_problem`).

    Ruling 12: the probe's `theorem` (and the fingerprint's, when it names one) must be that
    target, and both JSONs' `source_sha256` (the --file each check was given) must be the
    artifact's CURRENT sha256. A mismatch or an absent value is refused (final review I2).
    Final review I1: the target is the node's registered theorem
    (`guard_anchors.resolve_theorem`, the declaration the grant gate matches); a `--target`
    naming anything else is refused. Final review I3 (kept as a second line after step 5): the
    probe and fingerprint JSONs' replay `axioms` lists must agree, be a subset of CLEAN_AXIOMS
    and include the closure audit's axioms for the target; the list is recorded.

    The JSON inputs are unsigned operator files: reading verdicts from them (never from flags)
    guards against mistakes, not against an operator who writes them by hand.

    Refuses (exit 2, no record): a malformed or unreadable JSON, an unknown probe verdict, a
    missing or mismatched `olean_sha256`, an ambiguous or unaudited fingerprint target, no
    proof link or a missing artifact, status `deprecated` or `refuted`, a non-isolated closure
    JSON for a node that needs checks, a closure `olean_sha256` that is not the probe's. Otherwise writes the
    record and exits 0 when it passes `provenance.checks_problem`, 1 when it does not (e.g.
    VACUOUS, or PROBE_ONLY without a `signoff:` in --note). Never changes the node's status.
    """
    import dataclasses as _dc
    import json as _json
    from datetime import date as _date

    from .missions.provenance import CHECKS_CUTOFF, checks_problem, checks_required, sha256_file
    from .missions.registry import load_campaign
    from .missions.schema import PROBE_VERDICTS, ChecksRecord, SchemaError, save_node, slug_of

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1
    node = camp.nodes.get(slug)
    if node is None:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1

    def refuse(msg: str) -> int:
        print(f"{slug}: {msg}. Refusing to record.", file=sys.stderr)
        return 2

    if node.proof is None:
        return refuse("no artifact linked; the checks are about an artifact")
    art = camp_root / node.proof.artifact
    if not art.exists():
        return refuse(f"artifact {node.proof.artifact!r} does not exist")
    if node.status in ("deprecated", "refuted"):
        return refuse(f"status is {node.status!r}; checks are recorded for a node that is or "
                      "may become proved")

    docs = {}
    for name, path in (("probe", args.probe_json), ("fingerprint", args.fingerprint_json),
                       ("closure", args.closure_json)):
        try:
            docs[name] = _json.loads(Path(path).read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            return refuse(f"cannot read the {name} JSON {path}: {exc}")
        if not isinstance(docs[name], dict):
            return refuse(f"the {name} JSON {path} is not an object")
    probe, fp, closure = docs["probe"], docs["fingerprint"], docs["closure"]

    verdict = probe.get("verdict")
    if verdict not in PROBE_VERDICTS:
        return refuse(f"the probe JSON's verdict {verdict!r} is not one of {PROBE_VERDICTS}")
    if "error" in fp or not isinstance(fp.get("fingerprints"), dict):
        why = fp.get("error", 'no "fingerprints" object')
        return refuse(f"the fingerprint JSON holds no fingerprints ({why})")
    if "verdict" not in closure or "ok" not in closure or not isinstance(closure.get("targets"), list):
        return refuse("the closure JSON is not `audit-closure --json` output (needs \"verdict\", "
                      "\"ok\" and \"targets\")")

    # Ruling 9: both checks ran on one replayed closure.
    p_olean, f_olean = probe.get("olean_sha256"), fp.get("olean_sha256")
    if not p_olean or not f_olean:
        return refuse("the probe and fingerprint JSONs must both carry olean_sha256 (the "
                      f"replayed closure); probe has {p_olean!r}, fingerprint has {f_olean!r}")
    if p_olean != f_olean:
        return refuse(f"the probe ran on olean_sha256 {str(p_olean)[:12]}... but the fingerprint "
                      f"on {str(f_olean)[:12]}...; run both checks on the same build")
    # Step 5 Task 7: the closure audit ran on that same replayed closure, never by importing the
    # submission (which could forge it).
    c_isolated = closure.get("isolated") is True
    if not c_isolated and checks_required(node):
        return refuse(f"the closure JSON is not isolated (\"isolated\": {closure.get('isolated')!r}): it "
                      "comes from `audit-closure --legacy-import` or a telperion from before step 5, which "
                      "IMPORTS the submission, whose code can forge it; a node created on or after "
                      f"{CHECKS_CUTOFF} needs the kernel-replayed audit (`telperion audit-closure` without "
                      "--legacy-import)")
    if c_isolated and not closure.get("olean_sha256"):
        return refuse("the closure JSON says isolated but its olean_sha256 is missing (no replayed closure to "
                      "compare with the probe's and the fingerprint's); re-run `telperion audit-closure` on the "
                      "same build")
    if c_isolated and closure["olean_sha256"] != p_olean:
        return refuse(f"the closure audit ran on olean_sha256 {str(closure['olean_sha256'])[:12]}... but "
                      f"the probe and the fingerprint on {str(p_olean)[:12]}...; run all three checks on the "
                      "same build")

    # Final review I1: the checks must be of the node's OWN theorem, the artifact declaration the
    # grant gate matches (`guard_anchors.resolve_theorem`), never a helper lemma beside it.
    from .missions import judge as _judge
    from .missions.statements import statement_path
    ga = _judge._guard_anchors()
    try:
        want = ga.resolve_theorem(art.read_text(encoding="utf-8"),
                                  statement_path(camp_root, node).read_text(encoding="utf-8"))
    except (OSError, ga.RegistryError) as exc:
        return refuse(f"cannot resolve the node's registered theorem ({exc})")
    fps = fp["fingerprints"]
    target = args.target if args.target is not None else want
    if target != want:
        return refuse(f"--target {target!r} is not the node's registered theorem {want!r}; checks of a "
                      "helper lemma do not cover the node")
    if target not in fps:
        return refuse(f"the fingerprint JSON has no target {target!r}, the node's registered theorem "
                      f"(has {sorted(fps)})")
    audited = [t.get("name") for t in closure["targets"] if isinstance(t, dict)]
    if target not in audited:
        return refuse(f"the closure audit's targets {audited} do not include {target!r}")

    # Ruling 12: one theorem across all three, and the probe and fingerprint ran on the
    # artifact's CURRENT source. Every value must be present and right (final review I2: no
    # waiver); re-run the checks with --file for a JSON that lacks one.
    cur_sha = sha256_file(art)
    if probe.get("theorem") is None:
        return refuse("the probe JSON names no theorem; re-run `probe-negation --json` with --file")
    if probe["theorem"] != target:
        return refuse(f"the probe was of theorem {probe['theorem']!r} but the fingerprint and "
                      f"closure audit are of {target!r}")
    if fp.get("theorem") is not None and fp["theorem"] != target:
        return refuse(f"the fingerprint JSON's theorem {fp['theorem']!r} is not {target!r}")
    for name, doc in (("probe", probe), ("fingerprint", fp)):
        src = doc.get("source_sha256")
        if src is None:
            return refuse(f"the {name} JSON has no source_sha256; re-run the {name} with --file <the "
                          "artifact>")
        if str(src).lower() != cur_sha:
            return refuse(f"the {name} ran on source_sha256 {str(src)[:12]}..., but the artifact "
                          f"on disk is {cur_sha[:12]}...; re-run the {name} on the current artifact")
        if doc.get("stale"):
            return refuse(f"the {name} JSON says its --file was newer than the module's olean "
                          "(a stale build); rebuild and re-run")
    note = args.note

    # Final review I3, kept as a second line now that the closure audit is replayed too (step 5
    # Task 7): the REPLAY's axiom list. The probe and the fingerprint must carry the same list, it
    # must be a subset of CLEAN_AXIOMS, and it must include the closure audit's axioms for the
    # target.
    from .comparator import CLEAN_AXIOMS
    p_ax, f_ax = probe.get("axioms"), fp.get("axioms")
    if not isinstance(p_ax, list) or not isinstance(f_ax, list):
        return refuse("the probe and fingerprint JSONs must both carry the replay's `axioms` list; "
                      "re-run them with the current telperion")
    if sorted(p_ax) != sorted(f_ax):
        return refuse(f"the probe's replay axioms {sorted(p_ax)} differ from the fingerprint's "
                      f"{sorted(f_ax)}")
    bad = [a for a in p_ax if a not in CLEAN_AXIOMS]
    if bad:
        return refuse(f"the replayed module uses non-standard axioms {bad}")
    c_ax = next((t.get("axioms") for t in closure["targets"]
                 if isinstance(t, dict) and t.get("name") == target), None)
    if not isinstance(c_ax, list) or not set(c_ax) <= set(p_ax):
        return refuse(f"the closure audit's axioms for {target!r} ({c_ax!r}) are not among the "
                      f"replay's {sorted(p_ax)}")

    closure_verdict = "PASS" if closure["verdict"] == "PASS" and closure["ok"] is True else "FAIL"
    try:
        rec = ChecksRecord(
            date=_date.today().isoformat(), artifact_sha256=cur_sha,
            olean_sha256=str(p_olean).lower(), probe_verdict=verdict,
            closure_verdict=closure_verdict,
            statement_fingerprint=str(fps[target]).lower(), theorem=target, note=note,
            axioms=tuple(sorted(p_ax)), closure_isolated=c_isolated)
    except SchemaError as exc:
        return refuse(str(exc))
    new = _dc.replace(node, checks=rec, updated=rec.date)
    save_node(new, camp_root / "nodes" / f"{slug}.toml")
    problem = checks_problem(camp_root, new)
    if problem:
        print(f"CHECKS NOT PASSING {slug}: {problem}", file=sys.stderr)
        return 1
    print(f"CHECKS PASS {slug}: probe {rec.probe_verdict}, closure {rec.closure_verdict}, "
          f"fingerprint {rec.statement_fingerprint[:12]}... artifact {rec.artifact_sha256[:12]}... "
          f"olean {rec.olean_sha256[:12]}...")
    return 0


def _nanoda_rev_path() -> Path:
    """The pinned nanoda rev, <project>/NANODA_REV, in the Arda and the standalone layout alike."""
    from . import paths
    return paths.project_root() / "NANODA_REV"


def _nanoda_direct_binding_problem(camp_root, node, slug, art, text, verdict) -> int:
    """Controller Ruling 0b-9 (2026-10-28), Fix 2: bind a nanoda-direct log to the node's
    OWN registered theorem and module. 0 when bound; 2 (after printing why) when not.

    The log must carry exactly one `REJUDGE-INFO ... theorem=T module=M ...` line before its
    EXPORT section (`nanoda_direct.info_binding`); T must equal
    `guard_anchors.resolve_theorem(artifact, statement)` -- the resolver `run_direct` uses --
    and M must equal `judge.module_name_of(<island lean dir>, artifact)`. A PASSING log's
    export must also declare T as a theorem (`export_declares_theorem`, lean4export's
    ndjson): a pass over an export of some other constant is no pass for this node. A
    failing log is still recorded as FAIL once its INFO binding checks out.
    """
    from .missions import judge as _judge
    from .missions import nanoda_direct as _nd
    from .missions.rejudge import RejudgeSetupError, island_of_artifact
    from .missions.statements import statement_path

    try:
        log_thm, log_mod = _nd.info_binding(text)
    except _nd.BindingError as exc:
        print(f"{slug}: nanoda-direct log does not bind its export to one theorem/module "
              f"({exc}); refusing to record.", file=sys.stderr)
        return 2
    artifact = Path(art).resolve()
    camp_root = Path(camp_root).resolve()
    troot = camp_root.parent.parent
    stmt = statement_path(camp_root, node)
    ga = _judge._guard_anchors()
    try:
        want_thm = ga.resolve_theorem(artifact.read_text(), stmt.read_text())
    except (OSError, ga.RegistryError) as exc:
        print(f"{slug}: cannot resolve the node's registered theorem ({exc}); refusing to "
              "record.", file=sys.stderr)
        return 2
    try:
        island = island_of_artifact(troot, artifact)
        want_mod = _judge.module_name_of(_judge.island_dir(troot, island), artifact)
    except (RejudgeSetupError, _judge.JudgeError, ValueError) as exc:
        print(f"{slug}: cannot resolve the artifact's module ({exc}); refusing to record.",
              file=sys.stderr)
        return 2
    if log_thm != want_thm:
        print(f"{slug}: log exported theorem {log_thm!r}, but the node's registered theorem is "
              f"{want_thm!r}; refusing to record.", file=sys.stderr)
        return 2
    if log_mod != want_mod:
        print(f"{slug}: log exported from module {log_mod!r}, but the artifact's module is "
              f"{want_mod!r}; refusing to record.", file=sys.stderr)
        return 2
    if verdict == "pass":
        parsed = _nd._parse_sections(text)
        if parsed is None or not _nd.export_declares_theorem(parsed[1], want_thm):
            print(f"{slug}: the log's export does not declare theorem {want_thm!r}; a pass "
                  "over some other constant is no pass for this node. Refusing to record.",
                  file=sys.stderr)
            return 2
    return 0


def cmd_mission_rejudge_backfill_closure(args) -> int:
    """Back-fill `[rejudge].closure_sha256` for a node whose closure files are
    git-verified unchanged since the re-judge queue started (step 0b Task 2, 2026-10-28).

    A node's `[rejudge]` record was written before closure binding existed (Task 1), so
    it carries no `closure_sha256`. Re-judging it needs Lean/Comparator; back-filling
    does not -- but ONLY when nothing in its import closure could have changed what the
    re-judge actually checked. The back-fill rule (BOTH must hold for every closure
    file):
      - `git log --format=%H <since>..HEAD -- <file>` is empty;
      - `git status --porcelain -- <file>` is empty (not dirty).
    Refuses (exit 2, no write) otherwise: that node must be RE-JUDGED, never back-filled.
    """
    import dataclasses as _dc
    import subprocess

    from .missions.provenance import (
        ClosureError, closure_digest, closure_files as _closure_files,
        closure_support_files as _closure_support_files,
    )
    from .missions.registry import load_campaign
    from .missions.schema import SchemaError, save_node, slug_of

    rebind = bool(getattr(args, "rebind", False))
    reason = " ".join(str(getattr(args, "reason", "") or "").split())
    slug = slug_of(args.slug)
    if rebind and not reason:
        print(f"{slug_of(args.slug)}: --rebind needs --reason TEXT (why the closure digest is "
              "being re-bound); it goes into the record's note.", file=sys.stderr)
        return 2
    camp_root = _resolve_campaign(_missions_root(args), slug, getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1
    node = camp.nodes.get(slug)
    if node is None:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1
    if node.rejudge is None:
        print(f"{slug}: no [rejudge] record to back-fill (`mission rejudge-record` first)",
              file=sys.stderr)
        return 2
    if node.rejudge.closure_sha256 and not rebind:
        print(f"{slug}: [rejudge] already has closure_sha256 "
              f"{node.rejudge.closure_sha256[:12]}...; pass --rebind to replace it.",
              file=sys.stderr)
        return 2
    if node.proof is None:
        print(f"{slug}: no artifact linked", file=sys.stderr)
        return 2

    camp_root = Path(camp_root).resolve()
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=str(camp_root),
                         capture_output=True, text=True)
    if top.returncode != 0:
        print(f"{slug}: cannot find the git repo root from {camp_root}: {top.stderr.strip()}",
              file=sys.stderr)
        return 2
    repo_root = Path(top.stdout.strip())

    try:
        files = _closure_files(camp_root, node)
        support = _closure_support_files(camp_root, node)
    except ClosureError as exc:
        print(f"{slug}: cannot resolve its import closure ({exc}); refusing to write.",
              file=sys.stderr)
        return 2
    if not files:
        print(f"{slug}: its import closure resolved to no files", file=sys.stderr)
        return 2
    # Controller Ruling 0b-3: the git rule also covers each lakefile.toml and
    # lake-manifest.json involved (the island's and every path-required sibling's) --
    # a changed srcDir, require path, or pinned rev could change the closure or its
    # digest without any closure .lean FILE itself changing.
    rel_files = []
    for f in list(files) + list(support):
        f = Path(f).resolve()
        try:
            rel_files.append(str(f.relative_to(repo_root)))
        except ValueError:
            print(f"{slug}: closure file {f} is outside the repo {repo_root}; the git "
                  "back-fill rule cannot be checked for it", file=sys.stderr)
            return 2

    dirty = subprocess.run(["git", "status", "--porcelain", "--", *rel_files],
                           cwd=str(repo_root), capture_output=True, text=True)
    if dirty.returncode != 0:
        print(f"{slug}: `git status` failed: {dirty.stderr.strip()}", file=sys.stderr)
        return 2
    if dirty.stdout.strip():
        print(f"{slug}: refused -- closure file(s) are dirty (uncommitted changes):\n"
              f"{dirty.stdout}", file=sys.stderr)
        return 2

    log = subprocess.run(["git", "log", "--format=%H", f"{args.since}..HEAD", "--", *rel_files],
                         cwd=str(repo_root), capture_output=True, text=True)
    if log.returncode != 0:
        print(f"{slug}: `git log` failed: {log.stderr.strip()}", file=sys.stderr)
        return 2
    if log.stdout.strip():
        commits = log.stdout.strip().splitlines()
        shown = ", ".join(c[:9] for c in commits[:5])
        print(f"{slug}: refused -- {len(commits)} commit(s) touched its closure since "
              f"{args.since}: {shown}{', ...' if len(commits) > 5 else ''}. Re-judge, do "
              "not back-fill.", file=sys.stderr)
        return 2

    try:
        digest = closure_digest(camp_root, node)
    except ClosureError as exc:
        print(f"{slug}: cannot resolve its import closure ({exc}); refusing to write.",
              file=sys.stderr)
        return 2
    from datetime import date as _date
    today = _date.today().isoformat()
    git_clause = (f"git: no change to {len(files)} closure files and {len(support)} support "
                  f"files since {args.since}")
    if rebind:
        # Controller Ruling 0b-9 (2026-10-28), Fix 4: the reason is the caller's, not a
        # hardcoded "after srcDir fix"; and a re-bind REPLACES any earlier re-bind clause
        # (they described a digest that no longer exists), so clauses never pile up.
        extra = f"closure re-bound {today}: {reason} ({git_clause})"
    else:
        extra = f"closure back-filled {today} ({git_clause})"
    note = _rebind_note(node.rejudge.note, extra, rebind=rebind)
    try:
        rec = _dc.replace(node.rejudge, closure_sha256=digest, closure_files=len(files),
                          note=note)
    except SchemaError as exc:
        print(f"{slug}: {exc}")
        return 1
    save_node(_dc.replace(node, rejudge=rec, updated=node.rejudge.date),
             camp_root / "nodes" / f"{slug}.toml")
    verb = "re-bound" if rebind else "back-filled"
    print(f"{slug}: closure {verb} ({len(files)} files, sha256 {digest[:16]}..., "
          f"no change since {args.since})")
    return 0


def _rebind_note(note: str, extra: str, *, rebind: bool) -> str:
    """The record's note with *extra* appended as a "; "-separated clause. Duplicate clauses
    are dropped; on a re-bind every earlier "closure re-bound ..." clause is dropped first
    (Controller Ruling 0b-9)."""
    clauses = [c.strip() for c in (note or "").split("; ") if c.strip()]
    if rebind:
        clauses = [c for c in clauses if not c.startswith("closure re-bound")]
    out = []
    for c in clauses + [extra]:
        if c not in out:
            out.append(c)
    return "; ".join(out)


def cmd_mission_second_kernel_mark(args) -> int:
    """Set the durable registry marker `second_kernel_route` (Controller Ruling 0b-9,
    2026-10-28) on a node -- refused (exit 2, no write) unless the node's CURRENT
    `[rejudge]` record is on exactly that route AND `rejudge_problem` finds nothing wrong
    with the node once marked (passing, current artifact, current closure digest, and for a
    node that needs a Comparator re-judge, route "comparator").

    Once set, deleting the `[rejudge]` table or editing its route fails `mission verify`
    instead of silently dropping or changing the claim."""
    import dataclasses as _dc

    from .missions.provenance import rejudge_problem
    from .missions.registry import load_campaign
    from .missions.schema import SECOND_KERNEL_ROUTES, SchemaError, save_node, slug_of

    slug = slug_of(args.slug)
    route = (args.route or "").strip()
    if route not in SECOND_KERNEL_ROUTES or not route:
        print(f"{slug}: --route must be one of {SECOND_KERNEL_ROUTES[1:]!r}, not {route!r}",
              file=sys.stderr)
        return 2
    camp_root = _resolve_campaign(_missions_root(args), slug, getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1
    node = camp.nodes.get(slug)
    if node is None:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1
    r = node.rejudge
    if r is None:
        print(f"{slug}: no [rejudge] record; record a passing re-judge on route {route!r} "
              "first.", file=sys.stderr)
        return 2
    if r.route != route:
        print(f"{slug}: its [rejudge] record is on route {r.route!r}, not {route!r}; "
              "refusing to mark.", file=sys.stderr)
        return 2
    marked = _dc.replace(node, second_kernel_route=route)
    problem = rejudge_problem(camp.root, marked)
    if problem:
        print(f"{slug}: its current [rejudge] does not pass on route {route!r}: {problem}; "
              "refusing to mark.", file=sys.stderr)
        return 2
    save_node(marked, camp_root / "nodes" / f"{slug}.toml")
    print(f"{slug}: second_kernel_route = {route!r} (record {r.date}, verdict {r.verdict}, "
          f"closure {r.closure_sha256[:12]}...)")
    return 0


def cmd_mission_comparator_record(args) -> int:
    """Record a PASSING Comparator run on a proved node (a sidecar, never a status change)."""
    import dataclasses as _dc
    from datetime import date as _date

    from .missions.provenance import sha256_file
    from .missions.registry import load_campaign
    from .missions.schema import ComparatorRecord, SchemaError, save_node, slug_of

    slug = slug_of(args.slug)
    camp_root = _resolve_campaign(_missions_root(args), slug,
                                  getattr(args, "campaign", None))
    if camp_root is None:
        return 1
    try:
        camp = load_campaign(camp_root)
    except SchemaError as exc:
        print(f"Schema error: {exc}")
        return 1
    node = camp.nodes.get(slug)
    if node is None:
        print(f"Node {slug!r} not found in campaign {camp_root.name!r}")
        return 1
    if node.status != "proved" or node.proof is None:
        print(f"{slug}: status is {node.status!r}; a Comparator record only makes sense on a "
              "proved node with a Lean artifact.")
        return 1
    art = camp_root / node.proof.artifact
    if not art.exists():
        print(f"{slug}: artifact {node.proof.artifact!r} does not exist")
        return 1
    lean_only = bool(getattr(args, "lean_kernel_only", False))
    if not lean_only and node.heavy_certificates:
        print(f"{slug}: node declares heavy_certificates = true, so the judge config had "
              "enable_nanoda = false; pass --lean-kernel-only to record that honestly.")
        return 1

    # Read the verdict out of the judge's own job log rather than trusting the arguments.
    # The JOB, never the run's conclusion: pushing this record to the same pull request
    # supersedes the run that validated the artifact, so the run can read "cancelled" while
    # the judging job succeeded (cl/kwin, 2026-09-25).
    from .missions.judge_log import check as _check_log
    run_id = str(args.run_id).strip()
    theorem = args.theorem.strip()
    job_id = str(getattr(args, "job_id", "") or "").strip()
    job_url = str(getattr(args, "job_url", "") or "").strip()
    head_sha = str(getattr(args, "head_sha", "") or "").strip()
    kernel_mode, log_check, head_check = "", "skipped", "skipped"
    judge_mode, parts = "", ()
    if node.compose is not None and (getattr(args, "no_verify", False) or getattr(args, "log", None)):
        print(f"{slug}: this node is judged COMPOSITIONALLY; its record must be read from the "
              "judge's own job logs (every part's job is located and checked), so neither "
              "--log nor --no-verify is accepted.")
        return 1
    log_text = None
    if getattr(args, "log", None):
        log_text = Path(args.log).read_text(errors="replace")
        log_check = "verified-offline"
        # When `gh` is reachable the caller's --head-sha is not taken on trust either.
        api_sha = _job_head_sha(job_id) if job_id else None
        if api_sha and head_sha and not (api_sha == head_sha or api_sha.startswith(head_sha)):
            print(f"{slug}: --head-sha {head_sha} is not the head of job {job_id}, which the "
                  f"API says is {api_sha}.")
            return 1
        if not head_sha:
            print(f"{slug}: --log needs --head-sha, the commit the judging job checked out, or "
                  "the artifact-at-that-commit check silently does not happen.  Find it with "
                  f"`gh api repos/<owner>/<repo>/actions/jobs/<job-id> --jq .head_sha`.")
            return 1
    elif not getattr(args, "no_verify", False):
        found = _fetch_judge_job(run_id, slug)
        if found is None:
            print(f"{slug}: could not read the judge logs for run {run_id} (is `gh` installed and "
                  "authenticated?).  Pass --log FILE with the job log and --head-sha, or "
                  "--no-verify to record without checking -- which the record will then say.")
            return 1
        job, errs = found
        if errs:
            for e in errs:
                print(f"{slug}: {e}")
            return 1
        job_id, job_url, head_sha, log_text = job.job_id, job.job_url, job.head_sha, job.log
        log_check = "verified"
    if log_text is not None:
        errs = _check_log(log_text, node=slug, theorem=theorem, run_id=run_id,
                          expect_lean_kernel_only=lean_only)
        if errs:
            for e in errs:
                print(f"{slug}: {e}")
            return 1
        from .missions.judge_log import parse_verdicts as _pv
        verdict = _pv(log_text)[slug]
        # A pre-#632 log states no kernel mode; say so instead of inferring one from the switch.
        kernel_mode = verdict.kernel or "unstated"
        if verdict.judge or node.compose is not None:
            parts_or_errs = _compositional_parts(node, slug, verdict, log_text, run_id, head_sha,
                                                 art, offline=(log_check != "verified"))
            if isinstance(parts_or_errs, str):
                print(f"{slug}: {parts_or_errs}")
                return 1
            judge_mode, parts = "compositional", parts_or_errs
        # The judge saw the artifact as of the job's own head commit, which is not necessarily
        # the working tree.  Hash the blob there and require it to match, so a PASS on an older
        # version of the artifact cannot be cited for the current one.
        at_head = _blob_sha256(head_sha, art)
        if at_head is None:
            _try_fetch(art, head_sha)          # a PR head is normally fetchable
            at_head = _blob_sha256(head_sha, art)
        # Store the FULL 40-hex commit: a provenance field must not leave a verifier
        # disambiguating an abbreviation years later.
        head_sha = _full_sha(art, head_sha) or head_sha
        here = sha256_file(art)
        if at_head is None:
            if not getattr(args, "allow_unresolved_head", False):
                print(f"{slug}: cannot resolve {art.name} at the judged commit {head_sha[:9]} "
                      "even after fetching it, so nothing here confirms the judge saw THIS "
                      "version of the artifact.  Fetch that commit, or pass "
                      "--allow-unresolved-head, which records head_check = \"unresolved\".")
                return 1
            print(f"{slug}: NOTE recording with head_check = \"unresolved\": {art.name} could not "
                  f"be resolved at {head_sha[:9]}, so the hash below is the working tree's.")
            head_check = "unresolved"
        elif at_head != here:
            print(f"{slug}: the judge saw {art.name} at {at_head[:16]}... but the working "
                  f"tree has {here[:16]}...; that PASS is for a different version of the "
                  "artifact and must not be recorded for this one.")
            return 1
        else:
            head_check = "matched"
    else:
        print(f"{slug}: WARNING --no-verify: recording without reading the judge log, so the "
              "theorem name and the kernel mode are unchecked.  The record says "
              "log_check = \"skipped\".")
    if lean_only:
        second = "none: heavy_certificates"
    elif kernel_mode == "unstated":
        # The log predates the field, so nothing read here says nanoda replayed the export.
        # Do not write the default, which would assert it.
        second = "unstated (pre-#632 log)"
    else:
        second = "nanoda"
    rec = ComparatorRecord(
        run_id=run_id, date=_date.today().isoformat(),
        artifact_sha256=sha256_file(art), theorem=theorem,
        run_url=(args.run_url or "").strip(), second_kernel=second,
        job_id=job_id, job_url=job_url, kernel_mode=kernel_mode,
        judged_head_sha=head_sha, log_check=log_check, head_check=head_check,
        judge_mode=judge_mode, parts=tuple(parts),
    )
    new_node = _dc.replace(node, comparator=rec, updated=rec.date)
    save_node(new_node, camp_root / "nodes" / f"{slug}.toml")
    print(f"{slug}: comparator run {rec.run_id} recorded for {rec.theorem} "
          f"(artifact sha256 {rec.artifact_sha256[:16]}...; second kernel: {rec.second_kernel})")
    return 0




def _compositional_parts(node, slug, verdict, log_text, run_id, head_sha, art, *, offline):
    """The record's `parts` for a compositional verdict, or a refusal string.

    The verdict line must say `judge=compositional` with the right part count; the verdict
    job's `COMPOSE PART` lines must list exactly the node's parts, all PASS and axiom-clean; and
    EVERY part slug must have its own passing Comparator job in the same run (located here, not
    taken from the verdict job's word).  Each part module is pinned by its sha256 at the judged
    commit, so `comparator_staleness` can tell when any of them changes.
    """
    from .missions.compose import CLEAN_AXIOMS, expected_parts
    from .missions.judge_log import parse_parts
    spec = node.compose
    if spec is None:
        return (f"the log calls this verdict judge={verdict.judge!r}, but the node has no "
                "[compose] table; refusing to record a compositional verdict for it")
    if verdict.judge != "compositional":
        return (f"the node is judged compositionally, but the PASS line says "
                f"judge={verdict.judge or '(none)'}; that is not the compositional verdict")
    if offline:
        return "a compositional verdict can only be recorded from the judge's own job logs"
    if verdict.theorem != spec.theorem:
        return (f"the verdict names theorem {verdict.theorem!r}, not the node's implication "
                f"{spec.theorem!r}")
    want = expected_parts(slug, spec)
    if verdict.parts != len(want):
        return f"the verdict glued {verdict.parts} part(s); the node's spec has {len(want)}"
    # Re-run the glue HERE on the part files the run uploaded, rather than taking the verdict
    # job's word for it: identity by export bytes, closure, axioms -- all re-checked locally.
    import tempfile
    from .missions.compose import load_parts, verify as _verify_parts
    with tempfile.TemporaryDirectory() as td:
        if not _download_compose_parts(run_id, Path(td)):
            return (f"could not download the compose-part-* artifacts of run {run_id}, so the "
                    "glue cannot be re-checked here; refusing to record on the verdict job's word")
        errs = _verify_parts(slug, spec, load_parts(Path(td)))
    if errs:
        return "re-checking the uploaded parts FAILED: " + "; ".join(errs)
    lines = {d["part"]: d for d in parse_parts(log_text, slug)}
    if set(lines) != set(want):
        return (f"the verdict job lists parts {sorted(lines)}, the node's spec "
                f"{sorted(want)}")
    theorems = {f"seg:{nm}": thm for nm, _s, thm, _m in spec.segments}
    theorems["compose"] = spec.theorem
    modules = {f"seg:{nm}": mod for nm, _s, _t, mod in spec.segments}
    modules["compose"] = spec.module
    out = []
    for label in sorted(want):
        d = lines[label]
        if d["slug"] != want[label] or d["comparator"] != "PASS":
            return f"part {label}: the verdict job reports {d['slug']} comparator={d['comparator']}"
        if not set(d["axioms"].split(",")) <= CLEAN_AXIOMS:
            return f"part {label}: axioms {d['axioms']} are not all whitelisted"
        found = _fetch_judge_job(run_id, want[label])
        if found is None:
            return f"could not read the judge logs of run {run_id} for part {label}"
        job, errs = found
        if errs:
            return f"part {label}: " + "; ".join(errs)
        if job.verdict.kernel != verdict.kernel:
            return (f"part {label} was judged with kernel={job.verdict.kernel}, the verdict says "
                    f"{verdict.kernel}")
        src = art.parent / (modules[label].replace(".", "/") + ".lean")
        sha = _blob_sha256(head_sha, src)
        if sha is None:
            _try_fetch(src, head_sha)
            sha = _blob_sha256(head_sha, src)
        if sha is None:
            return f"part {label}: cannot resolve {src.name} at the judged commit {head_sha[:9]}"
        from .missions.provenance import sha256_file
        if sha256_file(src) != sha:
            return (f"part {label}: {src.name} on disk differs from the judged commit's; that "
                    "verdict is for a different version and must not be recorded")
        out.append(f"part={label} slug={want[label]} theorem={theorems[label]} "
                   f"module={modules[label]} sha256={sha} job={job.job_id}")
    return out


def _download_compose_parts(run_id: str, dest: Path) -> bool:
    """Download a heavy-judge run's `compose-part-*` artifacts into `dest`; False when `gh`
    cannot (absent, unauthenticated, artifacts expired)."""
    r = _run_ok(["gh", "run", "download", str(run_id), "-R", _gh_repo(), "-p", "compose-part-*",
                 "-D", str(dest)], text=True)
    return r is not None and any(Path(dest).rglob("*.part.json"))


def _fetch_judge_job(run_id: str, slug: str):
    """((the job to cite), errors) for `slug` in this run, or None when `gh` cannot be used.

    Reads EVERY job of the run, not the first one that mentions the node: a job whose log we
    could not download is not a job that said nothing, and a node judged by two shards could
    pass in one and fail in the other.  `judge_log.choose` applies those rules.
    """
    import json
    import subprocess

    from .missions.judge_log import JobVerdict, choose, failed_nodes, parse_verdicts

    def gh(*a):
        r = _run_ok(["gh", *a], text=True)
        return r.stdout if r is not None else None

    out = gh("api", f"repos/{_gh_repo()}/actions/runs/{run_id}/jobs?per_page=100")
    if out is None:
        return None
    try:
        jobs = json.loads(out).get("jobs", [])
    except json.JSONDecodeError:
        return None
    seen = []
    for job in jobs:
        if job.get("conclusion") == "skipped":
            # A skipped job never executed (e.g. the heavy workflow's ladder-only `heavy-seg` and
            # `verdict` jobs when a node is judged in build-targets mode, #716), so GitHub keeps no
            # log for it and it cannot hold a PASS or a FAIL.  Treating it as "unreadable" would
            # make every targets-mode heavy run uncertifiable.
            continue
        log = gh("api", f"repos/{_gh_repo()}/actions/jobs/{job['id']}/logs")
        jid = str(job["id"])
        if log is None:
            seen.append(JobVerdict(jid, job.get("html_url", ""), str(job.get("head_sha", "")),
                                   None, False, False))
            continue
        v = parse_verdicts(log).get(slug)
        failed = slug in failed_nodes(log)
        if v is None and not failed:
            continue                      # this shard simply did not judge the node
        seen.append(JobVerdict(jid, job.get("html_url", ""), str(job.get("head_sha", "")),
                               v, failed, True, log))
    return choose(seen, slug)




def _run_ok(cmd, **kw):
    """subprocess.run that returns None when the tool is absent or fails.

    A missing `gh` or `git` must surface as "cannot check", which callers turn into a clean
    refusal; a traceback out of a provenance command helps nobody.
    """
    import subprocess

    try:
        r = subprocess.run(cmd, capture_output=True, **kw)
    except (FileNotFoundError, OSError):
        return None
    return r if r.returncode == 0 else None

def _full_sha(path: Path, commit: str):
    """`commit` as a full 40-hex commit id in the artifact's repository, or None."""
    import subprocess

    if not commit:
        return None
    top = _run_ok(["git", "-C", str(path.resolve().parent), "rev-parse", "--show-toplevel"],
                  text=True)
    if top is None:
        return None
    r = _run_ok(["git", "-C", top.stdout.strip(), "rev-parse", f"{commit}^{{commit}}"], text=True)
    out = r.stdout.strip() if r is not None else ""
    return out if len(out) == 40 else None


def _job_head_sha(job_id: str):
    """The head commit GitHub reports for a job, or None when `gh` cannot answer."""
    import json
    import subprocess

    r = _run_ok(["gh", "api", f"repos/{_gh_repo()}/actions/jobs/{job_id}"], text=True)
    if r is None:
        return None
    try:
        return str(json.loads(r.stdout).get("head_sha") or "") or None
    except json.JSONDecodeError:
        return None

def _try_fetch(path: Path, commit: str) -> None:
    """Best-effort `git fetch origin <commit>`, so an unfetched PR head stops being a dead end."""
    import subprocess

    if not commit:
        return
    top = _run_ok(["git", "-C", str(path.resolve().parent), "rev-parse", "--show-toplevel"],
                  text=True)
    if top is None:
        return
    _run_ok(["git", "-C", top.stdout.strip(), "fetch", "--quiet", "origin", commit])


def _gh_repo() -> str:
    """owner/name of the origin remote, for the GitHub API."""
    import os
    import re
    import subprocess

    env = os.environ.get("GITHUB_REPOSITORY")
    if env:
        return env
    r = _run_ok(["git", "remote", "get-url", "origin"], text=True)
    m = re.search(r"github\.com[:/](?P<repo>[^/]+/[^/.]+)", (r.stdout if r else "") or "")
    return m.group("repo") if m else "DrMurphyIsIn/Arda"



def _blob_sha256(commit: str, path: Path):
    """sha256 of `path` as of `commit`, or None when it cannot be resolved here."""
    import hashlib
    import subprocess

    # Resolve the repository from the ARTIFACT's own location, not the process's cwd: the
    # registry and the artifact can live in a different checkout than the one we run in
    # (e.g. `mission --missions-root <other worktree>`), and a cwd-based lookup would then
    # silently report "cannot check".
    art = path.resolve()
    top = _run_ok(["git", "-C", str(art.parent), "rev-parse", "--show-toplevel"], text=True)
    if top is None:
        return None
    root = Path(top.stdout.strip()).resolve()
    try:
        rel = art.relative_to(root)
    except ValueError:
        return None
    blob = _run_ok(["git", "-C", str(root), "cat-file", "blob", f"{commit}:{rel.as_posix()}"])
    if blob is None:
        return None
    return hashlib.sha256(blob.stdout).hexdigest()

def cmd_mission_verify(args) -> int:
    from .missions.verify import verify_campaign

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    any_fail = False
    # Some warnings are repo-global (the orphan-island list) and would otherwise repeat
    # once per campaign; print each distinct warning once.
    seen_warnings: set[str] = set()
    for camp_root in roots:
        deep = getattr(args, "deep_lean", False)
        try:
            report = verify_campaign(camp_root, deep_lean=deep,
                                     strict_provenance=getattr(args, 'strict_provenance', False))
        except Exception as exc:
            # A campaign whose records cannot even be read fails verify; it does not abort
            # the run with a traceback (step 5 fix round 4).
            print(f"ERROR [{camp_root.name}]: verify could not complete: "
                  f"{type(exc).__name__}: {exc}")
            any_fail = True
            continue
        if report.errors:
            for e in report.errors:
                print(f"ERROR [{camp_root.name}]: {e}")
        if report.warnings:
            for w in report.warnings:
                if w in seen_warnings:
                    continue
                seen_warnings.add(w)
                print(f"WARN  [{camp_root.name}]: {w}")
        if report.ok:
            print(f"verify [{camp_root.name}]: OK")
        else:
            any_fail = True
    return 1 if any_fail else 0


def cmd_mission_graph(args) -> int:
    from .missions.registry import load_campaign, render_dot

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    for camp_root in roots:
        try:
            camp = load_campaign(camp_root)
        except Exception as exc:
            print(f"Error loading {camp_root.name}: {exc}")
            continue
        print(render_dot(camp))
    return 0


def cmd_mission(args) -> int:
    return args.mission_fn(args)


def cmd_kernel_policy_check(args) -> int:
    """Lean toolchain floor + shrink-only exception list (spec 5.1). Exit 1 if any problem.

    With --base REF, also enforces that the exception list only shrinks relative to
    REF: the base-ref copy of the exceptions file is read with `git show`, treating
    "path does not exist at REF" as a brand-new file (every current entry then counts
    as added) and any other git error as a hard failure."""
    import subprocess

    from .checks import kernel_policy as kp

    root = Path(args.root)
    exceptions_path = Path(args.exceptions) if args.exceptions else root / "kernel_policy_exceptions.toml"
    try:
        exceptions = kp.load_exceptions(exceptions_path)
    except ValueError as e:
        print(e)
        return 1
    projects = kp.find_projects(root)
    problems = kp.policy_problems(root, exceptions)
    base = getattr(args, "base", None)
    if base:
        try:
            relpath = exceptions_path.resolve().relative_to(root.resolve())
        except ValueError:
            relpath = Path(exceptions_path.name)
        result = subprocess.run(["git", "show", f"{base}:{relpath.as_posix()}"],
                                cwd=root, capture_output=True, text=True)
        if result.returncode == 0:
            base_text = result.stdout
        elif "does not exist in" in result.stderr or "exists on disk, but not in" in result.stderr:
            base_text = None
        else:
            print(f"kernel-policy check: cannot read {relpath} at {base}: {result.stderr.strip()}")
            return 1
        try:
            problems += kp.shrink_problems(base_text, exceptions)
        except ValueError as e:
            print(e)
            return 1
    if problems:
        for p in problems:
            print(p)
        return 1
    print(f"kernel policy: OK ({len(projects)} projects, {len(exceptions)} exceptions)")
    return 0


def _trust_kwargs(args) -> dict:
    """The --trusted-env / --trusted-manifest / --olean-dir options that were given, as keyword arguments."""
    kw = {}
    if getattr(args, "trusted_env", None):
        kw["trusted_env"] = Path(args.trusted_env)
    if getattr(args, "trusted_manifest", None):
        kw["manifest"] = Path(args.trusted_manifest)
    if getattr(args, "olean_dirs", None):
        kw["untrusted_paths"] = [Path(d) for d in args.olean_dirs]
    if getattr(args, "memory_mb", None) is not None:
        kw["memory_mb"] = args.memory_mb or None
    return kw


def _source_sha256(path) -> "str | None":
    """sha256 of the `--file` source a check was given, or None (no file, or unreadable)."""
    import hashlib as _hashlib
    if not path:
        return None
    try:
        return _hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return None


def _staleness(args, module) -> dict:
    """The honest stale-build guard (final review I4): {"source_mtime", "olean_mtime", "stale"} for --file against
    the module's .olean as an import resolves it in <project>/.lake/build/lib/lean and the --olean-dir dirs ({} when
    there is no --file, no single module or no built olean). `stale` is true when --file is newer than that olean: the build is
    older than the source being asserted. It catches a forgotten rebuild, not an adversary (mtimes are settable)."""
    import os as _os

    from .checks.lean_replay import resolve_olean, submission_paths
    if not getattr(args, "file", None) or not module:
        return {}
    try:
        dirs = submission_paths(Path(args.project), getattr(args, "olean_dirs", None) or ())
        olean = resolve_olean(dirs, module)
        src_m = _os.path.getmtime(args.file)
    except (OSError, ValueError):
        return {}
    if not olean:
        return {}                     # nothing built to compare with: the replay reports the missing module
    ol_m = _os.path.getmtime(olean)
    return {"source_mtime": src_m, "olean_mtime": ol_m, "stale": src_m > ol_m}


def cmd_probe_negation(args) -> int:
    """Negation probe of one theorem's ELABORATED constant (checks/negation_probe.py), run on the module's KERNEL
    REPLAY into the pinned trusted env; the module itself is never imported.

    Exit 0 PROBE_ONLY or WITNESSED, 1 VACUOUS or REFUTED, 2 ERROR (including an unbuilt module, no trusted env or
    manifest, or any unexpected failure). With --json, stdout is exactly {"verdict": ..., "detail": ...,
    "module": ..., "theorem": <the qualified name probed>, "source_sha256": <sha256 of --file, or null>,
    "olean_sha256": ..., "olean_closure": [...]} (the last two when the module was replayed). --file only qualifies a
    short --theorem and is hashed into source_sha256; the statement is never read from it."""
    import json as _json
    import shlex

    from .checks import negation_probe as np_
    from .checks.negation_probe import ProbeResult, ProbeSpec, TACTIC_IMPORTS

    theorem = args.theorem
    stale = _staleness(args, args.module)
    try:
        if args.file:
            theorem = np_.qualify(Path(args.file).read_text(encoding="utf-8"), theorem)
        if stale.get("stale"):
            res = ProbeResult("ERROR", f"--file {args.file} is newer than the olean of {args.module}: a stale "
                                       "build; rebuild the module, then re-run the probe")
        else:
            spec = ProbeSpec(args.module, theorem, args.witness,
                             tuple(args.imports) if args.imports is not None else TACTIC_IMPORTS)
            res = np_.run_probe(spec, Path(args.project),
                                wrapper=None if args.wrapper is None else shlex.split(args.wrapper),
                                timeout=args.timeout, **_trust_kwargs(args))
    except Exception as exc:  # any surprise is ERROR (exit 2), never a traceback or a failing verdict
        res = ProbeResult("ERROR", f"probe-negation failed: {type(exc).__name__}: {exc}")
    if args.json:
        # Ruling 12: name what was probed and the source it came from (`mission checks-record`).
        out = res.to_json()
        out.update(module=args.module, theorem=theorem, source_sha256=_source_sha256(args.file), **stale)
        print(_json.dumps(out))
    else:
        print(f"probe-negation {args.theorem}: {res.verdict} -- {res.detail}")
    return {"PROBE_ONLY": 0, "WITNESSED": 0, "VACUOUS": 1, "REFUTED": 1}.get(res.verdict, 2)


def cmd_fingerprint(args) -> int:
    """Statement fingerprint of each target (checks/fingerprint.py): one `<target> <sha256>` line per target, or with
    --json {"fingerprints": {...}, "olean_sha256": <closure digest>, "olean_closure": [[module, part, sha256], ...],
    "module": ..., "theorem": ..., "source_sha256": <sha256 of --file, or null>} (module and theorem are null unless
    there is exactly one --import and one --target). The optional --file is only hashed, into source_sha256, which
    `mission checks-record` compares with the node's artifact. The modules are KERNEL-REPLAYED into the pinned
    trusted env, never imported.

    Exit 0 when every target was fingerprinted, 2 otherwise (a missing target, a refusal, a Lean error, no trusted
    env or manifest). Trust comes from --trusted-env (default $TELPERION_LEAN_ENV), never from --project."""
    import json as _json
    import shlex

    from .checks import fingerprint

    stale = _staleness(args, args.imports[0] if len(args.imports) == 1 else None)
    try:
        if stale.get("stale"):
            raise ValueError(f"--file {args.file} is newer than the olean of {args.imports[0]}: a stale build; "
                             "rebuild the module, then re-run the fingerprint")
        fps = fingerprint.run_fingerprint(Path(args.project), args.imports, args.targets,
                                          wrapper=None if args.wrapper is None else shlex.split(args.wrapper),
                                          timeout=args.timeout, **_trust_kwargs(args))
    except ValueError as exc:
        if args.json:
            print(_json.dumps({"error": str(exc)}))
        else:
            print(f"fingerprint: {exc}")
        return 2
    if args.json:
        # Ruling 12: `module`/`theorem` only when there is exactly one; `source_sha256` of --file.
        print(_json.dumps({"fingerprints": {t: fps[t] for t in args.targets},
                           "olean_sha256": getattr(fps, "olean_sha256", None),
                           "olean_closure": getattr(fps, "olean_closure", []),
                           "module": args.imports[0] if len(args.imports) == 1 else None,
                           "theorem": args.targets[0] if len(args.targets) == 1 else None,
                           "source_sha256": _source_sha256(args.file),
                           "axioms": getattr(fps, "axioms", None), **stale}))
        return 0
    for t in args.targets:
        print(f"{t} {fps[t]}")
    return 0


def cmd_trusted_manifest(args) -> int:
    """`trusted-manifest build`: write the sha256 manifest of the pinned env's trusted files (checks/lean_replay.py)
    to --out (default: outside the env, see lean_replay.default_manifest_path). `verify`: check it. Exit 0 or 2."""
    from .checks import lean_replay

    try:
        if args.trusted_manifest_cmd == "build":
            path = lean_replay.build_trusted_manifest(args.env, args.out, force=args.force)
            print(f"trusted manifest written: {path}")
        else:
            pinned = lean_replay.pinned_env(args.env)
            path = Path(args.out) if args.out else lean_replay.default_manifest_path(pinned.root)
            lean_replay.verify_trusted_manifest(pinned, path)
            print(f"trusted manifest OK: {path}")
    except (OSError, ValueError) as exc:
        print(f"trusted-manifest: {exc}")
        return 2
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="telperion")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("certify", help="run the symbolic self-checks for a family")
    p.add_argument("family", help="path/to/family.py:factory")
    p.add_argument("-v", "--verbose", action="store_true", help="per-instance progress")
    p.add_argument("--workers", type=int, default=1, help="parallel certification (fork)")
    p.add_argument("--profile", action="store_true", help="per-instance cost ledger")
    p.add_argument("--budget", type=float, default=None,
                   help="abort (with the hot-cell report) past this many seconds")
    p.set_defaults(fn=cmd_certify)

    p = sub.add_parser("init", help="scaffold a new Telperion proof project")
    p.add_argument("directory")
    p.add_argument("--namespace", default="MyProof")
    p.set_defaults(fn=cmd_init)

    p = sub.add_parser("palomar-mine",
                       help="mine the Palomar registry for candidate emitter shapes")
    p.add_argument("--topic", default=None,
                   help="comma-separated topics to scope to: rh, bg, pvsnp (default: all)")
    p.add_argument("--poll", action="store_true",
                   help="incremental: surface only entries new since the last run")
    p.add_argument("--state", default="palomar-seen.json",
                   help="seen-state file for --poll")
    p.add_argument("--file", default=None,
                   help="read a local registry file instead of the network (JSON, or RSS with --source feed)")
    p.add_argument("--source", choices=("recent", "feed"), default="recent",
                   help="registry source: recent.json (structured, default) or the RSS feed.xml")
    p.add_argument("--min-score", type=int, default=1)
    p.add_argument("--json", action="store_true", help="emit candidates as JSON")
    p.set_defaults(fn=cmd_palomar_mine)

    p = sub.add_parser("source-mine",
                       help="mine a math source (palomar/arxiv/github/zulip/all) for emitter leads")
    p.add_argument("--source", default="all",
                   choices=("all", "palomar", "palomar-feed", "arxiv", "github", "zulip"))
    p.add_argument("--topic", default=None, help="comma-separated: rh, bg, pvsnp (default: all)")
    p.add_argument("--poll", action="store_true",
                   help="incremental: surface only entries new since the last run")
    p.add_argument("--state-dir", default="~/.telperion/source-seen",
                   help="directory of per-source seen-state files for --poll")
    p.add_argument("--min-score", type=int, default=1)
    p.add_argument("--json", action="store_true")
    p.set_defaults(fn=cmd_source_mine)

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
        p.add_argument("--pilot", type=int, default=0,
                       help="emit only the first N instances (template validation)")
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
    p.add_argument("--ledger", help="route-ledger JSON to append refusals/disproofs to")
    p.set_defaults(fn=cmd_diagnose)

    p = sub.add_parser("margins", help="tightness analysis: ties + margins per certificate")
    p.add_argument("family")
    p.add_argument("--samples", type=int, default=60)
    p.add_argument("--all", action="store_true")
    p.add_argument("--adequacy", action="store_true",
                   help="bracket-slack fragility report (interval families)")
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

    p = sub.add_parser("sharpen", help="certificate boundary vs truth boundary over a cap")
    p.add_argument("builder", help="path.py:fn taking a sympy Rational cap -> family")
    p.add_argument("--lo", required=True)
    p.add_argument("--hi", required=True)
    p.add_argument("--steps", type=int, default=6)
    p.set_defaults(fn=cmd_sharpen)

    p = sub.add_parser("cilog", help="parse a lake log against the gotcha catalog")
    p.add_argument("log")
    p.set_defaults(fn=cmd_cilog)

    p = sub.add_parser("status", help="STATUS.md from executed checks (never asserted)")
    p.add_argument("--manifest", default="telperion.toml")
    p.add_argument("--group", default="all")
    p.add_argument("-o", "--out", default="STATUS.md")
    p.set_defaults(fn=cmd_status)

    p = sub.add_parser("review-brief", help="adversarial review checklist for a family")
    p.add_argument("family")
    p.add_argument("-o", "--out")
    p.set_defaults(fn=cmd_review_brief)

    p = sub.add_parser("ledger", help="render the route ledger (ROUTES.md)")
    p.add_argument("--ledger", default="ROUTES.json")
    p.add_argument("-o", "--out")
    p.set_defaults(fn=cmd_ledger)

    p = sub.add_parser("hunt", help="adversarial exact minimization (negative = disproof)")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u")
    p.add_argument("--iters", type=int, default=400)
    p.add_argument("--restarts", type=int, default=6)
    p.add_argument("--mode", default="descent", choices=["descent", "evolve", "diverse"],
                   help="descent = coordinate descent; evolve = GA + memetic refinement; "
                        "diverse = MAP-Elites archive of distinct near-tight points")
    p.add_argument("--ledger", help="route-ledger JSON to append refusals/disproofs to")
    p.set_defaults(fn=cmd_hunt)

    p = sub.add_parser("relax", help="smooth-vs-arithmetic verdict for an integer grid axis")
    p.add_argument("family")
    p.add_argument("--axis", required=True)
    p.add_argument("--iters", type=int, default=200)
    p.add_argument("--ledger", help="route-ledger JSON to append refusals/disproofs to")
    p.set_defaults(fn=cmd_relax)

    p = sub.add_parser("probe", help="check one expression for a Polya certificate")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u", help="comma-separated nonneg symbols")
    p.set_defaults(fn=cmd_probe)

    p = sub.add_parser("prove",
                       help="single-goal backend: emit Lean for 0 <= <expr>, or triage")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u", help="comma-separated nonneg symbols")
    p.add_argument("--name", default="Goal", help="theorem/namespace base name")
    p.add_argument("--namespace", default="", help="dotted Lean namespace (default: --name)")
    p.add_argument("--trials", type=int, default=400,
                   help="counterexample search budget on refusal")
    p.add_argument("--json", action="store_true",
                   help="emit the backend-bridge JSON contract (for a Lean tactic / prover tool call)")
    p.set_defaults(fn=cmd_prove)

    p = sub.add_parser("lint-lean",
                       help="static soundness pre-check of an emitted Lean file "
                            "(sorry/axiom/empty-tactic/missing-ascription/stub)")
    p.add_argument("file")
    p.add_argument("--strict", action="store_true",
                   help="also fail on warn-level issues (trivial/Prop:=True stubs)")
    p.set_defaults(fn=cmd_lint_lean)

    p = sub.add_parser("lint-provenance",
                       help="provenance-header lint for ported files (spec 7.4): "
                            "repo/file/commit in the first 30 lines")
    p.add_argument("dir", nargs="?", default=".", help="campaign root (default: .)")
    p.set_defaults(fn=cmd_lint_provenance)

    p = sub.add_parser("audit",
                       help="audit external Lean for sorry/axiom/stub/vacuity (the referee role)")
    p.add_argument("file")
    p.set_defaults(fn=cmd_audit)

    p = sub.add_parser("audit-closure",
                       help="kernel-level dependency-closure audit of theorems in a built Lake "
                            "project (census by root, non-library constants, name scan, "
                            "absences, axioms), run by kernel replay into the pinned trusted env (the "
                            "project is never imported; --legacy-import for the old import path)")
    p.add_argument("--project", required=True,
                   help="the Lake project in which the modules are BUILT (its .lake/build/lib/lean is untrusted)")
    p.add_argument("--legacy-import", dest="legacy_import", action="store_true",
                   help="run the old script that IMPORTS the submission with `lake env lean` in --project. NOT "
                        "ISOLATED: the submission's lakefile, initializers and elaborators run in the audit and "
                        "can forge it; `mission checks-record` refuses its output for post-cutoff nodes")
    p.add_argument("--spec", default=None, help="an AuditSpec as JSON (replaces the flags below)")
    p.add_argument("--import", dest="imports", action="append", default=None, metavar="MODULE",
                   help="module to import (repeatable)")
    p.add_argument("--target", action="append", default=None, metavar="NAME",
                   help="fully qualified theorem/definition to audit (repeatable)")
    p.add_argument("--library-root", dest="library_root", action="append", default=None,
                   help="root module counted as library, not listed (default: Init Lean Std "
                        "Batteries Mathlib Aesop Qq ProofWidgets Plausible LeanSearchClient "
                        "ImportGraph Lake Cli)")
    p.add_argument("--scan", action="append", default=None, metavar="SUBSTRING",
                   help="case-insensitive substring to scan constant and module names for "
                        "(repeatable; hits are reported, not failed)")
    p.add_argument("--absent-const", dest="absent_const", action="append", default=None,
                   help="constant that must not be in the closure (default: sorryAx)")
    p.add_argument("--absent-module", dest="absent_module", action="append", default=None,
                   help="module-name prefix that must not be in the closure (repeatable)")
    p.add_argument("--allow-axiom", dest="allow_axiom", action="append", default=None,
                   help="allowed axiom (default: propext Quot.sound Classical.choice)")
    p.add_argument("--no-recursors", dest="no_recursors", action="store_true",
                   help="reproduce the ConstantInfo.getUsedConstantsAsSet walk (no .rec for "
                        "every inductive); the default adds them")
    p.add_argument("--closure-out", dest="closure_out", default=None,
                   help="write the full module<TAB>constant listing here (absolute path)")
    p.add_argument("--fail-on-scan-hit", dest="fail_on_scan_hit", action="store_true")
    p.add_argument("--wrapper", default=None,
                   help="command prefix before the pinned `lean` (default: leanlock with one slot when "
                        "~/hodge-engine/leanlock.sh exists; '' for none); with --legacy-import, before "
                        "`lake env lean` (default: none)")
    p.add_argument("--timeout", type=int, default=3600)
    p.add_argument("--trusted-env", default=None, metavar="DIR",
                   help="the PINNED Lean env whose toolchain and .lake packages are trusted (default: "
                        "$TELPERION_LEAN_ENV). Nothing from --project is trusted")
    p.add_argument("--trusted-manifest", default=None, metavar="FILE",
                   help="the sha256 manifest of the trusted env's files, verified before every run (default: "
                        "~/telperion-tools/trusted-manifests/<hash of the env's pins>.json)")
    p.add_argument("--olean-dir", dest="olean_dirs", action="append", default=None, metavar="DIR",
                   help="an extra untrusted olean dir to replay modules from, besides <project>/.lake/build/lib/lean "
                        "(repeatable)")
    p.add_argument("--memory-mb", type=int, default=None, metavar="MB",
                   help="Lean's --memory bound for each run (default 8192; 0 for none). Best-effort until the "
                        "sandbox")
    p.add_argument("--script-path", dest="script_path", default=None,
                   help="with --legacy-import: write the rendered script here and keep it (default: temp file in "
                        "the project)")
    p.add_argument("--render-only", dest="render_only", default=None, metavar="FILE",
                   help="write the rendered Lean (the replay callback; the import script with --legacy-import) "
                        "and exit without running it")
    p.add_argument("--json", default=None, help="write the AuditResult as JSON here")
    p.set_defaults(fn=cmd_audit_closure)

    def _manifest_common(q):
        q.add_argument("--project", required=True, help="the Lake project directory")
        q.add_argument("--include", action="append", default=None, metavar="GLOB",
                       help="source glob relative to the project (default: **/*.lean; .lake and "
                            ".git are always excluded)")
        q.add_argument("--packages-dir", dest="packages_dir", default=None,
                       help="dependency checkout dir (default: lake-manifest packagesDir)")
        q.add_argument("--tool", action="append", default=None, metavar="LABEL=PATH",
                       help="tool binary to pin (checker, exporter, second kernel, sandbox shim)")
        q.add_argument("--extra", action="append", default=None, metavar="LABEL=PATH",
                       help="any other file to pin (Comparator JSON configs, scripts)")
        q.add_argument("--patch", action="append", default=None, metavar="PACKAGE=PATCHFILE",
                       help="patch whose reverse application is checked against that package")
        q.add_argument("--include-ignored", dest="include_ignored", action="store_true",
                       help="also list git-ignored files inside each package (outside .lake/)")
        q.add_argument("--no-toolchain-binary", dest="no_toolchain_binary", action="store_true",
                       help="do not hash the elan `lean` binary named by lean-toolchain")

    p = sub.add_parser("freeze-manifest",
                       help="pin a Lake project's source state (sources, lake files, toolchain, "
                            "dependency git state, tool binaries, configs) as JSON")
    _manifest_common(p)
    p.add_argument("--out", required=True, help="manifest JSON to write")
    p.add_argument("--text", default=None, help="also write a one-line-per-file text rendering")
    p.add_argument("--no-timestamp", dest="no_timestamp", action="store_true",
                   help="omit `created` (the digest never includes it)")
    p.set_defaults(fn=cmd_freeze_manifest)

    p = sub.add_parser("verify-manifest",
                       help="re-freeze with the manifest's own options and diff; exit 1 on any change")
    p.add_argument("--project", required=True, help="the Lake project directory")
    p.add_argument("--manifest", required=True, help="the manifest JSON written by freeze-manifest")
    p.add_argument("--tool", action="append", default=None, metavar="LABEL=PATH",
                   help="re-point a tool label whose binary moved (content is still compared)")
    p.add_argument("--out", default=None, help="write the recomputed manifest here")
    p.add_argument("--json", default=None, help="write the diff as JSON here")
    p.set_defaults(fn=cmd_verify_manifest)

    p = sub.add_parser("sonc",
                       help="find + verify a SONC circuit-polynomial nonnegativity certificate")
    p.add_argument("expression")
    p.add_argument("--symbols", default="x,y", help="comma-separated real symbols")
    p.set_defaults(fn=cmd_sonc)

    p = sub.add_parser("psd",
                       help="find + verify an exact LDLᵀ PSD certificate for a rational matrix")
    p.add_argument("matrix", help="Python-literal rows, e.g. '[[2,1],[1,2]]'")
    p.set_defaults(fn=cmd_psd)

    p = sub.add_parser("prime",
                       help="find + verify a Pratt/Lucas primality certificate for n")
    p.add_argument("n", type=int)
    p.set_defaults(fn=cmd_prime)

    p = sub.add_parser("benchmark",
                       help="run the certifiable-fragment benchmark (deterministic solve rate + timing)")
    p.set_defaults(fn=cmd_benchmark)

    p = sub.add_parser("evolve", help="island MAP-Elites evolution toward a certifying unimodal genome")
    p.add_argument("--islands", type=int, default=4)
    p.add_argument("--gens", type=int, default=20)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--model", default="qwen2.5-coder:7b")
    p.add_argument("--no-llm", action="store_true")
    p.set_defaults(fn=cmd_evolve)

    p2m = sub.add_parser("p2m", help="prove2.me solver bridge (see docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md)")
    p2m_sub = p2m.add_subparsers(dest="p2m_cmd", required=True)

    def _wsopt(p):
        p.add_argument("--workspace", default=None,
                       help="workspace root (default $HOME/prove2me_workspace)")

    q = p2m_sub.add_parser("login", help="auth chain: credentials -> key -> token")
    q.add_argument("--email", default=None); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_login)
    q = p2m_sub.add_parser("missions", help="list platform missions"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_missions)
    q = p2m_sub.add_parser("triage", help="rank open milestones vs emitter registry"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_triage)
    q = p2m_sub.add_parser("lift", help="scaffold a lift family for one milestone")
    q.add_argument("milestone_id"); q.add_argument("--statement", default=None)
    q.add_argument("--name", default=None); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_lift)
    q = p2m_sub.add_parser("attempt", help="certify, emit, gate, and submit one milestone")
    q.add_argument("milestone_id"); q.add_argument("--name", default=None)
    q.add_argument("--no-submit", action="store_true")
    q.add_argument("--explanation", default=None,
                   help="required for a live submission (I4); 2-4 factual sentences + source")
    _wsopt(q)
    q.set_defaults(fn=cmd_p2m_attempt)
    q = p2m_sub.add_parser("status", help="attempt ledger summary"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_status)
    q = p2m_sub.add_parser("coverage", help="shape-rule vs registry coverage report")
    q.set_defaults(fn=cmd_p2m_coverage)
    q = p2m_sub.add_parser("sync", help="clone or pull the official platform workspace repo")
    q.add_argument("repo_url", help="git URL of the official prove2.me workspace repo"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_sync)

    # ------------------------------------------------------------------
    # mission: internal missions registry subtree
    # ------------------------------------------------------------------
    mp = sub.add_parser("mission", help="internal missions registry: status, claims, prove, verify")
    mp.add_argument("--missions-root", dest="missions_root", default=None,
                    help="root dir containing campaign subdirectories (default: auto-resolved)")
    mp.set_defaults(fn=cmd_mission)
    msub = mp.add_subparsers(dest="mission_cmd", required=True)

    # status [CAMPAIGN]
    p = msub.add_parser("status", help="show campaign status tree")
    p.add_argument("campaign", nargs="?", default=None)
    p.set_defaults(mission_fn=cmd_mission_status)

    # open-leaves [CAMPAIGN] [--all]
    p = msub.add_parser("open-leaves", help="list open leaf nodes ready to work on")
    p.add_argument("campaign", nargs="?", default=None)
    p.add_argument("--all", action="store_true", dest="all",
                   help="include claimed nodes")
    p.set_defaults(mission_fn=cmd_mission_open_leaves)

    # claim SLUG [--campaign C] --session S [--ttl H] [--note N]
    # --campaign is OPTIONAL: when omitted, _resolve_campaign auto-discovers
    p = msub.add_parser("claim", help="claim a node for a session")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--session", required=True)
    p.add_argument("--ttl", type=int, default=24, help="TTL in hours")
    p.add_argument("--note", default="")
    p.set_defaults(mission_fn=cmd_mission_claim)

    # release SLUG [--campaign C] --session S
    p = msub.add_parser("release", help="release a node claim")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--session", required=True)
    p.set_defaults(mission_fn=cmd_mission_release)

    # add CAMPAIGN NAME --title T --kind K [--deps a,b] (--statement TEXT | --statement-file F)
    # add uses positional CAMPAIGN (not --campaign) so it stays required
    p = msub.add_parser("add", help="add a new node to a campaign")
    p.add_argument("campaign")
    p.add_argument("name", help="node name (e.g. My.lemma_x)")
    p.add_argument("--title", required=True)
    p.add_argument("--kind", required=True, choices=("goal", "milestone", "lemma", "definition"))
    p.add_argument("--deps", default=None, help="comma-separated depends_on slugs")
    p.add_argument("--statement", default=None, help="statement text")
    p.add_argument("--statement-file", default=None, dest="statement_file",
                   help="path to file containing statement text")
    p.add_argument("--session", default=None,
                   help="authoring session id (default: $CLAUDE_SESSION_ID); required non-empty")
    p.add_argument("--identity", default=None,
                   help="author identity (default: `git config user.email`); required non-empty")
    p.set_defaults(mission_fn=cmd_mission_add)

    # audit SLUG [--campaign C] --text T [--auditor LABEL] [--session S] [--identity I]
    p = msub.add_parser("audit", help="record an INDEPENDENT readback and promote draft -> open")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--text", required=True,
                   help="the read-back: your own rendering of the FORMAL statement "
                        "(at least 120 characters; not the title)")
    p.add_argument("--auditor", default=None,
                   help="display label only (default: the identity)")
    p.add_argument("--session", default=None,
                   help="auditing session id (default: $CLAUDE_SESSION_ID); refused if it "
                        "is the author's session")
    p.add_argument("--identity", default=None,
                   help="auditor identity (default: `git config user.email`); refused if it "
                        "is the author's identity")
    p.set_defaults(mission_fn=cmd_mission_audit)

    # link SLUG [--campaign C] --artifact P --kind K --via V
    p = msub.add_parser("link", help="record a proof artifact link (status unchanged)")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--artifact", required=True)
    p.add_argument("--kind", required=True, choices=("lean_module", "frozen_cert"))
    p.add_argument("--via", required=True, choices=("direct", "reduction"))
    p.add_argument("--force", action="store_true",
                   help="allow repointing the artifact of a node that is already "
                        "proved or refuted (its status will then rest on unchecked evidence)")
    p.set_defaults(mission_fn=cmd_mission_link)

    # attempt SLUG [--campaign C] --session S --route R --verdict V --detail D
    p = msub.add_parser("attempt", help="record a work attempt in the ledger")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--session", required=True)
    p.add_argument("--route", required=True)
    p.add_argument("--verdict", required=True,
                   choices=("Proved", "Refuted", "NoGo", "Stalled"))
    p.add_argument("--detail", required=True)
    p.set_defaults(mission_fn=cmd_mission_attempt)

    # grant SLUG [--campaign C] [--session S] [--identity I]
    p = msub.add_parser("grant", help="flip open -> proved/refuted via the verify gate")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--session", default=None,
                   help="granting session id (default: $CLAUDE_SESSION_ID); recorded in [grant]")
    p.add_argument("--identity", default=None,
                   help="granting identity (default: `git config user.email`); recorded in [grant]")
    p.set_defaults(mission_fn=cmd_mission_grant)

    # freeze CAMPAIGN [--session S] [--identity I]
    p = msub.add_parser("freeze",
                        help="record a campaign-level statement freeze (FREEZE.toml); "
                             "a post-cutoff node may not be granted until its campaign is "
                             "frozen")
    p.add_argument("campaign")
    p.add_argument("--session", default=None,
                   help="freezing session id (default: $CLAUDE_SESSION_ID); recorded in "
                        "FREEZE.toml")
    p.add_argument("--identity", default=None,
                   help="freezing identity (default: `git config user.email`); recorded in "
                        "FREEZE.toml")
    p.set_defaults(mission_fn=cmd_mission_freeze)

    # deviations-readback CAMPAIGN [--session S] [--identity I] [--date D]
    p = msub.add_parser("deviations-readback",
                        help="record an independent read-back of DEVIATIONS.md (spec "
                             "7.3); required, from an identity/session distinct from a "
                             "node's own author, before that node can be granted "
                             "post-cutoff")
    p.add_argument("campaign")
    p.add_argument("--session", default=None,
                   help="auditing session id (default: $CLAUDE_SESSION_ID); recorded in "
                        "DEVIATIONS.readback.toml")
    p.add_argument("--identity", default=None,
                   help="auditing identity (default: `git config user.email`); recorded "
                        "in DEVIATIONS.readback.toml")
    p.add_argument("--date", default=None,
                   help="read-back date (default: today)")
    p.set_defaults(mission_fn=cmd_mission_deviations_readback)

    # unfreeze CAMPAIGN --author A --reason R --readback-identity I
    p = msub.add_parser("unfreeze",
                        help="bump a campaign's freeze with a recorded, independently "
                             "read-back reason, and re-hash every current statement")
    p.add_argument("campaign")
    p.add_argument("--author", required=True,
                   help="who is making this change")
    p.add_argument("--reason", required=True,
                   help="why the freeze needs to move (e.g. which statement changed)")
    p.add_argument("--readback-identity", required=True, dest="readback_identity",
                   help="an INDEPENDENT identity (not --author) that read back the new "
                        "hashes before this was recorded; refused if it equals --author")
    p.set_defaults(mission_fn=cmd_mission_unfreeze)

    # audit-file CAMPAIGN
    p = msub.add_parser("audit-file",
                        help="generate <root>/lean/Audit.lean: one `import` per proved "
                             "node's artifact module, then one `#print axioms <theorem>` "
                             "per proved node")
    p.add_argument("campaign")
    p.set_defaults(mission_fn=cmd_mission_audit_file)

    # audit-crosscheck --print-axioms-out F --closure-json F
    p = msub.add_parser("audit-crosscheck",
                        help="cross-check `lake env lean Audit.lean`'s captured output "
                             "against a closure audit's per-target axiom lists")
    p.add_argument("--print-axioms-out", required=True, type=Path, dest="print_axioms_out",
                   help="captured stdout of `lake env lean Audit.lean`")
    p.add_argument("--closure-json", required=True, type=Path, dest="closure_json",
                   help="the file `telperion audit-closure --json FILE` wrote")
    p.set_defaults(mission_fn=cmd_mission_audit_crosscheck)

    # provenance-report [CAMPAIGN] [--strict]
    p = msub.add_parser("provenance-report",
                        help="per campaign: proved nodes whose read-back is unverified or "
                             "self-audited and that no passing Comparator run covers")
    p.add_argument("campaign", nargs="?", default=None)
    p.add_argument("--strict", action="store_true",
                   help="exit 1 when any proved node is flagged")
    p.set_defaults(mission_fn=cmd_mission_provenance_report)

    # provenance-migrate [CAMPAIGN]
    p = msub.add_parser("provenance-migrate",
                        help="mark every read-back without an independence value as "
                             "\"unverified\" (idempotent; changes no status)")
    p.add_argument("campaign", nargs="?", default=None)
    p.set_defaults(mission_fn=cmd_mission_provenance_migrate)

    # comparator-record SLUG [--campaign C] --run-id N --theorem T [--run-url U]
    p = msub.add_parser("comparator-record",
                        help="record a PASSING independent-judge (Comparator) run on a proved "
                             "node; a sidecar, never a status change")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--run-id", required=True, dest="run_id",
                   help="the GitHub Actions run id that passed")
    p.add_argument("--theorem", required=True,
                   help="fully qualified theorem name the Comparator config asserted")
    p.add_argument("--run-url", default=None, dest="run_url")
    p.add_argument("--lean-kernel-only", action="store_true", dest="lean_kernel_only",
                   help="the judge ran with enable_nanoda = false for this node "
                        "(heavy_certificates = true); the record says so")
    p.add_argument("--job-id", default=None, dest="job_id",
                   help="the shard job that printed the PASS line (found automatically when the "
                        "log is fetched; required with --log to make the record point at a job)")
    p.add_argument("--job-url", default=None, dest="job_url")
    p.add_argument("--log", default=None,
                   help="read the judge verdict from this file instead of fetching it (offline); "
                        "requires --head-sha")
    p.add_argument("--head-sha", default=None, dest="head_sha",
                   help="the commit the judging job checked out (with --log); the artifact is "
                        "hashed at that commit and must match")
    p.add_argument("--allow-unresolved-head", action="store_true", dest="allow_unresolved_head",
                   help="record even when the judged commit cannot be resolved here; the record "
                        "then says head_check = \"unresolved\"")
    p.add_argument("--no-verify", action="store_true", dest="no_verify",
                   help="record WITHOUT reading the judge log: the theorem name and the kernel "
                        "mode are then unchecked.  Last resort; say why in the commit message")
    p.set_defaults(mission_fn=cmd_mission_comparator_record)

    # ci-record SLUG [--campaign C] --workflow W --job J --run-id N [--head-sha S] [--conclusion C]
    p = msub.add_parser("ci-record",
                        help="record a run of a named (non-required) CI job on the node's "
                             "current artifact; consulted by grant/verify when the node "
                             "declares requires_ci_job = \"<workflow>:<job>\"")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--workflow", required=True, help="workflow file, e.g. telperion-zeta-reflection.yml")
    p.add_argument("--job", required=True, help="job name, e.g. anduril-kernel-ladder")
    p.add_argument("--run-id", required=True, dest="run_id")
    p.add_argument("--head-sha", default=None, dest="head_sha",
                   help="commit the run built (default: from `gh run view`)")
    p.add_argument("--conclusion", default=None,
                   help="the job's conclusion (default: from `gh run view`); the record only "
                        "satisfies requires_ci_job when it is \"success\"")
    p.add_argument("--run-url", default=None, dest="run_url")
    p.set_defaults(mission_fn=cmd_mission_ci_record)

    # rejudge-record SLUG --campaign C --log PATH --comparator-tag TAG [--peak-rss-kb N] [--note S]
    p = msub.add_parser("rejudge-record",
                        help="record a local Comparator run with nanoda ON for a heavy node")
    p.add_argument("slug")
    p.add_argument("--campaign", required=True)
    p.add_argument("--log", required=True, type=Path)
    p.add_argument("--comparator-tag", required=True, dest="comparator_tag")
    p.add_argument("--peak-rss-kb", type=int, default=0, dest="peak_rss_kb")
    p.add_argument("--note", default="")
    p.set_defaults(mission_fn=cmd_mission_rejudge_record)

    # checks-record SLUG --campaign C --probe-json F --closure-json F --fingerprint-json F
    #               [--target NAME] [--note S]
    p = msub.add_parser("checks-record",
                        help="record the negation probe, closure audit and statement fingerprint "
                             "(read from their JSON output) for a node")
    p.add_argument("slug")
    p.add_argument("--campaign", required=True)
    p.add_argument("--probe-json", required=True, type=Path, dest="probe_json",
                   help="`telperion probe-negation --json` output")
    p.add_argument("--closure-json", required=True, type=Path, dest="closure_json",
                   help="the file `telperion audit-closure --json FILE` wrote")
    p.add_argument("--fingerprint-json", required=True, type=Path, dest="fingerprint_json",
                   help="`telperion fingerprint --json` output")
    p.add_argument("--target", default=None,
                   help="the fingerprinted theorem (default and only allowed value: the node's registered "
                        "theorem, the artifact declaration the grant gate matches)")
    p.add_argument("--note", default="",
                   help="free text; a PROBE_ONLY verdict passes only with 'signoff: <who>' here")
    p.set_defaults(mission_fn=cmd_mission_checks_record)

    # rejudge-backfill-closure SLUG --campaign C [--since 23bda8b16] [--rebind]
    p = msub.add_parser("rejudge-backfill-closure",
                        help="back-fill [rejudge].closure_sha256 for a node whose closure "
                             "files are git-verified unchanged since --since; refuses "
                             "(exit 2) if any closure file is dirty or was touched since")
    p.add_argument("slug")
    p.add_argument("--campaign", required=True)
    p.add_argument("--since", default="23bda8b16",
                   help="commit the re-judge queue started at (default: 23bda8b16)")
    p.add_argument("--rebind", action="store_true",
                   help="replace an EXISTING closure_sha256 (refused without this flag); "
                        "same git rule, applied over the newly computed closure")
    p.add_argument("--reason", default="",
                   help="with --rebind: why the digest is re-bound; written into the note, "
                        "replacing any earlier re-bind clause (required with --rebind)")
    p.set_defaults(mission_fn=cmd_mission_rejudge_backfill_closure)

    # second-kernel-mark SLUG --campaign C --route R
    p = msub.add_parser("second-kernel-mark",
                        help="set the durable second_kernel_route marker on a node; refused "
                             "(exit 2) unless its current [rejudge] passes on that route")
    p.add_argument("slug")
    p.add_argument("--campaign", required=True)
    p.add_argument("--route", required=True, choices=("comparator", "nanoda-direct"))
    p.set_defaults(mission_fn=cmd_mission_second_kernel_mark)

    # verify [CAMPAIGN] [--deep-lean]
    p = msub.add_parser("verify", help="run the full invariant battery")
    p.add_argument("campaign", nargs="?", default=None)
    p.add_argument("--deep-lean", action="store_true", dest="deep_lean",
                   help="run lake build in lean/")
    p.add_argument("--strict-provenance", action="store_true", dest="strict_provenance",
                   help="treat a weakly checked Comparator record (written with --no-verify, "
                        "from a supplied log, or without the artifact check at the judged "
                        "commit) as an ERROR rather than a warning")
    p.set_defaults(mission_fn=cmd_mission_verify)

    # graph [CAMPAIGN]
    p = msub.add_parser("graph", help="emit DOT-language dependency graph to stdout")
    p.add_argument("campaign", nargs="?", default=None)
    p.set_defaults(mission_fn=cmd_mission_graph)

    kpp = sub.add_parser("kernel-policy", help="Lean toolchain floor + shrink-only exception list (spec 5.1)")
    kpp_sub = kpp.add_subparsers(dest="kernel_policy_cmd", required=True)
    p = kpp_sub.add_parser("check", help="print policy problems and exit 1 if any")
    p.add_argument("--root", default=".", help="repo root to scan (default: .)")
    p.add_argument("--exceptions", default=None,
                   help="exceptions TOML (default: <root>/kernel_policy_exceptions.toml)")
    p.add_argument("--base", default=None,
                   help="base git ref; also enforce that the exception list only shrinks "
                        "relative to this ref (read via `git show REF:<path>` in --root)")
    p.set_defaults(fn=cmd_kernel_policy_check)

    p = sub.add_parser("probe-negation",
                       help="one-sided probe of a theorem's ELABORATED constant: VACUOUS (its premises "
                            "prove False), REFUTED (plausible counterexample), WITNESSED, PROBE_ONLY or ERROR")
    p.add_argument("--project", required=True,
                   help="the Lake project in which --module is built (its .lake/build/lib/lean is untrusted)")
    p.add_argument("--module", required=True,
                   help="the theorem's own module, which must be BUILT in --project (lake build <module>); "
                        "the statement is the elaborated constant's type, so local definitions, notation "
                        "and attributes are exactly as in the file. An unbuilt module is ERROR")
    p.add_argument("--theorem", required=True, help="the theorem's name (fully qualified unless --file is given)")
    p.add_argument("--file", default=None,
                   help="the Lean file declaring the theorem (pass the node's artifact); used ONLY to qualify a "
                        "short --theorem with its namespace and hashed into the --json `source_sha256`, never to "
                        "read the statement")
    p.add_argument("--witness", default=None,
                   help="a term proving `∃ <premises>, True` (the hypotheses are satisfiable)")
    p.add_argument("--import", dest="imports", action="append", default=None, metavar="MODULE",
                   help="trusted tactic module imported before --module is replayed (repeatable; default: Mathlib)")
    p.add_argument("--wrapper", default=None,
                   help="command prefix before the pinned `lean` (default: leanlock with one slot "
                        "when ~/hodge-engine/leanlock.sh exists; '' for none)")
    p.add_argument("--timeout", type=int, default=1800, help="seconds for the Lean run")
    p.add_argument("--trusted-env", default=None, metavar="DIR",
                   help="the PINNED Lean env whose toolchain and .lake packages are trusted (default: "
                        "$TELPERION_LEAN_ENV; exit 2 if neither is set). Nothing from --project is trusted")
    p.add_argument("--trusted-manifest", default=None, metavar="FILE",
                   help="the sha256 manifest of the trusted env's files, verified before every run (default: "
                        "~/telperion-tools/trusted-manifests/<hash of the env's pins>.json; build it with "
                        "`telperion trusted-manifest build --env DIR`)")
    p.add_argument("--olean-dir", dest="olean_dirs", action="append", default=None, metavar="DIR",
                   help="an extra untrusted olean dir to replay modules from, besides <project>/.lake/build/lib/lean "
                        "(repeatable)")
    p.add_argument("--memory-mb", type=int, default=None, metavar="MB",
                   help="Lean's --memory bound for each run (default 8192; 0 for none). Best-effort until the "
                        "sandbox")
    p.add_argument("--json", action="store_true",
                   help='print {"verdict": ..., "detail": ..., "module": ..., "theorem": ..., "source_sha256": ..., '
                        '"olean_sha256": ..., "olean_closure": ...} only')
    p.set_defaults(fn=cmd_probe_negation)

    p = sub.add_parser("fingerprint",
                       help="sha256 of each theorem's statement, delta-unfolded past the library roots, "
                            "binder-name-insensitive",
                       description="Statement fingerprint. NOT a sandbox: building untrusted Lean (the imported "
                                   "modules, a submitted text) runs that code with your permissions, so fingerprint "
                                   "untrusted input only inside a sandbox (e.g. Comparator's Linux sandbox in CI).")
    p.add_argument("--project", required=True, help="a built Lake project in which the imports resolve")
    p.add_argument("--import", dest="imports", action="append", required=True, metavar="MODULE",
                   help="module to import (repeatable)")
    p.add_argument("--target", dest="targets", action="append", required=True, metavar="THEOREM",
                   help="fully qualified theorem name (repeatable)")
    p.add_argument("--file", default=None,
                   help="the theorem's source file; only hashed, into the --json `source_sha256` that "
                        "`mission checks-record` compares with the node's artifact")
    p.add_argument("--wrapper", default=None,
                   help="command prefix before the pinned `lean` (default: leanlock with one slot "
                        "when ~/hodge-engine/leanlock.sh exists; '' for none)")
    p.add_argument("--timeout", type=int, default=1800, help="seconds for each Lean run")
    p.add_argument("--trusted-env", default=None, metavar="DIR",
                   help="the PINNED Lean env whose toolchain and .lake packages are trusted (default: "
                        "$TELPERION_LEAN_ENV; exit 2 if neither is set). Nothing from --project is trusted")
    p.add_argument("--trusted-manifest", default=None, metavar="FILE",
                   help="the sha256 manifest of the trusted env's files, verified before every run (default: "
                        "~/telperion-tools/trusted-manifests/<hash of the env's pins>.json; build it with "
                        "`telperion trusted-manifest build --env DIR`)")
    p.add_argument("--olean-dir", dest="olean_dirs", action="append", default=None, metavar="DIR",
                   help="an extra untrusted olean dir to replay modules from, besides <project>/.lake/build/lib/lean "
                        "(repeatable)")
    p.add_argument("--memory-mb", type=int, default=None, metavar="MB",
                   help="Lean's --memory bound for each run (default 8192; 0 for none). Best-effort until the "
                        "sandbox")
    p.add_argument("--json", action="store_true",
                   help='print {"fingerprints": {...}, "olean_sha256": ..., "olean_closure": [...], "module": ..., '
                        '"theorem": ..., "source_sha256": ...} (or {"error": ...}) only')
    p.set_defaults(fn=cmd_fingerprint)

    p = sub.add_parser("trusted-manifest",
                       help="build or verify the sha256 manifest of a pinned Lean env's trusted files (the replay "
                            "checks refuse to run without a matching one)")
    tm_sub = p.add_subparsers(dest="trusted_manifest_cmd", required=True)
    for name, what in (("build", "write"), ("verify", "check")):
        q = tm_sub.add_parser(name, help=f"{what} the manifest of --env")
        q.add_argument("--env", required=True, metavar="DIR", help="the pinned Lean env")
        q.add_argument("--out", default=None, metavar="FILE",
                       help="the manifest path (default: ~/telperion-tools/trusted-manifests/<hash>.json)")
        if name == "build":
            q.add_argument("--force", action="store_true", help="overwrite an existing manifest")
        q.set_defaults(fn=cmd_trusted_manifest)

    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())

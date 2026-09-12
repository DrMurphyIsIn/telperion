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

    from .missions.registry import load_campaign
    from .missions.schema import Node, SchemaError, load_manifest, save_node, slug_of
    from .missions.statements import write_statement

    root = _missions_root(args) / args.campaign
    manifest = load_manifest(root / "mission.toml")

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
    )

    node_path = root / "nodes" / f"{new_slug}.toml"
    save_node(node, node_path)
    stmt_path = write_statement(root, node, stmt_text, manifest)
    print(f"node: {node_path}")
    print(f"statement: {stmt_path}")
    return 0


def cmd_mission_audit(args) -> int:
    import dataclasses as _dc
    from datetime import date as _date

    from .missions.registry import load_campaign, promote_to_open
    from .missions.schema import Readback, SchemaError, save_node, slug_of

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
    today = _date.today().isoformat()
    rb = Readback(text=args.text, auditor=args.auditor, date=today)
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

    try:
        node = grant_status(camp, slug)
    except GateError as exc:
        print(str(exc))
        return 1

    note = ""
    if node.proof is not None and node.proof.via == "reduction":
        note = f" (closure_clean={node.proof.closure_clean})"
    print(f"{slug}: status -> {node.status}{note}")
    return 0


def cmd_mission_verify(args) -> int:
    from .missions.verify import verify_campaign

    roots = _campaign_roots(_missions_root(args), getattr(args, "campaign", None))
    any_fail = False
    for camp_root in roots:
        deep = getattr(args, "deep_lean", False)
        report = verify_campaign(camp_root, deep_lean=deep)
        if report.errors:
            for e in report.errors:
                print(f"ERROR [{camp_root.name}]: {e}")
        if report.warnings:
            for w in report.warnings:
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

    p = sub.add_parser("audit",
                       help="audit external Lean for sorry/axiom/stub/vacuity (the referee role)")
    p.add_argument("file")
    p.set_defaults(fn=cmd_audit)

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
    p.set_defaults(mission_fn=cmd_mission_add)

    # audit SLUG [--campaign C] --text T --auditor A
    p = msub.add_parser("audit", help="record a readback and promote draft -> open")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--text", required=True)
    p.add_argument("--auditor", required=True)
    p.set_defaults(mission_fn=cmd_mission_audit)

    # link SLUG [--campaign C] --artifact P --kind K --via V
    p = msub.add_parser("link", help="record a proof artifact link (status unchanged)")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.add_argument("--artifact", required=True)
    p.add_argument("--kind", required=True, choices=("lean_module", "frozen_cert"))
    p.add_argument("--via", required=True, choices=("direct", "reduction"))
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

    # grant SLUG [--campaign C]
    p = msub.add_parser("grant", help="flip open -> proved/refuted via the verify gate")
    p.add_argument("slug")
    p.add_argument("--campaign", default=None,
                   help="campaign name (auto-resolved from slug when omitted)")
    p.set_defaults(mission_fn=cmd_mission_grant)

    # verify [CAMPAIGN] [--deep-lean]
    p = msub.add_parser("verify", help="run the full invariant battery")
    p.add_argument("campaign", nargs="?", default=None)
    p.add_argument("--deep-lean", action="store_true", dest="deep_lean",
                   help="run lake build in lean/")
    p.set_defaults(mission_fn=cmd_mission_verify)

    # graph [CAMPAIGN]
    p = msub.add_parser("graph", help="emit DOT-language dependency graph to stdout")
    p.add_argument("campaign", nargs="?", default=None)
    p.set_defaults(mission_fn=cmd_mission_graph)

    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())

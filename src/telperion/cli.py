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
    """Load ``path.py:attr`` and return the attribute (called if callable)."""
    path, _, attr = spec.partition(":")
    if not attr:
        raise SystemExit(f"expected path.py:attr, got {spec!r}")
    p = Path(path).resolve()
    modspec = importlib.util.spec_from_file_location(p.stem, p)
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


def cmd_certify(args) -> int:
    fam, _ = _load(args.family)
    try:
        cf = certify(fam)
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


def cmd_probe(args) -> int:
    """Quick answer to: does this expression have a Polya certificate?"""
    import sympy as sp

    from .certify import polya_certify

    syms = tuple(sp.Symbol(s.strip(), nonnegative=True) for s in args.symbols.split(","))
    expr = sp.parse_expr(args.expression, local_dict={str(s): s for s in syms})
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
    p.set_defaults(fn=cmd_certify)

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

    p = sub.add_parser("probe", help="check one expression for a Polya certificate")
    p.add_argument("expression")
    p.add_argument("--symbols", default="u", help="comma-separated nonneg symbols")
    p.set_defaults(fn=cmd_probe)

    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())

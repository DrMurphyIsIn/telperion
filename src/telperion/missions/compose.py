"""The COMPOSITIONAL independent judge for ladder capstones (2026-09-27).

Why.  The Comparator replays a theorem's whole dependency closure in ONE single-threaded kernel
run.  For a ladder capstone (`AND.ladder_h8000_kernel`) that closure is every segment's edge /
slab / line certificate: run 36274981386 built the challenge in 38 min, then spent > 4 h in the
Comparator's replay and was cancelled at the job timeout.  No hosted-runner timeout fixes that.

What.  A node with a `[compose]` table (schema.ComposeSpec) is judged in parts, each part a
normal Comparator run in its own job of missions-comparator-heavy.yml:

  * one SEGMENT challenge per segment:   `MissionJudge.<node>__seg_<name> : <statement>`
    proved by the segment theorem (its closure is that segment's certificates only);
  * one IMPLICATION challenge:           `MissionJudge.<node>__compose (b_<name> : <statement>)...
    : <the registered node statement>` proved by the island's implication theorem.

Composition is modus ponens, so it needs no kernel -- but it happens in THIS tooling instead of
in one kernel run, so all of the risk sits in the checks below (peer governance, 2026-09-27):

  (a) IDENTITY BY EXPORTED TYPE.  Each segment part's judged theorem has type exactly the bare
      constant `<statement>`; the implication's leading binders are exactly those constants, in
      order; and each `<statement>`'s lean4export in the segment job is byte-identical to its
      lean4export in the implication job.  Two bundles are two environments, so equal source
      text is not enough: equal export bytes means equal constants, all the way down.
  (b) EVERY PART AXIOM-CHECKED against the same whitelist, recorded per part.
  (c) THE IMPLICATION MUST NOT DEPEND ON THE SEGMENT PROOFS: no constant in its closure is
      declared by a module matching `forbidden_modules`.  Otherwise its closure drags the
      certificates back in, or it "proves" the implication from the capstone and the scheme
      silently degenerates.  The regex must also bite: every segment part's closure must hit it.
  (d) The verdict says what was done: `judge=compositional`, and the record lists every part.

Inputs are one JSON per part, written by the part's job AFTER its Comparator run passed:

    {"node", "part" ("seg:<name>" | "compose"), "slug", "comparator" ("PASS"), "run_id",
     "kernel", "inspect" (ComposeInspect.lean output), "statement_exports" {stmt: sha256}}
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence

#: The only axioms any part may use (the same whitelist as every Comparator config here).
CLEAN_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

_HEX64 = re.compile(r"[0-9a-f]{64}")


def seg_slug(node: str, name: str) -> str:
    return f"{node}__seg_{name}"


def compose_slug(node: str) -> str:
    return f"{node}__compose"


def bridge(slug: str) -> str:
    return f"MissionJudge.{slug}"


def expected_parts(node: str, spec) -> Dict[str, str]:
    """part label -> challenge slug, for every part the verdict needs."""
    out = {f"seg:{nm}": seg_slug(node, nm) for nm in spec.segment_names}
    out["compose"] = compose_slug(node)
    return out


def verify(node: str, spec, parts: Sequence[dict]) -> List[str]:
    """Every reason the parts do NOT compose into a verdict on `node`.  Empty list = PASS."""
    errs: List[str] = []
    want = expected_parts(node, spec)
    by_part: Dict[str, dict] = {}
    for p in parts:
        label = p.get("part", "")
        if p.get("node") != node:
            errs.append(f"part {label!r} is for node {p.get('node')!r}, not {node!r}")
            continue
        if label in by_part:
            errs.append(f"part {label!r} appears twice; refusing to pick one")
            continue
        by_part[label] = p
    missing = sorted(set(want) - set(by_part))
    extra = sorted(set(by_part) - set(want))
    if missing:
        errs.append(f"missing part(s): {', '.join(missing)} -- every segment and the implication "
                    "must be judged, or nothing composes")
    if extra:
        errs.append(f"unexpected part(s): {', '.join(extra)} (not in the node's [compose] spec)")
    runs = {str(p.get("run_id", "")) for p in by_part.values()}
    if len(runs) > 1:
        errs.append(f"parts come from different runs {sorted(runs)}; a verdict glues ONE run")

    # (b) every part passed its own Comparator run and is axiom-clean.
    for label, p in sorted(by_part.items()):
        if label not in want:
            continue
        if p.get("comparator") != "PASS":
            errs.append(f"{label}: its Comparator run did not PASS ({p.get('comparator')!r})")
        if p.get("slug") != want[label]:
            errs.append(f"{label}: judged slug {p.get('slug')!r}, expected {want[label]!r}")
        ins = p.get("inspect") or {}
        if ins.get("theorem") != bridge(want[label]):
            errs.append(f"{label}: inspected {ins.get('theorem')!r}, not the judged bridge "
                        f"theorem {bridge(want[label])!r}")
        ax = set(ins.get("axioms") or [])
        if not ins or "axioms" not in ins:
            errs.append(f"{label}: no axiom report")
        elif not ax <= CLEAN_AXIOMS:
            errs.append(f"{label}: uses non-whitelisted axiom(s) {sorted(ax - CLEAN_AXIOMS)}")

    comp = by_part.get("compose")
    forbidden = re.compile(spec.forbidden_modules)
    stmts = list(spec.segment_statements)

    # (a) identity: segment types, implication binders, export bytes.
    for nm, stmt, _thm, _mod in spec.segments:
        p = by_part.get(f"seg:{nm}")
        if p is None:
            continue
        ins = p.get("inspect") or {}
        if ins.get("type_const") != stmt:
            errs.append(f"seg:{nm}: the judged theorem's type is {ins.get('type_const')!r}, not "
                        f"the bare constant {stmt!r}")
        h_seg = (p.get("statement_exports") or {}).get(stmt, "")
        if not _HEX64.fullmatch(h_seg or ""):
            errs.append(f"seg:{nm}: no lean4export sha256 for {stmt}")
        if comp is not None:
            h_imp = (comp.get("statement_exports") or {}).get(stmt, "")
            if not _HEX64.fullmatch(h_imp or ""):
                errs.append(f"compose: no lean4export sha256 for {stmt}")
            elif _HEX64.fullmatch(h_seg or "") and h_seg != h_imp:
                errs.append(f"{stmt}: exported differently in seg:{nm} ({h_seg[:16]}...) and in "
                            f"the implication ({h_imp[:16]}...); the hypothesis is NOT the "
                            "statement that was judged")
        # (c) teeth: the forbidden regex must match this segment's own certificate modules.
        mods = ins.get("closure_modules") or []
        if not any(forbidden.match(m) for m in mods):
            errs.append(f"seg:{nm}: no module in its closure matches forbidden_modules "
                        f"{spec.forbidden_modules!r}; the regex does not name the certificate "
                        "modules, so the implication's closure check would be vacuous")

    if comp is not None:
        ins = comp.get("inspect") or {}
        binders = list(ins.get("binders") or [])
        n = len(stmts)
        if binders[:n] != stmts:
            errs.append(f"compose: the implication's leading hypotheses are {binders[:n]}, not "
                        f"exactly the segment statements {stmts} in order")
        if len(binders) > n and binders[n] in stmts:
            errs.append(f"compose: hypothesis {n + 1} is again a segment statement "
                        f"({binders[n]}); the implication has the wrong arity")
        # (c) the implication's closure contains no certificate module.
        mods = ins.get("closure_modules")
        if not mods:
            errs.append("compose: no closure-module report, so nothing shows the implication "
                        "is independent of the segment proofs")
        else:
            hits = sorted(m for m in mods if forbidden.match(m))
            if hits:
                errs.append(f"compose: the implication's closure contains certificate module(s) "
                            f"{hits[:6]}{' ...' if len(hits) > 6 else ''}: it depends on the "
                            "segment proofs, so composing it proves nothing new")
    return errs


def verdict_line(*, island: str, node: str, spec, run_id: str, kernel: str) -> str:
    return (f"COMPARATOR PASS island={island} node={node} theorem={spec.theorem} run={run_id} "
            f"kernel={kernel} judge=compositional parts={len(spec.segment_names) + 1}")


def load_parts(d: Path) -> List[dict]:
    return [json.loads(p.read_text()) for p in sorted(Path(d).rglob("*.part.json"))]


INSPECT_SCRIPT = Path(__file__).resolve().parents[3] / "missions" / "judge_tools" / "ComposeInspect.lean"


def export_sha256(bundle: Path, module: str, constant: str, lean4export: str) -> str:
    """sha256 of `lean4export <module> -- <constant>`, streamed (exports run to hundreds of MB).
    lean4export is deterministic: the same constants export to the same bytes whichever module
    they are exported from, so equal hashes across two jobs mean equal constants."""
    import hashlib
    import subprocess
    h = hashlib.sha256()
    proc = subprocess.Popen(["lake", "env", lean4export, module, "--", constant],
                            cwd=bundle, stdout=subprocess.PIPE)
    assert proc.stdout is not None
    for chunk in iter(lambda: proc.stdout.read(1 << 20), b""):
        h.update(chunk)
    if proc.wait() != 0:
        raise RuntimeError(f"lean4export {module} -- {constant} exited {proc.returncode}")
    return h.hexdigest()


def inspect(bundle: Path, module: str, theorem: str) -> dict:
    import subprocess
    out = subprocess.run(["lake", "env", "lean", "--run", str(INSPECT_SCRIPT), module, theorem],
                         cwd=bundle, stdout=subprocess.PIPE, check=True, text=True).stdout
    return json.loads(out.strip().splitlines()[-1])


def cmd_part(args) -> int:
    """Write one part's JSON.  Run ONLY after that part's Comparator run passed."""
    slug = args.slug
    module = f"MissionChallenges.{slug}"
    doc = {
        "node": args.node, "part": args.part, "slug": slug, "comparator": "PASS",
        "run_id": str(args.run_id), "kernel": args.kernel, "job": args.job,
        "inspect": inspect(args.bundle, module, bridge(slug)),
        "statement_exports": {c: export_sha256(args.bundle, module, c, args.lean4export)
                              for c in [x for x in args.exports.split(",") if x]},
    }
    Path(args.out).write_text(json.dumps(doc, indent=1) + "\n")
    ins = doc["inspect"]
    print(f"part {args.part}: {ins['theorem']} axioms={ins['axioms']} closure={ins['closure_size']} "
          f"type_const={ins['type_const'] or '-'} binders={len(ins['binders'])}")
    for c, h in doc["statement_exports"].items():
        print(f"  export {c}: sha256 {h}")
    return 0


def cmd_verify(args) -> int:
    from .schema import load_node
    node = load_node(args.telperion / "missions" / args.campaign / "nodes" / f"{args.node}.toml")
    if node.compose is None:
        print(f"::error::{args.node} has no [compose] table", file=sys.stderr)
        return 2
    parts = load_parts(args.parts)
    errs = verify(args.node, node.compose, parts)
    kernels = {p.get("kernel", "") for p in parts}
    if len(kernels) != 1:
        errs.append(f"parts disagree on the kernel mode: {sorted(kernels)}")
    for p in sorted(parts, key=lambda p: p.get("part", "")):
        ins = p.get("inspect") or {}
        print(f"COMPOSE PART node={args.node} part={p.get('part')} slug={p.get('slug')} "
              f"theorem={ins.get('theorem')} axioms={','.join(ins.get('axioms') or []) or '-'} "
              f"closure={ins.get('closure_size')} comparator={p.get('comparator')} "
              f"job={p.get('job', '')}")
    if errs:
        for e in errs:
            print(f"::error::COMPOSE FAIL node={args.node}: {e}")
        print(f"COMPARATOR FAIL island={args.island} node={args.node} (compositional)")
        return 1
    print(verdict_line(island=args.island, node=args.node, spec=node.compose,
                       run_id=args.run_id, kernel=kernels.pop()))
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="the compositional judge: write a part, or glue them")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("part", help="inspect + export one PASSED part and write its JSON")
    p.add_argument("--bundle", type=Path, required=True)
    p.add_argument("--node", required=True)
    p.add_argument("--part", required=True, help='"seg:<name>" or "compose"')
    p.add_argument("--slug", required=True)
    p.add_argument("--exports", required=True, help="comma-separated statement constants")
    p.add_argument("--run-id", required=True)
    p.add_argument("--kernel", required=True)
    p.add_argument("--job", default="")
    p.add_argument("--lean4export", required=True)
    p.add_argument("--out", required=True)
    p.set_defaults(fn=cmd_part)
    v = sub.add_parser("verify", help="glue the parts; print the verdict line or FAIL")
    v.add_argument("--telperion", type=Path, default=Path(__file__).resolve().parents[3])
    v.add_argument("--campaign", required=True)
    v.add_argument("--node", required=True)
    v.add_argument("--island", required=True)
    v.add_argument("--parts", type=Path, required=True, help="directory of *.part.json files")
    v.add_argument("--run-id", required=True)
    v.set_defaults(fn=cmd_verify)
    args = ap.parse_args(list(argv) if argv is not None else None)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())

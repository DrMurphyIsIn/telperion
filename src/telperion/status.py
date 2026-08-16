"""The executable status generator: claims that cannot outrun their checks.

The origin campaign's `conjecture1_status.py` rule — *status is checkable,
not asserted* — is why its honesty spine survived three audits.  This module
generates STATUS.md by EXECUTING the project's manifest checks and reading
the frozen provenance manifests; there is no code path that writes a claim
without running its verification first.  The review-brief generator is the
sibling: the adversarial checklist the campaign hand-wrote for every
dispatched review, filled with the family's actual facts.
"""
from __future__ import annotations

import datetime
import json
import subprocess
import sys
from pathlib import Path


def generate_status(manifest_path: Path, group: str = "all") -> tuple[str, bool]:
    """Run every manifest check; return (STATUS.md text, all_green)."""
    import tomllib

    root = manifest_path.resolve().parent
    with open(manifest_path, "rb") as f:
        manifest = tomllib.load(f)
    rows = []
    all_green = True
    for c in manifest.get("check", []):
        if group != "all" and c.get("group", "quick") != group:
            rows.append((c["name"], "SKIPPED (group)", "", ""))
            continue
        r = subprocess.run(
            [sys.executable, str(root / c["script"]), "--check"],
            cwd=root,
            capture_output=True,
            text=True,
        )
        ok = r.returncode == 0
        all_green &= ok
        # enrich from the frozen manifests next to the script
        script_dir = (root / c["script"]).parent
        theorems, hashes = 0, []
        for m in sorted(script_dir.glob("frozen/**/manifest.json")) + sorted(
            script_dir.glob("frozen/manifest.json")
        ):
            doc = json.loads(m.read_text())
            theorems += doc.get("n_theorems", 0)
            hashes.append(doc.get("input_hash", "")[:16])
        rows.append(
            (
                c["name"],
                "GREEN" if ok else "**RED**",
                str(theorems) if theorems else "?",
                ", ".join(f"`{h}`" for h in hashes) or "—",
            )
        )
    today = datetime.date.today().isoformat()
    out = [
        "# STATUS",
        "",
        f"Generated {today} by `telperion status` — every verdict below is the",
        "result of an EXECUTED regeneration-diff, not an assertion.  Do not",
        "edit; regenerate.  A hash here matches the corresponding Lean file",
        "headers and certificate exports byte-for-byte.",
        "",
        "| family | check | theorems | input hash(es) |",
        "|---|---|---|---|",
    ]
    for name, verdict, theorems, hashes in rows:
        out.append(f"| {name} | {verdict} | {theorems} | {hashes} |")
    out.append("")
    out.append(
        "**Overall: ALL GREEN**" if all_green else "**Overall: FAILURES PRESENT**"
    )
    ledger_path = root / "ROUTES.json"
    if ledger_path.exists():
        from .ledger import RouteLedger

        led = RouteLedger(ledger_path)
        out.append("")
        out.append(f"Route ledger: {len(led.entries)} refused route(s) recorded — "
                   "see ROUTES.md before attempting new certificate designs.")
    out.append("")
    out.append(
        "Reminder inherited from the origin campaign: a green table above means "
        "these certificates are machine-checked; it does NOT by itself prove "
        "any surrounding conjecture. Keep the honest-status discipline."
    )
    return "\n".join(out) + "\n", all_green


def review_brief(family, fam_path: str, ihash: str) -> str:
    """The adversarial review checklist, filled with this family's facts."""
    syms = ", ".join(str(s) for s in family.symbols)
    axes = ", ".join(f"{n}∈{list(v)}" for n, v in family.grid.axes)
    n = family.grid.size()
    has_ties = family.ties is not None
    has_anchors = family.anchors is not None
    int_axes = [n_ for n_, vs in family.grid.axes
                if all(isinstance(v, int) for v in vs) and len(vs) > 1]
    lines = [
        f"# Adversarial review brief: {family.name}",
        "",
        f"Input hash `{ihash[:16]}` — must match the Lean headers, the frozen",
        "manifest, and any certificate export.  {0} instance(s); symbols {1} ≥ 0;"
        .format(n, syms or "(none)"),
        f"grid {axes}.",
        "",
        "Work each item trying to REFUTE, not confirm:",
        "",
        "1. **Identity**: `telperion export-certs ... && telperion recheck ...` —",
        "   the stdlib rechecker must agree at random rational points.  Then pick",
        "   TWO instances by hand and verify the num/den identity in an",
        "   independent CAS.",
        "2. **Falsity hunt**: `telperion hunt` (modes descent AND diverse) on the",
        "   rawest spelling of the claim.  A negative value anywhere is a",
        "   disproof — do this before trusting anything else.",
        "3. **Tie exactness**: "
        + (
            "declared ties exist — confirm the certifier's tie checks ran "
            "(checks_passed count) and independently verify tightness at each."
            if has_ties
            else "**NO ties declared.**  Ask the author where equality holds; an "
            "inequality with no known tightness analysis is under-understood.  "
            "Run `telperion margins` and inspect the tight-first entries."
        ),
        "4. **Anchors**: "
        + (
            "declared — re-evaluate each anchor by hand."
            if has_anchors
            else "**none declared.**  Request at least one exact pinned "
            "evaluation tying the family to its source."
        ),
        "5. **Arithmetic vs smooth**: "
        + (
            f"integer axes {int_axes} — run `telperion relax --axis {int_axes[0]}`; "
            "an ARITHMETIC verdict means analytic certificates were never going "
            "to close this and the Lean must use integrality."
            if int_axes
            else "no multi-valued integer axes."
        ),
        "6. **Drift**: `telperion verify` (or the generate script with --check) —",
        "   frozen output must regenerate byte-for-byte; then `lake build` in the",
        "   consuming project: the kernel is the only verdict that counts.",
        "7. **Boundaries**: check the CHANGELOG's named-open items against what",
        "   this family uses — anything leaning on a named-open feature is a",
        "   review finding.",
        "",
        "Report findings with exact witnesses (rational points, hashes, file",
        "lines).  The origin campaign's reviews corrected the author three",
        "times; assume this one will too.",
    ]
    return "\n".join(lines) + "\n"

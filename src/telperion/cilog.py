"""The Lean-failure knowledge base: hard-won gotchas as executable diagnostics.

The origin campaign paid one CI round-trip (~20 min) each to learn these.
`parse_log` extracts every error (the COUNT is always reported first — the
campaign's own rule: 'grep-truncated error lists hide failures; always count
errors before concluding'), matches each against the catalog, and names the
known repair.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

CATALOG = [
    (
        r"unsolved goals[\s\S]{0,400}?⁻¹",
        "field_simp distributed-spelling gotcha: field_simp needs ≠0 hypotheses "
        "in the DISTRIBUTED spelling it produces — read the ⁻¹-atom in the "
        "residual goal verbatim and state that exact hypothesis.",
    ),
    (
        r"The `?ring`? tactic failed[\s\S]{0,200}?\^",
        "ring cannot split NUMERAL bases with atom exponents "
        "((513/80)^k ≠ (76/115)^k * (621/64)^k to ring) — rewrite explicitly "
        "with `rw [← mul_pow]; norm_num` first.",
    ),
    (
        r"[Nn]o goals",
        "trailing tactic after the goal already closed (the classic: `ring` "
        "after a `field_simp` that finished) — use `try ring`, or drop the "
        "trailing tactic.",
    ),
    (
        r"unknown (identifier|constant)",
        "import-DAG gotcha: lake imports are NOT a global namespace — a "
        "generated file referencing theorems from a parallel branch needs an "
        "EXPLICIT import (root-list imports don't propagate).",
    ),
    (
        r"maximum.*heartbeats|deterministic timeout",
        "heartbeat budget: raise `set_option maxHeartbeats` via "
        "LeanProfile.options (the origin needed 4000000 for its heaviest "
        "generated file) or shard the family (ShardSpec).",
    ),
    (
        r"«|»",
        "unfilled template hole reached Lean — the lint gate should have "
        "refused this; regenerate rather than hand-editing, and report the "
        "emitter bug.",
    ),
    (
        r"unsolved goals",
        "generic unsolved goals: diff the hkey statement against the "
        "post-simp goal — the usual causes are spelling drift (expanded vs "
        "factored denominators) or a push_cast normalization moving cast "
        "interiors (↑(a+b+1) → ↑(1+a+b) splits atoms; use a pure-scalar "
        "assembly lemma).",
    ),
]

_ERR = re.compile(r"^(?:.*?)error: ([^\n]*(?:\n(?!.*?(?:error|warning):)[^\n]*){0,8})", re.M)
_LOC = re.compile(r"([A-Za-z0-9_/\.]+\.lean):(\d+):(\d+)")


@dataclass(frozen=True)
class LogDiagnosis:
    total_errors: int
    findings: list      # (location, matched diagnosis or None, excerpt)

    def render(self) -> str:
        out = [f"TOTAL ERRORS: {self.total_errors}  (count first — truncated "
               "lists hide failures)"]
        for loc, diag, excerpt in self.findings:
            out.append(f"\n{loc or '(no location)'}")
            out.append(f"  {excerpt.strip().splitlines()[0][:120]}")
            if diag:
                out.append(f"  KNOWN CLASS: {diag}")
            else:
                out.append("  (no catalog match — a new failure class; consider "
                           "adding it to the catalog once understood)")
        return "\n".join(out)


def parse_log(text: str) -> LogDiagnosis:
    findings = []
    errors = list(_ERR.finditer(text))
    for m in errors:
        excerpt = m.group(1)
        loc_m = _LOC.search(m.group(0)) or _LOC.search(excerpt)
        loc = f"{loc_m.group(1)}:{loc_m.group(2)}" if loc_m else None
        diag = None
        for pattern, advice in CATALOG:
            if re.search(pattern, excerpt):
                diag = advice
                break
        findings.append((loc, diag, excerpt))
    return LogDiagnosis(total_errors=len(errors), findings=findings)

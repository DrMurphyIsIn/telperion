"""Proof-auditor (Phase 3): machine-checkable referee for externally-authored
Lean.

The Lean kernel rejects a *false* theorem, but a green build still hides the
"proved nothing" classes: `sorry`/`admit`, a smuggled `axiom`, an empty `:= by`,
a missing type ascription, a `Prop := True` stub — and per-theorem *vacuity*, a
reflexive tautology (`X = X`, `0 ≤ 0`) that compiles while asserting nothing.

`audit_lean_text` runs the soundness lint (`lean_lint`) and a per-theorem
vacuity pass over *any* Lean — an LLM prover's output, a human proof, a
self-verified generation — and returns one unified report.  Unlike
`check_nonvacuous` (which only refuses a *wholly* vacuous file), the auditor
names each reflexive theorem, so a single tautology smuggled into an otherwise
real file is surfaced, not averaged away.

This adds no trusted surface — it is a static reader.  A clean audit is
necessary, not sufficient (the kernel remains the arbiter of truth); a dirty
audit is a concrete, cited defect.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .lean_lint import lint_lean_text
from .nonvacuity import _is_reflexive, _iter_theorem_statements


@dataclass(frozen=True)
class AuditFinding:
    code: str          # "sorry" | "axiom" | "vacuous" | ... (lint codes + "vacuous")
    severity: str      # "error" | "warn"
    message: str
    line: int | None = None
    theorem: str | None = None


@dataclass(frozen=True)
class AuditReport:
    findings: list[AuditFinding] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        """True iff no error-severity finding.  Warn-level findings (decorative
        stubs, mixed-file reference identities) do not fail the audit by default."""
        return not any(f.severity == "error" for f in self.findings)

    def render(self) -> str:
        if not self.findings:
            return "audit: clean (no soundness or vacuity findings)"
        head = f"audit: {len(self.findings)} finding(s)" + ("" if self.ok else " — FAILED")
        rows = []
        for f in self.findings:
            loc = f"L{f.line}" if f.line else "   "
            who = f" [{f.theorem}]" if f.theorem else ""
            rows.append(f"  {loc} [{f.code}/{f.severity}]{who} {f.message}")
        return "\n".join([head, *rows])


def audit_lean_text(text: str, *, path: str | None = None) -> AuditReport:
    """Audit Lean source for soundness-lint and per-theorem vacuity defects."""
    findings: list[AuditFinding] = []

    for issue in lint_lean_text(text, path=path):
        findings.append(
            AuditFinding(
                code=issue.code,
                severity=issue.severity,
                message=issue.message,
                line=issue.line,
            )
        )

    for name, stmt in _iter_theorem_statements(text):
        if _is_reflexive(stmt):
            findings.append(
                AuditFinding(
                    code="VACUOUS",
                    severity="error",
                    message="reflexive conclusion (t = t) — theorem asserts nothing",
                    theorem=name,
                )
            )

    return AuditReport(findings=findings)


def audit_lean_file(path) -> AuditReport:
    with open(path, "r", encoding="utf-8") as fh:
        return audit_lean_text(fh.read(), path=str(path))

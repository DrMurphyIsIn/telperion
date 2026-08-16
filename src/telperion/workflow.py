"""The enforced workflow: certify -> validate -> emit -> (user compiles) -> freeze.

Enforcement is structural, not advisory.  emit() requires BOTH a
CertifiedFamily witness (only constructible by certify()) and a green
ValidationReport; there is no API path from an InequalityFamily to Lean text.
A refusal is a WorkflowError — loudly, before any file is written.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Sequence

from .certify import CertifiedFamily
from .lean import LeanProfile
from .provenance import EmitResult, family_hash, header


class WorkflowError(RuntimeError):
    pass


@dataclass(frozen=True)
class ValidationReport:
    """Result of the exact-numeric validation layer.

    checks: (name, ok) pairs — every claim asserted in exact arithmetic
    (fractions.Fraction / sympy Rational; no floats in certificate paths).
    """

    checks: tuple[tuple[str, bool], ...] = ()

    @property
    def ok(self) -> bool:
        return all(ok for _, ok in self.checks)

    @staticmethod
    def from_asserts(named_checks: Sequence[tuple[str, Callable[[], None]]]) -> "ValidationReport":
        """Run assert-style thunks; an exception marks that check failed (and re-raises
        after recording, so failures stay loud)."""
        results: list[tuple[str, bool]] = []
        first_exc: BaseException | None = None
        for name, thunk in named_checks:
            try:
                thunk()
                results.append((name, True))
            except BaseException as e:  # noqa: BLE001 — validation must record any failure
                results.append((name, False))
                if first_exc is None:
                    first_exc = e
        report = ValidationReport(checks=tuple(results))
        if first_exc is not None:
            raise WorkflowError(
                f"validation failed: {[n for n, ok in results if not ok]}"
            ) from first_exc
        return report


@dataclass
class Emitter:
    """Base emitter interface; concrete emitters live in emit.py / emit_adapters.py."""

    kind: str = field(default="", init=False)

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        """Return (Lean body text, number of theorems)."""
        raise NotImplementedError

    def config_fingerprint(self) -> str:
        """Stable serialization of this emitter's configuration for the input
        hash.  Callable fields cannot be hashed semantically; their effect is
        covered by the freeze/diff byte comparison instead."""
        parts = [self.kind]
        for k, v in sorted(vars(self).items()):
            if k != "kind" and not callable(v):
                parts.append(f"{k}={v!r}")
        return "|".join(parts)


def emit(
    fam: CertifiedFamily,
    profile: LeanProfile,
    emitters: Sequence[Emitter],
    validation: ValidationReport,
    file_name: str | None = None,
) -> EmitResult:
    """Render the certified family through the emitters into stamped Lean text.

    Refuses without a green ValidationReport.  Rendering is pure — all
    self-checks already ran in certify(); a rendering error here is a bug,
    not a soundness event (the Lean kernel is the only trusted component).
    """
    if not isinstance(fam, CertifiedFamily):
        raise WorkflowError("emit() requires a CertifiedFamily witness from certify()")
    if not validation.ok:
        raise WorkflowError(
            f"emit() refused: validation not green "
            f"({[n for n, ok in validation.checks if not ok]})"
        )
    import hashlib

    ihash = family_hash(fam.family, profile)
    h = hashlib.sha256(ihash.encode())
    for em in emitters:
        h.update(em.config_fingerprint().encode())
        h.update(b"\x00")
    ihash = h.hexdigest()
    bodies: list[str] = []
    n_theorems = 0
    for em in emitters:
        body, n = em.emit_body(fam, profile)
        bodies.append(body)
        n_theorems += n
    hdr = header(fam.family, ihash, n_theorems, fam.checks_passed)
    text = profile.file_shell(hdr, "\n".join(bodies))
    fname = file_name or f"{fam.family.name}.lean"
    return EmitResult(
        family_name=fam.family.name,
        input_hash=ihash,
        files={fname: text},
        n_theorems=n_theorems,
        n_checks=fam.checks_passed,
    )

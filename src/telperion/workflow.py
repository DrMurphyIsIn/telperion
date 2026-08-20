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
from .provenance import EmitResult, family_hash, header, heartbeat


class WorkflowError(RuntimeError):
    pass


@dataclass(frozen=True)
class ShardSpec:
    """Split emission across files: at most max_theorems per file.  Files are
    named from module_base's last component (Cells.lean, Cells2.lean, ...);
    shard n >= 2 imports every earlier shard's module and omits the prelude
    (which lives only in shard 1) -- the origin campaign's CertB/C/D split,
    automated, with the import-DAG gotcha handled."""

    max_theorems: int
    module_base: str


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
    # Names of prelude lemmas this emitter's Lean CALLS but does not itself
    # define — the profile must supply them (via prelude/imports).  emit()
    # checks this and raises locally, turning the "shipped Lean references an
    # unknown identifier" class from a CI-only failure into a build-time one
    # (the missing-bilinear_corner_nonneg H-floor incident, 2026-08-16).
    requires_prelude: tuple[str, ...] = field(default=(), init=False)

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        """Return (Lean body text, number of theorems)."""
        raise NotImplementedError

    def emit_units(self, fam: CertifiedFamily, profile: LeanProfile) -> list[tuple[str, int]]:
        """Per-instance (text, n_theorems) units, for sharding.  Default:
        re-render each instance through emit_body on a restricted view.
        Emitters with cross-instance state (e.g. a single assembled theorem)
        should override to return themselves as ONE unit."""
        import time

        from .certify import restrict_instances

        units = []
        t0, n = time.time(), len(fam.instances)
        for i in range(n):
            units.append(self.emit_body(restrict_instances(fam, [i]), profile))
            heartbeat(f"render {fam.family.name} [{self.kind}]", i + 1, n, t0)
        return units

    def code_fingerprint(self) -> str:
        """Version-stable hash of this emitter's own source — its class and every
        telperion base up the MRO.

        Folded into the input hash so a change to EMISSION LOGIC moves the hash
        even when the config fields are unchanged.  This closes the gap that let
        the G1 empty-binder regression ship under a stale hash: previously only
        config fields and the manual ``__version__`` string were covered, so an
        emitter-body edit that produced different Lean left every frozen hash
        untouched (REVIEW_20260816_TELPERION_G1).

        Hashes the RAW source text (``inspect.getsource``), newline-normalized —
        NOT ``ast.dump``, whose serialization format changes across Python
        versions and would make the input hash version-dependent, breaking the
        cross-version byte-stability the CI matrix (3.11–3.13) enforces. Raw
        source is identical under every interpreter. The trade-off is
        deliberate: ANY edit to the emitter source — including comments and
        formatting — moves the fingerprint, which for a drift net is the
        conservative behavior (any emitter change → refreeze → review). When
        source is unavailable (an emitter defined in a REPL) that class's
        contribution is the empty-source hash and the config-field serialization
        remains the residual signal. KNOWN RESIDUAL: module-level helper
        functions the emitter *calls* are not captured — only the class bodies —
        so a change confined to a shared helper still relies on the compile/diff
        gates as backstop.
        """
        import hashlib
        import inspect

        parts: list[str] = []
        for cls in type(self).__mro__:
            mod = getattr(cls, "__module__", "") or ""
            if not mod.startswith("telperion"):
                continue  # skip `object` and any non-telperion mixin
            try:
                src = "\n".join(inspect.getsource(cls).splitlines())
            except (OSError, TypeError):
                src = ""
            parts.append(f"{cls.__qualname__}={hashlib.sha256(src.encode()).hexdigest()[:16]}")
        return "|".join(parts)

    def config_fingerprint(self) -> str:
        """Stable serialization of this emitter's configuration AND code for the
        input hash.  Callable fields cannot be hashed semantically; their effect
        is covered by the freeze/diff byte comparison instead.  The emitter's
        code identity (``code_fingerprint``) is appended so emission-logic
        changes move the hash — not just config-field changes."""
        parts = [self.kind]
        for k, v in sorted(vars(self).items()):
            # `requires_prelude` is a validation declaration, not output config
            # — excluded so it does not perturb every family's input hash.
            if k not in ("kind", "requires_prelude") and not callable(v):
                parts.append(f"{k}={v!r}")
        parts.append("code:" + self.code_fingerprint())
        return "|".join(parts)


def emit(
    fam: CertifiedFamily,
    profile: LeanProfile,
    emitters: Sequence[Emitter],
    validation: ValidationReport,
    file_name: str | None = None,
    shard: "ShardSpec | None" = None,
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
    import sys
    import time

    from dataclasses import replace as _dc_replace

    from .lean_lint import check_lean_text
    from .lint import lint_files

    def _phase(msg: str) -> None:
        print(f"[telperion] emit {fam.family.name}: {msg}",
              file=sys.stderr, flush=True)

    # Prelude-dependency contract: a lemma an emitter CALLS but does not define
    # must be reachable — defined in the prelude, or supplied by a project
    # import.  We can verify the prelude textually; a custom import (anything
    # beyond "Mathlib") MIGHT supply it, so we trust it and let the compile
    # gate be the backstop.  The refusal fires only when neither is possible:
    # no prelude definition and no import that could carry it (the H-floor
    # self-contained-file incident, 2026-08-16).
    custom_imports = [i for i in profile.imports if i != "Mathlib"]
    for em in emitters:
        missing = [name for name in getattr(em, "requires_prelude", ())
                   if name not in profile.prelude and not custom_imports]
        if missing:
            raise WorkflowError(
                f"emit() refused: {em.kind} emits calls to {missing} but the "
                f"profile neither defines them in its prelude nor imports a "
                f"module that could (add to LeanProfile.prelude or .imports)")

    _phase(f"input hash over {fam.family.grid.size()} cells...")
    t_hash = time.time()
    ihash = family_hash(fam.family, profile)
    _phase(f"input hash done ({time.time() - t_hash:.1f}s); rendering...")
    t_render = time.time()
    h = hashlib.sha256(ihash.encode())
    for em in emitters:
        h.update(em.config_fingerprint().encode())
        h.update(b"\x00")
    if shard is not None:
        h.update(f"shard:{shard.max_theorems}:{shard.module_base}".encode())
    ihash = h.hexdigest()

    # Generated-body text per file, for the soundness gate (kept separate from
    # the assembled file so the gate lints the tool's OWN output, not the
    # trusted profile prelude/header).
    _gen_bodies: list[tuple[str, str]] = []
    if shard is None:
        bodies: list[str] = []
        n_theorems = 0
        for em in emitters:
            body, n = em.emit_body(fam, profile)
            bodies.append(body)
            n_theorems += n
        hdr = header(fam.family, ihash, n_theorems, fam.checks_passed)
        gen = "\n".join(bodies)
        text = profile.file_shell(hdr, gen)
        fname = file_name or f"{fam.family.name}.lean"
        files = {fname: text}
        _gen_bodies.append((fname, gen))
    else:
        units: list[tuple[str, int]] = []
        for em in emitters:
            units.extend(em.emit_units(fam, profile))
        n_theorems = sum(n for _, n in units)
        base = shard.module_base.rsplit(".", 1)[-1]
        # greedy in-order packing at instance boundaries
        packs: list[list[str]] = [[]]
        counts = [0]
        for text, n in units:
            if counts[-1] and counts[-1] + n > shard.max_theorems:
                packs.append([])
                counts.append(0)
            packs[-1].append(text)
            counts[-1] += n
        files = {}
        for i, (pack, cnt) in enumerate(zip(packs, counts), 1):
            hdr = header(fam.family, ihash, cnt, fam.checks_passed)
            if i == 1:
                prof_i = profile
                fname = f"{base}.lean"
            else:
                earlier = tuple(
                    shard.module_base if j == 1 else f"{shard.module_base}{j}"
                    for j in range(1, i)
                )
                prof_i = _dc_replace(profile, prelude="", imports=profile.imports + earlier)
                fname = f"{base}{i}.lean"
            pack_text = "\n".join(pack)
            files[fname] = prof_i.file_shell(hdr, pack_text)
            _gen_bodies.append((fname, pack_text))

    _phase(f"rendered {n_theorems} theorems in {len(files)} file(s) "
           f"({time.time() - t_render:.1f}s); linting...")
    lint_files(files)
    # Soundness gate (complements the structural lint above): refuse to freeze
    # Lean that would pass CI while proving nothing — a `sorry`/`admit`, a
    # smuggled `axiom`, an empty `:= by`, or a theorem with no type ascription.
    # Scoped to the tool's GENERATED bodies, not the user-supplied profile
    # prelude/header (trusted profile content — a full-file check is available
    # via `telperion lint-lean`).  Error-severity only (a legitimate `:= rfl` is
    # a WARN and does not block); validated to fire on none of the frozen
    # production families.
    for fname, gen in _gen_bodies:
        check_lean_text(gen, path=fname)
    # Non-vacuity gate (Telperion pointed at its own output): refuse a reflexive
    # tautology (`X = X`, `0 ≤ 0`) that compiles green while verifying nothing —
    # the one soundness-adjacent defect the kernel cannot catch (it lives in the
    # STATEMENT, not the proof).  A family that intentionally emits reference /
    # degenerate-boundary identities opts out via `LeanProfile(allow_reflexive=True)`.
    if not profile.allow_reflexive:
        from .nonvacuity import check_nonvacuous
        for fname, gen in _gen_bodies:
            check_nonvacuous(gen, path=fname)
    return EmitResult(
        family_name=fam.family.name,
        input_hash=ihash,
        files=files,
        n_theorems=n_theorems,
        n_checks=fam.checks_passed,
    )

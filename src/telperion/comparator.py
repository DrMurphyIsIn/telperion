"""Comparator bridge: emit ``openai/ten-proofs`` **Comparator** challenge configs
from Telperion output.

`Comparator <https://github.com/leanprover/comparator>`_ is an INDEPENDENT judge
for Lean proofs.  Given a *challenge* module and a *solution* module it:

  1. compiles both in a ``landrun`` sandbox,
  2. exports both with ``lean4export``,
  3. asserts the solution declares the SAME theorem statements (types) as the
     challenge -- not something weaker,
  4. asserts the solution's proof uses only a whitelist of axioms,
  5. replays the proof through the Lean kernel and -- with ``enable_nanoda`` --
     through ``nanoda_bin``, a SECOND, non-Lean kernel.

For Telperion this mechanizes the trust story and closes three seams the
``emit()`` pipeline cannot on its own:

  * **statement identity** -- the emitted proof must prove *exactly* the
    statement authored in an independent challenge module: a stronger,
    generator-independent form of :mod:`telperion.nonvacuity`'s reflexive-
    statement guard (the ``0 <= 0`` that ``bernoulli_k1`` emits is the exact
    defect this catches);
  * **axiom whitelist** -- a per-theorem, machine-checked form of the
    ``#print axioms`` AxiomGuard, forbidding e.g. ``native_decide``'s
    ``ofReduceBool``;
  * **independent kernel** -- ``nanoda`` re-verification, beyond Mathlib's own
    kernel.

The generator stays untrusted by design: a wrong certificate is a Comparator
failure, never a false theorem.

This module writes the JSON config only (pure, dependency-light, runnable with
no Lean toolchain).  Running ``lake exe comparator <config>.json`` is the CI
step; see ``examples/bernoulli/comparator/`` for a worked end-to-end scaffold.
"""
from __future__ import annotations

import json
import re
from collections import OrderedDict
from pathlib import Path
from typing import Mapping, Sequence

from .lean import LeanProfile
from .provenance import EmitResult

# The axiom set Telperion's kernel-clean production proofs live under (the BG
# capstone's ``#print axioms`` set).  Anything beyond this -- ``sorryAx``,
# ``ofReduceBool`` (native_decide), a smuggled ``axiom`` -- must be a Comparator
# failure, not a silent pass.
CLEAN_AXIOMS: tuple[str, ...] = ("propext", "Quot.sound", "Classical.choice")

# ``theorem foo`` / ``lemma foo`` / ``theorem «foo»`` at line start (post-header,
# the emitter never indents a top-level declaration).
_DECL_RE = re.compile(r"(?m)^\s*(?:theorem|lemma)\s+«?([A-Za-z_][\w'.]*)»?")
# A whole declaration up to its ``:= by`` / ``:=`` proof, for scaffolding a
# challenge module with matching signatures.
_SIG_RE = re.compile(r"(?ms)^\s*(?:theorem|lemma)\s+«?([A-Za-z_][\w'.]*)»?(.*?):=")


def _qualify(namespace: Sequence[str], name: str) -> str:
    """Fully-qualified Lean name -- Comparator matches theorems by this, so the
    challenge and solution modules may DIFFER while the names coincide (exactly
    how ten-proofs pairs module ``ComparatorChallenges.C_...`` with solution
    module ``Permanent`` under shared names ``PermanentFormulaLowerBound.*``)."""
    if "." in name:  # already qualified (e.g. an explicit open-namespace decl)
        return name
    return ".".join((*namespace, name))


def _module_of(fname: str) -> str:
    """Lean module name from an emitted file name: ``Foo/Bar.lean`` -> ``Foo.Bar``."""
    stem = re.sub(r"\.lean$", "", fname)
    return stem.replace("/", ".").replace("\\", ".")


def _stem(fname: str) -> str:
    return re.sub(r"\.lean$", "", fname).replace("\\", "/").rsplit("/", 1)[-1]


def _shard_module_for(fname: str, module_base: str) -> str:
    """The Lean *module* a sharded emit's file belongs to, reconstructed from the
    ``ShardSpec.module_base``.  ``emit()`` names shard files from ``module_base``'s
    last component -- ``Cells.lean``, ``Cells2.lean``, ... -- while the modules
    keep the full base: shard 1 is ``module_base``, shard *i* is
    ``f"{module_base}{i}"`` (that is exactly what shard *i*+1 imports).  So
    ``Cells3.lean`` under base ``R7Hyps.StarOfHubs.Cells`` is module
    ``R7Hyps.StarOfHubs.Cells3`` -- not the filename-derived ``Cells3``.
    """
    base = module_base.rsplit(".", 1)[-1]
    stem = _stem(fname)
    if stem == base:
        return module_base
    if stem.startswith(base) and stem[len(base):].isdigit():
        return f"{module_base}{stem[len(base):]}"
    raise ValueError(
        f"file {fname!r} is not a shard of module_base {module_base!r} "
        f"(expected {base}.lean / {base}<n>.lean)"
    )


def emitted_theorem_names(result: EmitResult, profile: LeanProfile) -> list[str]:
    """Fully-qualified names of every theorem/lemma Telperion emitted, in file
    then source order, de-duplicated.  These become the ``theorem_names`` the
    Comparator is asked to certify."""
    names: list[str] = []
    seen: set[str] = set()
    for fname in sorted(result.files):
        for m in _DECL_RE.finditer(result.files[fname]):
            q = _qualify(profile.namespace, m.group(1))
            if q not in seen:
                seen.add(q)
                names.append(q)
    return names


def _names_in(text: str, namespace: Sequence[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for m in _DECL_RE.finditer(text):
        q = _qualify(namespace, m.group(1))
        if q not in seen:
            seen.add(q)
            out.append(q)
    return out


def emitted_theorem_names_by_file(
    result: EmitResult, profile: LeanProfile
) -> "OrderedDict[str, list[str]]":
    """Per-file fully-qualified theorem names (file order = sorted), for sharded
    emits where each shard becomes its own Comparator solution module."""
    return OrderedDict(
        (fname, _names_in(result.files[fname], profile.namespace))
        for fname in sorted(result.files)
    )


def solution_module_of(result: EmitResult) -> str:
    """The Lean module a single-file emit produced (the Comparator
    ``solution_module``).  Raises for a sharded/multi-file emit -- pick one
    explicitly there."""
    if len(result.files) != 1:
        raise ValueError(
            f"emit produced {len(result.files)} files "
            f"({sorted(result.files)}); pass solution_module= explicitly"
        )
    return _module_of(next(iter(result.files)))


def challenge_config(
    *,
    challenge_module: str,
    solution_module: str,
    theorem_names: Sequence[str],
    permitted_axioms: Sequence[str] = CLEAN_AXIOMS,
    enable_nanoda: bool = True,
) -> "OrderedDict[str, object]":
    """A Comparator challenge config (the JSON ``lake exe comparator`` consumes).

    Field order and names mirror the ten-proofs challenge files exactly
    (e.g. ``ComparatorChallenges/C_PermanentFormulaLowerBound.json``)."""
    if not theorem_names:
        raise ValueError("challenge_config: theorem_names is empty")
    if not permitted_axioms:
        raise ValueError(
            "challenge_config: permitted_axioms is empty -- an empty whitelist "
            "rejects every proof; pass CLEAN_AXIOMS for the standard set"
        )
    for field, val in (("challenge_module", challenge_module),
                       ("solution_module", solution_module)):
        if not isinstance(val, str) or not val.strip():
            raise ValueError(f"challenge_config: {field} must be a non-empty module name")
    return OrderedDict(
        (
            ("challenge_module", challenge_module),
            ("solution_module", solution_module),
            ("theorem_names", list(theorem_names)),
            ("permitted_axioms", list(permitted_axioms)),
            ("enable_nanoda", bool(enable_nanoda)),
        )
    )


def challenge_for_result(
    result: EmitResult,
    profile: LeanProfile,
    *,
    challenge_module: str,
    solution_module: str | None = None,
    permitted_axioms: Sequence[str] = CLEAN_AXIOMS,
    enable_nanoda: bool = True,
) -> "OrderedDict[str, object]":
    """Build a challenge config straight from an :class:`EmitResult`: theorem
    names and (for a single-file emit) the solution module are derived, the
    challenge module is the independent statement authority you supply."""
    names = emitted_theorem_names(result, profile)
    if not names:
        raise ValueError("challenge_for_result: emit produced no theorems to certify")
    sol = solution_module if solution_module is not None else solution_module_of(result)
    return challenge_config(
        challenge_module=challenge_module,
        solution_module=sol,
        theorem_names=names,
        permitted_axioms=permitted_axioms,
        enable_nanoda=enable_nanoda,
    )


def write_challenge_config(path: str | Path, config: Mapping[str, object]) -> Path:
    """Write a challenge config as JSON (trailing newline, ten-proofs style)."""
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(config, indent=2) + "\n")
    return p


def _render_scaffold(
    src: str, profile: LeanProfile, *, module_name: str, independent_tactic: str
) -> str:
    """One challenge module from one emitted file's text: every theorem SIGNATURE
    re-stated (so Comparator's type-identity check is exercised) proved by an
    INDEPENDENT tactic instead of Telperion's certificate.  A standalone module
    (imports Mathlib + the profile's options only -- NOT the solution shards)."""
    blocks: list[str] = []
    for m in _SIG_RE.finditer(src):
        name, sig = m.group(1), m.group(2).rstrip()
        blocks.append(f"theorem {name}{sig} := by\n  {independent_tactic}")
    if not blocks:
        raise ValueError(f"no theorem signatures found for {module_name}")
    header = (
        f"/- Comparator challenge module for `{module_name}` -- INDEPENDENT statement\n"
        f"   authority for the Telperion-emitted solution.  Signatures are the\n"
        f"   emitted theorems' types (Comparator asserts the solution proves\n"
        f"   exactly these); the proofs here are independent of Telperion's\n"
        f"   certificate.  Replace with hand-authored statements to guard against\n"
        f"   certificate drift.  -/\n"
    )
    parts = [header, "import Mathlib", ""]
    if profile.options:
        parts.extend(profile.options)
        parts.append("")
    for ns in profile.namespace:
        parts.append(f"namespace {ns}")
    if profile.namespace:
        parts.append("")
    parts.append("\n\n".join(blocks))
    parts.append("")
    for ns in reversed(profile.namespace):
        parts.append(f"end {ns}")
    return "\n".join(parts) + "\n"


def render_challenge_scaffold(
    result: EmitResult,
    profile: LeanProfile,
    *,
    module_name: str,
    independent_tactic: str = "positivity",
) -> str:
    """Single-file challenge scaffold.  For sharded (multi-file) emits use
    :func:`render_sharded_challenge_scaffolds`.

    The signatures are copied so the pilot runs green out of the box; the point
    of the challenge module is that its *statement* is the authority.  In real
    use, hand-author these statements from the problem definition (not from the
    emitted proof) so a drifted certificate is caught.  The proof term is
    already independent of Telperion here, which alone exercises the axiom
    whitelist and the nanoda kernel replay against a second proof of each goal.
    """
    if len(result.files) != 1:
        raise ValueError(
            "render_challenge_scaffold supports single-file emits only; "
            "use render_sharded_challenge_scaffolds for a sharded emit"
        )
    src = next(iter(result.files.values()))
    return _render_scaffold(
        src, profile, module_name=module_name, independent_tactic=independent_tactic
    )


def _challenge_module_name(solution_module: str, suffix: str) -> str:
    """Challenge module paired with a solution module: suffix the last component
    so ``R7Hyps.StarOfHubs.Cells2`` -> ``R7Hyps.StarOfHubs.Cells2Challenge``."""
    return solution_module + suffix


def sharded_challenge_configs(
    result: EmitResult,
    profile: LeanProfile,
    *,
    module_base: str,
    challenge_suffix: str = "Challenge",
    permitted_axioms: Sequence[str] = CLEAN_AXIOMS,
    enable_nanoda: bool = True,
) -> list["OrderedDict[str, object]"]:
    """One Comparator config per shard of a sharded emit.

    Each shard file DECLARES its own theorems (they are not imported), so making
    each shard its own ``solution_module`` keeps every listed theorem genuinely
    declared in the module Comparator loads -- the interpretation-robust choice
    if "identical declarations" is read strictly.  The paired challenge module
    (``<shard>Challenge``) restates just that shard's statements.
    """
    by_file = emitted_theorem_names_by_file(result, profile)
    configs: list[OrderedDict[str, object]] = []
    for fname, names in by_file.items():
        if not names:
            continue  # a shard with no theorems (e.g. a pure-import umbrella) — skip
        sol = _shard_module_for(fname, module_base)
        configs.append(
            challenge_config(
                challenge_module=_challenge_module_name(sol, challenge_suffix),
                solution_module=sol,
                theorem_names=names,
                permitted_axioms=permitted_axioms,
                enable_nanoda=enable_nanoda,
            )
        )
    if not configs:
        raise ValueError("sharded_challenge_configs: emit produced no theorems")
    return configs


def render_sharded_challenge_scaffolds(
    result: EmitResult,
    profile: LeanProfile,
    *,
    module_base: str,
    challenge_suffix: str = "Challenge",
    independent_tactic: str = "positivity",
) -> "OrderedDict[str, str]":
    """One challenge module per shard, keyed by challenge *file name*
    (``Cells2Challenge.lean``).  Each restates its shard's signatures with an
    independent proof; standalone (imports Mathlib + profile options only)."""
    out: "OrderedDict[str, str]" = OrderedDict()
    for fname in sorted(result.files):
        src = result.files[fname]
        if not _DECL_RE.search(src):
            continue
        sol = _shard_module_for(fname, module_base)
        chal = _challenge_module_name(sol, challenge_suffix)
        chal_file = chal.rsplit(".", 1)[-1] + ".lean"
        out[chal_file] = _render_scaffold(
            src, profile, module_name=chal, independent_tactic=independent_tactic
        )
    if not out:
        raise ValueError("render_sharded_challenge_scaffolds: no theorems found")
    return out

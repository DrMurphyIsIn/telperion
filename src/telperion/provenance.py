"""Provenance: input hashing, header stamps, freeze manifests, drift detection.

Every emitted file begins with a structured header carrying the tool version
and a SHA-256 input hash over the canonical serialization of everything that
determines the output: the family (name, symbols, grid, constants, and the
canonical srepr of every grid point's expressions and box), the Lean profile,
and the template texts.  Timestamps are deliberately excluded — byte-identical
inputs give byte-identical files, so `diff` detects drift and nothing else.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

import sympy as sp

from . import __version__
from .expr import canonical_srepr
from .family import InequalityFamily
from .lean import DEFAULT_SKELETONS, LeanProfile


def family_hash(family: InequalityFamily, profile: LeanProfile) -> str:
    h = hashlib.sha256()

    def feed(tag: str, s: str) -> None:
        h.update(tag.encode())
        h.update(b"\x00")
        h.update(s.encode())
        h.update(b"\x01")

    feed("tool", __version__)
    feed("name", family.name)
    feed("kind", family.kind)
    feed("auto", f"{family.auto_lift},{family.auto_subdivide}")
    feed("symbols", ",".join(str(s) for s in family.symbols))
    feed("grid", json.dumps([[n, list(v)] for n, v in family.grid.axes]))
    feed(
        "constants",
        json.dumps({k: str(sp.Rational(v)) for k, v in sorted(family.constants.items())}),
    )
    for pt in family.grid.points():
        key = json.dumps(dict(pt), sort_keys=True)
        feed("pt", key)
        feed("lean_name", family.lean_name(pt))
        if family.kind == "direct":
            feed("target", canonical_srepr(family.target(pt)))
        else:
            feed("before", canonical_srepr(family.before(pt)))
            feed("after", canonical_srepr(family.after(pt)))
            for ax in family.box(pt):
                feed(
                    "axis",
                    f"{ax.symbol}|{canonical_srepr(ax.lo)}|{canonical_srepr(ax.hi)}|{ax.lo_is_floor}",
                )
        if family.den_atoms is not None:
            for a in family.den_atoms(pt):
                feed("den_atom", canonical_srepr(a))
        if family.ties is not None:
            for tie in family.ties(pt):
                feed("tie", json.dumps(sorted((str(k), str(v)) for k, v in tie.items())))
        if family.anchors is not None:
            for subs, val in family.anchors(pt):
                feed("anchor", json.dumps(sorted((str(k), str(v)) for k, v in subs.items())) + f"={val}")
    feed("profile.ns", ".".join(profile.namespace))
    feed("profile.imports", ",".join(profile.imports))
    feed("profile.prelude", profile.prelude)
    feed("profile.unfold", ",".join(profile.unfold_lemmas))
    feed("profile.options", ",".join(profile.options))
    for kind in sorted(DEFAULT_SKELETONS):
        feed(f"skeleton.{kind}", profile.skeleton(kind))
    return h.hexdigest()


def header(family: InequalityFamily, ihash: str, n_theorems: int, n_checks: int) -> str:
    return (
        f"/- telperion {__version__} | family {family.name} | "
        f"input-hash {ihash[:16]}\n"
        f"   {n_theorems} theorems, {n_checks} generation-time self-checks passed.\n"
        f"   Regenerate & verify:  forge diff --family <module:attr> --manifest "
        f"<manifest.json> --check\n"
        f"   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/\n"
    )


@dataclass(frozen=True)
class EmitResult:
    """What emit() produced: file name -> full text, plus the hash it was stamped with."""

    family_name: str
    input_hash: str
    files: dict[str, str]
    n_theorems: int
    n_checks: int


def freeze(result: EmitResult, out_dir: Path) -> Path:
    """Write the emitted files plus a manifest recording the input hash."""
    out_dir.mkdir(parents=True, exist_ok=True)
    for fname, text in result.files.items():
        (out_dir / fname).write_text(text)
    manifest = {
        "family": result.family_name,
        "input_hash": result.input_hash,
        "tool_version": __version__,
        "files": sorted(result.files),
        "n_theorems": result.n_theorems,
    }
    mpath = out_dir / "manifest.json"
    mpath.write_text(json.dumps(manifest, indent=2) + "\n")
    return mpath


@dataclass(frozen=True)
class DiffReport:
    ok: bool
    details: list[str]


def diff_frozen(result: EmitResult, out_dir: Path) -> DiffReport:
    """Regenerated output vs the frozen copy: byte comparison, hash included."""
    details: list[str] = []
    mpath = out_dir / "manifest.json"
    if not mpath.exists():
        return DiffReport(False, [f"missing manifest {mpath}"])
    manifest = json.loads(mpath.read_text())
    if manifest.get("input_hash") != result.input_hash:
        details.append(
            f"input hash drift: frozen {manifest.get('input_hash', '')[:16]} "
            f"vs regenerated {result.input_hash[:16]}"
        )
    for fname, text in result.files.items():
        fpath = out_dir / fname
        if not fpath.exists():
            details.append(f"missing frozen file {fname}")
        elif fpath.read_text() != text:
            details.append(f"content drift in {fname}")
    for fname in manifest.get("files", []):
        if fname not in result.files:
            details.append(f"frozen file {fname} no longer generated")
    return DiffReport(ok=not details, details=details)

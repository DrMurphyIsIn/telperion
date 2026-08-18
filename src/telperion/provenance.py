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
import sys
import time
from dataclasses import dataclass
from pathlib import Path

import sympy as sp

from . import __version__
from .expr import canonical_srepr
from .family import InequalityFamily
from .lean import DEFAULT_SKELETONS, LeanProfile


def heartbeat(phase: str, done: int, total: int, t0: float,
              every: int = 200) -> None:
    """Active progress logging for long serial phases (the R7 stall lesson:
    a silent 70-minute phase is indistinguishable from a hang — narrate).
    Prints to stderr, flushed, at most every `every` items plus the final."""
    if done % every and done != total:
        return
    dt = time.time() - t0
    rate = done / dt if dt > 0 else 0.0
    eta = (total - done) / rate if rate > 0 else float("inf")
    print(f"[telperion] {phase}: {done}/{total} ({dt:.0f}s, "
          f"eta {eta:.0f}s)", file=sys.stderr, flush=True)


def family_hash(family: InequalityFamily, profile: LeanProfile) -> str:
    h = hashlib.sha256()
    t0, total, done = time.time(), family.grid.size(), 0

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
        elif family.kind == "sos":
            # SOS reuses target (the polynomial p); the certificate is a function
            # of p and the monomial half-degree — both determine the output.
            feed("sos_target", canonical_srepr(family.target(pt)))
            feed("sos_half_deg", str(family.sos_half_deg))
        elif family.kind == "bracket":
            # A BracketSpec (frozen dataclass) fully determines the enclosure.
            from dataclasses import asdict

            feed("bracket", json.dumps(asdict(family.bracket(pt)),
                                       default=str, sort_keys=True))
        elif family.kind == "valuation":
            from dataclasses import asdict

            for fact in family.valuation_facts(pt):
                feed("valuation_fact", json.dumps(asdict(fact),
                                                  default=str, sort_keys=True))
        elif family.kind == "witness":
            for label, cand in family.witnesses(pt):
                feed("witness_cand", label + "|" + canonical_srepr(cand))
        elif family.kind == "equation":
            lhs, rhs = family.equation(pt)
            feed("eq_lhs", canonical_srepr(lhs))
            feed("eq_rhs", canonical_srepr(rhs))
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
        done += 1
        heartbeat(f"family_hash {family.name}", done, total, t0)
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

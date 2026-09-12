"""Missions registry schema: one small file per node/manifest/claim.

TOML I/O is a CLOSED LOOP: `dumps_toml` emits a restricted, deterministic
subset (sorted keys; str/int/bool, lists of strings, one level of nested
tables), and `loads_toml` reads via stdlib tomllib when available (Python
3.11+, the CI environment — repo convention, see status.py) with an
in-module fallback parser that accepts exactly what `dumps_toml` emits.
Round-trip is tested; hand-written files are read by tomllib in CI.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Tuple

STATUSES = ("draft", "open", "proved", "refuted", "deprecated")
KINDS = ("goal", "milestone", "lemma", "definition")
ARTIFACT_KINDS = ("lean_module", "frozen_cert")
VIAS = ("direct", "reduction")


class SchemaError(Exception):
    """A mission file violates the schema; message names path/field."""


class ClaimError(Exception):
    """A claim operation failed; message describes why."""


def slug_of(name: str) -> str:
    return name.replace(".", "_")


def dumps_toml(doc: dict) -> str:
    def scalar(v):
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, int):
            return str(v)
        if isinstance(v, str):
            return ('"' + v.replace("\\", "\\\\").replace('"', '\\"')
                    .replace("\n", "\\n").replace("\r", "\\r") + '"')
        raise SchemaError(f"unsupported TOML scalar: {type(v).__name__}")

    lines, tables = [], []
    for k in sorted(doc):
        v = doc[k]
        if isinstance(v, dict):
            tables.append((k, v))
        elif isinstance(v, (list, tuple)):
            lines.append(f"{k} = [" + ", ".join(scalar(x) for x in v) + "]")
        else:
            lines.append(f"{k} = {scalar(v)}")
    for name, tbl in tables:
        lines.append("")
        lines.append(f"[{name}]")
        for k in sorted(tbl):
            v = tbl[k]
            if isinstance(v, (list, tuple)):
                lines.append(f"{k} = [" + ", ".join(scalar(x) for x in v) + "]")
            else:
                lines.append(f"{k} = {scalar(v)}")
    return "\n".join(lines) + "\n"


def loads_toml(text: str) -> dict:
    try:
        import tomllib
        return tomllib.loads(text)
    except ModuleNotFoundError:
        return _mini_parse(text)


def _mini_parse(text: str) -> dict:
    """Parse exactly the subset dumps_toml emits (fallback for Python < 3.11)."""
    import ast
    doc: dict = {}
    target = doc
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            target = doc.setdefault(line[1:-1], {})
            continue
        key, _, val = line.partition(" = ")
        val = val.strip()
        if val in ("true", "false"):
            target[key] = val == "true"
        elif val.startswith("["):
            target[key] = list(ast.literal_eval(val))
        elif val.startswith('"'):
            target[key] = ast.literal_eval(val)
        else:
            target[key] = int(val)
    return doc


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Proof:
    artifact: str
    artifact_kind: str
    via: str
    closure_clean: bool = False

    def __post_init__(self):
        if self.artifact_kind not in ARTIFACT_KINDS:
            raise SchemaError(f"artifact_kind must be one of {ARTIFACT_KINDS!r}, got {self.artifact_kind!r}")
        if self.via not in VIAS:
            raise SchemaError(f"via must be one of {VIAS!r}, got {self.via!r}")


@dataclass(frozen=True)
class Readback:
    text: str
    auditor: str
    date: str


@dataclass(frozen=True)
class Node:
    name: str
    title: str
    kind: str
    status: str
    depends_on: Tuple[str, ...]
    statement_module: str
    source: str = ""
    proof: Optional[Proof] = None
    readback: Optional[Readback] = None
    refutation_statement: str = ""
    deprecated_reason: str = ""
    created: str = ""
    updated: str = ""

    def __post_init__(self):
        if self.status not in STATUSES:
            raise SchemaError(f"status must be one of {STATUSES!r}, got {self.status!r}")
        if self.kind not in KINDS:
            raise SchemaError(f"kind must be one of {KINDS!r}, got {self.kind!r}")
        if self.status == "deprecated" and not self.deprecated_reason:
            raise SchemaError("deprecated_reason must be set when status is 'deprecated'")
        if self.status in ("proved", "refuted") and self.proof is None:
            raise SchemaError("proof must be set when status is 'proved' or 'refuted'")
        # Coerce depends_on to tuple if a list was passed
        if not isinstance(self.depends_on, tuple):
            object.__setattr__(self, "depends_on", tuple(self.depends_on))


@dataclass(frozen=True)
class MissionManifest:
    name: str
    title: str
    description: str
    goal_node: str
    environment_toolchain: str
    environment_mathlib_rev: str
    sources: Tuple[str, ...] = ()

    def __post_init__(self):
        if not isinstance(self.sources, tuple):
            object.__setattr__(self, "sources", tuple(self.sources))


@dataclass(frozen=True)
class Claim:
    node: str
    session: str
    started: str
    ttl_hours: int = 24
    note: str = ""
    superseded: str = ""


# ---------------------------------------------------------------------------
# Serialization helpers
# ---------------------------------------------------------------------------

def _node_to_doc(node: Node) -> dict:
    doc: dict = {}
    # Scalar fields first
    for f in ("name", "title", "kind", "status", "statement_module"):
        doc[f] = getattr(node, f)
    if node.source:
        doc["source"] = node.source
    if node.refutation_statement:
        doc["refutation_statement"] = node.refutation_statement
    if node.deprecated_reason:
        doc["deprecated_reason"] = node.deprecated_reason
    if node.created:
        doc["created"] = node.created
    if node.updated:
        doc["updated"] = node.updated
    # List field
    if node.depends_on:
        doc["depends_on"] = list(node.depends_on)
    else:
        doc["depends_on"] = []
    # Nested tables
    if node.proof is not None:
        doc["proof"] = {
            "artifact": node.proof.artifact,
            "artifact_kind": node.proof.artifact_kind,
            "closure_clean": node.proof.closure_clean,
            "via": node.proof.via,
        }
    if node.readback is not None:
        doc["readback"] = {
            "auditor": node.readback.auditor,
            "date": node.readback.date,
            "text": node.readback.text,
        }
    return doc


def _doc_to_node(doc: dict, path: Path) -> Node:
    try:
        proof = None
        if "proof" in doc:
            p = doc["proof"]
            proof = Proof(
                artifact=p["artifact"],
                artifact_kind=p["artifact_kind"],
                via=p["via"],
                closure_clean=p.get("closure_clean", False),
            )
        readback = None
        if "readback" in doc:
            r = doc["readback"]
            readback = Readback(text=r["text"], auditor=r["auditor"], date=r["date"])
        depends_on = tuple(doc.get("depends_on", []))
        return Node(
            name=doc["name"],
            title=doc["title"],
            kind=doc["kind"],
            status=doc["status"],
            depends_on=depends_on,
            statement_module=doc["statement_module"],
            source=doc.get("source", ""),
            proof=proof,
            readback=readback,
            refutation_statement=doc.get("refutation_statement", ""),
            deprecated_reason=doc.get("deprecated_reason", ""),
            created=doc.get("created", ""),
            updated=doc.get("updated", ""),
        )
    except (KeyError, SchemaError) as exc:
        raise SchemaError(f"{path}: {exc}") from exc


def save_node(node: Node, path: Path) -> None:
    path = Path(path)
    doc = _node_to_doc(node)
    path.write_text(dumps_toml(doc))


def load_node(path: Path) -> Node:
    path = Path(path)
    try:
        text = path.read_text()
    except OSError as exc:
        raise SchemaError(f"{path}: cannot read: {exc}") from exc
    doc = loads_toml(text)
    return _doc_to_node(doc, path)


# ---------------------------------------------------------------------------
# Manifest I/O
# ---------------------------------------------------------------------------

def _manifest_to_doc(m: MissionManifest) -> dict:
    doc: dict = {
        "name": m.name,
        "title": m.title,
        "description": m.description,
        "goal_node": m.goal_node,
        "environment_mathlib_rev": m.environment_mathlib_rev,
        "environment_toolchain": m.environment_toolchain,
        "sources": list(m.sources),
    }
    return doc


def _doc_to_manifest(doc: dict, path: Path) -> MissionManifest:
    try:
        return MissionManifest(
            name=doc["name"],
            title=doc["title"],
            description=doc["description"],
            goal_node=doc["goal_node"],
            environment_toolchain=doc["environment_toolchain"],
            environment_mathlib_rev=doc["environment_mathlib_rev"],
            sources=tuple(doc.get("sources", [])),
        )
    except (KeyError, SchemaError) as exc:
        raise SchemaError(f"{path}: {exc}") from exc


def save_manifest(manifest: MissionManifest, path: Path) -> None:
    path = Path(path)
    path.write_text(dumps_toml(_manifest_to_doc(manifest)))


def load_manifest(path: Path) -> MissionManifest:
    path = Path(path)
    try:
        text = path.read_text()
    except OSError as exc:
        raise SchemaError(f"{path}: cannot read: {exc}") from exc
    return _doc_to_manifest(loads_toml(text), path)


# ---------------------------------------------------------------------------
# Claim I/O
# ---------------------------------------------------------------------------

def _claim_to_doc(c: Claim) -> dict:
    doc: dict = {
        "node": c.node,
        "session": c.session,
        "started": c.started,
        "ttl_hours": c.ttl_hours,
    }
    if c.note:
        doc["note"] = c.note
    if c.superseded:
        doc["superseded"] = c.superseded
    return doc


def _doc_to_claim(doc: dict, path: Path) -> Claim:
    try:
        return Claim(
            node=doc["node"],
            session=doc["session"],
            started=doc["started"],
            ttl_hours=int(doc.get("ttl_hours", 24)),
            note=doc.get("note", ""),
            superseded=doc.get("superseded", ""),
        )
    except (KeyError, SchemaError) as exc:
        raise SchemaError(f"{path}: {exc}") from exc


def save_claim(claim: Claim, path: Path) -> None:
    path = Path(path)
    path.write_text(dumps_toml(_claim_to_doc(claim)))


def load_claim(path: Path) -> Claim:
    path = Path(path)
    try:
        text = path.read_text()
    except OSError as exc:
        raise SchemaError(f"{path}: cannot read: {exc}") from exc
    return _doc_to_claim(loads_toml(text), path)

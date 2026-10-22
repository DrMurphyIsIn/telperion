"""Frozen-tree manifest: what, exactly, was the source state a verdict was produced from?

A kernel verdict, a Comparator verdict and a closure audit (:mod:`telperion.closure_audit`)
each describe the tree they ran on.  They describe the SAME proof only if the tree did not
change between them, and nobody can know that afterwards unless the tree was pinned before
the first run and re-checked after the last.  This module writes that pin as JSON and
re-checks it.

What the manifest records
-------------------------
* every source file matching the include globs (default: every ``.lean`` outside ``.lake/``
  and ``.git/``), with sha256, md5 and size; a symlink is recorded as a symlink (its target
  string) and hashed through to the target's content;
* the Lake files: ``lakefile.lean`` / ``lakefile.toml``, ``lake-manifest.json``,
  ``lean-toolchain``;
* the toolchain: the ``lean-toolchain`` string AND, when the named elan toolchain is
  installed, the sha256 of its ``lean`` and ``lake`` binaries (the file alone pins only a
  name);
* every dependency in ``lake-manifest.json`` (type, url, rev, inputRev) and, for each
  package directory present under the packages dir: git HEAD, whether tracked files are
  modified, the sha256 of ``git diff HEAD`` when they are, every untracked file with its
  hash, optionally every git-ignored file outside ``.lake/``, and -- when a patch file is
  supplied for the package -- the patch's hash, whether ``git apply --check -R`` confirms
  that the tracked tree equals HEAD + patch, and whether each untracked file is one the
  patch creates;
* any tool binaries and extra files (checker binaries, sandbox shims, Comparator JSON
  configs) the caller names, by label, with hash and size;
* a ``digest``: the sha256 of the canonical JSON of everything above except the timestamp,
  so two manifests of the same state compare equal by one string.

What it does NOT guarantee
--------------------------
* It hashes files, not behaviour.  A tool binary with the same hash is the same bytes; what
  those bytes do is a separate question.
* ``.olean`` build products are not hashed (they are rebuilt from the hashed sources by the
  hashed toolchain; a tampered olean that ``lake`` considers up to date is outside this
  manifest -- rebuild from clean if that is the threat).
* A dependency is pinned by its git HEAD, its diff and its untracked files.  Its history,
  its remote and the content of its own dependencies are not re-verified here.
* Git-ignored files inside a package are listed only with ``include_ignored``; the default
  follows ``git ls-files --others --exclude-standard`` and therefore misses them.
* Paths are recorded as given.  Give relative paths (or labels) for anything you will
  commit; the manifest does not scrub them.
* ``verify`` says whether the tree still matches; it does not say what ran in between.  The
  pattern is: freeze, run, verify, and record all three.
"""
from __future__ import annotations

import datetime as _dt
import hashlib
import json
import os
import re
import subprocess
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Mapping

FORMAT = "telperion-freeze-manifest/1"

DEFAULT_INCLUDE_GLOBS: tuple[str, ...] = ("**/*.lean",)
LAKE_FILES: tuple[str, ...] = ("lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")
_EXCLUDED_DIRS = (".lake", ".git")


class ManifestError(Exception):
    pass


@dataclass(frozen=True)
class ManifestOptions:
    """The parameters a manifest was made with.  Recorded inside it so ``verify`` recomputes
    with the same ones."""
    include_globs: tuple[str, ...] = DEFAULT_INCLUDE_GLOBS
    #: Packages directory relative to the project; None = ``packagesDir`` from the lake
    #: manifest, else ``.lake/packages``.
    packages_dir: str | None = None
    #: label -> path of a tool binary (checker, exporter, second kernel, sandbox shim).
    tools: tuple[tuple[str, str], ...] = ()
    #: label -> path of any other file to pin (Comparator JSON configs, scripts).
    extras: tuple[tuple[str, str], ...] = ()
    #: package name -> patch file whose reverse application is checked against the package.
    patches: tuple[tuple[str, str], ...] = ()
    include_ignored: bool = False
    hash_toolchain_binary: bool = True

    def to_dict(self) -> dict:
        d = asdict(self)
        d["include_globs"] = list(self.include_globs)
        d["tools"] = dict(self.tools)
        d["extras"] = dict(self.extras)
        d["patches"] = dict(self.patches)
        return d

    @classmethod
    def from_dict(cls, d: Mapping) -> "ManifestOptions":
        return cls(
            include_globs=tuple(d.get("include_globs", DEFAULT_INCLUDE_GLOBS)),
            packages_dir=d.get("packages_dir"),
            tools=tuple(sorted(dict(d.get("tools", {})).items())),
            extras=tuple(sorted(dict(d.get("extras", {})).items())),
            patches=tuple(sorted(dict(d.get("patches", {})).items())),
            include_ignored=bool(d.get("include_ignored", False)),
            hash_toolchain_binary=bool(d.get("hash_toolchain_binary", True)),
        )


# --------------------------------------------------------------------------------------
# Hashing helpers
# --------------------------------------------------------------------------------------

def _hashes(path: Path) -> dict:
    """sha256, md5 and size of a file's bytes (following symlinks)."""
    h256, hmd5, size = hashlib.sha256(), hashlib.md5(), 0
    with open(path, "rb") as fh:
        while True:
            chunk = fh.read(1 << 20)
            if not chunk:
                break
            h256.update(chunk)
            hmd5.update(chunk)
            size += len(chunk)
    return {"sha256": h256.hexdigest(), "md5": hmd5.hexdigest(), "size": size}


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _file_record(path: Path) -> dict:
    rec: dict = {}
    if path.is_symlink():
        rec["symlink"] = os.readlink(path)
    if path.exists():
        rec.update(_hashes(path))
    else:
        rec["missing"] = True
    return rec


def _excluded(rel: Path) -> bool:
    return any(part in _EXCLUDED_DIRS for part in rel.parts)


def _iter_source_files(project: Path, globs: Iterable[str]) -> list[Path]:
    out: set[Path] = set()
    for g in globs:
        for p in project.glob(g):
            rel = p.relative_to(project)
            if _excluded(rel):
                continue
            if p.is_file() or p.is_symlink():
                out.add(rel)
    return sorted(out)


# --------------------------------------------------------------------------------------
# Git helpers (read-only)
# --------------------------------------------------------------------------------------

def _git(dir_: Path, *args: str, binary: bool = False, timeout: int = 120):
    try:
        r = subprocess.run(["git", "-C", str(dir_), *args], capture_output=True,
                           timeout=timeout, text=not binary)
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    if r.returncode != 0:
        return None
    return r.stdout


def _package_record(pkg_dir: Path, *, include_ignored: bool,
                    patch: tuple[str, Path] | None) -> dict:
    """``patch`` is ``(path as given, resolved path)``; the record keeps the given spelling."""
    rec: dict = {"present": pkg_dir.is_dir()}
    if not pkg_dir.is_dir():
        return rec
    head = _git(pkg_dir, "rev-parse", "HEAD")
    if head is None:
        rec["git"] = False
        return rec
    rec["git"] = True
    rec["head"] = head.strip()
    status = _git(pkg_dir, "status", "--porcelain", "--untracked-files=no")
    dirty = bool(status and status.strip())
    rec["dirty"] = dirty
    if dirty:
        diff = _git(pkg_dir, "diff", "HEAD", binary=True)
        rec["diff_sha256"] = _sha256_bytes(diff or b"")
    created: set[str] = set()
    if patch is not None:
        given, patch = patch
        prec: dict = {"path": given}
        if patch.is_file():
            prec.update(_hashes(patch))
            created = _paths_created_by_patch(patch)
            chk = subprocess.run(["git", "-C", str(pkg_dir), "apply", "--check", "-R", str(patch)],
                                 capture_output=True, text=True)
            prec["reverse_check"] = "ok" if chk.returncode == 0 else "failed"
        else:
            prec["missing"] = True
            prec["reverse_check"] = "no-patch"
        rec["patch"] = prec
    untracked = _git(pkg_dir, "ls-files", "--others", "--exclude-standard", "-z")
    files = []
    for u in sorted(filter(None, (untracked or "").split("\0"))):
        f = pkg_dir / u
        if not f.is_file():
            continue
        row = {"path": u, **_hashes(f)}
        if patch is not None:
            row["created_by_patch"] = u in created
        files.append(row)
    rec["untracked"] = files
    if include_ignored:
        ignored = _git(pkg_dir, "ls-files", "--others", "--ignored", "--exclude-standard", "-z")
        rows = []
        for u in sorted(filter(None, (ignored or "").split("\0"))):
            if u.split("/", 1)[0] in _EXCLUDED_DIRS:
                continue
            f = pkg_dir / u
            if f.is_file():
                rows.append({"path": u, **_hashes(f)})
        rec["ignored"] = rows
    return rec


def _paths_created_by_patch(patch: Path) -> set[str]:
    """Paths a patch ADDS: the ``+++ b/<path>`` headers whose ``---`` side is /dev/null."""
    text = patch.read_text(encoding="utf-8", errors="replace")
    out: set[str] = set()
    prev_dev_null = False
    for line in text.splitlines():
        if line.startswith("--- "):
            prev_dev_null = line.strip() == "--- /dev/null"
        elif line.startswith("+++ b/") and prev_dev_null:
            out.add(line[len("+++ b/"):].strip())
            prev_dev_null = False
    return out


# --------------------------------------------------------------------------------------
# Toolchain
# --------------------------------------------------------------------------------------

def _toolchain_record(project: Path, hash_binary: bool) -> dict:
    tc_file = project / "lean-toolchain"
    rec: dict = {"file": tc_file.read_text(encoding="utf-8").strip() if tc_file.is_file() else None}
    if not hash_binary or not rec["file"]:
        rec["binary"] = None
        rec["lake_binary"] = None
        return rec
    # elan names the toolchain directory by replacing '/' and ':' with '--' and '---'.
    name = rec["file"].replace("/", "--").replace(":", "---")
    home = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    bin_dir = home / "toolchains" / name / "bin"
    lean_bin, lake_bin = bin_dir / "lean", bin_dir / "lake"
    # `lean` elaborates; `lake` resolves the imports and decides what is up to date, so it is
    # part of what produced the verdict and is hashed too (reviewer's nit on the first cut).
    rec["binary"] = {"toolchain_dir": name, **_hashes(lean_bin)} if lean_bin.is_file() else None
    rec["lake_binary"] = _hashes(lake_bin) if lake_bin.is_file() else None
    return rec


# --------------------------------------------------------------------------------------
# Build
# --------------------------------------------------------------------------------------

def _lake_manifest(project: Path) -> dict | None:
    p = project / "lake-manifest.json"
    if not p.is_file():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ManifestError(f"{p}: not JSON ({exc})") from exc


def _project_name(project: Path) -> str:
    toml = project / "lakefile.toml"
    if toml.is_file():
        m = re.search(r'^\s*name\s*=\s*"([^"]+)"', toml.read_text(encoding="utf-8"), re.MULTILINE)
        if m:
            return m.group(1)
    lm = _lake_manifest(project)
    if lm and lm.get("name"):
        return str(lm["name"])
    return project.resolve().name


def _resolve(project: Path, p: str) -> Path:
    q = Path(os.path.expanduser(p))
    return q if q.is_absolute() else (project / q)


def manifest_digest(doc: Mapping) -> str:
    body = {k: v for k, v in doc.items() if k not in ("created", "digest")}
    return _sha256_bytes(json.dumps(body, sort_keys=True, separators=(",", ":"),
                                    ensure_ascii=False).encode("utf-8"))


def freeze_manifest(project_dir: str | Path, options: ManifestOptions | None = None, *,
                    timestamp: bool = True) -> dict:
    """Build the manifest document for a Lake project directory."""
    project = Path(project_dir)
    if not project.is_dir():
        raise ManifestError(f"project directory {project} does not exist")
    opts = options or ManifestOptions()

    files: dict[str, dict] = {}
    for rel in _iter_source_files(project, opts.include_globs):
        files[rel.as_posix()] = _file_record(project / rel)
    lake: dict[str, dict] = {}
    for name in LAKE_FILES:
        p = project / name
        if p.is_file() or p.is_symlink():
            lake[name] = _file_record(p)

    lm = _lake_manifest(project)
    pkgs_dir_rel = opts.packages_dir or (lm or {}).get("packagesDir") or ".lake/packages"
    pkgs_dir = _resolve(project, pkgs_dir_rel)
    patches = {k: (v, _resolve(project, v)) for k, v in opts.patches}
    deps: dict[str, dict] = {}
    for pkg in (lm or {}).get("packages", []):
        name = pkg.get("name", "?")
        rec = {k: pkg.get(k) for k in ("type", "url", "rev", "inputRev", "dir") if k in pkg}
        rec.update(_package_record(pkgs_dir / name, include_ignored=opts.include_ignored,
                                   patch=patches.get(name)))
        deps[name] = rec
    for name, patch in patches.items():
        if name not in deps:
            deps[name] = {"present": (pkgs_dir / name).is_dir(), "unlisted": True,
                          **_package_record(pkgs_dir / name, include_ignored=opts.include_ignored,
                                            patch=patch)}

    tools = {label: {"path": p, "basename": Path(p).name, **_file_record(_resolve(project, p))}
             for label, p in opts.tools}
    extras = {label: {"path": p, **_file_record(_resolve(project, p))}
              for label, p in opts.extras}

    doc: dict = {
        "format": FORMAT,
        "project": _project_name(project),
        "options": opts.to_dict(),
        "toolchain": _toolchain_record(project, opts.hash_toolchain_binary),
        "lake_files": lake,
        "files": files,
        "dependencies": deps,
        "tools": tools,
        "extras": extras,
    }
    if timestamp:
        doc["created"] = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    doc["digest"] = manifest_digest(doc)
    return doc


def dumps_manifest(doc: Mapping) -> str:
    return json.dumps(doc, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def load_manifest(path: str | Path) -> dict:
    p = Path(path)
    try:
        doc = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ManifestError(f"cannot read manifest {p}: {exc}") from exc
    if doc.get("format") != FORMAT:
        raise ManifestError(f"{p}: format {doc.get('format')!r}, expected {FORMAT!r}")
    want = doc.get("digest")
    have = manifest_digest(doc)
    if want != have:
        raise ManifestError(f"{p}: recorded digest {want} does not match its content ({have}); "
                            "the manifest file was edited after it was written")
    return doc


# --------------------------------------------------------------------------------------
# Verify (re-freeze and diff)
# --------------------------------------------------------------------------------------

@dataclass
class ManifestDiff:
    unchanged: bool
    old_digest: str
    new_digest: str
    added: list[str] = field(default_factory=list)
    removed: list[str] = field(default_factory=list)
    changed: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return asdict(self)

    def render(self) -> str:
        if self.unchanged:
            return f"manifest verify: UNCHANGED (digest {self.old_digest[:16]}...)"
        lines = [f"manifest verify: CHANGED ({len(self.added)} added, {len(self.removed)} removed, "
                 f"{len(self.changed)} changed)"]
        lines += [f"  + {k}" for k in self.added]
        lines += [f"  - {k}" for k in self.removed]
        lines += [f"  ~ {k}" for k in self.changed]
        return "\n".join(lines)


def _flatten(doc: Mapping) -> dict[str, str]:
    """Leaf entries keyed ``section/path`` -> a comparable string (sha256 or JSON)."""
    out: dict[str, str] = {}
    for section in ("lake_files", "files", "tools", "extras"):
        for k, v in doc.get(section, {}).items():
            out[f"{section}/{k}"] = json.dumps(v, sort_keys=True)
    out["toolchain"] = json.dumps(doc.get("toolchain"), sort_keys=True)
    for k, v in doc.get("dependencies", {}).items():
        out[f"dependencies/{k}"] = json.dumps(v, sort_keys=True)
    return out


def diff_manifests(old: Mapping, new: Mapping) -> ManifestDiff:
    a, b = _flatten(old), _flatten(new)
    added = sorted(k for k in b if k not in a)
    removed = sorted(k for k in a if k not in b)
    changed = sorted(k for k in a if k in b and a[k] != b[k])
    od, nd = manifest_digest(old), manifest_digest(new)
    return ManifestDiff(unchanged=(od == nd and not added and not removed and not changed),
                        old_digest=od, new_digest=nd, added=added, removed=removed, changed=changed)


def verify_manifest(manifest_path: str | Path, project_dir: str | Path, *,
                    tool_overrides: Mapping[str, str] | None = None) -> tuple[ManifestDiff, dict]:
    """Re-freeze ``project_dir`` with the manifest's own options and diff.  ``tool_overrides``
    re-points tool labels whose binaries moved; the override is reflected in the
    recomputed manifest's ``options`` and therefore in its digest, so a moved tool with the
    same bytes shows as a change in ``options`` only if the recorded path differs."""
    old = load_manifest(manifest_path)
    opts = ManifestOptions.from_dict(old["options"])
    if tool_overrides:
        tools = dict(opts.tools)
        tools.update(tool_overrides)
        opts = ManifestOptions(**{**asdict(opts), "tools": tuple(sorted(tools.items()))})
    new = freeze_manifest(project_dir, opts, timestamp=True)
    # a tool override changes only the recorded path, which is not what verify is about:
    # compare with the OLD options so the digest comparison is about content.
    if tool_overrides:
        new_cmp = dict(new)
        new_cmp["options"] = old["options"]
        for label in tool_overrides:
            if label in new_cmp.get("tools", {}) and label in old.get("tools", {}):
                new_cmp["tools"] = dict(new_cmp["tools"])
                keep = {k: old["tools"][label][k] for k in ("path", "basename") if k in old["tools"][label]}
                new_cmp["tools"][label] = {**new_cmp["tools"][label], **keep}
        new_cmp["digest"] = manifest_digest(new_cmp)
        return diff_manifests(old, new_cmp), new
    return diff_manifests(old, new), new


# --------------------------------------------------------------------------------------
# Text rendering (for a reader; the JSON is the record)
# --------------------------------------------------------------------------------------

def render_text(doc: Mapping) -> str:
    lines = [f"# {FORMAT}  project {doc.get('project')}  created {doc.get('created', '-')}",
             f"# digest {doc.get('digest')}"]
    tc = doc.get("toolchain", {})
    b = tc.get("binary")
    lk = tc.get("lake_binary")
    lines.append(f"# toolchain {tc.get('file')}  lean binary sha256 "
                 f"{b['sha256'] if b else 'not hashed'}  lake binary sha256 "
                 f"{lk['sha256'] if lk else 'not hashed'}")
    for section in ("lake_files", "files"):
        for k, v in doc.get(section, {}).items():
            tag = f"  -> {v['symlink']}" if v.get("symlink") else ""
            lines.append(f"{v.get('sha256', 'MISSING'):<64}  {k}{tag}")
    deps = doc.get("dependencies", {})
    if deps:
        lines.append("# --- dependencies (lake-manifest.json; git state of each package dir) ---")
    for name, d in deps.items():
        state = "absent" if not d.get("present") else ("not git" if not d.get("git") else
                                                       ("dirty" if d.get("dirty") else "clean"))
        lines.append(f"#   {name} rev {d.get('rev')} head {d.get('head', '-')} {state}")
        if d.get("dirty"):
            lines.append(f"#     git-diff-HEAD sha256 {d.get('diff_sha256')}")
        p = d.get("patch")
        if p:
            lines.append(f"#     patch {p.get('path')} sha256 {p.get('sha256', '-')} reverse-check {p.get('reverse_check')}")
        for u in d.get("untracked", []):
            cb = f"  (created by the patch: {'yes' if u['created_by_patch'] else 'no'})" if "created_by_patch" in u else ""
            lines.append(f"#     untracked {u['sha256']}  {u['path']}{cb}")
        for u in d.get("ignored", []):
            lines.append(f"#     ignored   {u['sha256']}  {u['path']}")
    for section, title in (("tools", "tool binaries"), ("extras", "extra files")):
        if doc.get(section):
            lines.append(f"# --- {title} ---")
        for label, v in doc.get(section, {}).items():
            lines.append(f"{v.get('sha256', 'MISSING'):<64}  {label}  ({v.get('path')})")
    return "\n".join(lines) + "\n"


def parse_kv_pairs(items: Iterable[str], what: str) -> tuple[tuple[str, str], ...]:
    """``label=path`` CLI pairs -> sorted tuple; a bare path gets its basename as label."""
    out: dict[str, str] = {}
    for it in items:
        if "=" in it:
            label, path = it.split("=", 1)
        else:
            label, path = Path(it).name, it
        label, path = label.strip(), path.strip()
        if not label or not path:
            raise ManifestError(f"bad {what} entry {it!r}; expected label=path")
        if label in out:
            raise ManifestError(f"duplicate {what} label {label!r}")
        out[label] = path
    return tuple(sorted(out.items()))

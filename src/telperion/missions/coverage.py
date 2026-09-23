"""Build coverage: does CI actually compile the Lean an artifact lives in?

THE HOLE THIS CLOSES (audit 2026-09-18/19). `grant_status` checks that a node's artifact
file *exists* and *contains* the node's statement, and (since the 2026-09-18 hardening) that
it carries no `sorry`. It never asked the one question that makes any of that mean something:
**is this file compiled by anything?**

It is not a hypothetical. Twice in two days:

  * `ZeroFreePolylog.lean` / `ZeroFreeElementary.lean` -- artifacts of two `proved` rh nodes,
    imported by nothing, absent from `defaultTargets`, outside every axiom guard's closure.
    Three independently built worktrees had no `.olean` for either. CI compiled them for the
    first time on 2026-09-18, when they were finally wired in.
  * The whole `zeta_reflection` island -- home of all six `proved` anduril node artifacts,
    granted 2026-09-18, and referenced by **no workflow at all**.

Sorry-free is not verified. Containing the statement is not proving it. Only a kernel run is
evidence, and a kernel run that no job performs is not evidence either.

WHAT IS CHECKED HERE, AND WHAT IS NOT. Two questions, the second strictly stronger:

  1. ISLAND (`ci_built_islands`, the 2026-09-19 floor): does some CI step run `lake build`
     inside the island directory this artifact lives in?
  2. MODULE (`ci_covered_lean_files`, closure audit C2, 2026-09-22): is the artifact's own
     `.lean` file inside the import closure of something a *runnable* CI step actually
     compiles? That is, a `lake build` whose targets (named, or the lakefile's
     `defaultTargets` for a bare `lake build`) resolve -- through the step's lakefile, its
     `lean_lib` roots/globs and its path requires -- to root modules whose transitive local
     `import`s reach the artifact; or a `lean <file>.lean` guard invocation whose imports do.

The island check alone was a text match, and the audit showed what that let through: the
zeta_reflection workflow named five guard targets that did not exist (`unknown target`), ran a
`lake env` that could not spawn `lean` (E2BIG), and had never run once -- yet `coverage.py`
counted the island as built because the string `lake build` appeared under its directory, so
six `proved` nodes rested on a job that could not pass. The module check closes that shape:
an unknown target resolves to no module, so it vouches for nothing.

"Runnable" is static and conservative: the workflow must declare a trigger (`on:`); the job and
step must not be disabled by a literal-false `if:` nor softened by a non-false
`continue-on-error`; and the command must not have its failure masked on the same line (`|| true`
and friends; a `| tee` pipe without `pipefail`). A command whose directory or targets depend on
a shell variable that cannot be resolved statically vouches for nothing. What is still NOT
checked: that the build *succeeds* (that is CI's job, reported on the commit), and anything a
lakefile computes rather than declares (`lakefile.lean` is not parsed; an island that uses one
is reported uncovered rather than guessed at).
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

__all__ = [
    "island_of",
    "ci_built_islands",
    "ci_runnable_steps",
    "ci_covered_lean_files",
    "islands_with_lean",
    "artifact_coverage_error",
    "CoverageParseError",
]

#: `telperion/examples/<island>/...`
_ISLAND_RE = re.compile(r"(?:^|/)examples/([A-Za-z0-9_]+)(?:/|$)")

#: a `cd` into an island inside a `run:` block
_CD_RE = re.compile(r"cd\s+\S*?examples/([A-Za-z0-9_]+)/lean")

#: the command that constitutes actual verification
_BUILD_RE = re.compile(r"\blake\s+build\b")


def island_of(path: Path | str) -> Optional[str]:
    """The example-island name an artifact path lives in, or None if it is not in one."""
    m = _ISLAND_RE.search(str(path).replace("\\", "/"))
    return m.group(1) if m else None


def _workflow_paths(repo_root: Path) -> List[Path]:
    return sorted((repo_root / ".github" / "workflows").glob("*.y*ml"))


def _workflow_docs(repo_root: Path) -> Optional[List[dict]]:
    """Parsed workflow documents, or None when PyYAML is unavailable.

    Returning None (not []) is deliberate. An earlier revision swallowed the ImportError
    and returned an empty list, which made `ci_built_islands` answer "nothing is built" in
    any environment without PyYAML -- and the required `unit` job is exactly such an
    environment. Every proved node then failed the coverage check at once. A checker that
    degrades to a confident wrong answer is worse than one that admits it cannot parse.
    """
    try:
        import yaml
    except ImportError:
        return None
    docs: List[dict] = []
    for p in _workflow_paths(repo_root):
        try:
            doc = yaml.safe_load(p.read_text())
        except Exception:
            continue
        if isinstance(doc, dict):
            docs.append(doc)
    return docs


def _scan_islands_without_yaml(repo_root: Path) -> Set[str]:
    """Line-oriented fallback used when PyYAML is absent.

    Steps in these workflows are written with `working-directory:` before the `run:` it
    applies to, and job-level `defaults.run.working-directory` likewise precedes its steps,
    so carrying the most recent directory forward and attributing each `lake build` to it
    reproduces the YAML result on this repo. It is an approximation, and it is checked
    against the YAML path by a test.
    """
    built: Set[str] = set()
    for p in _workflow_paths(repo_root):
        current: Optional[str] = None
        for line in p.read_text().splitlines():
            m = re.search(r"working-directory:\s*(\S+)", line)
            if m:
                current = island_of(m.group(1))
                continue
            if _BUILD_RE.search(line):
                if current:
                    built.add(current)
            built.update(_CD_RE.findall(line))
    return built


class CoverageParseError(RuntimeError):
    """The workflow parser produced an answer that cannot be right."""


def _assert_parser_sane(repo_root: Path, built: Set[str], steps_seen: int) -> None:
    """Refuse to report "nothing is built" when the parser never actually read anything.

    This guards the failure this module itself shipped once: with PyYAML absent the parser
    returned an empty set, every proved node failed coverage at once, and the output looked
    like a registry catastrophe rather than a missing dependency. One loud error beats N
    confident false ones.

    The distinguishing signal is `steps_seen`, not emptiness. A repo whose build steps are
    all disabled is an empty answer that is CORRECT, and an earlier version of this guard
    wrongly raised on exactly that. Only a parse that walked no steps at all, while the
    workflow text plainly contains `lake build`, indicates a broken parser.
    """
    if built or steps_seen:
        return
    for p in _workflow_paths(repo_root):
        if _BUILD_RE.search(p.read_text()):
            raise CoverageParseError(
                f"workflow parsing walked no steps, yet {p.name} contains `lake build` "
                "-- the coverage parser is broken, not the registry. Refusing to report "
                "every proved node as uncovered."
            )


def _never_runs(node: dict) -> bool:
    """True when a job or step is disabled by a literal-false `if:`.

    A `lake build` that GitHub will never execute is not evidence that anything is built,
    and counting it would let a disabled step vouch for an island.
    """
    cond = node.get("if")
    if cond is None:
        return False
    return str(cond).strip().lower() in {"false", "${{ false }}", "${{false}}"}


def ci_built_islands(repo_root: Path) -> Set[str]:
    """Islands in which some workflow step runs `lake build`.

    A step's effective directory is its own `working-directory`, else the job's
    `defaults.run.working-directory`. A `cd .../examples/<x>/lean` inside the step's `run`
    counts too -- three jobs in this repo address their island that way rather than through
    `working-directory`, and missing them would produce false orphans.
    """
    docs = _workflow_docs(repo_root)
    if docs is None:
        built = _scan_islands_without_yaml(repo_root)
        # The fallback is line-oriented and does not model steps, so it reports 1 "step"
        # whenever it read any workflow text at all.
        _assert_parser_sane(repo_root, built, 1 if _workflow_paths(repo_root) else 0)
        return built
    built: Set[str] = set()
    steps_seen = 0
    for doc in docs:
        jobs = doc.get("jobs") or {}
        if not isinstance(jobs, dict):
            continue
        for job in jobs.values():
            if not isinstance(job, dict):
                continue
            if _never_runs(job):
                continue
            job_dir = (((job.get("defaults") or {}).get("run") or {}).get("working-directory"))
            for step in (job.get("steps") or []):
                if not isinstance(step, dict):
                    continue
                steps_seen += 1
                if _never_runs(step):
                    continue
                run = str(step.get("run") or "")
                if not _BUILD_RE.search(run):
                    continue
                where = step.get("working-directory") or job_dir
                if where:
                    name = island_of(str(where))
                    if name:
                        built.add(name)
                built.update(_CD_RE.findall(run))
    _assert_parser_sane(repo_root, built, steps_seen)
    return built


def islands_with_lean(repo_root: Path) -> Set[str]:
    """Every example island that has at least one `.lean` source of its own."""
    out: Set[str] = set()
    examples = repo_root / "telperion" / "examples"
    if not examples.is_dir():
        return out
    for d in examples.iterdir():
        lean = d / "lean"
        if lean.is_dir() and any(lean.rglob("*.lean")):
            out.add(d.name)
    return out


# ---------------------------------------------------------------------------------------------
# MODULE-LEVEL COVERAGE (closure audit C2, 2026-09-22)
# ---------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class CIStep:
    """One `run:` step that GitHub can execute and whose failure fails its job."""

    workflow: str
    job: str
    workdir: Optional[str]  # as written (repo-relative); None = repo root
    run: str
    pipefail: bool  # `shell: bash` runs with `-eo pipefail`; the default shell does not


# -- a dependency-free parser for the YAML subset GitHub workflows here are written in ---------

def _strip_yaml_comment(v: str) -> str:
    out, q = [], None
    for i, ch in enumerate(v):
        if q:
            if ch == q:
                q = None
        elif ch in "'\"":
            q = ch
        elif ch == "#" and (i == 0 or v[i - 1] in " \t"):
            break
        out.append(ch)
    return "".join(out).rstrip()


def _yaml_scalar(v: str) -> Any:
    v = _strip_yaml_comment(v).strip()
    if len(v) >= 2 and v[0] == v[-1] and v[0] in "'\"":
        return v[1:-1]
    if v in ("true", "True"):
        return True
    if v in ("false", "False"):
        return False
    return v


_KEY_RE = re.compile(r"""^(?:"([^"]*)"|'([^']*)'|([^\s#'"][^:#]*?))\s*:(?:\s+(.*))?$""")


class _MiniYaml:
    """Block mappings, block sequences, plain/quoted scalars and `|`/`>` block scalars.

    Flow collections (`[a, b]`) are kept as their literal string. That is all the structure
    the coverage walker reads (`on`, `jobs`, `defaults`, `steps`, `if`, `continue-on-error`,
    `working-directory`, `shell`, `run`), and a test pins this parser to PyYAML on the real
    workflows, so the required `unit` job gets the same answer with or without PyYAML.
    """

    def __init__(self, text: str) -> None:
        self.lines = text.splitlines()
        self.i = 0

    @staticmethod
    def _indent(line: str) -> int:
        return len(line) - len(line.lstrip(" "))

    def _skip(self) -> None:
        while self.i < len(self.lines):
            s = self.lines[self.i].strip()
            if s and not s.startswith("#") and s != "---":
                return
            self.i += 1

    def parse(self) -> Any:
        self._skip()
        if self.i >= len(self.lines):
            return None
        return self._node(self._indent(self.lines[self.i]))

    def _node(self, ind: int) -> Any:
        self._skip()
        if self.i >= len(self.lines):
            return None
        line = self.lines[self.i]
        if self._indent(line) < ind:
            return None
        if line.strip().startswith("- ") or line.strip() == "-":
            return self._seq(self._indent(line))
        return self._map(self._indent(line))

    def _block_scalar(self, ind: int, style: str) -> str:
        body: List[str] = []
        while self.i < len(self.lines):
            ln = self.lines[self.i]
            if ln.strip() and self._indent(ln) <= ind:
                break
            body.append(ln)
            self.i += 1
        while body and not body[-1].strip():
            body.pop()
        nonblank = [b for b in body if b.strip()]
        cut = min((self._indent(b) for b in nonblank), default=0)
        body = [b[cut:] for b in body]
        if style.startswith(">"):
            return " ".join(b.strip() for b in body if b.strip())
        return "\n".join(body) + ("" if style.startswith("|-") else "\n")

    def _value(self, rest: Optional[str], ind: int) -> Any:
        if rest is None or not _strip_yaml_comment(rest).strip():
            self._skip()
            if self.i < len(self.lines):
                nxt = self.lines[self.i]
                ni = self._indent(nxt)
                if ni > ind or (ni == ind and nxt.strip().startswith("-")):
                    return self._node(ni)
            return None
        r = _strip_yaml_comment(rest).strip()
        if r[:1] in ("|", ">"):
            return self._block_scalar(ind, r)
        return _yaml_scalar(r)

    def _map(self, ind: int) -> Dict[Any, Any]:
        out: Dict[Any, Any] = {}
        while True:
            self._skip()
            if self.i >= len(self.lines):
                return out
            line = self.lines[self.i]
            li = self._indent(line)
            if li != ind or line.strip().startswith("- "):
                return out
            m = _KEY_RE.match(line.strip())
            if not m:
                self.i += 1
                continue
            key = next(g for g in m.groups()[:3] if g is not None).strip()
            self.i += 1
            out[key] = self._value(m.group(4), ind)

    def _seq(self, ind: int) -> List[Any]:
        out: List[Any] = []
        while True:
            self._skip()
            if self.i >= len(self.lines):
                return out
            line = self.lines[self.i]
            if self._indent(line) != ind or not (line.strip().startswith("- ") or line.strip() == "-"):
                return out
            content = line.strip()[1:].lstrip()
            item_ind = ind + (len(line.strip()) - len(content))
            if not content:
                self.i += 1
                out.append(self._node(ind + 1))
                continue
            if _KEY_RE.match(content) and not content.startswith(("'", '"')) or (
                content[:1] in "'\"" and _KEY_RE.match(content)
            ):
                # `- key: v` opens a mapping whose keys sit at the column after "- "
                self.lines[self.i] = " " * item_ind + content
                out.append(self._map(item_ind))
            else:
                self.i += 1
                out.append(_yaml_scalar(content))


def _mini_yaml_load(text: str) -> Any:
    return _MiniYaml(text).parse()


def _all_workflow_docs(repo_root: Path, use_yaml: bool = True) -> List[Tuple[str, dict]]:
    docs: List[Tuple[str, dict]] = []
    loader = None
    if use_yaml:
        try:
            import yaml

            loader = yaml.safe_load
        except ImportError:
            loader = None
    for p in _workflow_paths(repo_root):
        try:
            doc = (loader or _mini_yaml_load)(p.read_text())
        except Exception:
            continue
        if isinstance(doc, dict):
            docs.append((p.name, doc))
    return docs


def _has_trigger(doc: dict) -> bool:
    # YAML 1.1 (PyYAML) reads the bare key `on` as the boolean True.
    return any(doc.get(k) for k in ("on", True, "true"))


def _may_swallow_failure(node: dict) -> bool:
    """`continue-on-error` anything but literal false: a red build would not fail the job."""
    v = node.get("continue-on-error")
    if v is None or v is False:
        return False
    return str(v).strip().lower() not in {"false", "${{ false }}", "${{false}}"}


def ci_runnable_steps(repo_root: Path, *, use_yaml: bool = True) -> List[CIStep]:
    """Every `run:` step that GitHub will execute and whose failure fails its job."""
    out: List[CIStep] = []
    for name, doc in _all_workflow_docs(repo_root, use_yaml):
        if not _has_trigger(doc):
            continue
        jobs = doc.get("jobs") or {}
        if not isinstance(jobs, dict):
            continue
        for jname, job in jobs.items():
            if not isinstance(job, dict) or _never_runs(job) or _may_swallow_failure(job):
                continue
            jrun = ((job.get("defaults") or {}).get("run") or {})
            job_dir = jrun.get("working-directory")
            job_shell = jrun.get("shell")
            for step in (job.get("steps") or []):
                if not isinstance(step, dict) or "run" not in step:
                    continue
                if _never_runs(step) or _may_swallow_failure(step):
                    continue
                shell = str(step.get("shell") or job_shell or "")
                run = str(step.get("run") or "")
                out.append(CIStep(
                    workflow=name, job=str(jname),
                    workdir=(str(step.get("working-directory") or job_dir or "") or None),
                    run=run,
                    pipefail=(shell.strip() == "bash") or ("pipefail" in run),
                ))
    return out


# -- Lake workspaces ----------------------------------------------------------------------------

def _load_toml(path: Path) -> Optional[dict]:
    try:
        import tomllib as _toml  # type: ignore[import-not-found]
    except ImportError:  # Python < 3.11
        try:
            import tomli as _toml  # type: ignore[import-not-found,no-redef]
        except ImportError:
            _toml = None
    text = path.read_text()
    if _toml is not None:
        try:
            return _toml.loads(text)
        except Exception:
            return None
    return _mini_toml(text)


def _mini_toml(text: str) -> dict:
    """The lakefile.toml subset read here: top-level keys + [[lean_lib]]/[[lean_exe]]/[[require]]."""
    doc: Dict[str, Any] = {}
    cur: Dict[str, Any] = doc
    buf = ""
    for raw in text.splitlines():
        line = _strip_yaml_comment(raw).strip()
        if buf:
            buf += " " + line
            if buf.count("[") > buf.count("]"):
                continue
            line, buf = buf, ""
        if not line:
            continue
        m = re.match(r"^\[\[\s*([\w.]+)\s*\]\]$", line)
        if m:
            cur = {}
            doc.setdefault(m.group(1), []).append(cur)
            continue
        if re.match(r"^\[[^\[]", line):
            cur = {}  # a plain [table]: not read here
            continue
        m = re.match(r"^([\w-]+)\s*=\s*(.*)$", line)
        if not m:
            continue
        key, val = m.group(1), m.group(2).strip()
        if val.startswith("[") and val.count("[") > val.count("]"):
            buf = line
            continue
        if val.startswith("["):
            cur[key] = re.findall(r'"([^"]*)"', val)
        elif val[:1] == '"':
            cur[key] = val[1:].split('"', 1)[0]
        else:
            cur[key] = val
    return doc


@dataclass
class _Package:
    name: str
    dir: Path
    src_dirs: List[Path]
    libs: Dict[str, Tuple[List[str], List[str], Path]]  # name -> (roots, globs, srcdir)
    exes: Dict[str, str]  # name -> root module
    default_targets: List[str]
    requires: List[Path]


@lru_cache(maxsize=None)
def _package(pkg_dir: Path) -> Optional[_Package]:
    toml = pkg_dir / "lakefile.toml"
    if not toml.is_file():
        return None  # no lakefile, or a lakefile.lean (not parsed: reported, not guessed)
    doc = _load_toml(toml)
    if not isinstance(doc, dict):
        return None
    base = pkg_dir / str(doc.get("srcDir") or ".")
    libs: Dict[str, Tuple[List[str], List[str], Path]] = {}
    src_dirs: List[Path] = [base]
    for lib in doc.get("lean_lib") or []:
        if not isinstance(lib, dict) or "name" not in lib:
            continue
        sd = base / str(lib.get("srcDir") or ".")
        if sd not in src_dirs:
            src_dirs.append(sd)
        libs[str(lib["name"])] = (
            [str(r) for r in (lib.get("roots") or [lib["name"]])],
            [str(g) for g in (lib.get("globs") or [])],
            sd,
        )
    exes = {
        str(e["name"]): str(e.get("root") or e["name"])
        for e in (doc.get("lean_exe") or []) if isinstance(e, dict) and "name" in e
    }
    reqs = [
        (pkg_dir / str(r["path"])) for r in (doc.get("require") or [])
        if isinstance(r, dict) and r.get("path")
    ]
    return _Package(
        name=str(doc.get("name") or pkg_dir.name), dir=pkg_dir, src_dirs=src_dirs, libs=libs,
        exes=exes, default_targets=[str(t) for t in (doc.get("defaultTargets") or [])],
        requires=reqs,
    )


@lru_cache(maxsize=None)
def _workspace(root_dir: Path) -> Tuple[_Package, ...]:
    """The root package plus every package reachable through `path` requires."""
    seen: Dict[Path, _Package] = {}
    stack = [root_dir]
    while stack:
        d = stack.pop()
        try:
            d = d.resolve()
        except OSError:
            continue
        if d in seen:
            continue
        pkg = _package(d)
        if pkg is None:
            continue
        seen[d] = pkg
        stack.extend(pkg.requires)
    ordered = [seen[root_dir.resolve()]] if root_dir.resolve() in seen else []
    ordered += [p for k, p in seen.items() if k != root_dir.resolve()]
    return tuple(ordered)


def _module_file(ws: Tuple[_Package, ...], mod: str) -> Optional[Path]:
    rel = Path(*mod.replace("«", "").replace("»", "").split(".")).with_suffix(".lean")
    for pkg in ws:
        for sd in pkg.src_dirs:
            f = sd / rel
            if f.is_file():
                return f.resolve()
    return None


_HEADER_IMPORT_RE = re.compile(
    r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$"
)


@lru_cache(maxsize=None)
def _imports(path: Path) -> Tuple[str, ...]:
    """Module names imported by the header of a Lean file (comments stripped)."""
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return ()
    # strip (possibly nested) block comments, then line comments
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    mods: List[str] = []
    for line in "".join(out).splitlines():
        line = line.split("--", 1)[0].strip()
        if not line or line in ("module", "prelude"):
            continue
        m = _HEADER_IMPORT_RE.match(line)
        if not m:
            break  # the header ends at the first non-import command
        mods.extend(m.group(1).split())
    return tuple(mods)


def _closure(ws: Tuple[_Package, ...], files: Iterable[Path]) -> Set[Path]:
    seen: Set[Path] = set()
    stack = [f.resolve() for f in files]
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        for mod in _imports(f):
            g = _module_file(ws, mod)
            if g is not None and g not in seen:
                stack.append(g)
    return seen


def _glob_files(srcdir: Path, glob: str) -> List[Path]:
    if glob.endswith(".+") or glob.endswith(".*"):
        stem = glob[:-2]
        base = srcdir / Path(*stem.split("."))
        found = sorted(base.rglob("*.lean")) if base.is_dir() else []
        if glob.endswith(".+"):
            own = base.with_suffix(".lean")
            if own.is_file():
                found.insert(0, own)
        return found
    f = srcdir / Path(*glob.split(".")).with_suffix(".lean")
    return [f] if f.is_file() else []


def _lib_files(root: Tuple[List[str], List[str], Path]) -> List[Path]:
    roots, globs, sd = root
    files: List[Path] = []
    for r in roots:
        f = sd / Path(*r.split(".")).with_suffix(".lean")
        if f.is_file():
            files.append(f)
    for g in globs:
        files.extend(_glob_files(sd, g))
    return files


def _lib_module_file(ws: Tuple[_Package, ...], mod: str) -> Optional[Path]:
    """The file of `mod` if it is a LOCAL module of some lib (a root, a submodule of a root, or
    a glob match) -- the only modules Lake accepts as a bare `lake build` target. A `.lean` file
    sitting in the package directory is NOT enough: `lake build AxiomGuardA4` against a lakefile
    that does not declare it fails with `unknown target` (closure audit C2)."""
    for pkg in ws:
        for roots, globs, sd in pkg.libs.values():
            ok = any(mod == r or mod.startswith(r + ".") for r in roots)
            for g in globs:
                if g.endswith(".+"):
                    ok = ok or mod == g[:-2] or mod.startswith(g[:-2] + ".")
                elif g.endswith(".*"):
                    ok = ok or mod.startswith(g[:-2] + ".")
                else:
                    ok = ok or mod == g
            if ok:
                f = sd / Path(*mod.split(".")).with_suffix(".lean")
                if f.is_file():
                    return f.resolve()
    return None


def _target_files(
    ws: Tuple[_Package, ...], target: str, allow_pkg: bool = True
) -> Optional[List[Path]]:
    """Root files one `lake build` target argument compiles; None when Lake would reject it."""
    t = target.lstrip("@")
    t = t.split(":", 1)[0]
    if not t:
        return None
    if t.startswith("+"):
        f = _lib_module_file(ws, t[1:])
        return [f] if f else None
    pkgs = list(ws)
    if "/" in t:
        pname, t = t.split("/", 1)
        pkgs = [p for p in ws if p.name == pname]
        if not pkgs:
            return None
        if not t:
            return _defaults(ws, pkgs)
    for p in pkgs:
        if t in p.libs:
            return _lib_files(p.libs[t])
        if t in p.exes:
            f = _module_file(ws, p.exes[t])
            return [f] if f else None
    if allow_pkg:
        for p in pkgs:
            if t == p.name:
                return _defaults(ws, [p])
    f = _lib_module_file(ws, t)
    return [f] if f else None


def _defaults(ws: Tuple[_Package, ...], pkgs: List[_Package]) -> Optional[List[Path]]:
    out: List[Path] = []
    for p in pkgs:
        for d in p.default_targets:
            got = _target_files(ws, d, allow_pkg=False)
            if got is None:
                return None
            out.extend(got)
    return out


# -- reading the shell of a `run:` step -----------------------------------------------------------

_FOR_RE = re.compile(r"\bfor\s+(\w+)\s+in\s+(.*?)\s*(?:;|\n)\s*do\b")
_VAR_RE = re.compile(r"\$\{?(\w+)\}?")
_LAKE_BUILD_RE = re.compile(r"\blake\s+(?:(?:-d|--dir)[\s=]+(\S+)\s+)?build\b(.*)$")
_LEAN_CMD_RE = re.compile(
    r"""(?:^|[\s;&|(])(?:lake\s+(?:env\s+)?lean|["']?\$\{?LEAN\w*\}?["']?|(?:\S*/)?lean)\s+(.*)$"""
)


def _unquote(tok: str) -> str:
    return tok.strip().strip("'\"")


def _masked(rest: str, line_tail: str, pipefail: bool) -> bool:
    """Is a failure of the command at the head of `rest` hidden from the step's exit status?

    `rest` is the command's own segment; `line_tail` is the rest of the logical line from the
    command on, so a handler split off into `{ ...; exit 1; }` is still seen.
    """
    if "||" in rest:
        after = line_tail.split("||", 1)[1]
        if "exit" not in after:
            return True
    if re.search(r"(?<!\|)\|(?!\|)", rest.split("||", 1)[0]) and not pipefail:
        return True
    return False


def _expand(tok: str, env: Dict[str, List[str]]) -> Optional[List[str]]:
    """Expand loop variables in one token; None when some `$var` is not statically known."""
    names = _VAR_RE.findall(tok)
    if not names:
        return [tok]
    outs = [tok]
    for n in names:
        if n not in env:
            return None
        outs = [re.sub(r"\$\{?" + n + r"\}?", v, o) for o in outs for v in env[n]]
    return outs


def _split_segments(line: str) -> List[str]:
    """Split a logical shell line at `;`, `&&`, `(`, `)` and `{`/`}` -- NOT at `||`/`|`,
    which stay attached so `_masked` can see them."""
    segs, cur, q = [], [], None
    i = 0
    while i < len(line):
        ch = line[i]
        if q:
            cur.append(ch)
            if ch == q:
                q = None
        elif ch in "'\"":
            q = ch
            cur.append(ch)
        elif (
            ch == ";" or line[i:i + 2] == "&&"
            or (ch in "()" and not (ch == "(" and i and line[i - 1] == "$"))
            or (ch == "{" and line[i + 1:i + 2] in ("", " ", "\t"))
            or (ch == "}" and (i == 0 or line[i - 1] in " \t;"))
        ):
            segs.append("".join(cur))
            cur = []
            if line[i:i + 2] == "&&":
                i += 1
        else:
            cur.append(ch)
        i += 1
    segs.append("".join(cur))
    return [s.strip() for s in segs if s.strip()]


@dataclass(frozen=True)
class _Evidence:
    project: Path  # directory the command runs in (the Lake workspace root)
    kind: str  # "build" | "lean"
    args: Tuple[str, ...]
    where: str


def _step_evidence(repo_root: Path, step: CIStep) -> List[_Evidence]:
    base = (repo_root / step.workdir) if step.workdir else repo_root
    text = re.sub(r"\\\n\s*", " ", step.run)  # join backslash continuations
    env: Dict[str, List[str]] = {}
    cwd: Optional[Path] = base
    out: List[_Evidence] = []
    where = f"{step.workflow}:{step.job}"
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        for m in _FOR_RE.finditer(stripped):
            words = [_unquote(w) for w in m.group(2).split()]
            if all("$" not in w and "*" not in w for w in words):
                env[m.group(1)] = words
            else:
                env.pop(m.group(1), None)
        line_cwd = cwd
        subshell = stripped.startswith("(")
        pos = 0
        for seg in _split_segments(stripped):
            at = stripped.find(seg, pos)
            pos = at + len(seg) if at >= 0 else pos
            line_tail = stripped[at:] if at >= 0 else seg
            words = seg.split()
            if not words:
                continue
            if words[0] == "cd":
                tgt = _unquote(words[1]) if len(words) > 1 else ""
                if not tgt or "$" in tgt or line_cwd is None:
                    line_cwd = None
                else:
                    line_cwd = (line_cwd / tgt)
                continue
            if words[0] in ("echo", "printf", "grep", "test", "[") or line_cwd is None:
                continue
            mb = _LAKE_BUILD_RE.search(seg)
            if mb:
                rest = mb.group(2)
                if _masked(rest, line_tail, step.pipefail):
                    continue
                proj = line_cwd / _unquote(mb.group(1)) if mb.group(1) else line_cwd
                head = re.split(r"\|\|?|\d*>|&>", rest, 1)[0]
                toks = [_unquote(t) for t in head.split() if not t.startswith("-")]
                expanded: List[str] = []
                ok = True
                for t in toks:
                    e = _expand(t, env)
                    if e is None:
                        ok = False
                        break
                    expanded.extend(e)
                if ok:
                    out.append(_Evidence(proj, "build", tuple(expanded), where))
                continue
            ml = _LEAN_CMD_RE.search(" " + seg)
            if ml and not seg.startswith(("lake build", "lake exe", "lake update")):
                rest = ml.group(1)
                if _masked(rest, line_tail, step.pipefail):
                    continue
                head = re.split(r"\|\|?|\d*>|&>", rest, 1)[0]
                files: List[str] = []
                for t in head.split():
                    t = _unquote(t)
                    if not t.endswith(".lean"):
                        continue
                    e = _expand(t, env)
                    if e is not None:
                        files.extend(e)
                if files:
                    out.append(_Evidence(line_cwd, "lean", tuple(files), where))
        if not subshell:
            cwd = line_cwd
        if stripped.startswith("done"):
            env.clear()
    return out


def _evidence_files(ev: _Evidence) -> Tuple[Set[Path], bool]:
    """(files this command compiles, whether the command is certain to FAIL).

    A `lake build` naming a target that the (parsed) lakefile does not declare fails before
    building anything -- Lake resolves every target first -- so it vouches for nothing, and
    every later step of its job never runs. That is exactly the old zeta_reflection job.
    """
    proj = ev.project.resolve()
    ws = _workspace(proj)
    if ev.kind == "build":
        if not ws:
            return set(), False  # no parseable lakefile.toml here: vouches for nothing
        roots = _defaults(ws, [ws[0]]) if not ev.args else []
        if roots is None:
            return set(), True
        for t in ev.args:
            got = _target_files(ws, t)
            if got is None:
                return set(), True
            roots.extend(got)
        return _closure(ws, roots), False
    # `lean F.lean`: F elaborates against oleans of its imports, which therefore exist
    files = [(proj / f) for f in ev.args if (proj / f).is_file()]
    if len(files) != len(ev.args):
        return set(), bool(ws)  # `lean` on a missing file errors
    if not ws:
        ws = (_Package(name="", dir=proj, src_dirs=[proj], libs={}, exes={},
                       default_targets=[], requires=[]),)
    return _closure(ws, files), False


def ci_covered_lean_files(repo_root: Path, *, use_yaml: bool = True) -> Dict[Path, Set[str]]:
    """Resolved `.lean` files some runnable CI step compiles, mapped to the jobs that do.

    A file is covered when it is in the transitive local-import closure of (a) the root modules
    of a `lake build` step's targets -- named targets, or `defaultTargets` for a bare
    `lake build` -- resolved through the lakefile.toml of the directory the command runs in and
    its `path` requires, or (b) a `.lean` file handed to `lean` / `lake env lean`.
    """
    repo_root = Path(repo_root)
    covered: Dict[Path, Set[str]] = {}
    doomed: Set[Tuple[str, str]] = set()
    for step in ci_runnable_steps(repo_root, use_yaml=use_yaml):
        job = (step.workflow, step.job)
        if job in doomed:
            continue  # an earlier step of this job cannot pass, so this one never runs
        for ev in _step_evidence(repo_root, step):
            files, fails = _evidence_files(ev)
            if fails:
                doomed.add(job)
                break
            for f in files:
                covered.setdefault(f, set()).add(ev.where)
    return covered


def artifact_coverage_error(
    artifact_path: Path,
    repo_root: Path,
    built: Optional[Set[str]] = None,
    covered: Optional[Dict[Path, Set[str]]] = None,
) -> Optional[str]:
    """Return an error string if no runnable CI step compiles this artifact, else None.

    Two gates, in order: the island must be built at all (`ci_built_islands`), and the
    artifact's own file must be inside the import closure of something a runnable step
    compiles (`ci_covered_lean_files`). The second is what the closure audit (C2) found
    missing: an island can have a `lake build` step that never builds the artifact, or that
    cannot run at all.

    An artifact outside `telperion/examples/**` is not judged here: campaign-local Lean is
    covered by the campaign's own build, and a non-Lean artifact has nothing to compile.
    """
    if artifact_path.suffix != ".lean":
        return None
    # Attribute the island from the RESOLVED path. `island_of` on the raw string is
    # caller-controlled: `../../examples/wired/lean/../../unbuilt/lean/U.lean` reads as the
    # built island `wired` while the file actually lives in the unbuilt one. Resolving first
    # is what makes the check about the file rather than about how it was spelled.
    resolved = Path(artifact_path).resolve()
    name = island_of(resolved)
    if name is None:
        return None
    if built is None:
        built = ci_built_islands(repo_root)
    if name not in built:
        return (
            f"artifact lives in example island {name!r}, which no CI workflow builds "
            f"(no step runs `lake build` in telperion/examples/{name}/lean). A node may not be "
            f"`proved` against Lean that nothing compiles -- wire the island into "
            f".github/workflows/ or move the artifact to one that is wired."
        )
    if covered is None:
        covered = ci_covered_lean_files(repo_root)
    if resolved in covered:
        return None
    return (
        f"artifact module {resolved.stem!r} (island {name!r}) is compiled by no runnable CI "
        f"step: island {name!r} has a `lake build` step, but no runnable step's `lake build` "
        f"targets (named, or defaultTargets for a bare `lake build`) nor any `lean <guard>.lean` "
        f"invocation has this file in its import closure. Add the module to the island's "
        f"defaultTargets or to a guard lib that a workflow builds (closure audit C2)."
    )

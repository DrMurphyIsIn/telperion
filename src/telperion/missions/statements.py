"""Statement file management: render, write, provenance, package scaffold.

Files are written under <root>/lean/Statements/<Slug>.lean.
Every file carries a provenance header that encodes a sha256 of the
normalized post-header body + node slug + manifest env.  regen_diff
detects hand edits by re-deriving that hash from the on-disk post-header
content and comparing it to the value stored in the header.

Root import (added 2026-09-24).  A statement module is only ELABORATED by CI if the
package root `<root>/lean/Statements.lean` imports it: the `mission-statements-compile`
job runs `lake build` on the default target, and lake builds exactly the root's import
closure.  Fifteen registered modules (eleven rh, four mirrormere, several of them
`status = "proved"`) had been written by `write_statement` and never added to the
root, so the design invariant "a statement that does not elaborate cannot enter the
graph" was not enforced for them; one (`MM_weil_positivity_window_tenth`) had no
`import` line at all.  `write_statement` therefore now also appends the module to
the root (`ensure_root_import`), and `verify_campaign` fails on any module the root
does not import (`missing_root_imports`) or any statement without an import header
(`import_header_error`).
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
from typing import List, Sequence, Tuple

from .schema import atomic_write_text, MissionManifest, Node, slug_of

# The sentinel that all generated files carry
_SENTINEL = "DO NOT EDIT BY HAND"


# ---------------------------------------------------------------------------
# Path helper
# ---------------------------------------------------------------------------

def statement_path(root: Path, node: Node) -> Path:
    """Return <root>/lean/Statements/<Slug>.lean."""
    return Path(root) / "lean" / "Statements" / f"{slug_of(node.name)}.lean"


# ---------------------------------------------------------------------------
# Body normalisation (applied before hashing and writing)
# ---------------------------------------------------------------------------

_DECL_KEYWORD = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example)\b"
)


def _last_declaration_has_proof(body: str) -> bool:
    """Does the final declaration in `body` already carry a proof or definition body?

    True iff a `:=` appears at bracket depth zero within that declaration, ignoring
    comments and string literals.  Depth matters: `(h : a := b)` is a binder default,
    not a proof body, and `⟨x, y⟩` must not unbalance the scan.
    """
    starts = [m.start() for m in _DECL_KEYWORD.finditer(body)]
    tail = body[starts[-1]:] if starts else body

    depth = 0
    i = 0
    n = len(tail)
    while i < n:
        two = tail[i:i + 2]
        if two == "--":
            j = tail.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if two == "/-":
            j = tail.find("-/", i + 2)
            i = n if j < 0 else j + 2
            continue
        ch = tail[i]
        if ch == '"':
            i += 1
            while i < n and tail[i] != '"':
                i += 2 if tail[i] == "\\" else 1
            i += 1
            continue
        if ch in "([{\u27e8":
            depth += 1
        elif ch in ")]}\u27e9":
            depth -= 1
        elif two == ":=" and depth == 0:
            return True
        i += 1
    return False


def _build_body(statement: str) -> str:
    """Split statement into (preamble_lines, declaration_body) and normalize.

    import/open lines are preserved; the final declaration is appended
    ':= by sorry' if it has no proof body.
    Returns the full post-header content (without the header line).
    """
    lines = statement.split("\n")
    preamble_lines: List[str] = []
    body_lines: List[str] = []
    in_preamble = True
    for line in lines:
        stripped = line.strip()
        if in_preamble and (stripped.startswith("import ") or stripped.startswith("open ")):
            preamble_lines.append(line)
        else:
            in_preamble = False
            body_lines.append(line)

    body = "\n".join(body_lines)
    body_stripped = body.rstrip()

    # Normalize: append ':= by sorry' only if the FINAL declaration has no proof body.
    #
    # This used to test `endswith(":= by sorry") or endswith(":= sorry")`, which
    # recognises only the two one-line spellings.  A statement whose declaration already
    # carried a multi-line proof got a SECOND one appended, producing the nonsense
    # `sorry := by sorry`.  That happened live while authoring
    # MM_leakage_composite_zero.
    #
    # The test is deliberately scoped to the LAST declaration.  A statement module may
    # open with local `def`s, each with its own `:=`, before the theorem it exists to
    # state; asking merely whether the body contains a top-level `:=` would see those
    # and skip the suffix the theorem needs.
    if not _last_declaration_has_proof(body_stripped):
        body = body_stripped + " := by sorry"
    else:
        body = body_stripped

    if preamble_lines:
        return "\n".join(preamble_lines) + "\n" + body
    return body


# ---------------------------------------------------------------------------
# Hash — computed over (slug + normalized_body + toolchain + mathlib_rev)
# ---------------------------------------------------------------------------

def _body_hash(slug: str, body: str, manifest: MissionManifest) -> str:
    """16-char sha256 hex of (slug + normalized_body + toolchain + mathlib_rev).

    The hash basis is the NORMALIZED post-header body — the same bytes
    regen_diff re-derives from disk.  A raw-input basis would be unverifiable
    since the raw statement text is not stored in the written file.
    """
    material = "\n".join([
        slug,
        body,
        manifest.environment_toolchain,
        manifest.environment_mathlib_rev,
    ])
    return hashlib.sha256(material.encode()).hexdigest()[:16]


# ---------------------------------------------------------------------------
# Render
# ---------------------------------------------------------------------------

def render_statement(node: Node, statement: str, manifest: MissionManifest) -> str:
    """Return the full file content for this node's statement file.

    Structure (one header line, then the normalized body):
        -- DO NOT EDIT BY HAND — generated by telperion mission; node <slug>; sha256 <hash>
        <import/open lines>
        <theorem/def declaration, ending with ':= by sorry' if no body was given>

    The sha256 in the header covers the normalized post-header body (not the raw
    statement input), so regen_diff can re-derive it from the file alone.
    """
    slug = slug_of(node.name)
    body = _build_body(statement)
    h = _body_hash(slug, body, manifest)
    header = (
        f"-- {_SENTINEL} — generated by telperion mission; "
        f"node {slug}; sha256 {h}"
    )
    return header + "\n" + body + "\n"


# ---------------------------------------------------------------------------
# Write
# ---------------------------------------------------------------------------

def write_statement(
    root: Path,
    node: Node,
    statement: str,
    manifest: MissionManifest,
) -> Path:
    """Render and write the statement file; create parent dirs as needed.

    Also appends the module to the package root (`ensure_root_import`) so that CI's
    `lake build` of the root actually elaborates it.  Writing the file without the
    import is exactly the hole that left fifteen registered statements unbuilt.
    """
    path = statement_path(root, node)
    path.parent.mkdir(parents=True, exist_ok=True)
    atomic_write_text(path, render_statement(node, statement, manifest))
    ensure_root_import(root, module_of_statement_file(path))
    return path


def statement_body(root: Path, node: Node) -> str:
    """The on-disk statement text minus the provenance header (imports/opens included).

    This is what `write_statement` needs to re-render the file: the post-header content
    is exactly the `statement` argument after normalization, so feeding it back is
    idempotent for a well-formed file.
    """
    text = statement_path(root, node).read_text()
    lines = text.split("\n")
    if lines and _SENTINEL in lines[0]:
        lines = lines[1:]
    return "\n".join(lines).strip("\n")


def regenerate_statement(
    root: Path,
    node: Node,
    manifest: MissionManifest,
    prepend_imports: Sequence[str] = (),
) -> Tuple[Path, str, str]:
    """Re-render a statement file through the normal tooling from its own body.

    Returns (path, old_hash, new_hash).  The body is `statement_body`, optionally with
    `import <m>` lines for `prepend_imports` placed first (for a file written without
    the standard header).  Also appends the module to the package root via
    `write_statement`.  The hash changes iff the body changes, i.e. iff the old file
    was malformed; a caller that sees old != new records the change in the node file.
    """
    path = statement_path(root, node)
    old_text = path.read_text()
    old_hash = old_text.split("\n")[0].split("sha256 ")[-1].strip()[:16] if _SENTINEL in old_text.split("\n")[0] else ""
    body = statement_body(root, node)
    if prepend_imports:
        body = "\n".join(f"import {m}" for m in prepend_imports) + "\n" + body
    write_statement(root, node, body, manifest)
    new_hash = path.read_text().split("\n")[0].split("sha256 ")[-1].strip()[:16]
    return path, old_hash, new_hash


# ---------------------------------------------------------------------------
# Root module (<root>/lean/Statements.lean) — the import list CI actually builds
# ---------------------------------------------------------------------------

def root_module_path(root: Path) -> Path:
    """Return <root>/lean/Statements.lean, the package root lake builds."""
    return Path(root) / "lean" / "Statements.lean"


_IMPORT_LINE = re.compile(r"(?m)^\s*import\s+(\S+)")


def root_imports(root: Path) -> List[str]:
    """Module names the package root imports, in file order ([] if the root is absent)."""
    path = root_module_path(root)
    if not path.exists():
        return []
    return _IMPORT_LINE.findall(path.read_text())


def ensure_root_import(root: Path, module: str) -> bool:
    """Append `import <module>` to the package root unless already present.

    Creates the root file if it does not exist.  Returns True iff a line was added.
    Appending (not sorting) keeps the diff to the one new line, which is what every
    hand-maintained root in the tree looks like today.
    """
    path = root_module_path(root)
    present = root_imports(root)
    if module in present:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    text = path.read_text() if path.exists() else ""
    if text and not text.endswith("\n"):
        text += "\n"
    atomic_write_text(path, text + f"import {module}\n")
    return True


def module_of_statement_file(path: Path) -> str:
    """`Statements/<Slug>.lean` -> `Statements.<Slug>`."""
    return f"Statements.{Path(path).stem}"


def missing_root_imports(root: Path, nodes) -> List[str]:
    """Every module CI would silently skip: statement files on disk, and every node's
    `statement_module` whose file exists, that the root does not import.

    Both directions of the mismatch are reported: a module the root names but whose
    file is missing breaks `lake build` outright, so it is included too, prefixed
    `(no file)`.  Sorted, deduplicated.
    """
    root = Path(root)
    imported = set(root_imports(root))
    stmts_dir = root / "lean" / "Statements"
    missing: set = set()
    if stmts_dir.is_dir():
        for lean_file in stmts_dir.glob("*.lean"):
            mod = module_of_statement_file(lean_file)
            if mod not in imported:
                missing.add(mod)
    for node in nodes:
        if statement_path(root, node).exists() and node.statement_module not in imported:
            missing.add(node.statement_module)
    for mod in imported:
        if mod.startswith("Statements.") and not (stmts_dir / (mod.split(".", 1)[1] + ".lean")).exists():
            missing.add(f"(no file) {mod}")
    return sorted(missing)


def defs_modules(root: Path) -> List[str]:
    """The campaign's shared-vocabulary modules: `Statements/*Defs.lean` (e.g. RHDefs)."""
    stmts_dir = Path(root) / "lean" / "Statements"
    if not stmts_dir.is_dir():
        return []
    return sorted(module_of_statement_file(p) for p in stmts_dir.glob("*Defs.lean"))


def import_header_error(root: Path, node: Node) -> str:
    """"" iff the node's statement file carries the campaign's standard import header.

    The standard header is at least one `import` line, and among them either `Mathlib`
    or one of the campaign's `*Defs` modules (which import Mathlib themselves).  Every
    statement in the four live campaigns satisfies this except the one that motivated
    the check, which had no imports at all and so could only have elaborated by
    accident of some other module's environment -- it never did, because nothing
    imported it either.  Missing file -> "" (regen_diff reports that).
    """
    path = statement_path(root, node)
    if not path.exists():
        return ""
    imports = _IMPORT_LINE.findall(path.read_text())
    slug = slug_of(node.name)
    if not imports:
        return f"node {slug}: statement file has no `import` line"
    ok = {"Mathlib", *defs_modules(root)}
    if not any(m == "Mathlib" or m.startswith("Mathlib.") or m in ok for m in imports):
        return (
            f"node {slug}: statement imports {imports!r} but neither Mathlib nor a "
            f"campaign Defs module ({', '.join(defs_modules(root)) or 'none present'})"
        )
    return ""


# ---------------------------------------------------------------------------
# regen_diff
# ---------------------------------------------------------------------------

def regen_diff(root: Path, node: Node, manifest: MissionManifest) -> str:
    """Return "" iff the on-disk file's header hash matches its body; else a description.

    Re-derives the hash from the on-disk post-header content and compares to
    the hash embedded in the header line.  A hand edit changes the body, so
    the fresh hash will differ from the stored one.
    """
    path = statement_path(root, node)
    slug = slug_of(node.name)

    if not path.exists():
        return f"node {slug}: statement file missing"

    text = path.read_text()
    lines = text.split("\n")

    if not lines or _SENTINEL not in lines[0]:
        return f"node {slug}: header missing"

    header_line = lines[0]
    # Parse "sha256 <16hex>" from the header
    try:
        sha_part = header_line.split("sha256 ")[1].strip()
        stored_hash = sha_part[:16]
    except IndexError:
        return f"node {slug}: header malformed (no sha256)"

    # Post-header content: everything after the first line, stripped of the
    # trailing newline added by render (so body matches what _build_body returns).
    post_header = "\n".join(lines[1:])
    # Remove the leading "\n" separator between header and body
    post_header = post_header.lstrip("\n")
    # Remove trailing newline added at end of render
    post_header = post_header.rstrip("\n")

    fresh_hash = _body_hash(slug, post_header, manifest)

    if fresh_hash != stored_hash:
        return (
            f"node {slug}: hash mismatch "
            f"(header has {stored_hash!r}, current body hashes to {fresh_hash!r})"
        )

    # Staleness of the package ROOT, not just the file (2026-09-24).  A statement file
    # whose module the root does not import is as unverified as one with a stale hash:
    # CI builds the root's import closure and nothing else, so the file has never been
    # elaborated.  Reported here so every regen_diff caller sees it, not only verify.
    module = module_of_statement_file(path)
    if module not in root_imports(root):
        return (
            f"node {slug}: statement file exists but the package root "
            f"lean/Statements.lean does not import {module} (CI never elaborates it)"
        )
    return ""


# ---------------------------------------------------------------------------
# scaffold_package
# ---------------------------------------------------------------------------

def scaffold_package(root: Path, manifest: MissionManifest) -> List[Path]:
    """Write lean/ package files; return list of written paths.

    Files written:
      lean/lean-toolchain    — manifest.environment_toolchain (verbatim)
      lean/lakefile.toml     — mathlib rev = manifest.environment_mathlib_rev,
                               lib name = Statements
      lean/Statements.lean   — imports Statements.<Slug> for every present
                               statement file, sorted

    Existing statement files under lean/Statements/ are scanned to build
    the root import list; only files already written count.
    """
    root = Path(root)
    lean_dir = root / "lean"
    lean_dir.mkdir(parents=True, exist_ok=True)

    written: List[Path] = []

    # lean/lean-toolchain
    toolchain_path = lean_dir / "lean-toolchain"
    atomic_write_text(toolchain_path, manifest.environment_toolchain + "\n")
    written.append(toolchain_path)

    # lean/lakefile.toml
    lakefile_path = lean_dir / "lakefile.toml"
    lakefile_content = (
        'name = "Statements"\n'
        'defaultTargets = ["Statements"]\n'
        "\n"
        "[[require]]\n"
        'name = "mathlib"\n'
        'scope = "leanprover-community"\n'
        f'rev = "{manifest.environment_mathlib_rev}"\n'
        "\n"
        "[[lean_lib]]\n"
        'name = "Statements"\n'
    )
    atomic_write_text(lakefile_path, lakefile_content)
    written.append(lakefile_path)

    # Collect present statement modules (sorted)
    stmts_dir = lean_dir / "Statements"
    module_names: List[str] = []
    if stmts_dir.is_dir():
        for lean_file in sorted(stmts_dir.glob("*.lean")):
            module_names.append(f"Statements.{lean_file.stem}")
    module_names.sort()

    # lean/Statements.lean — root module
    root_module_path = lean_dir / "Statements.lean"
    root_module_lines = [f"import {m}" for m in module_names]
    atomic_write_text(root_module_path, "\n".join(root_module_lines) + "\n")
    written.append(root_module_path)

    return written

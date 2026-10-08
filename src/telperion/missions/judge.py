"""Independent judge for the missions registry: Comparator challenges from registered statements.

WHAT THIS IS. For every PROVED node whose Lean artifact lives on an example island, emit an
openai/ten-proofs Comparator (github.com/leanprover/comparator) challenge whose statement is
the node's REGISTERED statement and whose proof is the artifact's theorem:

    -- MissionChallenges/<Slug>.lean, generated from the registry
    import <artifact module>            -- the solution
    import <island AxiomGuard modules>  -- the whole island (see "shadowing" below)
    <the statement file's `open` lines>
    theorem MissionJudge.<Slug> : forall <binders>, <conclusion> := <artifact theorem>

`<binders>` and `<conclusion>` are the registered statement's own text (the file under
`missions/<campaign>/lean/Statements/`, header hash intact), split at its top-level colon;
nothing else is written by hand. The Comparator config then asserts `MissionJudge.<Slug>`
with permitted axioms [propext, Quot.sound, Classical.choice] and nanoda on.

WHAT THE JUDGE THEN ESTABLISHES, on a machine and in a program the author did not write:
  1. statement identity -- the bridge theorem's TYPE is the registered statement, and its
     proof term is the artifact constant; the Lean kernel and nanoda accept that term only if
     the artifact's type is definitionally the registered statement. A weaker theorem
     (`P ∨ True`), a different constant, or a wrong vocabulary does not type-check;
  2. axiom whitelist -- checked on the export, so `sorryAx`, `ofReduceBool` (native_decide)
     and a smuggled `axiom` anywhere in the proof's closure are refused;
  3. two kernels -- the export is replayed through Lean's kernel AND nanoda (Rust).
What it does NOT do: read the title. Whether the formal statement says what its title claims
is still the read-back's job. And it resolves the statement's names in the ARTIFACT'S
environment, not the campaign's vocabulary mirror (`Statements.RHDefs` etc.), because the
Comparator needs one Lake workspace; mirror fidelity is missions/mirrors.py's check.

WHY A BRIDGE THEOREM AND NOT COMPARATOR'S OWN "same name, same type" MODE. That mode needs
the challenge to declare the theorem under the artifact's name WITHOUT importing the
artifact, so the challenge can only import the artifact's imports. On dbn that works (the
vocabulary lives in DBNDefs); on rvm_bridge 28 of 52 statements use definitions declared in
the artifact module itself (`RvMBridge14.effectiveThreshold` in E6Bridge14), so the literal
challenge does not elaborate. The bridge form elaborates everywhere and is checked by the
same two kernels; the identity it certifies is definitional rather than syntactic, which is
the right notion for "proves the registered proposition".

SHADOWING. An artifact that avoided importing the island's vocabulary module and declared its
own `DBN.H` would make the registered statement resolve to the impostor. The challenge
therefore also imports the island's AxiomGuard modules (which import every island module):
a constant declared twice on the island is a duplicate-declaration error, so the challenge
fails to build and the judge fails.
On an island with no AxiomGuard lean_lib (bg: the R3Cert package, whose AxiomGuard.lean is a
loose file and whose full library includes R47PC6Cells, ~70 min / 18 GB that no node needs)
the challenge instead imports the island modules its campaign's vocabulary mirror cites as
the source of each copied block (`-- ===== ExactCruxes.lean:70 =====` in BGDefs.lean). That
catches an artifact re-declaring a mirrored vocabulary constant; it does NOT catch a
shadowed constant that is not in the mirror (the whole-island import would).
On li_positivity the two AxiomGuard libs cannot co-import (`ZeroFreeBridge.zeta_sphere_bound`
is declared in both closures), so each challenge imports only the first guard whose import
closure holds its artifact (`GUARD_POLICY_ONE_CONTAINING`), and the root module imports
nothing: CI builds the bridge modules by name. quasicrystal has no AxiomGuard lean_lib and no
vocabulary mirror hook, so its challenges import the artifact alone and the shadowing guard
does not apply there (its `AxiomGuardQC.lean` is a loose file the island CI runs).

OUT-OF-TREE ISLANDS (`OUT_OF_TREE_ISLANDS`): bg lives at proof/formalization, not
telperion/examples/<island>/lean. Its proved nodes are the registry nodes whose [proof]
artifact lies under that directory; everything else is the same.

MATERIALIZED-ROOT ISLANDS (`MATERIALIZED_ROOT_ISLANDS`): oai_qrh_bridge is a RECIPE, not a
Lake package. Its materialize.sh checks out openai/math's lean/ at the pin in OAI_PIN (Lean
v4.34.1, Mathlib d13f23b), copies the island's `lean/*.lean` files (and the single-pin dbn port)
into that workspace's root, and appends the island's lakefile stanza. OpenAI's lakefile patches
its dependencies from hooks that refuse a non-root workspace, so the bundle cannot path-require
the island. Instead the bundle has NO lakefile of its own: it carries `lakefile-stanza.lean`
(one `lean_lib MissionChallenges`), and telperion/scripts/judge_materialize.sh copies the bridge
modules and configs into the materialized workspace and appends that stanza. Everything else is
the same: the bridge imports the artifact and the island's AxiomGuard modules (every top-level
`lean/AxiomGuard*.lean`, each required to be a lean_lib root in the island stanza; on
oai_qrh_bridge AxiomGuardDBNUnconditional and AxiomGuardQRHBridge, which co-import). The
shadowing guard covers the island modules in the guards' closure, NOT the rest of OpenAI's root
package (about 2,900 modules the guards do not import). There is no v4.34.1 Comparator tag; the
bundle names v4.34.0, built with its lean-toolchain set to v4.34.1 (MANIFEST.json records both),
exactly as .github/workflows/oai-qrh-bridge.yml does. Before the island's first grant its
committed bundle is EMPTY (no proved node; MANIFEST.json lists none) rather than an error.

PENDING (`--pending`, default OFF, never used in CI): also renders draft and open nodes, each
bridge module saying so and MANIFEST.json listing them under `pending_not_proved`. It must be
written with `--out` to a scratch directory (refused otherwise, and `--check` is refused); it is
local pre-grant evidence only. `mission comparator-record` refuses a node that is not proved, so
the order is always audit, grant, missions-comparator CI run, comparator-record.

NOT CONSUMABLE (reported, never skipped silently): a statement that declares anything besides
its final theorem (local `def`s would collide with the artifact's copies; 2 of 97 nodes,
both on islands outside the CI matrix), an island whose toolchain has no Comparator tag, or
an island whose package cannot be path-required (zeta_zero_localization's monolith lakefile).

Output layout (`--out`, default `telperion/missions/judge/<island>/`):
  lean-toolchain                       copy of the island's
  lakefile.toml                        path-requires the island; one lib `MissionChallenges`
  MissionChallenges.lean               root import of every challenge
  MissionChallenges/<Slug>.lean        the challenge (bridge) module
  <Slug>.comparator.json               the Comparator config
  MANIFEST.json                        node -> (campaign, theorem, solution module, digests)
A materialized-root island has `lakefile-stanza.lean` in place of `lakefile.toml`, and its
MANIFEST.json adds `comparator_toolchain` and `materialized_root` (recipe, pin, install command).

conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
import tomllib
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from ..comparator import CLEAN_AXIOMS, challenge_config

_SENTINEL = "DO NOT EDIT BY HAND"

#: Comparator tags exist for these island toolchains (git ls-remote --tags, 2026-09-23).
#: The Comparator must be built with the SAME toolchain as the modules it exports, so the tag
#: is per island, not the v4.32.0 the BG bridge pins.
COMPARATOR_TAG_FOR_TOOLCHAIN = {
    "leanprover/lean4:v4.32.0": "v4.32.0",
    "leanprover/lean4:v4.33.0-rc2": "v4.33.0-rc2",
    "leanprover/lean4:v4.34.0-rc1": "v4.34.0-rc1",
    "leanprover/lean4:v4.34.0": "v4.34.0",
}


class JudgeError(Exception):
    """The island or a node cannot be turned into a Comparator challenge; message says why."""


# ---------------------------------------------------------------------------
# guard_anchors (the registry -> theorem-name derivation lives in scripts/, stdlib-only)
# ---------------------------------------------------------------------------

def _guard_anchors():
    if "guard_anchors" in sys.modules:
        return sys.modules["guard_anchors"]
    path = Path(__file__).resolve().parents[3] / "scripts" / "guard_anchors.py"
    spec = importlib.util.spec_from_file_location("guard_anchors", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["guard_anchors"] = mod
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------
# Island facts
# ---------------------------------------------------------------------------

_NAME_RE = re.compile(r'(?m)^name\s*=\s*"([^"]+)"')
_IMPORT_RE = re.compile(r"(?m)^import\s+(\S+)[ \t]*$")
_OPEN_RE = re.compile(r"(?m)^open\b.*$")


@dataclass(frozen=True)
class OutOfTreeIsland:
    """An island that is not `telperion/examples/<island>/lean`."""
    #: Lake package directory, relative to telperion/.
    lean_dir: str
    #: Vocabulary mirror (relative to telperion/) whose `-- ===== <Module>.lean... =====` block
    #: headers name the island modules the vocabulary is copied from. Used for the shadowing
    #: guard when the island has no `AxiomGuard*` lean_lib (see `island_guard_modules`).
    vocab_mirror: str


#: The BG island is the R3Cert package under proof/formalization (toolchain v4.32.0). It has no
#: AxiomGuard lean_lib (its AxiomGuard.lean is a loose file CI runs with `lake env lean`), and
#: importing every R3Cert module would drag in R47PC6Cells (~70 min, 18 GB) that no BG node
#: needs, so its challenges import the vocabulary's home modules instead.
OUT_OF_TREE_ISLANDS = {
    "bg": OutOfTreeIsland(lean_dir="../proof/formalization",
                          vocab_mirror="missions/bg/lean/Statements/BGDefs.lean"),
}


@dataclass(frozen=True)
class MaterializedRootIsland:
    """An island that is a RECIPE, not a Lake package: a script materializes a foreign
    workspace whose lakefile must stay the workspace root, and copies the island's `lean/*.lean`
    files into that workspace's root directory (see the module docstring)."""
    #: Recipe directory, relative to telperion/ (holds the pin file, the materialize script and
    #: `lean/`, whose top-level `.lean` files the script copies to the workspace root).
    recipe: str
    #: `key=value` pin file in the recipe directory (must carry `toolchain=`).
    pin_file: str
    #: The island's own lean_lib stanza appended to the workspace lakefile by the recipe. Every
    #: AxiomGuard module the judge imports must be a root there, or the bridge cannot build.
    island_stanza: str
    #: The root package's name (the workspace lakefile's `package <name>`), for MANIFEST.json.
    package: str
    #: Workspace lakefile name, to which the bundle's `lakefile-stanza.lean` is appended.
    lakefile: str
    #: Comparator tag to build. There may be no tag for the workspace toolchain itself; the
    #: tag is then built with its `lean-toolchain` overwritten by the workspace toolchain
    #: (recorded in MANIFEST.json as `comparator_toolchain`).
    comparator_tag: str


#: oai_qrh_bridge: openai/math @ adc7f124 (lean/, Lean v4.34.1, Mathlib d13f23b), whose lakefile
#: patches 23 dependencies from hooks that refuse a non-root workspace, so the island cannot be
#: path-required. There is no v4.34.1 Comparator tag; v4.34.0 is built with toolchain v4.34.1,
#: exactly as .github/workflows/oai-qrh-bridge.yml does.
MATERIALIZED_ROOT_ISLANDS = {
    "oai_qrh_bridge": MaterializedRootIsland(
        recipe="examples/oai_qrh_bridge", pin_file="OAI_PIN",
        island_stanza="lean/lakefile-stanza.lean", package="OAI", lakefile="lakefile.lean",
        comparator_tag="v4.34.0"),
}

#: Statuses the judge renders. The committed bundle judges PROVED nodes only; `--pending`
#: (written to a temp `--out`, never committed) also renders draft and open nodes so a
#: registered-but-ungranted node can be judged before its grant (see `build_bundle`).
PROVED_STATUSES = ("proved",)
PENDING_STATUSES = ("proved", "open", "draft")


def read_pin(path: Path) -> "OrderedDict[str, str]":
    """`key=value` lines of a pin file (comments and blank lines ignored)."""
    out: "OrderedDict[str, str]" = OrderedDict()
    for ln in Path(path).read_text().splitlines():
        ln = ln.strip()
        if not ln or ln.startswith("#") or "=" not in ln:
            continue
        k, v = ln.split("=", 1)
        out[k.strip()] = v.strip()
    return out


def materialized_facts(telperion_root: Path, island: str) -> "OrderedDict[str, object]":
    """What MANIFEST.json records about a materialized-root island's workspace."""
    spec = MATERIALIZED_ROOT_ISLANDS[island]
    recipe = Path(telperion_root) / spec.recipe
    pin = read_pin(recipe / spec.pin_file)
    if "toolchain" not in pin:
        raise JudgeError(f"{recipe / spec.pin_file}: no `toolchain=` line")
    return OrderedDict(
        recipe=spec.recipe, pin_file=spec.pin_file, pin=pin,
        workspace_lakefile=spec.lakefile, island_stanza=spec.island_stanza,
        comparator_toolchain=pin["toolchain"],
        install=f"telperion/scripts/judge_materialize.sh telperion/missions/judge/{island} "
                f"<materialized workspace>")


def island_dir(telperion_root: Path, island: str) -> Path:
    if island in MATERIALIZED_ROOT_ISLANDS:
        spec = MATERIALIZED_ROOT_ISLANDS[island]
        recipe = Path(telperion_root) / spec.recipe
        d = recipe / "lean"
        for need in (recipe / spec.pin_file, recipe / spec.island_stanza):
            if not need.is_file():
                raise JudgeError(f"materialized island {island!r}: missing {need}")
        return d
    if island in OUT_OF_TREE_ISLANDS:
        d = (Path(telperion_root) / OUT_OF_TREE_ISLANDS[island].lean_dir).resolve()
    else:
        d = Path(telperion_root) / "examples" / island / "lean"
    if not (d / "lakefile.toml").is_file():
        raise JudgeError(f"island {island!r}: no lakefile.toml under {d}")
    return d


def island_package_name(lean_dir: Path) -> str:
    m = _NAME_RE.search((lean_dir / "lakefile.toml").read_text())
    if not m:
        raise JudgeError(f"{lean_dir / 'lakefile.toml'}: no top-level `name = ...`")
    return m.group(1)


def island_toolchain(lean_dir: Path) -> str:
    tc = (lean_dir / "lean-toolchain")
    if not tc.is_file():
        raise JudgeError(f"{lean_dir}: no lean-toolchain")
    return tc.read_text().strip()


def comparator_tag(toolchain: str) -> str:
    try:
        return COMPARATOR_TAG_FOR_TOOLCHAIN[toolchain]
    except KeyError:
        raise JudgeError(
            f"no known Comparator tag for toolchain {toolchain!r}; add it to "
            "COMPARATOR_TAG_FOR_TOOLCHAIN once github.com/leanprover/comparator has one")


def module_name_of(lean_dir: Path, artifact: Path) -> str:
    """`<island>/lean/Probes/Foo.lean` -> `Probes.Foo` (no srcDir remapping: every wired island
    keeps its libs at the package root)."""
    rel = Path(artifact).resolve().relative_to(Path(lean_dir).resolve())
    if rel.suffix != ".lean":
        raise JudgeError(f"artifact {artifact} is not a .lean file")
    return ".".join(rel.with_suffix("").parts)


_LIB_RE = re.compile(r'(?ms)^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"')


def island_guard_modules(lean_dir: Path) -> List[str]:
    """The island's `AxiomGuard*` lean_libs, which by convention import every island module.
    Importing them into a challenge makes a shadowed vocabulary constant a build error."""
    text = (lean_dir / "lakefile.toml").read_text()
    # PREFIX MATCH ON PURPOSE (2026-09-26): only `AxiomGuard*` libs are imported. The ladder's
    # per-segment guards (Arb4_AxiomGuard_h*, RS5_AxiomGuard, H11K_AxiomGuard) do NOT match, so
    # ordinary challenges stay light; only a challenge whose OWN artifact is a ladder capstone
    # (e.g. Arb4_h8000, whose import closure is every segment's edge certificates) needs the
    # ladder built -- those nodes carry `judge_via = "heavy"` and are judged by
    # missions-comparator-heavy.yml, not here.
    return sorted(m.group(1) for m in _LIB_RE.finditer(text) if m.group(1).startswith("AxiomGuard"))


_STANZA_ROOT_RE = re.compile(r"`([A-Za-z_][\w.]*)")


def materialized_guard_modules(telperion_root: Path, island: str) -> List[str]:
    """The AxiomGuard modules of a materialized-root island: its top-level `lean/AxiomGuard*.lean`
    files (copied to the workspace root by the recipe), each of which must be a lean_lib root in
    the island's lakefile stanza. Same convention as `island_guard_modules`: the guards import
    every island module, so importing them makes a shadowed constant a duplicate declaration."""
    spec = MATERIALIZED_ROOT_ISLANDS[island]
    recipe = Path(telperion_root) / spec.recipe
    mods = sorted(p.stem for p in (recipe / "lean").glob("AxiomGuard*.lean") if p.is_file())
    if not mods:
        raise JudgeError(f"materialized island {island!r}: no lean/AxiomGuard*.lean; the "
                         "shadowing guard needs at least one")
    roots = set(_STANZA_ROOT_RE.findall(
        _guard_anchors().strip_lean_comments((recipe / spec.island_stanza).read_text())))
    missing = [m for m in mods if m not in roots]
    if missing:
        raise JudgeError(f"materialized island {island!r}: guard module(s) {missing} are not "
                         f"lean_lib roots in {spec.island_stanza}, so the bridge could not build "
                         "them")
    return mods


#: Islands whose AxiomGuard libs cannot all be imported into one module. li_positivity:
#: `ZeroFreeBridge.zeta_sphere_bound` is declared in both DlvpZetaDisk (in
#: AxiomGuardLiPositivity's closure) and ZeroFreeElementary (in AxiomGuardZeroFree's), so a
#: bridge that imports both fails with "environment already contains". For these islands the
#: bridge imports only the FIRST guard (sorted) whose import closure contains the artifact,
#: so the shadowing check covers that guard's closure rather than the whole island. Every
#: other island imports all of its guards (they co-import; zeta_reflection has ten).
GUARD_POLICY_ONE_CONTAINING = frozenset({"li_positivity"})


def artifact_imports(text: str) -> List[str]:
    """The `import` lines of a Lean source (comments stripped)."""
    ga = _guard_anchors()
    return [m.group(1) for m in _IMPORT_RE.finditer(ga.strip_lean_comments(text))]


def import_closure(lean_dir: Path, module: str, _seen: Optional[set] = None) -> set:
    """Island-local import closure of `module` (modules whose source is under `lean_dir`;
    external packages are not followed). Includes `module` itself."""
    seen = _seen if _seen is not None else set()
    if module in seen:
        return seen
    seen.add(module)
    src = Path(lean_dir) / (module.replace(".", "/") + ".lean")
    if src.is_file():
        for dep in artifact_imports(src.read_text()):
            import_closure(lean_dir, dep, seen)
    return seen


def guards_for(lean_dir: Path, island: str, guards: Sequence[str], solution_module: str) -> List[str]:
    """Which guard libs a bridge for `solution_module` imports (see GUARD_POLICY_ONE_CONTAINING)."""
    if island not in GUARD_POLICY_ONE_CONTAINING:
        return list(guards)
    for g in guards:
        if solution_module in import_closure(lean_dir, g):
            return [g]
    return []


_MIRROR_HEADER_RE = re.compile(r"(?m)^--\s*=====(.*)$")
_MIRROR_FILE_RE = re.compile(r"([\w/]+)\.lean\b")


def vocabulary_home_modules(lean_dir: Path, mirror_text: str) -> List[str]:
    """Island modules named in a vocabulary mirror's block headers
    (`-- ===== GStepCore.lean:25 / CappedJointConfig.lean:33-46 =====`), as module names.

    The shadowing guard for an island without an AxiomGuard lean_lib: an artifact that
    re-declares `R3Cert.rhoB` instead of importing ExactCruxes is a duplicate declaration once
    the challenge also imports ExactCruxes. A header naming no unique island file is an error
    (the mirror and the island disagree, which missions/mirrors.py should also report)."""
    lean_dir = Path(lean_dir).resolve()
    names: List[str] = []
    for hm in _MIRROR_HEADER_RE.finditer(mirror_text):
        for fm in _MIRROR_FILE_RE.finditer(hm.group(1)):
            if fm.group(1) not in names:
                names.append(fm.group(1))
    mods: List[str] = []
    for n in names:
        hits = [p for p in lean_dir.rglob(f"{n}.lean")
                if ".lake" not in p.relative_to(lean_dir).parts]
        if len(hits) != 1:
            raise JudgeError(f"vocabulary mirror cites {n}.lean; {len(hits)} match(es) on the "
                             f"island {lean_dir}")
        m = module_name_of(lean_dir, hits[0])
        if m not in mods:
            mods.append(m)
    return sorted(mods)


def island_anchors(telperion_root: Path, island: str, lean_dir: Path,
                   statuses: Sequence[str] = PROVED_STATUSES) -> list:
    """The grant gate's anchors (proved node -> artifact theorem) on this island. For an
    out-of-tree island this is guard_anchors.load_anchors with the island test replaced by
    "the artifact lies under the island's package directory". With `statuses` beyond
    ("proved",) (`--pending`) the same scan also returns draft/open nodes; their theorem is
    resolved exactly as the grant gate would resolve it."""
    ga = _guard_anchors()
    if island not in OUT_OF_TREE_ISLANDS and tuple(statuses) == PROVED_STATUSES:
        return ga.load_anchors(telperion_root, island)
    lean_dir = Path(lean_dir).resolve()
    anchors, errors = [], []
    for toml_path in sorted((Path(telperion_root) / "missions").glob("*/nodes/*.toml")):
        campaign_root = toml_path.parent.parent
        try:
            doc = tomllib.loads(toml_path.read_text())
        except (OSError, tomllib.TOMLDecodeError) as e:
            errors.append(f"{toml_path}: unreadable ({e})")
            continue
        art = (doc.get("proof") or {}).get("artifact")
        if doc.get("status") not in statuses or not art or not str(art).endswith(".lean"):
            continue
        artifact = (campaign_root / art).resolve()
        if island in OUT_OF_TREE_ISLANDS:
            if not artifact.is_relative_to(lean_dir):
                continue
        elif ga.island_of(artifact) != island:
            continue
        slug = str(doc.get("name", toml_path.stem)).replace(".", "_")
        stmt = campaign_root / "lean" / "Statements" / f"{slug}.lean"
        try:
            thm = ga.resolve_theorem(artifact.read_text(), stmt.read_text())
        except (OSError, ga.RegistryError) as e:
            errors.append(f"{campaign_root.name}/{slug}: {e}")
            continue
        anchors.append(ga.Anchor(slug, campaign_root.name, artifact, thm))
    if errors:
        raise ga.RegistryError("\n".join(errors))
    return anchors


def challenge_guard_modules(telperion_root: Path, island: str,
                            lean_dir: Path) -> tuple[List[str], bool]:
    """(modules every challenge imports for the shadowing guard, whether they are the
    vocabulary-home fallback rather than the island's AxiomGuard libs)."""
    if island in MATERIALIZED_ROOT_ISLANDS:
        return materialized_guard_modules(telperion_root, island), False
    guards = island_guard_modules(lean_dir)
    if guards or island not in OUT_OF_TREE_ISLANDS:
        return guards, False
    mirror = Path(telperion_root) / OUT_OF_TREE_ISLANDS[island].vocab_mirror
    return vocabulary_home_modules(lean_dir, mirror.read_text()), True


# ---------------------------------------------------------------------------
# The challenge (bridge) module
# ---------------------------------------------------------------------------

_OTHER_DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*"
    r"(def|abbrev|instance|structure|inductive|class|axiom|opaque|variable|universe|namespace|section|mutual)\b")


def statement_parts(statement_text: str) -> tuple[str, List[str], str]:
    """(header hash, open lines, body) of a registered statement file.

    The body is everything after the header line with `import`/`open` lines removed --
    byte-identical to what the grant gate normalised, `:= by sorry` included.
    """
    lines = statement_text.split("\n")
    k = 0
    while k < len(lines) and not lines[k].strip():
        k += 1
    if k >= len(lines) or _SENTINEL not in lines[k]:
        raise JudgeError("statement file has no provenance header")
    m = re.search(r"sha256 ([0-9a-f]{16})", lines[k])
    if not m:
        raise JudgeError("statement header carries no sha256")
    rest = lines[k + 1:]
    opens = [ln.strip() for ln in rest if _OPEN_RE.match(ln.strip())]
    body = [ln for ln in rest
            if not ln.strip().startswith("import ") and not _OPEN_RE.match(ln.strip())]
    return m.group(1), opens, "\n".join(body).strip("\n")


_OPENERS, _CLOSERS = "([{\u2983\u27e8", ")]}\u2984\u27e9"


def _scan_depth0(text: str, want: str, *, last: bool = False) -> int:
    """Offset of the first (or last) occurrence of `want` at bracket depth 0 outside string
    literals, or -1. `want` is ":" (not followed by "=") or ":="."""
    depth = 0
    i, n = 0, len(text)
    found = -1
    while i < n:
        ch = text[i]
        if ch == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(want, i):
            if want == ":" and text[i:i + 2] == ":=":
                i += 2
                continue
            if want == ":" and i > 0 and text[i - 1] == ":":
                i += 1
                continue
            found = i
            if not last:
                return found
            i += len(want)
            continue
        i += 1
    return found


def split_signature(body: str) -> tuple[str, str, str]:
    """(short name, binders, conclusion) of the FINAL theorem/lemma in a statement body.

    Refuses a body that declares anything else: the bridge module imports the artifact, so a
    local `def` in the statement would collide with the artifact's copy.
    """
    ga = _guard_anchors()
    code = ga.strip_lean_comments(body)
    other = _OTHER_DECL_RE.search(code)
    if other:
        raise JudgeError(
            f"statement declares `{other.group(1)}` besides its theorem; only a single "
            "theorem/lemma can be judged (local definitions would collide with the artifact)")
    decls = list(ga._DECL_RE.finditer(code))
    if len(decls) != 1:
        raise JudgeError(f"statement declares {len(decls)} theorems/lemmas; expected exactly one")
    d = decls[0]
    short = d.group(2)
    rest = code[d.end():]
    colon = _scan_depth0(rest, ":")
    if colon < 0:
        raise JudgeError("statement theorem has no top-level `:`")
    binders = rest[:colon].strip()
    tail = rest[colon + 1:]
    assign = _scan_depth0(tail, ":=", last=True)
    concl = (tail if assign < 0 else tail[:assign]).strip()
    if not concl:
        raise JudgeError("statement theorem has an empty conclusion")
    return short, binders, concl


_OPEN_LINE_RE = re.compile(r"(?m)^[ \t]*(open\b[^\n]*?)(?:[ \t]+in)?[ \t]*$")


def artifact_context(artifact_text: str, statement_text: str) -> tuple[str, List[str]]:
    """(namespace, open lines) in force where the artifact declares the registered statement.

    The statement's unqualified names resolve in the ARTIFACT'S context -- its enclosing
    `namespace` and the `open` directives above the declaration -- and the campaign mirror
    may spell the same vocabulary under other namespaces (`open Quasicrystal` in a mirrormere
    statement, `RvMBridge.zetaOrdinates` on the island). So the bridge module re-creates the
    artifact's context and drops the statement file's own `open` lines. Every `open` above
    the declaration is kept, including ones whose section has closed: an extra `open` can
    only make a name ambiguous (a build error, hence a judge failure), never resolve it to
    something the artifact did not see.
    """
    ga = _guard_anchors()
    short, needle = ga.statement_decl(statement_text)
    code = ga.strip_string_literals(ga.strip_lean_comments(artifact_text))
    pat = re.compile(r"(?<![\w.'])(theorem|lemma)\s+" + re.escape(short) + r"(?![\w.'])")
    for m in pat.finditer(code):
        rest = ga.normalize_lean(code[m.start():])
        if rest.startswith(needle) and ga._PROOF_BODY_RE.match(rest[len(needle):]):
            ns = ".".join(ga._namespace_at(code, m.start()))
            opens: List[str] = []
            for om in _OPEN_LINE_RE.finditer(code, 0, m.start()):
                line = re.sub(r"\s+", " ", om.group(1)).strip()
                if line not in opens:
                    opens.append(line)
            return ns, opens
    raise JudgeError(f"artifact does not declare the registered statement `{short}`")


def decl_context(module_text: str, theorem: str) -> tuple[str, List[str]]:
    """(namespace, open lines) in force where `module_text` declares `theorem` -- for the
    IMPLICATION part of a compositional judgement, whose module does not declare the registered
    statement itself.  The statement then resolves in the implication's own context, exactly as
    `artifact_context` makes it resolve in the artifact's."""
    ga = _guard_anchors()
    short = theorem.rsplit(".", 1)[-1]
    code = ga.strip_string_literals(ga.strip_lean_comments(module_text))
    pat = re.compile(r"(?<![\w.'])(theorem|lemma)\s+" + re.escape(short) + r"(?![\w.'])")
    for m in pat.finditer(code):
        ns = ".".join(ga._namespace_at(code, m.start()))
        if (ns + "." + short if ns else short) != theorem:
            continue
        opens: List[str] = []
        for om in _OPEN_LINE_RE.finditer(code, 0, m.start()):
            line = re.sub(r"\s+", " ", om.group(1)).strip()
            if line not in opens:
                opens.append(line)
        return ns, opens
    raise JudgeError(f"implication module does not declare `{theorem}`")


def bridge_theorem_name(slug: str) -> str:
    return f"MissionJudge.{slug}"


def render_challenge(*, slug: str, campaign: str, theorem: str, solution_module: str,
                     guard_modules: Sequence[str], statement_text: str,
                     artifact_text: str, vocab_guard: bool = False,
                     hypotheses: Sequence[tuple] = (), materialized: bool = False,
                     pending_status: str = "") -> str:
    """The Comparator challenge for one node.  With `hypotheses` [(binder, constant), ...] it is
    instead the IMPLICATION part of a compositional judgement (see compose.py): the registered
    statement under those leading hypotheses, proved by the island's implication `theorem`."""
    stmt_hash, _mirror_opens, body = statement_parts(statement_text)
    short, binders, concl = split_signature(body)
    ns, opens = (decl_context(artifact_text, theorem) if hypotheses
                 else artifact_context(artifact_text, statement_text))
    if not hypotheses and theorem != short and \
            not theorem.endswith("." + short.removeprefix("_root_.")):
        raise JudgeError(
            f"artifact theorem {theorem!r} does not end with the statement's declared name "
            f"{short!r}")
    prop = f"\u2200 {binders}, {concl}" if binders else concl
    imports = [solution_module] + [g for g in guard_modules if g != solution_module]
    out: List[str] = [
        f"/- {_SENTINEL} -- generated by telperion.missions.judge.",
        f"   Comparator CHALLENGE for registry node {campaign}/{slug}.",
        f"   The TYPE below is the registered statement, missions/{campaign}/lean/Statements/",
        f"   {slug}.lean (header sha256 {stmt_hash}), binders and conclusion verbatim; the",
        f"   PROOF is the artifact constant `{theorem}` from {solution_module}. Both kernels",
        "   accept this module only if the artifact proves exactly the registered proposition.",
    ]
    if pending_status:
        out += [
            f"   PENDING RENDER: the node's status is {pending_status!r}, not proved. This module",
            "   comes from `--pending` (a temp bundle, never committed); a pass here is pre-grant",
            "   evidence and cannot be recorded with `mission comparator-record`.",
        ]
    if materialized:
        out += [
            "   This island is MATERIALIZED: its workspace is a foreign root package that the",
            "   island's recipe checks out at a pinned commit, plus the island's own modules. The",
            "   AxiomGuard imports load every island module, so a vocabulary constant shadowed by",
            "   the artifact is a duplicate declaration here; root-package modules outside their",
            "   import closure are not loaded. The",
        ]
    elif vocab_guard:
        out += [
            "   The other imports are the island modules the campaign's vocabulary mirror copies",
            "   from, so a vocabulary constant shadowed by the artifact is a duplicate",
            "   declaration here, not a silent substitution. The",
        ]
    elif not [g for g in guard_modules if g != solution_module]:
        out += [
            "   No shadowing guard is imported: this island has no AxiomGuard lean_lib (or none",
            "   whose closure holds the artifact), so a re-declared vocabulary constant is NOT",
            "   caught here; the island's own axiom-guard CI job covers the whole island. The",
        ]
    else:
        out += [
            "   The AxiomGuard imports load the whole island, so a vocabulary constant shadowed by",
            "   the artifact is a duplicate declaration here, not a silent substitution. The",
        ]
    out += [
        "   `namespace` and the `open` lines inside it are the artifact's own at its",
        "   declaration, so every name in the statement resolves exactly as it does there. -/",
    ]
    out += [f"import {m}" for m in imports]
    out.append("")
    if ns:
        out.append(f"namespace {ns}")
        out.append("")
    # The artifact's `open` lines go INSIDE its namespace: an `open BombieriLagarias` written
    # under `namespace RvMBridge15` names `RvMBridge15.BombieriLagarias`, which does not
    # resolve at the top level. Opening a top-level namespace from inside another is fine.
    if opens:
        out += opens
        out.append("")
    name = ("_root_." if ns else "") + bridge_theorem_name(slug)
    if hypotheses:
        out.append(f"theorem {name}")
        for b, c in hypotheses:
            out.append(f"    ({b} : _root_.{c})")
        out.append("    :")
    else:
        out.append(f"theorem {name} :")
    out.append(f"    {prop} :=")
    out.append(f"  {theorem}" + "".join(f" {b}" for b, _c in hypotheses))
    if ns:
        out.append("")
        out.append(f"end {ns}")
    return "\n".join(out) + "\n"


def render_segment_challenge(*, node: str, campaign: str, name: str, statement: str,
                             theorem: str, module: str) -> str:
    """A SEGMENT part of a compositional judgement: the bare statement constant, proved by the
    segment theorem.  The type is written `_root_.<statement>` so nothing can re-resolve it;
    ComposeInspect then confirms the judged type IS that constant."""
    from .compose import seg_slug
    slug = seg_slug(node, name)
    return "\n".join([
        f"/- {_SENTINEL} -- generated by telperion.missions.judge.",
        f"   Comparator CHALLENGE, compositional part: segment {name} of registry node",
        f"   {campaign}/{node}.  The TYPE is the bare constant `{statement}`, the PROOF the",
        f"   segment theorem `{theorem}` from {module}.  The implication part must take exactly",
        "   this constant as a hypothesis; compose.py checks the two by lean4export bytes. -/",
        f"import {module}",
        "",
        f"theorem {bridge_theorem_name(slug)} : _root_.{statement} :=",
        f"  {theorem}",
    ]) + "\n"


# ---------------------------------------------------------------------------
# Bundle
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Challenge:
    slug: str
    campaign: str
    theorem: str
    solution_module: str
    challenge_module: str
    bridge_theorem: str
    #: False when the node declares `heavy_certificates = true` (nanoda off for this node).
    nanoda: bool
    challenge_text: str
    config: "OrderedDict[str, object]"
    artifact_sha256: str
    statement_sha256: str
    #: "" for an ordinary node; "seg:<name>" or "compose" for a part of a compositional one.
    part: str = ""
    #: The statement constants this part's job exports (lean4export) for compose.py's identity
    #: check: a segment's own statement, or every segment statement for the implication.
    exports: tuple = ()
    #: The registry node a part belongs to ("" = the challenge IS the node).
    node: str = ""


@dataclass(frozen=True)
class Bundle:
    island: str
    package: str
    toolchain: str
    comparator_tag: str
    challenges: List[Challenge]
    #: "campaign/slug: why" for proved nodes on this island the judge cannot consume.
    skipped: tuple
    #: The island's package directory relative to the bundle directory (the committed bundle's by
    #: default; a heavy bundle rendered to a temp `--out` replaces it with the path from there).
    require_path: str
    #: "campaign/slug" of proved nodes EXCLUDED BY RULE (`judge_via = "heavy"`): judged by
    #: missions-comparator-heavy.yml instead. Written into MANIFEST.json so the bundle itself
    #: says which nodes it does not judge and where they are judged.
    excluded: tuple = ()
    #: MATERIALIZED_ROOT_ISLANDS only: what MANIFEST.json records about the workspace (recipe,
    #: pin, Comparator toolchain, install command). None for every other island, whose bundle
    #: is then byte-for-byte what it was before materialized islands existed.
    materialized: Optional["OrderedDict[str, object]"] = None
    #: `--pending` only: "campaign/slug: status" of rendered nodes that are NOT proved.
    pending: tuple = ()

    def files(self) -> "OrderedDict[str, str]":
        """Relative path -> text for everything the bundle writes."""
        files: "OrderedDict[str, str]" = OrderedDict()
        files["lean-toolchain"] = self.toolchain + "\n"
        if self.materialized is not None:
            return self._materialized_files(files)
        files["lakefile.toml"] = (
            f'name = "MissionJudge_{self.island}"\n'
            "# Generated by telperion.missions.judge -- DO NOT EDIT BY HAND.\n"
            f"# Path-requires the {self.island} island so its artifact modules and these\n"
            "# challenge modules share one workspace for `lake env comparator`.\n"
            'defaultTargets = ["MissionChallenges"]\n\n'
            "[[require]]\n"
            f'name = "{self.package}"\n'
            f'path = "{self.require_path}"\n\n'
            "[[lean_lib]]\n"
            'name = "MissionChallenges"\n'
        )
        if self.island in GUARD_POLICY_ONE_CONTAINING:
            # A root that imports every bridge would co-import the guards that cannot coexist
            # (li_positivity: zeta_sphere_bound). CI builds the bridge modules by name, never
            # the root, so the root is a comment here rather than a build failure.
            files["MissionChallenges.lean"] = (
                f"-- {_SENTINEL}. No root imports on `{self.island}`: its AxiomGuard libs cannot\n"
                "-- be imported together, so each bridge module imports one of them and is built by\n"
                "-- name (`lake build MissionChallenges.<Slug>`), never through this root.\n")
        else:
            files["MissionChallenges.lean"] = "".join(
                f"import {c.challenge_module}\n" for c in self.challenges)
        for c in self.challenges:
            files[f"MissionChallenges/{c.slug}.lean"] = c.challenge_text
            files[f"{c.slug}.comparator.json"] = json.dumps(c.config, indent=2) + "\n"
        manifest = OrderedDict(
            island=self.island, package=self.package, toolchain=self.toolchain,
            comparator_tag=self.comparator_tag,
            not_consumable=list(self.skipped),
            nodes=[OrderedDict(
                slug=c.slug, campaign=c.campaign, theorem=c.theorem,
                solution_module=c.solution_module, challenge_module=c.challenge_module,
                bridge_theorem=c.bridge_theorem, config=f"{c.slug}.comparator.json",
                nanoda=c.nanoda,
                artifact_sha256=c.artifact_sha256, statement_sha256=c.statement_sha256,
                **({"part_of": c.node, "part": c.part, "exports": list(c.exports)}
                   if c.part else {}),
            ) for c in self.challenges],
        )
        if self.pending:
            manifest["pending_not_proved"] = list(self.pending)
        if self.excluded:
            manifest["judged_elsewhere"] = [
                dict(node=e, judge_via="heavy", workflow=HEAVY_WORKFLOW) for e in self.excluded]
        files["MANIFEST.json"] = json.dumps(manifest, indent=2) + "\n"
        return files

    def _materialized_files(self, files: "OrderedDict[str, str]") -> "OrderedDict[str, str]":
        """The bundle of a MATERIALIZED_ROOT_ISLANDS island: no lakefile of its own (the foreign
        root package must stay the workspace root), but a `lakefile-stanza.lean` that
        telperion/scripts/judge_materialize.sh appends to the workspace lakefile after copying
        the challenge modules and configs into the workspace root."""
        m = self.materialized
        files["lakefile-stanza.lean"] = (
            f"-- ===== Arda missions judge bundle for {self.island} (appended by "
            "telperion/scripts/judge_materialize.sh) =====\n"
            f"-- {_SENTINEL}: generated by telperion.missions.judge. One lib holding the bridge\n"
            "-- modules; they import the island's artifact and AxiomGuard modules, which the\n"
            "-- island's own stanza (appended by the recipe) already builds.\n"
            "lean_lib MissionChallenges where\n"
            "  roots := #[`MissionChallenges]\n"
            "  globs := #[.andSubmodules `MissionChallenges]\n")
        if self.challenges:
            files["MissionChallenges.lean"] = "".join(
                f"import {c.challenge_module}\n" for c in self.challenges)
        else:
            files["MissionChallenges.lean"] = (
                f"-- {_SENTINEL}. No proved registry node has its artifact on `{self.island}` "
                "yet,\n-- so there is nothing to judge; a grant adds one bridge module per node.\n")
        for c in self.challenges:
            files[f"MissionChallenges/{c.slug}.lean"] = c.challenge_text
            files[f"{c.slug}.comparator.json"] = json.dumps(c.config, indent=2) + "\n"
        manifest = OrderedDict(
            island=self.island, package=self.package, toolchain=self.toolchain,
            comparator_tag=self.comparator_tag,
            comparator_toolchain=m["comparator_toolchain"],
            materialized_root=OrderedDict((k, v) for k, v in m.items()
                                          if k != "comparator_toolchain"),
            not_consumable=list(self.skipped),
            nodes=[OrderedDict(
                slug=c.slug, campaign=c.campaign, theorem=c.theorem,
                solution_module=c.solution_module, challenge_module=c.challenge_module,
                bridge_theorem=c.bridge_theorem, config=f"{c.slug}.comparator.json",
                nanoda=c.nanoda,
                artifact_sha256=c.artifact_sha256, statement_sha256=c.statement_sha256,
            ) for c in self.challenges],
        )
        if self.pending:
            manifest["pending_not_proved"] = list(self.pending)
        if self.excluded:
            manifest["judged_elsewhere"] = [
                dict(node=e, judge_via="heavy", workflow=HEAVY_WORKFLOW) for e in self.excluded]
        files["MANIFEST.json"] = json.dumps(manifest, indent=2) + "\n"
        return files


def _node_status(node_toml: Path) -> str:
    """The node's `status` ("" when unreadable)."""
    try:
        return str(tomllib.loads(Path(node_toml).read_text()).get("status", ""))
    except (OSError, tomllib.TOMLDecodeError):
        return ""


def _heavy_certificates(node_toml: Path) -> bool:
    """The node's `heavy_certificates` flag (False when absent or unreadable)."""
    import tomllib
    try:
        return bool(tomllib.loads(Path(node_toml).read_text()).get("heavy_certificates", False))
    except (OSError, tomllib.TOMLDecodeError):
        return False


#: The dispatch-only workflow that judges `judge_via = "heavy"` nodes.
HEAVY_WORKFLOW = "missions-comparator-heavy.yml"


def _judge_via(node_toml: Path) -> str:
    """The node's `judge_via` ("" = per-PR bundle; "heavy" = the dispatch-only heavy path)."""
    import tomllib
    try:
        return str(tomllib.loads(Path(node_toml).read_text()).get("judge_via", "") or "").strip()
    except (OSError, tomllib.TOMLDecodeError):
        return ""


def _sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build_bundle(telperion_root: Path, island: str, *, enable_nanoda: bool = True,
                 only: Optional[Sequence[str]] = None, heavy: bool = False,
                 pending: bool = False) -> Bundle:
    """Render the challenge bundle.

    Per-PR mode (heavy=False): nodes with `judge_via = "heavy"` are EXCLUDED BY RULE (listed in
    `Bundle.excluded`, never rendered), so the committed bundle and `--check` stay consistent.
    Heavy mode (heavy=True): render ONLY the `--only` nodes, and REFUSE any of them that is not
    `judge_via = "heavy"` -- the heavy path must never become a way to route an ordinary node
    around the per-PR judge. A heavy bundle is written to a temp `--out`, never committed.
    Pending mode (pending=True): ALSO render draft and open nodes whose artifact is on the
    island (`Bundle.pending` lists them; each bridge module says so). Like a heavy bundle it is
    written to a temp `--out`, never committed: a pass on it is pre-grant evidence only.

    A MATERIALIZED_ROOT_ISLANDS island may have no proved node yet; its committed bundle is then
    empty (the root says so, MANIFEST.json lists no node) instead of an error, so the island
    can be wired before its first grant. Every other island still refuses an empty bundle.
    """
    if heavy and not only:
        raise JudgeError("--heavy needs --only <slug>: the heavy path judges named nodes only")
    if heavy and pending:
        raise JudgeError("--heavy and --pending are separate paths; use one")
    telperion_root = Path(telperion_root)
    ga = _guard_anchors()
    lean_dir = island_dir(telperion_root, island)
    materialized = island in MATERIALIZED_ROOT_ISLANDS
    if materialized:
        facts = materialized_facts(telperion_root, island)
        package = MATERIALIZED_ROOT_ISLANDS[island].package
        toolchain = str(facts["comparator_toolchain"])
        tag = MATERIALIZED_ROOT_ISLANDS[island].comparator_tag
    else:
        facts = None
        package = island_package_name(lean_dir)
        toolchain = island_toolchain(lean_dir)
        tag = comparator_tag(toolchain)
    statuses = PENDING_STATUSES if pending else PROVED_STATUSES
    try:
        anchors = island_anchors(telperion_root, island, lean_dir, statuses)
    except ga.RegistryError as e:
        raise JudgeError(f"island {island!r}: {e}") from e
    if not anchors and not (materialized and not only):
        what = "registered (draft/open/proved)" if pending else "proved"
        raise JudgeError(f"island {island!r}: no {what} registry node has its artifact here")
    pending_nodes: List[str] = []
    challenges: List[Challenge] = []
    guards, vocab_guard = challenge_guard_modules(telperion_root, island, lean_dir)
    problems: List[str] = []
    excluded: List[str] = []
    for a in anchors:
        if only and a.node not in only:
            continue
        via = _judge_via(telperion_root / "missions" / a.campaign / "nodes" / f"{a.node}.toml")
        if heavy and via != "heavy":
            raise JudgeError(f"{a.campaign}/{a.node}: judge_via = {via!r}, not 'heavy'; the heavy "
                             "path refuses ordinary nodes (they are judged by the per-PR bundle)")
        if not heavy and via == "heavy":
            excluded.append(f"{a.campaign}/{a.node}")
            continue
        stmt_path = telperion_root / "missions" / a.campaign / "lean" / "Statements" / f"{a.node}.lean"
        statement_text = stmt_path.read_text()
        if heavy:
            from .schema import load_node
            spec = load_node(telperion_root / "missions" / a.campaign / "nodes"
                             / f"{a.node}.toml").compose
            if spec is not None:
                challenges += compose_parts(
                    node=a.node, campaign=a.campaign, spec=spec, lean_dir=lean_dir,
                    guards=guards_for(lean_dir, island, guards, spec.module),
                    vocab_guard=vocab_guard, statement_text=statement_text,
                    artifact_sha256=_sha256(a.artifact), statement_sha256=_sha256(stmt_path))
                continue
        status = _node_status(telperion_root / "missions" / a.campaign / "nodes"
                              / f"{a.node}.toml")
        sol = module_name_of(lean_dir, a.artifact)
        chal = f"MissionChallenges.{a.node}"
        try:
            if materialized and "." in sol:
                # The recipe copies only lean/*.lean to the workspace root; a nested artifact
                # would not exist there under this module name.
                raise JudgeError(f"artifact module {sol!r} is not a top-level file of the "
                                 "materialized island's lean/ directory")
            text = render_challenge(
                slug=a.node, campaign=a.campaign, theorem=a.theorem, solution_module=sol,
                guard_modules=guards_for(lean_dir, island, guards, sol),
                statement_text=statement_text, artifact_text=a.artifact.read_text(),
                vocab_guard=vocab_guard, materialized=materialized,
                pending_status="" if status == "proved" else status)
        except JudgeError as e:
            problems.append(f"{a.campaign}/{a.node}: {e}")
            continue
        if status != "proved":
            pending_nodes.append(f"{a.campaign}/{a.node}: {status}")
        bridge = bridge_theorem_name(a.node)
        # Per-node: `heavy_certificates = true` in the node toml turns nanoda off for that
        # node only (its exact certificates exhaust a 16 GB runner under nanoda; the Lean
        # kernel replay and the axiom whitelist still run). Recorded as "Lean kernel only".
        # NOT `heavy`: that is this function's PARAMETER (the heavy-judge mode).  Reassigning it
        # here made the first node with `heavy_certificates = true` flip the mode for every node
        # after it, so the next ordinary node hit the heavy path's "judge_via is not heavy"
        # refusal and the whole bundle failed to build -- latent on main, where no node carries
        # the flag, and fatal on any branch that sets it (cl/kwin, cl/kwin2).
        node_heavy = _heavy_certificates(
            telperion_root / "missions" / a.campaign / "nodes" / f"{a.node}.toml")
        node_nanoda = enable_nanoda and not node_heavy
        cfg = challenge_config(
            challenge_module=chal, solution_module=chal, theorem_names=[bridge],
            permitted_axioms=CLEAN_AXIOMS, enable_nanoda=node_nanoda)
        challenges.append(Challenge(
            slug=a.node, campaign=a.campaign, theorem=a.theorem, solution_module=sol,
            challenge_module=chal, bridge_theorem=bridge, nanoda=node_nanoda,
            challenge_text=text, config=cfg,
            artifact_sha256=_sha256(a.artifact), statement_sha256=_sha256(stmt_path)))
    if problems and not challenges:
        raise JudgeError(f"island {island!r}: no consumable node:\n  " + "\n  ".join(problems))
    if not challenges and not (materialized and not only):
        raise JudgeError(f"island {island!r}: --only matched no proved node")
    # A materialized bundle is COPIED into the workspace, so it path-requires nothing.
    require = "" if materialized else os.path.relpath(
        lean_dir.resolve(), default_out(telperion_root, island).resolve())
    return Bundle(island=island, package=package, toolchain=toolchain, comparator_tag=tag,
                  challenges=challenges, skipped=tuple(problems), require_path=require,
                  excluded=tuple(excluded), materialized=facts, pending=tuple(pending_nodes))


def compose_parts(*, node: str, campaign: str, spec, lean_dir: Path, guards: Sequence[str],
                  vocab_guard: bool, statement_text: str, artifact_sha256: str,
                  statement_sha256: str) -> List[Challenge]:
    """The challenges of a COMPOSITIONAL judgement (see compose.py): one per segment, plus the
    implication.  Every part is Lean-kernel-only: the segments carry the heavy certificates, and
    one kernel mode per verdict keeps the record honest."""
    from .compose import compose_slug, seg_slug
    out: List[Challenge] = []
    for nm, stmt, thm, mod in spec.segments:
        slug = seg_slug(node, nm)
        chal = f"MissionChallenges.{slug}"
        br = bridge_theorem_name(slug)
        out.append(Challenge(
            slug=slug, campaign=campaign, theorem=thm, solution_module=mod,
            challenge_module=chal, bridge_theorem=br, nanoda=False,
            challenge_text=render_segment_challenge(node=node, campaign=campaign, name=nm,
                                                    statement=stmt, theorem=thm, module=mod),
            config=challenge_config(challenge_module=chal, solution_module=chal,
                                    theorem_names=[br], permitted_axioms=CLEAN_AXIOMS,
                                    enable_nanoda=False),
            artifact_sha256=artifact_sha256, statement_sha256=statement_sha256,
            part=f"seg:{nm}", exports=(stmt,), node=node))
    slug = compose_slug(node)
    chal = f"MissionChallenges.{slug}"
    br = bridge_theorem_name(slug)
    comp_path = lean_dir / (spec.module.replace(".", "/") + ".lean")
    if not comp_path.is_file():
        raise JudgeError(f"{campaign}/{node}: compose.module {spec.module!r} has no source file "
                         f"{comp_path}")
    text = render_challenge(
        slug=slug, campaign=campaign, theorem=spec.theorem, solution_module=spec.module,
        guard_modules=guards, statement_text=statement_text, artifact_text=comp_path.read_text(),
        vocab_guard=vocab_guard,
        hypotheses=[(f"b_{nm}", stmt) for nm, stmt, _t, _m in spec.segments])
    out.append(Challenge(
        slug=slug, campaign=campaign, theorem=spec.theorem, solution_module=spec.module,
        challenge_module=chal, bridge_theorem=br, nanoda=False, challenge_text=text,
        config=challenge_config(challenge_module=chal, solution_module=chal, theorem_names=[br],
                                permitted_axioms=CLEAN_AXIOMS, enable_nanoda=False),
        artifact_sha256=artifact_sha256, statement_sha256=statement_sha256,
        part="compose", exports=tuple(spec.segment_statements), node=node))
    return out


def shard(challenges: Sequence[Challenge], spec: Optional[str]) -> List[Challenge]:
    """Challenges for shard `I/N` (0-based I) of the slug-sorted list; all when spec is None.
    Sharding is by slug order, so a shard is stable across runs and every node lands in
    exactly one shard."""
    ordered = sorted(challenges, key=lambda c: c.slug)
    if not spec:
        return ordered
    m = re.fullmatch(r"(\d+)/(\d+)", spec.strip())
    if not m or int(m.group(2)) == 0 or int(m.group(1)) >= int(m.group(2)):
        raise JudgeError(f"--shard must be I/N with 0 <= I < N, got {spec!r}")
    i, n = int(m.group(1)), int(m.group(2))
    return [c for k, c in enumerate(ordered) if k % n == i]


def default_out(telperion_root: Path, island: str) -> Path:
    return Path(telperion_root) / "missions" / "judge" / island


def write_bundle(bundle: Bundle, out_dir: Path) -> List[Path]:
    out_dir = Path(out_dir)
    written: List[Path] = []
    for rel, text in bundle.files().items():
        p = out_dir / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        written.append(p)
    return written


def check_bundle(bundle: Bundle, out_dir: Path) -> List[str]:
    """Differences between the committed bundle and a fresh render (empty = in sync)."""
    out_dir = Path(out_dir)
    problems: List[str] = []
    expected = bundle.files()
    for rel, text in expected.items():
        p = out_dir / rel
        if not p.is_file():
            problems.append(f"missing: {rel}")
        elif p.read_text() != text:
            problems.append(f"stale: {rel} (regenerate with `python -m telperion.missions.judge "
                            f"--island {bundle.island}`)")
    for p in sorted(out_dir.rglob("*")):
        if p.is_file() and ".lake" not in p.parts and "lake-manifest.json" != p.name:
            rel = str(p.relative_to(out_dir))
            if rel not in expected:
                problems.append(f"unexpected file in bundle: {rel}")
    return problems


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--island", required=True)
    ap.add_argument("--telperion", type=Path, default=Path(__file__).resolve().parents[3],
                    help="telperion/ directory (default: this package's)")
    ap.add_argument("--out", type=Path, default=None,
                    help="bundle directory (default: telperion/missions/judge/<island>)")
    ap.add_argument("--check", action="store_true",
                    help="verify the committed bundle matches the registry; write nothing")
    ap.add_argument("--no-nanoda", action="store_true", help="enable_nanoda = false")
    ap.add_argument("--only", nargs="*", default=None, help="restrict to these node slugs")
    ap.add_argument("--heavy", action="store_true",
                    help="render ONLY the --only nodes, each of which must be judge_via = \"heavy\" "
                         "(refused otherwise); write it with --out to a temp dir, never commit it. "
                         "Without --heavy, judge_via = \"heavy\" nodes are excluded by rule.")
    ap.add_argument("--pending", action="store_true",
                    help="ALSO render draft and open nodes whose artifact is on the island (pre-grant "
                         "judging); write it with --out to a temp dir, never commit it. A pass on "
                         "it cannot be recorded (comparator-record needs a proved node)")
    ap.add_argument("--list", action="store_true", help="print the nodes and exit")
    ap.add_argument("--configs", action="store_true",
                    help="print `slug<TAB>config<TAB>solution_module<TAB>theorem<TAB>bridge<TAB>"
                         "nanoda|lean-kernel-only` for the (sharded) node set and exit -- what "
                         "the CI job iterates over")
    ap.add_argument("--shard", default=None, metavar="I/N",
                    help="with --configs: only nodes whose sorted index mod N == I")
    args = ap.parse_args(list(argv) if argv is not None else None)
    try:
        bundle = build_bundle(args.telperion, args.island, enable_nanoda=not args.no_nanoda,
                              only=args.only, heavy=args.heavy, pending=args.pending)
    except JudgeError as e:
        print(f"::error::{e}", file=sys.stderr)
        return 2
    out = args.out or default_out(args.telperion, args.island)
    if args.heavy:
        import os
        import dataclasses
        bundle = dataclasses.replace(bundle, require_path=os.path.relpath(
            island_dir(args.telperion, args.island), Path(out).resolve()))
    # Diagnostics go to STDERR: `--configs` output is machine-read (the CI job builds lake
    # targets from it), and a ::warning:: line on stdout once became the target
    # `MissionChallenges.::warning::zeta_reflection:` ("too many ':'").
    for sk in bundle.skipped:
        print(f"::warning::{args.island}: not consumable, skipped: {sk}", file=sys.stderr)
    for ex in bundle.excluded:
        print(f"::notice::{args.island}: {ex} is judge_via = \"heavy\": excluded from this bundle "
              f"by rule, judged by {HEAVY_WORKFLOW}", file=sys.stderr)
    for pn in bundle.pending:
        print(f"::notice::{args.island}: PENDING render of a node that is not proved: {pn}",
              file=sys.stderr)
    if args.pending and args.check:
        print("::error::--pending bundles are never committed, so there is nothing to --check",
              file=sys.stderr)
        return 2
    if args.pending and not args.out and not (args.configs or args.list):
        print("::error::--pending needs --out <temp dir>: a pending bundle must never be written "
              "over the committed bundle", file=sys.stderr)
        return 2
    if args.heavy and args.check:
        print("::error::--heavy bundles are never committed, so there is nothing to --check",
              file=sys.stderr)
        return 2
    if args.heavy and not args.out and not (args.configs or args.list):
        print("::error::--heavy needs --out <temp dir>: a heavy bundle must never be written "
              "over the committed per-PR bundle", file=sys.stderr)
        return 2
    if args.configs:
        try:
            chosen = shard(bundle.challenges, args.shard)
        except JudgeError as e:
            print(f"::error::{e}", file=sys.stderr)
            return 2
        for c in chosen:
            # Columns 7-8 (compositional parts only): the part label and the statement
            # constants its job must lean4export, comma-separated.  Empty for ordinary nodes.
            print(f"{c.slug}\t{c.slug}.comparator.json\t{c.solution_module}\t{c.theorem}\t{c.bridge_theorem}\t{'nanoda' if c.nanoda else 'lean-kernel-only'}\t{c.part}\t{','.join(c.exports)}")
        return 0
    if args.list:
        for c in bundle.challenges:
            print(f"{c.campaign}/{c.slug}\t{c.theorem}\t{c.solution_module}")
        print(f"{len(bundle.challenges)} node(s); toolchain {bundle.toolchain}; "
              f"comparator {bundle.comparator_tag}")
        return 0
    if args.check:
        problems = check_bundle(bundle, out)
        for p in problems:
            print(f"::error::{args.island}: {p}", file=sys.stderr)
        if problems:
            return 1
        print(f"OK: {out} matches the registry ({len(bundle.challenges)} challenge(s))")
        return 0
    for p in write_bundle(bundle, out):
        print(f"wrote {p}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

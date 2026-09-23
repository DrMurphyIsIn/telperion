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

conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
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


def island_dir(telperion_root: Path, island: str) -> Path:
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
    return sorted(m.group(1) for m in _LIB_RE.finditer(text) if m.group(1).startswith("AxiomGuard"))


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


def bridge_theorem_name(slug: str) -> str:
    return f"MissionJudge.{slug}"


def render_challenge(*, slug: str, campaign: str, theorem: str, solution_module: str,
                     guard_modules: Sequence[str], statement_text: str,
                     artifact_text: str) -> str:
    stmt_hash, _mirror_opens, body = statement_parts(statement_text)
    short, binders, concl = split_signature(body)
    ns, opens = artifact_context(artifact_text, statement_text)
    if theorem != short and not theorem.endswith("." + short.removeprefix("_root_.")):
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
        "   The AxiomGuard imports load the whole island, so a vocabulary constant shadowed by",
        "   the artifact is a duplicate declaration here, not a silent substitution. The",
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
    out.append(f"theorem {name} :")
    out.append(f"    {prop} :=")
    out.append(f"  {theorem}")
    if ns:
        out.append("")
        out.append(f"end {ns}")
    return "\n".join(out) + "\n"


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
    challenge_text: str
    config: "OrderedDict[str, object]"
    artifact_sha256: str
    statement_sha256: str


@dataclass(frozen=True)
class Bundle:
    island: str
    package: str
    toolchain: str
    comparator_tag: str
    challenges: List[Challenge]
    #: "campaign/slug: why" for proved nodes on this island the judge cannot consume.
    skipped: tuple = ()

    def files(self) -> "OrderedDict[str, str]":
        """Relative path -> text for everything the bundle writes."""
        files: "OrderedDict[str, str]" = OrderedDict()
        files["lean-toolchain"] = self.toolchain + "\n"
        files["lakefile.toml"] = (
            f'name = "MissionJudge_{self.island}"\n'
            "# Generated by telperion.missions.judge -- DO NOT EDIT BY HAND.\n"
            f"# Path-requires the {self.island} island so its artifact modules and these\n"
            "# challenge modules share one workspace for `lake env comparator`.\n"
            'defaultTargets = ["MissionChallenges"]\n\n'
            "[[require]]\n"
            f'name = "{self.package}"\n'
            f'path = "../../../examples/{self.island}/lean"\n\n'
            "[[lean_lib]]\n"
            'name = "MissionChallenges"\n'
        )
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
                artifact_sha256=c.artifact_sha256, statement_sha256=c.statement_sha256,
            ) for c in self.challenges],
        )
        files["MANIFEST.json"] = json.dumps(manifest, indent=2) + "\n"
        return files


def _sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build_bundle(telperion_root: Path, island: str, *, enable_nanoda: bool = True,
                 only: Optional[Sequence[str]] = None) -> Bundle:
    telperion_root = Path(telperion_root)
    ga = _guard_anchors()
    lean_dir = island_dir(telperion_root, island)
    package = island_package_name(lean_dir)
    toolchain = island_toolchain(lean_dir)
    tag = comparator_tag(toolchain)
    try:
        anchors = ga.load_anchors(telperion_root, island)
    except ga.RegistryError as e:
        raise JudgeError(f"island {island!r}: {e}") from e
    if not anchors:
        raise JudgeError(f"island {island!r}: no proved registry node has its artifact here")
    challenges: List[Challenge] = []
    guards = island_guard_modules(lean_dir)
    problems: List[str] = []
    for a in anchors:
        if only and a.node not in only:
            continue
        stmt_path = telperion_root / "missions" / a.campaign / "lean" / "Statements" / f"{a.node}.lean"
        statement_text = stmt_path.read_text()
        sol = module_name_of(lean_dir, a.artifact)
        chal = f"MissionChallenges.{a.node}"
        try:
            text = render_challenge(
                slug=a.node, campaign=a.campaign, theorem=a.theorem, solution_module=sol,
                guard_modules=guards, statement_text=statement_text,
                artifact_text=a.artifact.read_text())
        except JudgeError as e:
            problems.append(f"{a.campaign}/{a.node}: {e}")
            continue
        bridge = bridge_theorem_name(a.node)
        cfg = challenge_config(
            challenge_module=chal, solution_module=chal, theorem_names=[bridge],
            permitted_axioms=CLEAN_AXIOMS, enable_nanoda=enable_nanoda)
        challenges.append(Challenge(
            slug=a.node, campaign=a.campaign, theorem=a.theorem, solution_module=sol,
            challenge_module=chal, bridge_theorem=bridge, challenge_text=text, config=cfg,
            artifact_sha256=_sha256(a.artifact), statement_sha256=_sha256(stmt_path)))
    if problems and not challenges:
        raise JudgeError(f"island {island!r}: no consumable node:\n  " + "\n  ".join(problems))
    if not challenges:
        raise JudgeError(f"island {island!r}: --only matched no proved node")
    return Bundle(island=island, package=package, toolchain=toolchain, comparator_tag=tag,
                  challenges=challenges, skipped=tuple(problems))


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
    ap.add_argument("--list", action="store_true", help="print the nodes and exit")
    ap.add_argument("--configs", action="store_true",
                    help="print `slug<TAB>config<TAB>solution_module<TAB>theorem` for the "
                         "(sharded) node set and exit -- what the CI job iterates over")
    ap.add_argument("--shard", default=None, metavar="I/N",
                    help="with --configs: only nodes whose sorted index mod N == I")
    args = ap.parse_args(list(argv) if argv is not None else None)
    try:
        bundle = build_bundle(args.telperion, args.island, enable_nanoda=not args.no_nanoda,
                              only=args.only)
    except JudgeError as e:
        print(f"::error::{e}")
        return 2
    out = args.out or default_out(args.telperion, args.island)
    for sk in bundle.skipped:
        print(f"::warning::{args.island}: not consumable, skipped: {sk}")
    if args.configs:
        try:
            chosen = shard(bundle.challenges, args.shard)
        except JudgeError as e:
            print(f"::error::{e}")
            return 2
        for c in chosen:
            print(f"{c.slug}\t{c.slug}.comparator.json\t{c.solution_module}\t{c.theorem}\t{c.bridge_theorem}")
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
            print(f"::error::{args.island}: {p}")
        if problems:
            return 1
        print(f"OK: {out} matches the registry ({len(bundle.challenges)} challenge(s))")
        return 0
    for p in write_bundle(bundle, out):
        print(f"wrote {p}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

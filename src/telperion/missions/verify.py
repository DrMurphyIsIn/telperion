"""Verify gate: invariant battery, proved/refuted status flip, closure fixpoint.

This module is the SOLE path through which a node's status becomes `proved` or
`refuted`. Every other mutator (set_proof, promote_to_open, deprecate) is
explicitly prohibited from making that flip.

Key functions:
  normalize_lean      -- strip comments, collapse whitespace, drop trailing sorry
  statement_matches   -- normalized containment check (artifact contains statement)
  refutation_matches  -- containment of refutation_statement (or ¬ + proposition)
  _compute_closures   -- pure fixpoint over reduction-proved nodes; no I/O
  recompute_closures  -- _compute_closures + write-back to disk (used by grant_status)
  grant_status        -- the gate: flip open -> proved/refuted, raise GateError on fail
  verify_campaign     -- full invariant battery (read-only); returns VerifyReport
"""
from __future__ import annotations

import dataclasses
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional

from .attempts import AttemptLog
from .claims import is_stale, load_claims
from .coverage import (
    artifact_coverage_error,
    ci_built_islands,
    ci_covered_lean_files,
    islands_with_lean,
)
from .provenance import (
    ProvenanceError,
    build_grant,
    comparator_staleness,
    grant_digest_errors,
    readback_is_self_audit,
    require_identity,
    required_ci_problem,
)
from .registry import Campaign, load_campaign
from .schema import Node, SchemaError, save_node, slug_of
from .statements import _SENTINEL, regen_diff, statement_path


# ---------------------------------------------------------------------------
# GateError
# ---------------------------------------------------------------------------

class GateError(Exception):
    """The verify gate rejected a status flip; node is left unchanged."""


# ---------------------------------------------------------------------------
# VerifyReport
# ---------------------------------------------------------------------------

@dataclass
class VerifyReport:
    errors: List[str]
    warnings: List[str]

    @property
    def ok(self) -> bool:
        return len(self.errors) == 0


# ---------------------------------------------------------------------------
# normalize_lean
# ---------------------------------------------------------------------------


def _repo_root(campaign_root: Path) -> Path:
    """Repository root from a campaign root (`<repo>/telperion/missions/<campaign>`)."""
    return Path(campaign_root).resolve().parents[2]

def _strip_lean_comments(text: str) -> str:
    """Single-pass comment stripper in Lean lexing order.

    Handles `--` line comments, NESTED `/- ... -/` block comments (Lean 4
    block comments nest — and `/--` doc comments open a block, so stripping
    line comments first would mutilate the opener and leave prose residue;
    that exact bug broke containment on the 2026-09-16 grant pre-flight),
    and double-quoted string literals (comment markers inside strings are
    inert). An unterminated block comment swallows the rest of the text,
    matching Lean's own lexer.
    """
    out = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == "-" and text[i:i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif ch == "/" and text[i:i + 2] == "/-":
            depth = 1
            i += 2
            while i < n and depth:
                if text[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                elif text[i:i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif ch == '"':
            out.append(ch)
            i += 1
            while i < n:
                out.append(text[i])
                if text[i] == "\\" and i + 1 < n:
                    out.append(text[i + 1])
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def normalize_lean(text: str) -> str:
    """Strip Lean comments, collapse whitespace, drop trailing := by sorry / := sorry."""
    text = _strip_lean_comments(text)
    # Collapse all whitespace runs to a single space
    text = re.sub(r"\s+", " ", text).strip()
    # Drop trailing := by sorry or := sorry
    text = re.sub(r":=\s*by\s+sorry$", "", text).strip()
    text = re.sub(r":=\s*sorry$", "", text).strip()
    return text


# ---------------------------------------------------------------------------
# artifact_incompleteness_markers
# ---------------------------------------------------------------------------

#: Tokens that mean "this Lean is not a finished proof". `native_decide` is included
#: because it discharges a goal through the compiler rather than the kernel, which is
#: outside the trust story every campaign doc claims.
_INCOMPLETE_TOKENS = ("sorry", "admit", "native_decide")

#: Keywords that let an artifact ASSUME what it claims to prove. Audit 2026-09-19 granted a
#: node whose artifact read `axiom cheat : ...` / `theorem hard_thm := cheat n`.
#:
#: Until 2026-09-23 this was `^\s*(axiom|unsafe)\s`, i.e. line start only, so every
#: modifier form walked past it: `private axiom`, `protected axiom`, `noncomputable axiom`,
#: `@[simp] axiom`, `private unsafe def`, and (since Lean commands need no newline between
#: them) `theorem a : True := trivial axiom cheat : False` on one line. Both words are
#: reserved keywords in Lean 4, so they cannot occur as ordinary identifiers; matching the
#: bare keyword anywhere in comment-stripped code is exact, not heuristic. `#print axioms`
#: (the axiom guards' own idiom) does not trip it: `axioms` is a different word.
_ASSUMPTION_KEYWORD_RE = re.compile(r"(?<![\w'.])(axiom|unsafe)(?![\w'!?])")

#: Trust-boundary escapes: tokens that replace a kernel-checked term by something the kernel
#: never sees, or tell the kernel not to look (closure-run audit 2026-09-22, section 2b):
#:   opaque              -- a constant whose body the kernel never unfolds (and, with
#:                          `implemented_by`, whose runtime body is unrelated to its type)
#:   implemented_by      -- `@[implemented_by f]`: compiled code substituted for the def
#:   extern              -- `@[extern "c_fn"]`: compiled code is foreign C
#:   debug.skipKernelTC  -- `set_option debug.skipKernelTC true`: kernel type-check OFF
#:   ofReduceBool / ofReduceNat -- the axioms compiler reflection rests on (`native_decide`
#:                          elaborates to `Lean.ofReduceBool`); spelt directly they bypass
#:                          the `native_decide` token check above
#:   sorryAx             -- the term `sorry` elaborates to; spelt directly it bypasses the
#:                          `sorry` token check (closure-run finding C1: the scan returned
#:                          `[]` for it)
#: A qualified spelling (`Lean.ofReduceBool`) counts, so a preceding `.` is allowed here.
_TRUST_ESCAPE_TOKENS = (
    "opaque",
    "implemented_by",
    "extern",
    "debug.skipKernelTC",
    "ofReduceBool",
    "ofReduceNat",
    "sorryAx",
)


def artifact_incompleteness_markers(artifact_text: str) -> List[str]:
    """Return the incompleteness tokens genuinely present in a Lean artifact.

    Comments (line, nested block, doc) are stripped first via the same lexer-order stripper
    the containment check uses, so prose such as "no `sorry`" in a docstring does NOT count.
    String-literal CONTENTS are kept, not blanked: that stripper keeps them on purpose, and
    blanking them here would hide code inside interpolations (`s!"{sorry}"`,
    `throwError "{...}"`) and let a mis-lexed char literal `'"'` swallow real code. A token
    inside a plain string therefore counts; that errs toward refusing, never toward granting.
    No proved artifact carried one when this was checked (2026-09-23, 78 artifact files).

    WHY (audit 2026-09-18): `grant_status` checked only that the artifact CONTAINS the
    node's statement. It never asked whether the artifact PROVES it, so an artifact whose
    body was `:= by sorry` satisfied the gate. Worse, `normalize_lean` strips a trailing
    `:= by sorry` before comparison, which made a stub match more easily, not less.
    """
    code = _strip_lean_comments(artifact_text)
    found = [tok for tok in _INCOMPLETE_TOKENS
             if re.search(rf"(?<![\w.]){re.escape(tok)}(?![\w.])", code)]
    found += sorted({m.group(1) for m in _ASSUMPTION_KEYWORD_RE.finditer(code)})
    found += [tok for tok in _TRUST_ESCAPE_TOKENS
              if re.search(rf"(?<![\w']){re.escape(tok)}(?![\w'!?])", code)]
    return found


# ---------------------------------------------------------------------------
# _normalized_statement / statement_matches / refutation_matches
# ---------------------------------------------------------------------------

def _normalized_statement(node: Node, root: Path) -> str:
    """Derive the normalized proposition from the node's statement file.

    Per the controller ruling: read statement_path, skip leading blank lines,
    drop the header line iff it contains the DO-NOT-EDIT sentinel, drop
    import/open lines, normalize the remaining body.

    Falls back to the empty string (never to node.statement_module, which is
    a module name, not a proposition) if the statement file does not exist.
    Callers must treat an empty result as a gate error.
    """
    path = statement_path(root, node)
    if not path.exists():
        return ""

    text = path.read_text()
    lines = text.split("\n")

    # Skip leading blank lines, then drop first non-blank line iff it is the header
    non_blank_start = 0
    while non_blank_start < len(lines) and not lines[non_blank_start].strip():
        non_blank_start += 1
    if non_blank_start < len(lines) and _SENTINEL in lines[non_blank_start]:
        lines = lines[non_blank_start + 1:]
    else:
        lines = lines[non_blank_start:]

    # Drop import/open lines
    body_lines = [
        ln for ln in lines
        if not ln.strip().startswith("import ") and not ln.strip().startswith("open ")
    ]

    return normalize_lean("\n".join(body_lines))


#: what may follow a matched statement: the proof body, and nothing else
_PROOF_BODY_RE = re.compile(r"^\s*(:=|by\b)")


def _strip_string_literals(text: str) -> str:
    """Blank the contents of double-quoted literals.

    `_strip_lean_comments` preserves them on purpose (comment markers inside a string are
    inert), but for CONTAINMENT they are attacker-controlled text: audit 2026-09-19 granted
    a node whose statement appeared only inside a `String` literal in the artifact.
    """
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', text)


def statement_matches(artifact_text: str, node_statement: str) -> bool:
    """True iff the artifact DECLARES the node's statement and then proves it.

    Plain substring containment is not enough, and the failure is not exotic. The normalized
    statement ends at the conclusion, so an artifact that CONTINUES the conclusion still
    contains it: a node claiming `NoZero s` was granted against an artifact proving the
    strictly weaker `NoZero s \u2228 True` (audit 2026-09-19). So a match counts only when the
    text immediately after it begins the proof body (`:=` or `by`), which is exactly the
    point at which the statement has ended.
    """
    needle = normalize_lean(node_statement)
    if not needle:
        return False
    hay = normalize_lean(_strip_string_literals(artifact_text))
    start = hay.find(needle)
    while start != -1:
        if _PROOF_BODY_RE.match(hay[start + len(needle):]):
            return True
        start = hay.find(needle, start + 1)
    return False


def refutation_matches(artifact_text: str, node: Node, root: Path) -> bool:
    """Return True iff the artifact matches as a refutation.

    If node.refutation_statement is set: normalized containment of it in the artifact.
    Otherwise (fallback): artifact must contain both '¬' and the normalized
    proposition derived from the node's statement file (not the module name).
    """
    norm_artifact = normalize_lean(artifact_text)
    if node.refutation_statement:
        return normalize_lean(node.refutation_statement) in norm_artifact
    # Fallback: require ¬ and the proposition from the statement file
    norm_prop = _normalized_statement(node, root)
    if not norm_prop:
        return False
    return "¬" in norm_artifact and norm_prop in norm_artifact


# ---------------------------------------------------------------------------
# _compute_closures (pure) and recompute_closures (pure + write-back)
# ---------------------------------------------------------------------------



def compute_universe_closures(universe) -> Dict[tuple, bool]:
    """Global closure fixpoint across every campaign, keyed by (campaign, slug).

    Same rules as the single-campaign pass, but dependency edges may cross
    campaigns.  The result is cached on the universe as ``.closures`` so a
    single load serves every consumer.  Anything that does not resolve stays
    dirty; there is no path here that turns an unresolved edge clean.
    """
    from .registry import parse_dep

    closure: Dict[tuple, bool] = {}
    for cname, camp in universe.campaigns.items():
        for sl, node in camp.nodes.items():
            if node.proof is not None:
                closure[(cname, sl)] = node.proof.closure_clean

    changed = True
    while changed:
        changed = False
        for cname, camp in universe.campaigns.items():
            for sl, node in camp.nodes.items():
                if node.proof is None or node.proof.via != "reduction":
                    continue
                ok = True
                for dep in node.depends_on:
                    dcamp, dtarget = parse_dep(dep, cname)
                    tgt = universe.campaigns.get(dcamp)
                    tnode = tgt.nodes.get(dtarget) if tgt is not None else None
                    if (tnode is None or tnode.status != "proved"
                            or not closure.get((dcamp, dtarget), False)):
                        ok = False
                        break
                if ok != closure.get((cname, sl), False):
                    closure[(cname, sl)] = ok
                    changed = True

    try:
        universe.closures = closure
    except Exception:
        pass
    return closure


def _dep_is_clean(campaign, dep: str, closure: Dict[str, bool], universe=None) -> bool:
    """Is this dependency edge satisfied for closure purposes?

    THE ANTI-CASCADE RULE.  An edge counts only when its target genuinely
    resolves, is `proved`, and is itself closure-clean.  An EXTERNAL edge with
    no universe supplied, or one whose target does not resolve, is FALSE --
    never True.  A cross-campaign reference must not be able to launder an
    unverified premise into a clean closure, which is exactly the failure mode
    the 2026-09-18 registry audit demonstrated on a throwaway campaign.
    """
    from .registry import parse_dep

    home = campaign.root.name
    camp, target = parse_dep(dep, home)
    if camp == home:
        node = campaign.nodes.get(target)
        return node is not None and node.status == "proved" and closure.get(target, False)
    if universe is None:
        return False
    ext = universe.resolve(home, dep)
    if ext is None or ext.status != "proved":
        return False
    # NEVER fall back to the target's STORED closure_clean flag: a reduction
    # node's stored flag can say True while its own dependency chain is dirty,
    # which is precisely how transitive dirt would get laundered across a
    # campaign boundary.  Compute the global fixpoint instead (cached on the
    # universe), and treat anything unavailable as dirty.
    ext_closure = getattr(universe, "closures", None)
    if ext_closure is None:
        ext_closure = compute_universe_closures(universe)
    return bool(ext_closure.get((camp, target), False))


def _compute_closures(campaign: Campaign, universe=None) -> Dict[str, bool]:
    """Pure fixpoint: compute closure_clean for every node with a proof link.

    Rules, as the code below actually behaves:
    - A direct-proved node's STORED flag is authoritative and is never recomputed
      here.  It is not a derived fact about discharged hypotheses and must not be
      read as one.  An earlier version of this docstring claimed such a node "is
      always clean (True)"; the code deliberately does not do that, and the
      mismatch is why the real rule is spelled out.
    - A reduction-proved node is clean iff every depends_on target has
      status 'proved' AND its own closure is clean.  Only these are recomputed.
    - Nodes without proof: not included in result.

    Extending this fixpoint to direct proofs is ascent-plan ops F1-3/F1-4.  That
    changes what closure_clean means for every already-clean node, so it is an
    owner's decision and is deliberately not made here.

    Does NOT read or write any files. Uses only campaign.nodes as provided.
    Returns a dict mapping slug -> bool for every node that has a proof link.
    """
    closure: Dict[str, bool] = {}
    for sl, node in campaign.nodes.items():
        if node.proof is None:
            continue
        # Seed from the stored closure_clean flag for ALL via types.
        #
        # For direct proofs: the stored flag IS authoritative — grant_status
        # writes True for normal grants, but a controller ruling may leave it
        # False (e.g. cross-island artifacts whose kernel authority lives on
        # a different Lean island and has not yet been wired into this campaign's
        # CI).  We must not overwrite that deliberate False with an unconditional
        # True here.
        #
        # For reduction proofs: the fixpoint loop below will correct the stored
        # value based on the transitive dependency chain regardless.
        closure[sl] = node.proof.closure_clean

    # Fixpoint iteration until stable
    changed = True
    while changed:
        changed = False
        for sl, node in campaign.nodes.items():
            if node.proof is None or node.proof.via != "reduction":
                continue
            all_clean = all(
                _dep_is_clean(campaign, dep, closure, universe)
                for dep in node.depends_on
            )
            if all_clean != closure.get(sl, False):
                closure[sl] = all_clean
                changed = True

    return closure


def recompute_closures(campaign: Campaign) -> Dict[str, bool]:
    """Compute closure_clean flags and write any changes back to disk.

    Calls _compute_closures (pure), then saves nodes whose closure_clean flag
    changed. Updates campaign.nodes in place so callers see the new state.

    Returns the same dict as _compute_closures.
    """
    closure = _compute_closures(campaign)

    for sl, node in campaign.nodes.items():
        if node.proof is None:
            continue
        new_clean = closure.get(sl, node.proof.closure_clean)
        if new_clean != node.proof.closure_clean:
            new_proof = dataclasses.replace(node.proof, closure_clean=new_clean)
            new_node = dataclasses.replace(node, proof=new_proof)
            node_path = campaign.root / "nodes" / f"{sl}.toml"
            save_node(new_node, node_path)
            campaign.nodes[sl] = new_node

    return closure


# ---------------------------------------------------------------------------
# grant_status  -- THE GATE
# ---------------------------------------------------------------------------

def grant_status(campaign: Campaign, slug: str, universe=None, *,
                 identity: str = "", session: str = "") -> Node:
    """The ONLY code path that flips a node to proved or refuted.

    `identity` and `session` are who is running the gate (git identity, session id); both
    are required and are written into the node's `[grant]` block together with the artifact
    and statement digests (provenance, 2026-09-23). The gate also refuses a read-back whose
    structured auditor is the node's author.

    Preconditions checked (GateError raised if any fail, status left unchanged):
    1. Node must be open.
    2. Node must have a proof link (proof field set).
    3. Artifact file must exist at campaign.root / node.proof.artifact.
    4. Normalized statement must be non-empty (statement file must exist and
       contain a proposition beyond import/open lines).
    5. Artifact must match: statement_matches -> proved;
       only refutation_matches -> refuted; neither -> GateError.
    6. For a `via = "reduction"` proof ONLY: every depends_on target must
       already be `proved`.  A reduction's dependency edges are load-bearing --
       the proof IS the chain -- so granting one over a draft or open premise
       would assert something the registry has not established.  A `direct`
       proof is deliberately exempt: it stands on its own artifact and the gate
       that checked it, and its edges are documentary.  That asymmetry is why
       unsupported edges could accumulate for months without making any node
       falsely clean (see docs/CROSS_CAMPAIGN_EDGES_2026-09-19.md).

    After flipping, recompute_closures is run on the campaign.

    Returns the updated Node.
    """
    node = campaign.nodes.get(slug)
    if node is None:
        raise GateError(f"Node {slug!r} not found in campaign.")

    try:
        require_identity(identity, session, "grant")
    except ProvenanceError as exc:
        raise GateError(str(exc)) from exc

    if node.status != "open":
        raise GateError(
            f"Node {slug!r} has status {node.status!r}; "
            "grant_status only operates on open nodes."
        )

    if node.proof is None:
        raise GateError(
            f"Node {slug!r} has no proof link; call set_proof first."
        )

    artifact_path = campaign.root / node.proof.artifact
    if not artifact_path.exists():
        raise GateError(
            f"Node {slug!r}: artifact file {artifact_path} does not exist."
        )

    artifact_text = artifact_path.read_text()

    # Derive normalized statement from the statement file
    norm_stmt = _normalized_statement(node, campaign.root)
    if not norm_stmt:
        raise GateError(
            f"Node {slug!r}: normalized statement is empty — statement file "
            "may be missing or contain only import/open lines."
        )

    # The statement file must still be the one the node describes. `regen_diff` is checked
    # by the read-only battery, but it was NOT checked here, so a hand-edited statement (with
    # its self-computed header hash re-forged, which costs nothing) could be granted against.
    drift = regen_diff(campaign.root, node, campaign.manifest)
    if drift:
        raise GateError(
            f"Node {slug!r}: statement file does not match the node ({drift}); "
            "refusing to grant against a drifted statement."
        )

    # A readback is required for draft -> open, but nothing re-checked it at grant time, so a
    # node set to `open` by hand could be granted with no read-back on record at all.
    if node.readback is None:
        raise GateError(
            f"Node {slug!r}: no read-back on record; refusing to grant. Run "
            "`mission audit` with an independent read-back first."
        )
    # A read-back written by the author's own session or identity is exactly the testimony
    # this gate must not rest on (governance 2026-09-23). `mission audit` refuses to write
    # one, so reaching this means the file was edited by hand; refuse all the same.
    if readback_is_self_audit(node):
        raise GateError(
            f"Node {slug!r}: the read-back's auditor is the node's author "
            f"(session {node.readback.auditor_session!r}, identity "
            f"{node.readback.auditor_identity!r}); a self-audit cannot support a grant. "
            "Obtain a read-back from a different session and identity."
        )

    # These two are paid by BOTH outcomes. Until 2026-09-19 they guarded only the `proved`
    # branch, so a node could be flipped to `refuted` against an artifact carrying `sorry`
    # in an island CI never builds -- and a false `refuted` on an RH node is as loud a claim
    # as a false `proved`.
    markers = artifact_incompleteness_markers(artifact_text)
    if markers:
        raise GateError(
            f"Node {slug!r}: artifact {node.proof.artifact!r} carries "
            f"{', '.join(markers)} in Lean code; refusing to grant against an "
            "unfinished artifact."
        )
    cov = artifact_coverage_error(artifact_path, _repo_root(campaign.root))
    if cov:
        raise GateError(f"Node {slug!r}: {cov}")
    # Owner ruling 2026-09-24: a node may name a non-required CI job whose passing run on the
    # exact artifact digest is a precondition for granting.
    ci = required_ci_problem(campaign.root, node)
    if ci:
        raise GateError(f"Node {slug!r}: {ci}")

    stmt_ok = statement_matches(artifact_text, norm_stmt)
    refut_ok = refutation_matches(artifact_text, node, campaign.root)

    if stmt_ok:
        new_status = "proved"
    elif refut_ok:
        new_status = "refuted"
    else:
        raise GateError(
            f"Node {slug!r}: artifact does not contain the node's statement "
            f"or refutation. Normalized statement: {norm_stmt!r}"
        )

    # 6. A reduction proof may not be granted over an unproved premise.
    if node.proof.via == "reduction":
        from .registry import parse_dep
        home = campaign.root.name
        uni = universe if universe is not None else _autoload_universe(campaign.root)
        for dep in node.depends_on:
            dcamp, dtarget = parse_dep(dep, home)
            if dcamp == home:
                target_node = campaign.nodes.get(dtarget)
            else:
                target_node = uni.resolve(home, dep) if uni is not None else None
            if target_node is None:
                raise GateError(
                    f"Node {slug!r}: reduction proof depends on {dep!r}, which does "
                    f"not resolve. A reduction may not be granted over an "
                    f"unresolvable premise."
                )
            if target_node.status != "proved":
                raise GateError(
                    f"Node {slug!r}: reduction proof depends on {dep!r}, whose status "
                    f"is {target_node.status!r}, not 'proved'. A reduction may not be "
                    f"granted over an unproved premise."
                )

    # Flip the status.
    #
    # This writes closure_clean as a copy of status, so a grant turns a stored False
    # into True.  That laundered a real ruling in the live corpus: the read-back on
    # MM_bragg_defect_witness says its off-line leg "CARRIES the Arb
    # exponential-enclosure hypothesis, hence closure_clean = false until that
    # enclosure is itself reflected", and the stored flag read True because granting
    # wrote it.
    #
    # It cannot be repaired here, and I tried.  Nodes are authored with
    # closure_clean = False, so "preserve a stored False" leaves EVERY first-time
    # grant dirty; there is no way to tell a deliberate False from a default one
    # without a field that records the ruling.  That field is ascent-plan op
    # F1-3/F1-4's closure_override_reason, an owner's decision.  Until then a
    # deliberate dirty flag is set by hand AFTER granting, and it survives, because
    # _compute_closures treats a direct proof's stored flag as authoritative.
    new_proof = dataclasses.replace(node.proof, closure_clean=(new_status == "proved"))
    # The [grant] block: digests of the artifact and statement THIS gate run checked, the
    # gate's rule-set version, and who ran it. `verify` recomputes the digests from disk.
    grant = build_grant(campaign.root, node, identity=identity, session=session)
    new_node = dataclasses.replace(node, status=new_status, proof=new_proof, grant=grant)
    node_path = campaign.root / "nodes" / f"{slug}.toml"
    save_node(new_node, node_path)
    campaign.nodes[slug] = new_node

    # Update closure flags across the campaign
    recompute_closures(campaign)

    return campaign.nodes[slug]


# ---------------------------------------------------------------------------
# verify_campaign  -- READ-ONLY audit battery
# ---------------------------------------------------------------------------


def _autoload_universe(root: Path):
    """Best-effort: load the sibling campaigns so external edges can resolve.

    Returns None if the siblings cannot be loaded for any reason, which leaves
    every external edge dirty -- the safe direction.
    """
    try:
        from .registry import load_universe
        return load_universe(Path(root).parent)
    except Exception:
        return None


def verify_campaign(
    root: Path,
    deep_lean: bool = False,
    runner: Optional[Callable] = None,
    universe=None,
) -> VerifyReport:
    """Full invariant battery (read-only). Returns VerifyReport(errors, warnings, ok).

    Does NOT mutate any files. Uses _compute_closures (pure) to check closure
    coherence against the stored flags as they exist on disk.

    Checks (errors unless noted as warnings):
    1. Schema: load_campaign parses all node/manifest files and checks acyclicity.
    2. Status coherence for proved/refuted nodes:
       a. Artifact file exists.
       b. statement or refutation matches.
       c. Closure flags consistent with a fresh _compute_closures result
          (compares against stored values; does NOT repair them).
    3. regen_diff clean for every node that has a statement file.
    4. Claims hygiene (WARNINGS): stale claims; claims on non-open nodes.
    5. Attempts ledger parses (errors on parse failure).
    6. Every deprecated node has a reason (caught by schema load).
    7. deep_lean: runs `lake build` in root/lean (never in unit tests — inject runner).
    """
    root = Path(root)
    errors: List[str] = []
    warnings: List[str] = []

    # 1. Schema load + acyclicity
    try:
        campaign = load_campaign(root)
    except SchemaError as exc:
        errors.append(f"Schema error: {exc}")
        return VerifyReport(errors=errors, warnings=warnings)

    manifest = campaign.manifest

    # Compute fresh closure flags WITHOUT writing to disk (read-only audit)
    # Cross-campaign edges resolve only when a universe is supplied.  Without
    # one, an external edge is treated as dirty, so the battery can warn but
    # never certify an external dependency as satisfied.
    if universe is None:
        universe = _autoload_universe(root)
    fresh_closures = _compute_closures(campaign, universe)

    # Build coverage: which example islands does CI actually run `lake build` in?
    # Computed once per campaign -- it parses every workflow file.
    repo_root = _repo_root(root)
    built_islands = ci_built_islands(repo_root)
    # ...and, per file, is the artifact MODULE itself inside what a runnable step compiles?
    # (closure audit C2: an island-level text match of `lake build` let six nodes rest on a
    # job that named nonexistent targets and could not run.)
    covered_files = ci_covered_lean_files(repo_root)

    # 2. Status coherence for proved/refuted nodes
    for sl, node in campaign.nodes.items():
        if node.status not in ("proved", "refuted"):
            continue

        # 2a. Artifact must exist
        if node.proof is None:
            errors.append(f"Node {sl!r}: status is {node.status!r} but proof is None.")
            continue

        artifact_path = root / node.proof.artifact
        if not artifact_path.exists():
            errors.append(
                f"Node {sl!r}: status is {node.status!r} but artifact "
                f"{node.proof.artifact!r} does not exist."
            )
            continue

        artifact_text = artifact_path.read_text()

        # 2b. Statement / refutation match
        norm_stmt = _normalized_statement(node, root)
        # Same predicate as the gate: a match must land on a declaration that is then
        # proved, not merely appear somewhere in the file.
        stmt_ok = bool(norm_stmt) and statement_matches(artifact_text, norm_stmt)
        refut_ok = refutation_matches(artifact_text, node, root)

        if node.status == "proved" and not stmt_ok:
            errors.append(
                f"Node {sl!r}: status is 'proved' but artifact does not "
                f"contain the normalized statement."
            )
        elif node.status == "proved":
            markers = artifact_incompleteness_markers(artifact_text)
            if markers:
                errors.append(
                    f"Node {sl!r}: status is 'proved' but artifact "
                    f"{node.proof.artifact!r} carries {', '.join(markers)} in Lean code."
                )
            cov = artifact_coverage_error(artifact_path, repo_root, built_islands, covered_files)
            if cov:
                errors.append(f"Node {sl!r}: status is 'proved' but {cov}")
        elif node.status == "refuted" and not refut_ok:
            errors.append(
                f"Node {sl!r}: status is 'refuted' but artifact does not "
                f"match refutation criteria."
            )

        # 2e. Provenance (2026-09-23). A [grant] block pins the artifact and statement the
        # gate saw; if either file has changed since, the status rests on unchecked evidence.
        for err in grant_digest_errors(root, node):
            errors.append(f"Node {sl!r}: {err}")
        # A read-back whose structured auditor is the node's author can never support a
        # proved status. Legacy read-backs (no structured fields) are `unverified`, which
        # `mission provenance-report` lists; they are not errors here.
        if node.status == "proved" and readback_is_self_audit(node):
            errors.append(
                f"Node {sl!r}: status is 'proved' but its read-back is a self-audit "
                f"(auditor session/identity matches the [author] block)."
            )
        stale = comparator_staleness(root, node)
        if stale:
            warnings.append(f"Node {sl!r}: {stale}")
        ci = required_ci_problem(root, node)
        if ci and node.status == "proved":
            errors.append(f"Node {sl!r}: status is 'proved' but it {ci}")

        # 2c. Closure flag coherence: compare STORED flag vs freshly computed
        if node.proof.via == "reduction":
            expected_clean = fresh_closures.get(sl, False)
            # node.proof.closure_clean is the stored (unmodified) value
            if node.proof.closure_clean != expected_clean:
                errors.append(
                    f"Node {sl!r}: stored closure_clean={node.proof.closure_clean} "
                    f"but recomputed value={expected_clean}."
                )

    # 2d. Orphan islands (WARNING, not an error): Lean in the tree that no workflow builds.
    # Only a *proved node* pointing into one is an error (checked above). An island with no
    # node attached is scratch or in-flight work, and failing the battery on it would turn
    # this check into an allowlist that rots. Surfacing it is what stops it quietly becoming
    # a granted artifact later -- which is exactly how zeta_reflection got six.
    orphans = sorted(islands_with_lean(repo_root) - built_islands)
    if orphans:
        warnings.append(
            f"Example islands with Lean sources that no CI workflow builds ({len(orphans)}): "
            f"{', '.join(orphans)}. Lean there is unverified until some job runs `lake build` "
            "in it, and no node may be granted against it."
        )

    # 3. regen_diff for every node with a statement file
    for sl, node in campaign.nodes.items():
        sp = statement_path(root, node)
        if sp.exists():
            diff = regen_diff(root, node, manifest)
            if diff:
                errors.append(f"Statement file drift: {diff}")

    # 4. Claims hygiene (WARNINGS)
    all_claims = load_claims(root)
    for claim_slug, claim_obj in all_claims.items():
        if is_stale(claim_obj):
            warnings.append(
                f"Stale claim on node {claim_slug!r} by session "
                f"{claim_obj.session!r}."
            )
        node = campaign.nodes.get(claim_slug)
        if node is not None and node.status != "open":
            warnings.append(
                f"Claim on non-open node {claim_slug!r} "
                f"(status: {node.status!r})."
            )

    # 5. Attempts ledger (if it exists)
    ledger_path = root / "attempts.jsonl"
    if ledger_path.exists():
        log = AttemptLog(ledger_path)
        try:
            log.records()
            # A malformed line anywhere is skipped so one bad record cannot crash the
            # loader, but skipping it silently means a session's recorded work simply
            # disappears from the ledger. Surface the count.
            skipped = getattr(log, "skipped_lines", 0)
            if skipped:
                warnings.append(
                    f"Attempts ledger: {skipped} malformed line(s) skipped in "
                    f"{ledger_path.name}; those attempts are absent from every digest."
                )
        except Exception as exc:
            errors.append(f"Attempts ledger parse error: {exc}")

    # 7. deep_lean: run lake build (only when explicitly requested)
    if deep_lean:
        lean_dir = root / "lean"
        _runner = runner if runner is not None else subprocess.run
        try:
            result = _runner(
                ["lake", "build"],
                cwd=str(lean_dir),
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                errors.append(
                    f"lake build failed (exit {result.returncode}): "
                    f"{result.stderr.strip()}"
                )
        except Exception as exc:
            errors.append(f"lake build error: {exc}")

    return VerifyReport(errors=errors, warnings=warnings)

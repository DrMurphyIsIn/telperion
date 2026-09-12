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

def normalize_lean(text: str) -> str:
    """Strip Lean comments, collapse whitespace, drop trailing := by sorry / := sorry.

    Block comments (/- ... -/) are handled non-nestedly (sufficient for our
    artifact matching use-case; nested block comments in Lean 4 are legal but
    the payloads we deal with don't use them).
    """
    # Remove -- single-line comments (rest of line)
    text = re.sub(r"--[^\n]*", "", text)
    # Remove /- ... -/ block comments (non-greedy, non-nested)
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    # Collapse all whitespace runs to a single space
    text = re.sub(r"\s+", " ", text).strip()
    # Drop trailing := by sorry or := sorry
    text = re.sub(r":=\s*by\s+sorry$", "", text).strip()
    text = re.sub(r":=\s*sorry$", "", text).strip()
    return text


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


def statement_matches(artifact_text: str, node_statement: str) -> bool:
    """Return True iff normalize_lean(artifact_text) contains normalize_lean(node_statement)."""
    return normalize_lean(node_statement) in normalize_lean(artifact_text)


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

def _compute_closures(campaign: Campaign) -> Dict[str, bool]:
    """Pure fixpoint: compute closure_clean for every node with a proof link.

    Rules:
    - A direct-proved node's closure is always clean (True).
    - A reduction-proved node is clean iff every depends_on target has
      status 'proved' AND its own closure is clean.
    - Nodes without proof: not included in result.

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
                dep in campaign.nodes
                and campaign.nodes[dep].status == "proved"
                and closure.get(dep, False)
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

def grant_status(campaign: Campaign, slug: str) -> Node:
    """The ONLY code path that flips a node to proved or refuted.

    Preconditions checked (GateError raised if any fail, status left unchanged):
    1. Node must be open.
    2. Node must have a proof link (proof field set).
    3. Artifact file must exist at campaign.root / node.proof.artifact.
    4. Normalized statement must be non-empty (statement file must exist and
       contain a proposition beyond import/open lines).
    5. Artifact must match: statement_matches -> proved;
       only refutation_matches -> refuted; neither -> GateError.

    After flipping, recompute_closures is run on the campaign.

    Returns the updated Node.
    """
    node = campaign.nodes.get(slug)
    if node is None:
        raise GateError(f"Node {slug!r} not found in campaign.")

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

    norm_artifact = normalize_lean(artifact_text)
    stmt_ok = norm_stmt in norm_artifact
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

    # Flip the status
    new_proof = dataclasses.replace(node.proof, closure_clean=(new_status == "proved"))
    new_node = dataclasses.replace(node, status=new_status, proof=new_proof)
    node_path = campaign.root / "nodes" / f"{slug}.toml"
    save_node(new_node, node_path)
    campaign.nodes[slug] = new_node

    # Update closure flags across the campaign
    recompute_closures(campaign)

    return campaign.nodes[slug]


# ---------------------------------------------------------------------------
# verify_campaign  -- READ-ONLY audit battery
# ---------------------------------------------------------------------------

def verify_campaign(
    root: Path,
    deep_lean: bool = False,
    runner: Optional[Callable] = None,
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
    fresh_closures = _compute_closures(campaign)

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
        norm_artifact = normalize_lean(artifact_text)
        stmt_ok = bool(norm_stmt) and norm_stmt in norm_artifact
        refut_ok = refutation_matches(artifact_text, node, root)

        if node.status == "proved" and not stmt_ok:
            errors.append(
                f"Node {sl!r}: status is 'proved' but artifact does not "
                f"contain the normalized statement."
            )
        elif node.status == "refuted" and not refut_ok:
            errors.append(
                f"Node {sl!r}: status is 'refuted' but artifact does not "
                f"match refutation criteria."
            )

        # 2c. Closure flag coherence: compare STORED flag vs freshly computed
        if node.proof.via == "reduction":
            expected_clean = fresh_closures.get(sl, False)
            # node.proof.closure_clean is the stored (unmodified) value
            if node.proof.closure_clean != expected_clean:
                errors.append(
                    f"Node {sl!r}: stored closure_clean={node.proof.closure_clean} "
                    f"but recomputed value={expected_clean}."
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

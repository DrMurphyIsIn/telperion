"""The Telperion MCP server: the certify/validate/emit workflow as agent tools.

Run with:  telperion-mcp   (requires `pip install "telperion[mcp]"`)

Register in Claude Code:
  claude mcp add telperion -- telperion-mcp

Tools mirror the enforced workflow — there is no emit tool that skips
certification or validation.  `certify_family`/`emit_family` import the family
module the caller names: point this server only at projects you trust, exactly
as you would an editor or test runner.

The transcendental-free rule holds: every tool answers from exact arithmetic;
nothing here trusts floats or asserts truth — the Lean kernel downstream does.
"""
from __future__ import annotations

import io
import json
from contextlib import redirect_stdout
from pathlib import Path

try:
    from mcp.server.fastmcp import FastMCP
except ImportError as e:  # pragma: no cover
    raise SystemExit(
        'the MCP server needs the optional extra:  pip install "telperion[mcp]"'
    ) from e

mcp = FastMCP(
    "telperion",
    instructions=(
        "Telperion certifies families of rational-function inequalities in "
        "sympy and batch-emits kernel-checked Lean 4. Workflow (enforced): "
        "define a family module -> certify_family -> emit_family (requires the "
        "module to define validation()) -> compile the emitted Lean in the "
        "project's CI -> diff_family to detect drift. Use polya_probe first to "
        "test whether a single inequality is certifiable at all. A refusal "
        "names the failing (grid point, corner) — fix the family, never the "
        "emitted Lean."
    ),
)


def _cli(args: list[str]) -> tuple[int, str]:
    from .cli import main

    buf = io.StringIO()
    with redirect_stdout(buf):
        try:
            code = main(args)
        except SystemExit as e:
            code = int(e.code) if e.code is not None else 0
    return code, buf.getvalue()


@mcp.tool()
def polya_probe(expression: str, symbols: str = "u") -> str:
    """Test whether a single rational expression in nonnegative symbols has a
    Polya certificate (all-nonneg-integer numerator / positive-factored
    denominator). expression: sympy syntax, e.g. '(1 + u)/(2 + u) - 1/(u + 3)'.
    symbols: comma-separated, e.g. 'u,v'. Returns the certificate or the
    refusal reason."""
    code, out = _cli(["probe", expression, "--symbols", symbols])
    return out.strip() or f"exit {code}"


@mcp.tool()
def diagnose(target: str, symbols: str = "u", trials: int = 400) -> str:
    """Triage a refused inequality: distinguishes FALSE (returns an exact
    rational counterexample — a proof of falsity), NOT_POLYA_IN_THIS_FORM
    (with remedy hints naming the negative monomials and cheap
    transformations), and CERTIFIABLE. target: 'path/to/family.py:factory'
    to triage every failing instance of a family, or a raw sympy expression
    with the symbols argument."""
    args = ["diagnose", target, "--symbols", symbols, "--trials", str(trials)]
    code, out = _cli(args)
    return out.strip() or f"exit {code}"


@mcp.tool()
def certify_family(family: str) -> str:
    """Run every symbolic self-check for a family. family: 'path/to/family.py:factory'
    where factory() returns an InequalityFamily. Returns the green summary or
    the refusal listing every failing (grid point, reason)."""
    code, out = _cli(["certify", family])
    return out.strip() or f"exit {code}"


@mcp.tool()
def emit_family(
    family: str,
    out_dir: str,
    profile: str = "",
    validation: str = "",
    file_name: str = "",
) -> str:
    """Certify, validate, and emit a family to provenance-stamped Lean files in
    out_dir. Requires validation: either the family module defines
    validation() -> ValidationReport, or pass validation='path.py:fn'.
    profile: optional 'path.py:factory' for the LeanProfile (namespace,
    imports, prelude, tactic-skeleton overrides)."""
    args = ["emit", family, "-o", out_dir]
    if profile:
        args += ["--profile", profile]
    if validation:
        args += ["--validation", validation]
    if file_name:
        args += ["--file-name", file_name]
    code, out = _cli(args)
    return out.strip() or f"exit {code}"


@mcp.tool()
def diff_family(
    family: str, frozen_dir: str, profile: str = "", validation: str = ""
) -> str:
    """Regenerate a family in memory and byte-compare against its frozen
    output (the reviewer's drift check). Returns OK or the drift details."""
    args = ["diff", family, "--frozen", frozen_dir]
    if profile:
        args += ["--profile", profile]
    if validation:
        args += ["--validation", validation]
    code, out = _cli(args)
    return out.strip() or f"exit {code}"


@mcp.tool()
def init_project(directory: str, namespace: str = "MyProof") -> str:
    """Scaffold a new Telperion proof project in an empty directory: family
    template with the validation discipline built in, generate script, drift
    manifest, pinned Lean/Mathlib project shell, and a lean-verify GitHub
    workflow. namespace must be an UpperCamel Lean module name."""
    code, out = _cli(["init", directory, "--namespace", namespace])
    return out.strip() or f"exit {code}"


@mcp.tool()
def verify_project(manifest: str = "telperion.toml", group: str = "all") -> str:
    """Run every check in the project manifest (regeneration diffs for all
    frozen families; fails on unlisted generate scripts). group: quick |
    heavy | all."""
    code, out = _cli(["verify", "--manifest", manifest, "--group", group])
    return out.strip() or f"exit {code}"


@mcp.tool()
def read_manifest(frozen_dir: str) -> str:
    """Read a frozen directory's provenance manifest (family, input hash,
    tool version, files, theorem count)."""
    p = Path(frozen_dir) / "manifest.json"
    if not p.exists():
        return f"no manifest at {p}"
    return json.dumps(json.loads(p.read_text()), indent=2)


@mcp.resource("telperion://tactic-contract")
def tactic_contract() -> str:
    """The exact Mathlib tactic assumptions of the default templates."""
    doc = Path(__file__).resolve().parents[2] / "docs" / "TACTIC_CONTRACT.md"
    return doc.read_text() if doc.exists() else "TACTIC_CONTRACT.md not found"


@mcp.resource("telperion://methodology")
def methodology() -> str:
    """The trust model and the numeric-first discipline."""
    doc = Path(__file__).resolve().parents[2] / "docs" / "METHODOLOGY.md"
    return doc.read_text() if doc.exists() else "METHODOLOGY.md not found"


def main() -> None:  # entry point: telperion-mcp
    mcp.run()


if __name__ == "__main__":
    main()

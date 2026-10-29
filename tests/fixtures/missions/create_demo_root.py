"""One-shot script to create the demo_root fixture: a miniature telperion root with one proved campaign.

Run from the telperion/ directory:
    python3 tests/fixtures/missions/create_demo_root.py

`demo/` (create_demo.py) is a registry-only campaign: no node is proved and nothing lives on an island. The
re-judge and nanoda-direct tests need the other shape -- proved nodes whose artifacts sit on an example island,
carrying current [rejudge] records -- so this fixture is laid out like a checkout:

    demo_root/examples/demo_island/lean/   the island (lakefile.toml, lean-toolchain, one artifact per node)
    demo_root/missions/demo_proved/        the campaign (mission.toml, nodes/, lean/Statements/)

Every statement is a toy arithmetic fact. The four nodes cover the four second-kernel shapes `mission verify`
distinguishes:

    Demo_add     judged Lean-kernel-only (a [comparator] record with second_kernel = "none: ..."), no
                 heavy_certificates flag, a passing Comparator-route re-judge
    Demo_direct  marked second_kernel_route = "nanoda-direct", with a passing nanoda-direct re-judge
    Demo_heavy   heavy_certificates + judge_via = "heavy", marked "comparator", no [comparator] record,
                 a passing Comparator-route re-judge
    Demo_nanoda  judged with nanoda on (second_kernel = "nanoda"): no re-judge needed, none recorded

Every [rejudge] record is bound to the artifact and closure digests as they are on disk, so a fresh copy of
the campaign passes the re-judge checks; re-run this script after editing any island file.
"""
import dataclasses
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "src"))

from telperion.missions.provenance import closure_digest, closure_files, sha256_file  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    ComparatorRecord, MissionManifest, Node, Proof, RejudgeRecord, save_manifest, save_node,
)
from telperion.missions.statements import write_statement  # noqa: E402

ROOT = Path(__file__).parent / "demo_root"
ISLAND = ROOT / "examples" / "demo_island" / "lean"
CAMPAIGN = ROOT / "missions" / "demo_proved"
DATE = "2026-10-28"

# slug -> (module, theorem, statement)
NODES = {
    "Demo_add": ("DemoAdd", "demo_add", "1 + 1 = 2"),
    "Demo_direct": ("DemoDirect", "demo_direct", "2 + 2 = 4"),
    "Demo_heavy": ("DemoHeavy", "demo_heavy", "3 + 3 = 6"),
    "Demo_nanoda": ("DemoNanoda", "demo_nanoda", "4 + 4 = 8"),
}


def _rejudge(node: Node, route: str) -> RejudgeRecord:
    return RejudgeRecord(date=DATE, machine="demo", nanoda_rev="f" * 40, comparator_tag="v4.32.0",
                         artifact_sha256=sha256_file(CAMPAIGN / node.proof.artifact), verdict="pass",
                         log_sha256="c" * 64, closure_sha256=closure_digest(CAMPAIGN, node),
                         closure_files=len(closure_files(CAMPAIGN, node)), route=route,
                         note="synthetic fixture record (create_demo_root.py)")


def _comparator(node: Node, second_kernel: str) -> ComparatorRecord:
    return ComparatorRecord(run_id="1", date=DATE, artifact_sha256=sha256_file(CAMPAIGN / node.proof.artifact),
                            theorem=NODES[node.name.replace(".", "_", 1)][1], second_kernel=second_kernel)


def main():
    shutil.rmtree(ROOT, ignore_errors=True)
    ISLAND.mkdir(parents=True)
    libs = "".join(f'\n[[lean_lib]]\nname = "{m}"\n' for m, _t, _s in NODES.values())
    targets = ", ".join(f'"{m}"' for m, _t, _s in NODES.values())
    (ISLAND / "lakefile.toml").write_text(f'name = "DemoIsland"\ndefaultTargets = [{targets}]\n{libs}')
    (ISLAND / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
    for module, thm, stmt in NODES.values():
        (ISLAND / f"{module}.lean").write_text(f"theorem {thm} : {stmt} := rfl\n")

    (CAMPAIGN / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="DemoProved.goal", title="Demo Proved Campaign",
        description="A synthetic campaign whose proved nodes live on an example island.",
        goal_node="Demo_add", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, CAMPAIGN / "mission.toml")

    def base(slug: str, **kw) -> Node:
        module, thm, stmt = NODES[slug]
        node = Node(name=slug.replace("_", ".", 1), title=f"Demo: {stmt}", kind="lemma", status="proved",
                    depends_on=(), statement_module=f"Statements.{slug}",
                    proof=Proof(f"../../examples/demo_island/lean/{module}.lean", "lean_module", "direct"),
                    created=DATE, updated=DATE, **kw)
        write_statement(CAMPAIGN, node, f"import Mathlib\ntheorem {thm} : {stmt}", manifest)
        return node

    add = base("Demo_add")
    add = dataclasses.replace(add, comparator=_comparator(add, "none: heavy_certificates"))
    save_node(dataclasses.replace(add, rejudge=_rejudge(add, "comparator")), CAMPAIGN / "nodes" / "Demo_add.toml")

    direct = base("Demo_direct", second_kernel_route="nanoda-direct")
    save_node(dataclasses.replace(direct, rejudge=_rejudge(direct, "nanoda-direct")),
              CAMPAIGN / "nodes" / "Demo_direct.toml")

    heavy = base("Demo_heavy", heavy_certificates=True, judge_via="heavy", second_kernel_route="comparator")
    save_node(dataclasses.replace(heavy, rejudge=_rejudge(heavy, "comparator")),
              CAMPAIGN / "nodes" / "Demo_heavy.toml")

    nanoda = base("Demo_nanoda")
    save_node(dataclasses.replace(nanoda, comparator=_comparator(nanoda, "nanoda")),
              CAMPAIGN / "nodes" / "Demo_nanoda.toml")

    print("demo_root fixture written to", ROOT)


if __name__ == "__main__":
    main()

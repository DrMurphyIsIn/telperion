# Step 4: The AXLE-inspired Checks, Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the four spec 5.2 checks:
- a kernel-rejection verdict;
- a negation probe;
- a statement fingerprint;
- closure-audit gating.

Each check has a must-fail and a must-pass test. They are wired into the missions grant through one `[checks]` record, and
apply to NEW grants only.

**Architecture:**
- Build on what exists rather than duplicating it:
  - `verify.py`'s error-block parser gains a kernel classification;
  - `closure_audit.py` and the `telperion audit-closure` CLI already deliver the closure audit (#4), including the
    transitive closure, the allowed axioms, and the absent constants and modules;
  - `statement_match.py` (signature match) and `nonvacuity.py` (reflexive statements) stay as they are.
- New modules under `src/telperion/checks/`:
  - `negation_probe.py`, two Lean probes;
  - `fingerprint.py`, a delta-unfolded, binder-name-insensitive statement hash computed by a Lean metaprogram.
- One record, `[checks]`, written by `mission checks-record`, gates `grant_status` for nodes created on or after the
  cutoff date `2026-10-28`. Older nodes are `pre-process` (spec 7).

**Tech Stack:** Python 3.11+, Lean 4 metaprogramming (`CoreM` / `MetaM` `#eval`), pytest, GitHub Actions. Repo:
`~/telperion-repo`.

**Spec:** `docs/superpowers/specs/2026-10-27-telperion-standalone-design.md`, section 5.2 and rollout step 4. The negation
probe's limit is stated in the spec: it is one-sided. Failing to find `False` proves nothing. The verdict is therefore
`VACUOUS`, `REFUTED` or `PROBE_ONLY`, never "consistent".

## Global Constraints

- Lean runs go through `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`. Never `lake update`. Never a shared packagesDir.
- Lean-dependent tests:
  - They are skipped unless `TELPERION_LEAN_ENV` points at a BUILT Lake project with Mathlib, as checked by
    `tests/lean_env.py::lean_env_ready`.
  - Task 6 adds a CI job that builds such an env, so the must-fail controls actually run in CI.
  - For local runs, the implementer builds `~/telperion-tools/lean-env`, using Lean v4.35.0, Mathlib `lake exe cache get`,
    and leanlock.
- **Library roots** for the fingerprint: `Mathlib, Init, Lean, Std, Batteries, Aesop, Qq, Plausible, ProofWidgets`.
  Constants from any other module, including the probed file itself, are unfolded.
- **Grant cutoff:** nodes whose `created` date is `>= 2026-10-28` need a passing `[checks]` record to be granted proved.
  Earlier nodes show `pre-process` in the provenance report and are not retro-required.
- **Git:** run as peterwmurphy in `~/telperion-repo`. The trailer is `Co-Authored-By: Claude Opus 5.5
  <noreply@anthropic.com>`, with no Claude-Session trailer, and nothing is pushed.

## Review Focus

1. **A kernel error printed without the `(kernel)` prefix** but carrying a kernel phrase, such as "declaration has
   metavariables". Classify by the prefix only, and document that. Never guess (Task 1 `test_non_prefixed_is_elab`).
2. **A negation probe that "succeeds" because the probe file failed to elaborate**, for example a syntax error in rendered
   binders. That must be `ERROR`, not `VACUOUS` (Task 2 `test_probe_error_is_not_vacuous`).
3. **`plausible` timing out or giving up.** That must be `PROBE_ONLY`, not `REFUTED` (Task 2 `test_plausible_gave_up`).
4. **The fingerprint changing under a cosmetic binder rename.** It must not change (Task 3 `test_binder_rename_same_hash`).
5. **A `[checks]` record from an older artifact.** It must not satisfy the grant (Task 4 `test_checks_stale_artifact`).

---

### Task 1: `KERNEL_REJECTED` in `verify.py`

**Files:**
- Modify: `src/telperion/verify.py`, the `VerifyResult` dataclass and `_parse_output`, around lines 67-183.
- Test: `tests/test_verify_kernel_rejected.py`

**Interfaces:**
- Produces:
  - `VerifyResult.kernel_rejected: bool` (default False);
  - `VerifyResult.kernel_errors: list[str]`, the error blocks whose first line begins with `(kernel)`;
  - `summary()` shows the tag `KERNEL_REJECTED` before `FAIL` when `kernel_rejected` is set.

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_verify_kernel_rejected.py
from telperion.verify import _parse_output

KERNEL = "f.lean:3:0: error: (kernel) declaration type mismatch, 'bad' has type\n  Nat\nbut is expected\n  Bool\n"
ELAB = "f.lean:3:8: error: unknown identifier 'x'\n"
META = "f.lean:5:0: error: declaration has metavariables 'z'\n"


def _r(out, rc=1):
    from telperion.verify import VerifyResult
    return VerifyResult(**_parse_output(out, rc, decls=(), permitted=("propext",)))


def test_kernel_prefixed_is_kernel_rejected():
    r = _r(KERNEL)
    assert r.kernel_rejected and len(r.kernel_errors) == 1 and not r.okay
    assert r.summary().startswith("[KERNEL_REJECTED")


def test_elab_error_is_not_kernel():
    r = _r(ELAB)
    assert not r.kernel_rejected and r.kernel_errors == []


def test_non_prefixed_is_elab():
    assert not _r(META).kernel_rejected


def test_mixed_reports_both():
    r = _r(ELAB + KERNEL)
    assert r.kernel_rejected and len(r.errors) == 2 and len(r.kernel_errors) == 1
```
If `_parse_output`'s return keys or `VerifyResult`'s constructor differ from this, adapt the `_r` helper only, and keep the
assertions.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_verify_kernel_rejected.py -q -p no:cacheprovider`
Expected: FAIL with an AttributeError on `kernel_rejected`.

- [ ] **Step 3: Implement.**
  - Add the two fields to `VerifyResult`.
  - In `_parse_output`, after the error blocks are built: `kernel_errors = [e for e in errors if e.lstrip().startswith("(kernel)")]`,
    and include `kernel_errors` and `kernel_rejected=bool(kernel_errors)` in the returned dict.
  - In `summary()`, use `tag = "KERNEL_REJECTED" if self.kernel_rejected else ("OK" if ... else "FAIL")`.
  - Document in the module docstring that classification is by the Lean `(kernel)` prefix only.

- [ ] **Step 4: Run** the new tests plus `tests/test_verify*.py`. Expected: all pass.

- [ ] **Step 5: Commit** with the message `verify: KERNEL_REJECTED verdict for (kernel)-prefixed errors`.

---

### Task 2: The negation probe

**Files:**
- Create: `src/telperion/checks/negation_probe.py`
- Modify: `src/telperion/cli.py`, adding `telperion probe-negation --project P --file F --theorem T [--witness W]`
- Test: `tests/test_negation_probe.py`

**Interfaces:**
- Produces:
  - `ProbeResult(verdict: str, detail: str)`, where verdict is one of `VACUOUS`, `REFUTED`, `PROBE_ONLY`, `WITNESSED` or
    `ERROR`;
  - `render_probes(imports: list[str], prelude: str, binders: str, conclusion: str, witness: str | None) -> dict[str, str]`,
    which returns Lean source for the keys `"false"`, `"negation"` and, when a witness is given, `"witness"`;
  - `classify(outputs: dict[str, tuple[int, str]]) -> ProbeResult`, a pure function over `(returncode, output)` per probe;
  - `run_probe(spec, project: Path, wrapper) -> ProbeResult`, which writes the files, runs `lake env lean` through
    leanlock, and calls `classify`.

**The probes.**
- **`false`:** this probe tries to derive `False` from the hypotheses alone. If it compiles, the hypotheses contradict each
  other and the verdict is VACUOUS. Rendered as:
  ```lean
  example <binders> : False := by
    first | (exfalso; omega) | linarith | (simp_all; done) | (norm_num at *; done) | aesop
  ```
- **`negation`:** this probe asks `plausible` for a counterexample. If the output contains `Found a counter-example!`, the
  verdict is REFUTED. Rendered as:
  ```lean
  example : <∀ binders, conclusion> := by plausible (config := { numInst := 200 })
  ```
- **`witness`:** this probe checks a supplied witness. If it compiles, the verdict is WITNESSED. Rendered as
  `example : <∃-closure or the hypothesis structure> := <witness>`.

**Classification order:** ERROR if any probe file failed with an error unrelated to its purpose. Then VACUOUS if `false`
compiled (rc 0, no errors). Then REFUTED if the negation output has the counterexample line. Then WITNESSED if `witness`
compiled. Otherwise PROBE_ONLY.

`set_option maxHeartbeats 200000` is placed before each probe.

**Errors unrelated to the probe's purpose** are any error EXCEPT:
- for `false`: tactic failures, "linarith failed", "omega could not prove", "aesop: failed", "simp made no progress", and
  unsolved goals;
- for `negation`: `plausible` failing to find a counterexample, or giving up ("Gave up", "Unable to find").

- [ ] **Step 1: Write the failing tests.** Pure `classify` tests always run; Lean tests run only when an env is set.

```python
# tests/test_negation_probe.py
import os
from pathlib import Path
import pytest
from telperion.checks.negation_probe import classify, render_probes

OK = (0, "")


def test_false_compiled_is_vacuous():
    assert classify({"false": OK, "negation": (1, "error: plausible gave up")}).verdict == "VACUOUS"


def test_counterexample_is_refuted():
    out = (1, "error: \n===================\nFound a counter-example!\nx := 3\n")
    assert classify({"false": (1, "error: linarith failed"), "negation": out}).verdict == "REFUTED"


def test_plausible_gave_up():
    r = classify({"false": (1, "error: linarith failed"), "negation": (1, "error: Gave up after 200 tests")})
    assert r.verdict == "PROBE_ONLY"


def test_probe_error_is_not_vacuous():
    r = classify({"false": (1, "error: unknown identifier 'Foo'"), "negation": (1, "error: unknown identifier 'Foo'")})
    assert r.verdict == "ERROR"


def test_witness():
    r = classify({"false": (1, "error: linarith failed"), "negation": (1, "error: Gave up"), "witness": OK})
    assert r.verdict == "WITNESSED"


def test_render_contains_parts():
    src = render_probes(["Mathlib"], "", "(x : ℕ) (h : x < 3)", "x < 5", None)
    assert "example (x : ℕ) (h : x < 3) : False" in src["false"]
    assert "plausible" in src["negation"] and "witness" not in src


LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")


@lean
def test_lean_contradictory_hypotheses_vacuous():          # MUST-FAIL control
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ) (h1 : x < 2) (h2 : 5 < x)", "x = 7", None), Path(LEAN_ENV))
    assert r.verdict == "VACUOUS", r.detail


@lean
def test_lean_false_claim_refuted():                        # MUST-FAIL control
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ)", "x * x ≠ 16", None), Path(LEAN_ENV))
    assert r.verdict == "REFUTED", r.detail


@lean
def test_lean_true_claim_probe_only():                      # MUST-PASS control
    from telperion.checks.negation_probe import run_probe, ProbeSpec
    r = run_probe(ProbeSpec(["Mathlib"], "", "(x : ℕ) (h : x < 3)", "x < 5", None), Path(LEAN_ENV))
    assert r.verdict == "PROBE_ONLY", r.detail
```

- [ ] **Step 2: Run the tests to verify they fail**, with `ModuleNotFoundError`.

- [ ] **Step 3: Implement.** In `negation_probe.py`:
  - Define a `ProbeSpec` dataclass with fields `(imports, prelude, binders, conclusion, witness)`.
  - Implement `render_probes` per the rendered forms above, including `set_option maxHeartbeats 200000 in` before each
    example.
  - Implement `classify` per the classification order. Write the "errors unrelated to the probe's purpose" lists as
    module constants, each with a comment.
  - In `run_probe`, write each probe to `<project>/.telperion_probe/<key>.lean`, run
    `[wrapper..., "lake", "env", "lean", file]` with `cwd=project`, where `wrapper` defaults to
    `["env", "ARDA_LEAN_SLOTS=1", os.path.expanduser("~/hodge-engine/leanlock.sh")]` when that script exists, else `[]`.
    Delete the probe directory afterwards.
  - The CLI reads the theorem's binders and conclusion from `--file`/`--theorem`, using `missions/judge.py`'s
    `split_signature` and `decl_context`. Read those first. It prints the verdict and exits 0 for PROBE_ONLY or WITNESSED,
    1 for VACUOUS or REFUTED, and 2 for ERROR.

- [ ] **Step 4: Run the tests.** Then build the local env and run the Lean tests:
  ```bash
  mkdir -p ~/telperion-tools/lean-env && cd ~/telperion-tools/lean-env
  printf 'leanprover/lean4:v4.35.0\n' > lean-toolchain
  printf 'name = "probeenv"\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\nrev = "v4.35.0"\n' > lakefile.toml
  ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh lake exe cache get && ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh lake build
  cd ~/telperion-repo && TELPERION_LEAN_ENV=~/telperion-tools/lean-env PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_negation_probe.py -q -p no:cacheprovider
  ```
  Expected: all pass, with no skips when the env is set. If the true claim comes back REFUTED or VACUOUS, the probe is
  unsound. STOP and report.

- [ ] **Step 5: Commit** with the message `checks: negation probe (VACUOUS/REFUTED/PROBE_ONLY/WITNESSED; one-sided by design)`.

---

### Task 3: The statement fingerprint

**Files:**
- Create: `src/telperion/checks/fingerprint.py`
- Modify: `src/telperion/cli.py`, adding `telperion fingerprint --project P --import M... --target T...`
- Test: `tests/test_fingerprint.py`

**Interfaces:**
- Produces:
  - `render_fingerprint_script(imports, targets, library_roots=LIBRARY_ROOTS) -> str`;
  - `parse_fingerprints(output: str) -> dict[str, str]`, which maps each target to the sha256 hex of its canonical
    statement string;
  - `run_fingerprint(project, imports, targets, wrapper) -> dict[str, str]`.
  - The canonical string is the statement type, delta-unfolded through every constant outside the library roots, with
    binder names erased, pretty-printed with `pp.all`.

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_fingerprint.py
import os
from pathlib import Path
import pytest
from telperion.checks.fingerprint import parse_fingerprints, render_fingerprint_script


def test_parse():
    out = "noise\nFP-BEGIN foo\n∀ (_ : Nat), ...\nFP-END foo\nFP-BEGIN bar\nX\nFP-END bar\n"
    fp = parse_fingerprints(out)
    assert set(fp) == {"foo", "bar"} and len(fp["foo"]) == 64 and fp["foo"] != fp["bar"]


def test_parse_missing_target_raises():
    with pytest.raises(ValueError, match="baz"):
        parse_fingerprints("FP-MISSING baz\n")


def test_render_mentions_targets_and_roots():
    s = render_fingerprint_script(["Mathlib"], ["foo"])
    assert "`foo" in s and "deltaExpand" in s and "`Mathlib" in s


LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set")


def _fp(tmp_text: str, target: str) -> str:
    from telperion.checks.fingerprint import run_fingerprint_on_text
    return run_fingerprint_on_text(Path(LEAN_ENV), tmp_text, target)


@lean
def test_shadowed_definition_changes_hash():                 # MUST-FAIL control
    a = "import Mathlib\ndef bound : ℕ := 5\ntheorem t : ∀ n : ℕ, n < bound → n < 10 := by intro n h; unfold bound at h; omega\n"
    b = a.replace(":= 5", ":= 6")
    assert _fp(a, "t") != _fp(b, "t")


@lean
def test_binder_rename_same_hash():                          # MUST-PASS control
    a = "import Mathlib\ntheorem t : ∀ n : ℕ, n < 3 → n < 10 := by omega\n"
    b = a.replace("∀ n : ℕ, n < 3 → n < 10", "∀ m : ℕ, m < 3 → m < 10")
    assert _fp(a, "t") == _fp(b, "t")
```
This adds one more interface: `run_fingerprint_on_text(project, text, target) -> str`, which writes the text to a temp
module in the project and fingerprints the target.

- [ ] **Step 2: Run the tests to verify they fail**, with `ModuleNotFoundError`.

- [ ] **Step 3: Implement.** The Lean script that `render_fingerprint_script` emits (`__IMPORTS__`, `__TARGETS__` and
  `__ROOTS__` are filled in from the arguments):

```lean
__IMPORTS__
import Lean
open Lean Meta

partial def tpEraseNames : Expr → Expr
  | .forallE _ t b bi => .forallE `_ (tpEraseNames t) (tpEraseNames b) bi
  | .lam _ t b bi => .lam `_ (tpEraseNames t) (tpEraseNames b) bi
  | .letE _ t v b nd => .letE `_ (tpEraseNames t) (tpEraseNames v) (tpEraseNames b) nd
  | .app f a => .app (tpEraseNames f) (tpEraseNames a)
  | .mdata _ e => tpEraseNames e
  | .proj s i e => .proj s i (tpEraseNames e)
  | e => e

def tpRoots : List Name := __ROOTS__

def tpIsLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => tpRoots.any (·.isPrefixOf (env.header.moduleNames[idx.toNat]!))
  | none => false

#eval show MetaM Unit from do
  let env ← getEnv
  for t in (__TARGETS__ : List Name) do
    match env.find? t with
    | none => IO.println s!"FP-MISSING {t}"
    | some ci =>
      let e ← deltaExpand ci.type (fun n => !tpIsLib env n)
      let s ← withOptions (fun o => o.setBool `pp.all true) (ppExpr (tpEraseNames e))
      IO.println s!"FP-BEGIN {t}\n{s}\nFP-END {t}"
```
`parse_fingerprints` takes the sha256 of the UTF-8 text between the markers, with surrounding whitespace stripped, and
raises `ValueError` naming any `FP-MISSING` target.

If `deltaExpand`'s signature differs in Lean v4.35.0 (it is in `Lean.Meta` as `deltaExpand (e : Expr) (p : Name → Bool) :
CoreM Expr`), adapt the call and record the change in the report. Do not substitute `whnf`, because it would unfold library
constants as well.

The CLI prints one line per target, `<target> <sha256>`, and exits 2 on a `FP-MISSING` target.

- [ ] **Step 4: Run** the pure tests and then the Lean tests, with `TELPERION_LEAN_ENV` set. All must pass with no skips.
  If the binder-rename control fails, `pp.all` is still printing hygienic names. Fix the erasure, never the test.

- [ ] **Step 5: Commit** with the message `checks: statement fingerprint (delta-unfolded past library roots, binder-name-insensitive)`.

---

### Task 4: The `[checks]` record and the grant gate (new nodes only)

**Files:**
- Modify: `src/telperion/missions/schema.py`, adding a `ChecksRecord` dataclass next to `RejudgeRecord`, a `Node.checks`
  field, `"checks"` in `_MODELLED_NODE_KEYS`, serialisation and parsing. Follow the pattern `RejudgeRecord` uses exactly.
- Modify: `src/telperion/missions/provenance.py`, adding `checks_problem(campaign_root, node) -> str`.
- Modify: `src/telperion/missions/verify.py`. In `grant_status`, when `new_status == "proved"` and
  `node.created >= "2026-10-28"`, raise `GateError` if `checks_problem` is non-empty.
- Modify: `src/telperion/cli.py`, adding `mission checks-record SLUG --campaign C --probe-json F --closure-json F
  --fingerprint HEX`.
- Test: `tests/test_missions_checks.py`

**Interfaces:**
- `ChecksRecord(date, artifact_sha256, probe_verdict, closure_verdict, statement_fingerprint, note="")`:
  - `probe_verdict` is one of PROBE_ONLY, WITNESSED, VACUOUS, REFUTED or ERROR;
  - `closure_verdict` is PASS or FAIL;
  - the fingerprint is 64 hex characters.
- `checks_problem` returns "" iff all of these hold:
  - the artifact sha256 is current;
  - `probe_verdict` is WITNESSED, or PROBE_ONLY with a note containing `signoff:`, the reviewer's sign-off (spec 5.2);
  - `closure_verdict` is PASS.

  Anything else returns a reason. The provenance report prints `pre-process` for nodes created before the cutoff.
- `checks-record` reads the probe verdict from `probe-negation --json` output and the closure verdict from
  `audit-closure --json` output, never from flags.

- [ ] **Step 1: Write the failing tests.** Mirror `tests/test_missions_rejudge.py`'s structure and its `missions_fixtures`
  helper. Cases:
  - `test_checks_roundtrip`;
  - `test_checks_stale_artifact`, where an older sha is not current;
  - `test_vacuous_blocks_grant`;
  - `test_probe_only_needs_signoff`, which fails without `signoff:` in the note and passes with it;
  - `test_closure_fail_blocks`;
  - `test_pre_cutoff_node_not_required`, where a node created on 2026-10-01 is granted without `[checks]`;
  - `test_post_cutoff_node_required`;
  - `test_cli_reads_verdicts_from_json`, which uses tmp JSON files in the formats the two CLIs emit. Read `ClosureAudit`'s
    `to_json` keys and use them.

- [ ] **Steps 2-4:** RED, then implement, then GREEN. Run the new tests plus `tests/test_missions_*.py`.

- [ ] **Step 5: Commit** with the message `missions: [checks] record (probe + closure + fingerprint) gates new grants`.

---

### Task 5: Docs and the Lean CI job

**Files:**
- Modify: `.github/workflows/ci.yml`, adding a `lean-checks` job that builds the probe env (as in Task 2 Step 4, cached on
  the toolchain hash) and runs `pytest tests/test_negation_probe.py tests/test_fingerprint.py` with `TELPERION_LEAN_ENV`
  set. Copy the elan and Mathlib cache steps from Arda's `.github/workflows/telperion-lean-e2e.yml`.
- Modify: `docs/MISSIONS_HOWTO.md`, adding a "Checks before grant" section that covers:
  - the four checks;
  - the verdict meanings, including that PROBE_ONLY is one-sided;
  - the sign-off rule;
  - the cutoff;
  - how to run `probe-negation`, `audit-closure`, `fingerprint` and `checks-record`.

- [ ] **Step 1:** Write the job and the docs section.
- [ ] **Step 2:** Validate the YAML locally with `~/telperion-tools/venv314/bin/python -c "import yaml,sys;yaml.safe_load(open('.github/workflows/ci.yml'))"`.
- [ ] **Step 3: Commit** with the message `ci: lean-checks job runs the probe and fingerprint must-fail controls; docs`.

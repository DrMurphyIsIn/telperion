# Proof-auditor demo — Telperion as a referee for third-party Lean

The Lean kernel rejects a **false** theorem, but a green build still hides
**meaning-level** defects the kernel is structurally blind to — because they live
in the *statement*, not the proof. As the field ships confident, LLM-generated,
self-verified proofs, a deterministic machine-checkable referee for *anyone's*
Lean is an axis no frontier prover occupies. This is that referee, demonstrated.

## Run it

```bash
python examples/audit_demo/run_audit.py
```

`telperion audit <file.lean>` (here via `audit_lean_text`) is run on two
third-party samples:

| Sample | Expected |
|---|---|
| [`clean_proof.lean.txt`](clean_proof.lean.txt) | **clean** — substantive theorems, no holes |
| [`defective_proof.lean.txt`](defective_proof.lean.txt) | **flagged** — the defect classes below |

The defective sample compiles-adjacent but hides four defects a confident prover
might ship:

1. **`sorry`** — an incomplete proof the kernel accepts as an axiom-like hole
   (CI green, nothing proved). → `SORRY` (error)
2. **smuggled `axiom`** — bypasses the kernel's trust entirely. → `AXIOM` (error)
3. **vacuity** — a reflexive tautology (`42 = 42`) dressed as a headline result;
   the kernel checks it happily and it proves nothing. → `VACUOUS` (error), named
   to the offending theorem.
4. **`Prop := True` stub** — decorative, content-free. → `TRIVIAL_STUB` (warn)

The kernel catches **none** of (1)–(4) as a *meaning* problem; the auditor
catches all of them, deterministically, with no proof search.

## Why it matters

The soundness story of every frontier prover stops at *"the kernel checked it."*
Telperion's referee adds the layer above the kernel: **vacuity, smuggled axioms,
and holes in anyone's output** — the failure modes that scale *up* as proofs get
more confident and more machine-generated. Verified by
[`tests/test_audit_demo.py`](../../tests/test_audit_demo.py) (pure-Python; no Lean
build needed — the auditor is a static analyzer).

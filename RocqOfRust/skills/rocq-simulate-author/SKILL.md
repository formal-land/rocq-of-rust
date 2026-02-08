---
name: rocq-simulate-author
description: Create or update Rocq simulate files in this repository, including imports, executable definitions, and corresponding _eq lemmas with the project’s proof/admission conventions.
---

# Rocq Simulate Author

Use this skill when asked to create or complete files under `**/simulate/**/*.v`.

## Goals
- Add a simulate `Definition` that mirrors the links/run behavior at the right abstraction level.
- Add the matching `_eq` lemma connecting `run_*` and the simulate definition.
- Keep the file compiling with project flags.

## Repository Conventions
- Compile with:
```sh
coqc -R . RocqOfRust -impredicative-set path/to/file.v
```
- Prefer explicit imports; do not assume aggregator modules exist.
- In this repo, many `_eq` lemmas are intentionally `Admitted` during iteration.
- Use `id` instead of `(fun interpreter => interpreter)`.
- Prefer record notation when clearer (for example `Range` records).

## Procedure
1. Locate links source and nearby simulate examples.
- Read corresponding links file (`.../links/...`) to extract `run_*` signature and parameter order.
- Read one neighboring simulate file in same folder for style.

2. Build imports explicitly.
- `Require Import simulate.RocqOfRust.` first.
- Add links/simulate imports used by the definition.
- Add missing imports only when compile errors require them.

3. Write the simulate definition.
- Keep shape close to Rust intent and existing sibling files.
- Use existing macros (`gas_macro`, `push_macro`, etc.) consistently.
- Avoid overfitting proofs in the definition.

4. Write `_eq` lemma.
- Match argument order of `run_*` exactly.
- Prefer class-level `Run` assumptions in Eq-style files.
- If proof is not ready, keep `Admitted` unless user asked no admitted.

5. Compile and iterate.
- Compile touched file first.
- Fix minimal issues (imports, type annotations, argument order).

## Starter Skeleton
```coq
Require Import simulate.RocqOfRust.
(* other explicit imports *)

Definition <name>
    {A ... : Set} `{Link ...}
    ...
    (x : ...) : ... :=
  ... .

Lemma <name>_eq
    {A ... : Set} `{Link ...}
    ...
    (x : ...) :
  ...
.
Proof.
Admitted.
```

## Common Failure Fixes
- `module-not-found`: add explicit `Require Import ...` for split per-function links/simulate files.
- Type mismatch in `run_*`: compare with links instance signature and reorder args.
- Numeric inference to `Z`: use typed literals like `(0 : usize)`.
- Missing class projections in Eq files: add appropriate class-level `*.Run` assumption.

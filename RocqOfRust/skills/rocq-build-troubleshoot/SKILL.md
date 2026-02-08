---
name: rocq-build-troubleshoot
description: Fast workflow to diagnose and fix Rocq/Coq compile errors in this repository, especially missing imports after links/simulate splits and per-file compile checks.
---

# Rocq Build Troubleshoot

Use this skill when a `.v` file fails to compile and the goal is a minimal targeted fix.

## Scope
- Repository: `RocqOfRust`
- Commands use project flags: `-R . RocqOfRust -impredicative-set`
- Prefer single-file checks first, then dependency checks.

## Workflow
1. Reproduce exactly:
```sh
coqc -R . RocqOfRust -impredicative-set path/to/file.v
```

2. If error references missing module/loadpath:
- Add explicit `Require Import ...` in the failing file.
- Do not rely on removed aggregator modules.
- Prefer per-function imports in `revm/revm_interpreter/instructions/{links,simulate}/...`.

3. If error is argument-order/type mismatch in `run_*` call:
- Compare the local `run_*` instance signature in `.../links/...`.
- Align call order exactly; remove placeholder `_` arguments unless required by implicit params.

4. If `Range` literals fail type inference:
- Use record notation with typed zeros:
```coq
{|
  Range.start := (0 : usize);
  Range.end_ := (0 : usize)
|}
```

5. Recompile touched file(s):
```sh
coqc -R . RocqOfRust -impredicative-set path/to/file.v
```

6. Optional dependency sanity check:
```sh
make path/to/file.vo
```

## Guardrails
- Keep fixes minimal and local.
- Do not reintroduce removed aggregators.
- Preserve `Admitted` where the project intentionally keeps placeholders.
- If proving `_eq` fails, check semantic alignment before attempting `Qed`.

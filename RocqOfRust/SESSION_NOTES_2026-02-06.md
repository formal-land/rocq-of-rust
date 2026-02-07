# Session Notes — 2026-02-06

## Objective
Capture stable conventions and decisions from today so future work can continue with the same style and assumptions.

## Style And Architecture Conventions
- Prefer `Export (hints)` at module end instead of `Global Instance` for exposing instances/hints.
- Avoid module synonyms like `Module X := ...` unless explicitly requested.
- Prefer using class-instance projection style with `::` fields where appropriate in links/simulate class records.
- Keep Rust naming/alignment when requested (types/fields/method names should follow Rust source ordering and naming).
- For host/context simulate classes, avoid redundant type aliases and redundant duplicate type parameters.
- Use `Host.Types.t` directly (no `links.host.` prefix when unnecessary).
- Remove redundant local aliases like `Module Types := ...` when requested.
- In parameter lists, avoid duplicated binders (e.g. duplicated `H_types`).

## Revm Context Interface Work
- Added/iterated simulate layers for `Cfg`, `Block`, `CfgGetter`, `Transaction`, `Host` traits/classes.
- Added Eq classes for multiple traits and wired `Host.Eq` to consume those trait-level Eq classes.
- `Cfg` simulate should take `types` parameter similarly to links.
- `TransactionError` simulate should include `Error_for_Self` and avoid adding `well_formed` when requested.
- Classes should be `Set` where possible/preferred.

## Interpreter Block Info Work
- `chainid` and `coinbase` are the reference style for defining/proving block-info instruction simulations.
- Keep push-macro call signatures readable unless explicitly asked otherwise.
- Utility conversions that are not direct Rust symbols should be inlined when requested.
- Ongoing proof work in `revm/revm_interpreter/instructions/simulate/block_info.v` (several lemmas still admitted in that file).

## Core Convert / Default / Option Work
- Added simulate traits in `core/convert/simulate/mod.v`:
  - `From.C`, `From.Eq.C`
  - `Into.C`, `Into.Eq.C`
  - simulate for `Impl_Into_for_From_T` and Eq proof.
- `core/links/default.v`:
  - switched method proof endings from `exact run_default...` to `typeclasses eauto`.
  - added missing `Export (hints) Impl_Default_for_unit`.
- `core/simulate/default.v` exists with simulate `Default.C` and `Default.Eq.C` for unit/bool/integers.
- `core/simulate/option.v` was expanded significantly to track links-side coverage.
- For `expect` in option simulate: keep only `expect_eq` (no extra `expect` definition) per latest request.

## FnOnce Decision
- There was no simulate layer for `FnOnce` initially.
- Added `core/ops/simulate/function.v` with:
  - `FnOnce.C` (pure simulate callable)
  - `FnOnce.Eq.C` (links execution equivalence)
- Important distinction:
  - `function.FnOnce.Run` is execution evidence (`Run.Trait`), not a pure function value.
  - Pure simulate definitions (like option map semantics) should rely on simulate class (`FnOnce.C`) plus Eq assumptions for proof correspondence.

## Ruint Work
- In `ruint/simulate/from.v`, added missing unsigned `TryFrom` simulate modules:
  - `TryFrom_u16_for_Uint`
  - `TryFrom_u32_for_Uint`
  - `TryFrom_u128_for_Uint`
- Kept local proof style consistent with neighboring modules (several lemmas are admitted placeholders).

## Contract Simulate Naming Cleanup
- Replaced `H_types_sim` with `H_types` across relevant contract simulate files.
- Removed duplicated `H_types` binders in some lemma parameter lists (notably in `call.v` and `delegate_call.v`).

## Links Host Split For Compile Time
- Split heavy file `revm/revm_interpreter/instructions/links/host.v` into one file per instance under:
  - `revm/revm_interpreter/instructions/links/host/*.v`
- Replaced parent `host.v` with an aggregator of `Require Export ...` lines.
- Motivation: reduce per-file typechecking bottleneck and improve incremental recompilation behavior.

## Practical Workflow Conventions From Today
- When a proof is too brittle, keep file compiling with targeted `Admitted` and continue incremental refactors.
- Prefer minimal local compile checks on touched targets (e.g., `make <file>.vo -j1`).
- Keep definitions and proofs in same order as links/Rust when requested.
- Keep comments minimal and remove generated helper comments when requested.

## Open/Follow-Up Items
- Several proofs remain admitted in:
  - `revm/revm_interpreter/instructions/simulate/block_info.v`
  - `revm/revm_interpreter/instructions/simulate/contract/extcall_input.v`
  - parts of `core/simulate/option.v` (Try/FromResidual/map proofs)
- `core/simulate/option.v` now depends on new `core/ops/simulate/function.v` and updated links behavior (`run_map` as `Run.Trait`).

## Reminder For Next Session
- Start by reading this file and then check current diffs/status before new edits:
  - `SESSION_NOTES_2026-02-06.md`
  - `git status --short`

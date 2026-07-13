# AGENTS Instructions for RocqOfRust

This file is the canonical merged guide. It consolidates previous `CLAUDE.md` and `SESSION_NOTES_2026-02-06.md`.

## Source Merge
- Included: `CLAUDE.md`
- Included: `SESSION_NOTES_2026-02-06.md`

---

# Claude Instructions for RocqOfRust Links Development

This document captures patterns and guidelines for creating "links" files in the RocqOfRust project. Links files provide formal Rocq specifications that connect Rust types to their Rocq models, enabling symbolic execution and proofs.

## Current Repository State (verified 2026-02-08)

This section overrides older notes below when they conflict.

- Project flags are defined in `_RocqProject`:
  - `-R . RocqOfRust`
  - `-arg -impredicative-set`
- Two valid compile workflows:
  - `make path/to/file.vo`
  - direct: `coqc -R . RocqOfRust -impredicative-set path/to/file.v`
- `revm/revm_interpreter/instructions/links/` is now split by area:
  - `control/`, `host/`, `memory/`, `system/`, `contract/`, `bitwise/`
- `revm/revm_interpreter/instructions/simulate/` is also split similarly:
  - notably `memory/` and `system/` are per-function directories.
- Aggregator files were intentionally removed in places:
  - `revm/revm_interpreter/instructions/links/memory.v` is gone.
  - `revm/revm_interpreter/instructions/simulate/memory.v` is gone.
  - Use explicit per-function imports (e.g. `...links.memory.mload`).
- New simulate files added recently:
  - `core/ops/simulate/arith.v`
  - `core/intrinsics/simulate/mod.v` (contains `three_way_compare` simulate lemma scaffold).
- For split links/simulates, do not assume a parent aggregator module exists.
- In this repo, many `_eq` lemmas are intentionally `Admitted` while definitions evolve; do not force `Qed` if semantics are not aligned yet.
- Typical source of failures after split:
  - missing explicit imports previously provided transitively by aggregators.
  - stale `.vo` assumption mismatches after changing dependencies; recompile in dependency order.

## Corrections To Outdated Guidance

- Older snippets mentioning `Require Import RocqOfRust.simulate.M.` are outdated.
  - Use `Require Import simulate.RocqOfRust.` in simulate files.
- Older snippets using aggregate imports like `...instructions.links.system.` or `...instructions.links.host.` are often outdated in this repo state.
  - Prefer explicit per-function imports.
- "Always use -j3" is not a hard rule.
  - Use `-j3` for faster local loops, but prefer single-file `coqc` checks when isolating proof/import issues.

## Recent Practical Lessons

- When splitting a links file, also update all simulate imports immediately; otherwise loadpath warnings appear as:
  - `library ... links.host/system is required and has not been found in the loadpath`.
- Prefer per-function imports in simulate files:
  - `revm.revm_interpreter.instructions.links.system.<fn>`
  - `revm.revm_interpreter.instructions.links.host.<fn>`
  - `revm.revm_interpreter.instructions.links.memory.<fn>`
- After changing a dependency signature (or admitted/defined status), recompile dependent links first, then simulate targets.
- If a proof for a `_eq` lemma fails after simplification, confirm semantic alignment first:
  - if `run_*` executes more behavior than the current simulate definition, `Qed` is not possible without updating the definition.
- Keep path alignment strict:
  - simulate files mirror source/links area layout (e.g. split memory/system/control).
- For host instruction simulations, match Rust control-flow order exactly (e.g. checks/gas before stack or host calls), or `_eq` proofs will fail against `run_*`.
- Added simulate macro `require_non_staticcall_macro` in `revm/revm_interpreter/instructions/simulate/macros.v`:
  - behavior: if `runtime_flag.is_static` then set `StateChangeDuringStaticCall` and exit; otherwise continue.
  - use `require_non_staticcall_macro_eq` in proofs instead of manually reproducing the static-guard branch.
- `tstore` and `tload` should include EIP-1153 gates from Rust:
  - `check_macro ... SpecId.CANCUN`
  - (for `tstore`) `require_non_staticcall_macro`
  - `gas_macro ... constants.WARM_STORAGE_READ_COST`
  - then stack pop / host call logic.
- When updating `simulate/README.md` summary counts, recompute from section tables; do not trust stale totals (tx_info row drifted once).

## Log of tips (newest first)

- Use the links plugin for repetitive link type boilerplate.

## Directory Structure

Links files are placed in a `links/` subdirectory next to the generated `.v` files:
```
some_crate/
  lib.v           # Generated Rocq code from Rust
  links/
    lib.v         # Links file with specifications
```

## Compile

To compile a file and check that it works, with its dependencies, run:

```sh
make path/file.vo
```

Note the extension `.vo` instead of `.v`.

## Basic Link Structure for Types

### Simple Enum (No Type Parameters)

```coq
Module TokenError.
  Inductive t : Set :=
  | NotRentExempt
  | InsufficientFunds
  (* ... more variants *).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "crate_name::TokenError";
    φ x :=
      match x with
      | NotRentExempt =>
          Value.StructTuple "crate_name::TokenError::NotRentExempt" [] [] []
      | InsufficientFunds =>
          Value.StructTuple "crate_name::TokenError::InsufficientFunds" [] [] []
      (* ... *)
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "crate_name::TokenError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  (* of_value lemmas for each variant - BOTH Smpl Add lines are required *)
  Lemma of_value_with_NotRentExempt :
    Value.StructTuple "crate_name::TokenError::NotRentExempt" [] [] [] =
    φ NotRentExempt.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_NotRentExempt : of_value.  (* Register the lemma *)
  Definition of_value_NotRentExempt :
    OfValue.t (Value.StructTuple "crate_name::TokenError::NotRentExempt" [] [] []).
  Proof. econstructor; apply of_value_with_NotRentExempt. Defined.
  Smpl Add apply of_value_NotRentExempt : of_value.  (* Register the OfValue.t definition *)
End TokenError.
```

### Polymorphic Enum (With Type Parameter)

```coq
Module COption.
  Inductive t (T : Set) : Set :=
  | None
  | Some (value : T).
  Arguments None {T}.
  Arguments Some {T}.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "crate::COption") [] [Φ T];
    φ x :=
      match x with
      | None => Value.StructTuple "crate::COption::None" [] [Φ T] []
      | Some v => Value.StructTuple "crate::COption::Some" [] [Φ T] [φ v]
      end
  }.

  Definition of_ty ty :
    OfTy.t ty ->
    OfTy.t (Ty.apply (Ty.path "crate::COption") [] [ty]).
  Proof.
    intros [T]; eapply OfTy.Make with (A := t T).
    subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  (* For polymorphic None, include type equality hypothesis *)
  Lemma of_value_with_None {T : Set} `{Link T} T' :
    T' = Φ T ->
    Value.StructTuple "crate::COption::None" [] [T'] [] =
    φ (@None T).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with_None : of_value.

  (* For Some, include both type and value hypotheses *)
  Lemma of_value_with_Some T' (T : Set) `{Link T} value' (value : T) :
    T' = Φ T ->
    value' = φ value ->
    Value.StructTuple "crate::COption::Some" [] [T'] [value'] =
    φ (Some value).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add unshelve eapply of_value_with_Some : of_value.
End COption.
```

### Record Type (Struct)

```coq
Module Account.
  Record t : Set := {
    mint : Address.t;
    owner : Address.t;
    amount : U64.t;
    (* ... more fields *)
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "crate::Account";
    φ x :=
      Value.StructRecord "crate::Account" [] [] [
        ("mint", φ x.(mint));
        ("owner", φ x.(owner));
        ("amount", φ x.(amount))
        (* ... *)
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "crate::Account").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
    (mint : Address.t) (mint' : Value.t)
    (owner : Address.t) (owner' : Value.t)
    (amount : U64.t) (amount' : Value.t)
    :
    mint' = φ mint ->
    owner' = φ owner ->
    amount' = φ amount ->
    Value.StructRecord "crate::Account" [] [] [
      ("mint", mint');
      ("owner", owner');
      ("amount", amount')
    ] = φ (Build_t mint owner amount).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  (* SubPointers for field access *)
  Module SubPointer.
    Definition get_mint : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "crate::Account" "mint") :=
    {|
      SubPointer.Runner.projection x := Some x.(mint);
      SubPointer.Runner.injection x y := Some (x <| mint := y |>);
    |}.

    Lemma get_mint_is_valid :
      SubPointer.Runner.Valid.t get_mint.
    Proof. now constructor. Qed.
    Smpl Add apply get_mint_is_valid : run_sub_pointer.
  End SubPointer.
End Account.
```

### Opaque Types

For complex types that don't need internal structure exposed:

```coq
Module OpaqueType.
  Parameter t : forall (T : Set) `{Link T}, Set.

  Parameter to_value : forall {T : Set} `{Link T}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "crate::OpaqueType") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "crate::OpaqueType") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End OpaqueType.
```

## Trait Implementations

### Defining a Trait

```coq
Module Pack.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("crate::Pack", [], [], Φ Self).

  Definition Run_unpack (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "unpack" (fun method =>
      forall (input : '& (list U8.t)),
        Run.Trait method [] [] [φ input] (Result.t Self ProgramError.t)
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    unpack : Run_unpack Self;
    (* ... more methods *)
  }.
End Pack.
```

### Implementing a Trait

```coq
Module Impl_Pack_for_Account.
  Instance run : Pack.Run Account.t.
  Admitted.
End Impl_Pack_for_Account.
Export Impl_Pack_for_Account.
```

### From/Into Traits

```coq
(* impl From<TokenError> for ProgramError *)
Module Impl_From_TokenError_for_ProgramError.
  Instance run : From.Run ProgramError.t TokenError.t.
  Admitted.
End Impl_From_TokenError_for_ProgramError.
Export Impl_From_TokenError_for_ProgramError.
```

## Function Implementations

### Instance Method

```coq
Instance run_is_frozen
    (self : '& Account.t) :
  Run.Trait module.Impl_crate_Account.is_frozen [] [] [φ self]
    bool.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_is_frozen.
```

### Associated Function

```coq
Instance run_checked_add (self rhs: U64.t) :
  Run.Trait num.Impl_u64.checked_add [] [] [ φ self; φ rhs ] (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_checked_add.
```

## Proofs with Destructs

When proving functions that use traits, you often need to destruct trait instances:

```coq
Proof.
  constructor.
  destruct (Impl_Try_for_Result.run Account.t ProgramError.t).
  destruct (Impl_FromResidual_for_Result.run unit ProgramError.t).
  destruct (Impl_Into_for_From_T.run Impl_From_TokenError_for_ProgramError.run).
  destruct Impl_Pack_for_Account.run.
  run_symbolic.
Admitted.
```

## Common Imports

```coq
Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.convert.links.mod.  (* For From/Into *)
Require Import core.ops.links.try_trait.  (* For Try trait *)
Require Import core.ops.links.deref.  (* For Deref/DerefMut *)
```

## Important Notes

1. **Module naming**: Avoid naming modules `Ref` as it conflicts with the global `Ref` type. Use `CellRef` or similar instead.

2. **Export modules**: Use `Export ModuleName.` after trait implementations to make instances available.

3. **Smpl Add**: Register lemmas with `Smpl Add apply lemma_name : of_ty.` or `Smpl Add apply lemma_name : of_value.` for automation.

4. **Enum variants need TWO Smpl Add lines**: For each enum variant, register both:
   - The `of_value_with_*` lemma: `Smpl Add apply of_value_with_Variant : of_value.`
   - The `of_value_*` definition: `Smpl Add apply of_value_Variant : of_value.`
   Both are needed for proof automation to work correctly.

5. **Polymorphic of_value**: For polymorphic types, use `Smpl Add unshelve eapply ...` instead of `Smpl Add apply ...`.

6. **Global Opaque**: Mark instances as opaque after definition to prevent unfolding: `Global Opaque run_function_name.`

7. **Type paths**: The Rust path format is `crate_name::module::Type` with `::` separators.

8. **Polymorphic link types**: Use the links plugin generic commands when they support the type shape. If a polymorphic shape is not supported yet, keep it manual and note the blocker near the definition.

## Simulate Files

Simulate files (in `simulate/` subdirectories) provide pure Rocq definitions and proofs that relate symbolic execution to pure functional specifications.

### Directory Structure

```
some_crate/
  lib.v              # Generated Rocq code from Rust
  links/
    lib.v            # Links file with Run instances
  simulate/
    lib.v            # Simulate file with pure definitions and _eq lemmas
```

### Basic Structure for Simulate Proofs

For arithmetic/bitwise operations in the EVM interpreter, follow the pattern in `revm/revm_interpreter/instructions/simulate/arithmetic.v`:

```coq
Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.macros.

(* Pure definition of the operation *)
Definition add ... :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) (Impl_Uint.wrapping_add op1 op2) in
    interpreter
      <| Interpreter.stack := stack |>
  )).

(* Proof that symbolic execution matches pure definition *)
Lemma add_eq ... :
  {{ SimulateM.eval_f (run_add ...) ... 🌲 (Output.Success tt, [...]) }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] [] [] [] [] [] [] [] [] [] [] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. { apply Impl_Uint.wrapping_add_eq. }
  get_can_access.
  apply Run.Pure.
Qed.
```

### Key Tactics for Simulate Proofs

The convenience tactics are defined in `simulate/M.v`:

1. **`r.`** ("run"): Simplifies and handles reference access. Use this to progress through computation steps.
2. **`c.`** ("call"): Prepares a function call goal with `Run.Call`.
3. **`cw f_eq.`** ("call with"): Applies a call with a given equality lemma. Example: `cw Impl_usize.saturating_add_eq.`
4. **`cp.`** ("call pure"): Handles `SimulateM.Call` wrapping `Run.Pure`. Use when the goal has a `Run.PureSuccess` inside a `SimulateM.Call`.
5. **`l.`** ("let"): Handles let-binding goals with `Run.Let`.
6. **`lu.`** ("let unfold"): Handles let-binding by unfolding.
7. **`p.`** ("pure"): Closes a `SimulateM.Pure` goal with `Run.Pure`.
8. **`pf.`** ("pure with f_equal"): Closes goal with equality reasoning using `Run.PureEq` and `repeat f_equal`.

**Workflow for writing `_eq` proofs:**
1. Start with `with_strategy transparent [run_function] unfold run_function.`
2. Use `r. Show.` to see the current goal
3. For function calls, use `cw equality_lemma.`
4. For pure computations wrapped in calls, use `cp.`
5. For final pure results, use `p.`

**Macro-specific tactics:**
- **`gas_macro_eq InterpreterTypesEq`**: Handles gas recording, creates branches for OutOfGas case
- **`popn_macro_eq InterpreterTypesEq`**: Handles stack pop operations
- **`popn_top_macro_eq InterpreterTypesEq`**: Handles stack pop with top reference
- **`check_macro_eq InterpreterTypesEq`**: Handles spec ID checking

### The `_eq` Lemma Pattern

For each pure operation used in simulate definitions, create an `_eq` lemma in the corresponding simulate file:

```coq
(* In ruint/simulate/add.v *)
Definition wrapping_add {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
    lib.Uint.t BITS LIMBS :=
  {| lib.Uint.value := (x1.(lib.Uint.value) + x2.(lib.Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

Lemma wrapping_add_eq (stack : Stack.t)
    (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
  {{
    SimulateM.eval_f
      (Impl_Uint.run_wrapping_add BITS LIMBS x1 x2)
      stack 🌲
    (
      Output.Success (wrapping_add x1 x2),
      stack
    )
  }}.
Admitted.
```

### Macros in `macros.v`

The file `revm/revm_interpreter/instructions/simulate/macros.v` defines:

- **`gas_macro`**: Pure definition for gas handling (branches on record_cost result)
- **`popn_macro`**: Pure definition for popping N values from stack
- **`popn_top_macro`**: Pure definition for popping N values and getting a mutable reference to top
- **`check_macro`**: Pure definition for spec ID checking

Each macro has a corresponding `_eq` tactic (e.g., `gas_macro_eq`) that handles the proof obligations.

### Debugging Simulate Proofs

When a proof gets stuck:
1. Copy-paste the macro definition inline to see what's happening
2. Check that the `destruct InterpreterTypesEq` pattern matches the current typeclass structure
3. Verify that all necessary `_eq` lemmas exist for operations used in the definition
4. The `[|` selector in tactics means: first branch before `[|`, second branch after - useful for understanding branching in macros

### Important Notes for Simulate Files

1. **destruct is only for traits**: Only use `destruct` for trait instances, not for regular function instances
2. **Use Qed for `_eq` lemmas**: The `_eq` lemmas are in Prop, so use `Qed` (not `Defined`)
3. **Always use -j3**: When compiling with make, always use `make -j3` for parallel compilation

### Simulation File Placement

Simulate files should mirror the Rust source structure. If a function is defined in:
```
revm/revm_interpreter/interpreter/shared_memory.rs
```
Its simulation should be in:
```
revm/revm_interpreter/interpreter/simulate/shared_memory.v
```

### Creating Macros for Simulation

When creating Coq macros that correspond to Rust macros, follow these patterns:

1. **Use continuation-passing style (CPS)** with `k_exit` (failure continuation) and `k` (success continuation)

2. **For optional parameters** (like `$ret` in Rust macros), use either:
   - An `option` type where `None` means use default value
   - A generic type parameter `A` with a `ret : A` parameter

3. **Mirror the Rust macro structure** as closely as possible, including variable names like `words_num`, `offset`, `len`

4. **No comments for simulations** - the description is already in the Rust source code

Example Rust macro:
```rust
macro_rules! resize_memory {
    ($interpreter:expr, $offset:expr, $len:expr) => {
        $crate::resize_memory!($interpreter, $offset, $len, ())
    };
    ($interpreter:expr, $offset:expr, $len:expr, $ret:expr) => {
        let words_num = $crate::interpreter::num_words($offset.saturating_add($len));
        // ... rest of macro
    };
}
```

Corresponding Coq simulation:
```coq
Definition resize_memory_macro {WIRE K A : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (offset len : usize)
    (ret : A)
    (k_exit : A -> Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let words_num := num_words {| Integer.value := offset.(Integer.value) + len.(Integer.value) |} in
  (* ... rest of definition *)
```

### Helper Functions for Macros

When a Rust macro uses helper functions (like `num_words`), define them in the appropriate simulate file:

```coq
(* In revm/revm_interpreter/interpreter/simulate/shared_memory.v *)
Definition num_words (len : usize) : usize :=
  {| Integer.value := (len.(Integer.value) + 31) / 32 |}.

Lemma num_words_eq (len : usize) (stack : Stack.t) :
  {{
    SimulateM.eval_f (run_num_words len) stack 🌲
    (Output.Success (num_words len), stack)
  }}.
Proof.
Admitted.
```

---

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
  - `AGENTS.md`
  - `git status --short`

# Claude Instructions for RocqOfRust Links Development

This document captures patterns and guidelines for creating "links" files in the RocqOfRust project. Links files provide formal Rocq specifications that connect Rust types to their Rocq models, enabling symbolic execution and proofs.

## Log of tips (newest first)

- Run `make jinja` to re-build all the Jinja generated files.

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

8. **Polymorphic types in Jinja templates**: Keep polymorphic types (like `ToUintError<T>`) manual in links files with comment `(* Note: ... is polymorphic, kept manually for now *)` rather than generating them with Jinja macros.

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
Require Import RocqOfRust.simulate.M.
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

1. **`gas_macro_eq H gas set_instruction_result`**: Handles gas recording, creates branches for OutOfGas case
2. **`popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result`**: Handles stack pop operations, creates branches for StackUnderflow case
3. **`get_can_access`**: Handles reference access operations
4. **`eapply Run.Call. { apply SomeModule.some_eq. }`**: Handles method calls with their corresponding `_eq` lemmas
5. **`apply Run.Pure`**: Finalizes the proof when no more operations remain

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

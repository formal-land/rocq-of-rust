# Claude Instructions for RocqOfRust Links Development

This document captures patterns and guidelines for creating "links" files in the RocqOfRust project. Links files provide formal Rocq specifications that connect Rust types to their Rocq models, enabling symbolic execution and proofs.

## Directory Structure

Links files are placed in a `links/` subdirectory next to the generated `.v` files:
```
some_crate/
  lib.v           # Generated Rocq code from Rust
  links/
    lib.v         # Links file with specifications
```

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
      forall (input : Ref.t Pointer.Kind.Ref (list U8.t)),
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
    (self : Ref.t Pointer.Kind.Ref Account.t) :
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

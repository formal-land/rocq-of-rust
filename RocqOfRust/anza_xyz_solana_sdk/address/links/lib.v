Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import anza_xyz_solana_sdk.address.lib.
Require Import core.links.array.

(* pub struct Address(pub(crate) [u8; 32]); *)
Module Address.
  Record t : Set := {
    value : array.t U8.t {| Integer.value := 32 |};
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "solana_address::Address";
    φ x := Value.StructTuple "solana_address::Address" [] [] [φ x.(value)];
  }.

  Definition of_ty : OfTy.t (Ty.path "solana_address::Address").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with value value' :
    value' = φ value ->
    Value.StructTuple "solana_address::Address" [] [] [φ value] = φ (Build_t value).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (value : array.t U8.t {| Integer.value := 32 |}) value' :
    value' = φ value ->
    OfValue.t (Value.StructTuple "solana_address::Address" [] [] [φ value]).
  Proof. econstructor; eapply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "solana_address::Address" 0) :=
    {|
      SubPointer.Runner.projection x := Some x.(value);
      SubPointer.Runner.injection x y := Some (x <| value := y |>);
    |}.

    Lemma get_0_is_valid :
      SubPointer.Runner.Valid.t get_0.
    Proof. now constructor. Qed.
    Smpl Add apply get_0_is_valid : run_sub_pointer.
  End SubPointer.
End Address.

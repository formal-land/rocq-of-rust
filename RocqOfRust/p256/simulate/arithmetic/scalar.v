From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.links.aliases.
Require Import revm.revm_precompile.simulate.modexp.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

(** Executable specialization of p256/arithmetic/scalar.rs. Values are canonical
    residues, not Rust's Montgomery limbs. Valid records the representation
    bound. Arithmetic reduces explicitly; this is not a limb correspondence proof.
    Modular inversion reuses the existing Modexp.pow_mod mathematical helper;
    no REVM gas rules or precompile dispatcher are used here. *)
Module Scalar.
  Definition MODULUS : aliases.U256.t := {| Uint.value := 115792089210356248762697446949407573529996955224135760342422259061068512044369 |}.

  Record t : Set := { repr : aliases.U256.t }.

  Module Valid.
    Definition t (value : t) : Prop :=
      0 <= value.(repr).(Uint.value) < MODULUS.(Uint.value).
  End Valid.

  Definition ZERO : t := {| repr := {| Uint.value := 0 |} |}.

  Definition ONE : t := {| repr := {| Uint.value := 1 |} |}.

  Definition from_bytes (input : list u8) : option t :=
    if negb (Nat.eqb (List.length input) 32 &&
      List.forallb (fun byte => (0 <=? byte.(Integer.value)) &&
        (byte.(Integer.value) <? 256)) input) then None else
    let value := List.fold_left
      (fun accumulator byte => 256 * accumulator + byte.(Integer.value)) input 0 in
    if value <? MODULUS.(Uint.value)
    then Some {| repr := {| Uint.value := value |} |} else None.

  Definition add (left right : t) : t :=
    {| repr := {| Uint.value :=
      (left.(repr).(Uint.value) + right.(repr).(Uint.value)) mod MODULUS.(Uint.value) |} |}.

  Definition sub (left right : t) : t :=
    {| repr := {| Uint.value :=
      (left.(repr).(Uint.value) - right.(repr).(Uint.value)) mod MODULUS.(Uint.value) |} |}.

  Definition mul (left right : t) : t :=
    {| repr := {| Uint.value :=
      (left.(repr).(Uint.value) * right.(repr).(Uint.value)) mod MODULUS.(Uint.value) |} |}.

  Definition square (value : t) : t := mul value value.

  Definition is_zero (value : t) : bool := Z.eqb value.(repr).(Uint.value) 0.

  Definition eq (left right : t) : bool :=
    Z.eqb left.(repr).(Uint.value) right.(repr).(Uint.value).

  Definition invert (value : t) : option t :=
    if is_zero value then None else Some
      {| repr := {| Uint.value := Modexp.pow_mod value.(repr).(Uint.value)
        (MODULUS.(Uint.value) - 2) MODULUS.(Uint.value) |} |}.

  Definition reduce (value : aliases.U256.t) : t :=
    {| repr := {| Uint.value := value.(Uint.value) mod MODULUS.(Uint.value) |} |}.

  Definition reduce_bytes (input : list u8) : option t :=
    if negb (Nat.eqb (List.length input) 32 &&
      List.forallb (fun byte => (0 <=? byte.(Integer.value)) &&
        (byte.(Integer.value) <? 256)) input) then None else
    Some (reduce {| Uint.value := List.fold_left
      (fun accumulator byte => 256 * accumulator + byte.(Integer.value)) input 0 |}).
End Scalar.

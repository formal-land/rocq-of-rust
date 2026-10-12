From Stdlib Require Import Bool List ZArith.
Require Import revm.revm_precompile.simulate.sha256.

Import ListNotations.
Open Scope Z_scope.

(** The EIP-4844 point-evaluation precompile. This executable slice handles
    the identity commitment/proof pair. Arbitrary BLS12-381 KZG verification
    remains an explicit [Unsupported] result. *)
Module KzgPointEvaluation.
  Definition gas_cost : Z := 50000.
  Definition scalar_modulus : Z :=
    52435875175126190479447740508185965837690552500527637822603658699938581184513.

  Definition decode_be (input : list Z) : Z :=
    List.fold_left (fun value byte => 256 * value + byte) input 0.

  Definition encode_be (width : nat) (value : Z) : list Z :=
    List.map (fun i => Z.land (Z.shiftr value (8 * Z.of_nat (width - S i))) 255)
      (List.seq 0 width).

  Definition return_value : list Z :=
    encode_be 32 4096 ++ encode_be 32 scalar_modulus.

  (** The canonical IETF compressed encoding of the BLS12-381 G1 identity. *)
  Definition infinity : list Z := 192 :: List.repeat 0 47.

  Definition versioned_hash (commitment : list Z) : list Z :=
    1 :: List.tl (Sha256.hash commitment).

  Definition bytes_eq (left right : list Z) : bool :=
    if List.list_eq_dec Z.eq_dec left right then true else false.

  Module Result.
    Inductive t : Set :=
    | Success (cost : Z) (output : list Z)
    | OutOfGas
    | InvalidInput
    | Unsupported.
  End Result.

  Definition run (input : list Z) (gas_limit : Z) : Result.t :=
    if gas_limit <? gas_cost then Result.OutOfGas else
    if negb (Nat.eqb (List.length input) 192) then Result.InvalidInput else
    let expected_hash := List.firstn 32 input in
    let z := List.firstn 32 (List.skipn 32 input) in
    let y := List.firstn 32 (List.skipn 64 input) in
    let commitment := List.firstn 48 (List.skipn 96 input) in
    let proof := List.firstn 48 (List.skipn 144 input) in
    if negb (bytes_eq expected_hash (versioned_hash commitment))
    then Result.InvalidInput else
    if (scalar_modulus <=? decode_be z) || (scalar_modulus <=? decode_be y)
    then Result.InvalidInput else
    if bytes_eq commitment infinity && bytes_eq proof infinity
    then if decode_be y =? 0
      then Result.Success gas_cost return_value
      else Result.InvalidInput
    else Result.Unsupported.
End KzgPointEvaluation.

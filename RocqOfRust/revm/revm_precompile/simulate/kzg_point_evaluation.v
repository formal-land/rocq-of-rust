From Stdlib Require Import Bool List ZArith.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.arkworks.
Require Import revm.revm_precompile.simulate.sha256.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

(** Executable entry point following kzg_point_evaluation.rs. Rust byte and
    gas bounds are preconditions; the integer fixture adapter checks them. *)
Module kzg_point_evaluation.
  Definition GAS_COST : u64 := 50000.

  Definition VERSIONED_HASH_VERSION_KZG : u8 := 1.

  Definition RETURN_VALUE : list u8 :=
    List.repeat (0 : u8) 30 ++ [(16 : u8); (0 : u8)] ++
    [(115 : u8); (237 : u8); (167 : u8); (83 : u8); (41 : u8); (157 : u8); (125 : u8); (72 : u8);
      (51 : u8); (57 : u8); (216 : u8); (8 : u8); (9 : u8); (161 : u8); (216 : u8); (5 : u8);
      (83 : u8); (189 : u8); (164 : u8); (2 : u8); (255 : u8); (254 : u8); (91 : u8); (254 : u8);
      (255 : u8); (255 : u8); (255 : u8); (255 : u8); (0 : u8); (0 : u8); (0 : u8); (1 : u8)].

  (** The existing independent SHA-256 provider uses integer byte lists.
      Conversion is confined to this provider boundary. *)
  Definition kzg_to_versioned_hash (commitment : list u8) : list u8 :=
    VERSIONED_HASH_VERSION_KZG ::
      List.map (fun byte => ({| Integer.value := byte |} : u8))
        (List.tl (Sha256.hash (List.map Integer.value commitment))).

  Definition run (input : list u8) (gas_limit : u64) : option PrecompileResult.t :=
    if gas_limit.(Integer.value) <? GAS_COST.(Integer.value) then
      Some (Result.Err PrecompileError.OutOfGas)
    else if negb (Nat.eqb (List.length input) 192) then
      Some (Result.Err PrecompileError.BlobInvalidInputLength)
    else
      let versioned_hash := List.firstn 32 input in
      let commitment := List.firstn 48 (List.skipn 96 input) in
      if negb (List.forallb
          (fun pair => Z.eqb (fst pair).(Integer.value) (snd pair).(Integer.value))
          (List.combine (kzg_to_versioned_hash commitment) versioned_hash)) then
        Some (Result.Err PrecompileError.BlobMismatchedVersion)
      else
        let z := List.firstn 32 (List.skipn 32 input) in
        let y := List.firstn 32 (List.skipn 64 input) in
        let proof := List.firstn 48 (List.skipn 144 input) in
        match arkworks.verify_kzg_proof commitment z y proof with
        | Some true => Some (Result.Ok (Impl_PrecompileOutput.new GAS_COST
            (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice RETURN_VALUE)))
        | Some false => Some (Result.Err PrecompileError.BlobVerifyKzgProofFailed)
        | None => None
        end.
End kzg_point_evaluation.

(** Fixture-facing integer adapter. Unexpected pairing failures remain
    incomplete, distinct from an invalid proof. *)
Module KzgPointEvaluation.
  Definition gas_cost : Z := kzg_point_evaluation.GAS_COST.(Integer.value).

  Definition scalar_modulus : Z :=
    52435875175126190479447740508185965837690552500527637822603658699938581184513.

  Definition decode_be (input : list Z) : Z :=
    List.fold_left (fun value byte => 256 * value + byte) input 0.

  Definition encode_be (width : nat) (value : Z) : list Z :=
    List.map (fun i => Z.land (Z.shiftr value (8 * Z.of_nat (width - S i))) 255)
      (List.seq 0 width).

  Definition return_value : list Z :=
    List.map Integer.value kzg_point_evaluation.RETURN_VALUE.

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
    if negb (gas_limit <? 18446744073709551616) then Result.InvalidInput else
    if negb (List.forallb (fun byte => (0 <=? byte) && (byte <? 256)) input)
    then Result.InvalidInput else
    match kzg_point_evaluation.run
      (List.map (fun byte => ({| Integer.value := byte |} : u8)) input)
      ({| Integer.value := gas_limit |} : u64) with
    | Some (core.links.result.Result.Ok output) =>
      Result.Success output.(PrecompileOutput.gas_used).(Integer.value)
        (List.map Integer.value
          output.(PrecompileOutput.bytes).(alloy_primitives.bytes.links.mod.Bytes.value)
            .(bytes.links.bytes.Bytes.value))
    | Some (core.links.result.Result.Err PrecompileError.OutOfGas) => Result.OutOfGas
    | Some (core.links.result.Result.Err _) => Result.InvalidInput
    | None => Result.Unsupported
    end.
End KzgPointEvaluation.

Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.sha256.
Require Import revm.revm_precompile.simulate.ripemd160.
Require Import revm.revm_precompile.simulate.secp256k1.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.blake2.
Require Import revm.revm_precompile.simulate.bn254.
Require Import revm.revm_precompile.simulate.bn254_pairing_run.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.
Require Import revm.revm_precompile.simulate.bls12_381.g1_add.
Require Import revm.revm_precompile.simulate.bls12_381.g1_msm.
Require Import revm.revm_precompile.simulate.bls12_381.g2_add.
Require Import revm.revm_precompile.simulate.bls12_381.g2_msm.
Require Import revm.revm_precompile.simulate.bls12_381.pairing.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp_to_g1.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp2_to_g2.
Require Import revm.revm_precompile.simulate.secp256r1.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

Module EthereumPrecompiles.
  Definition addresses (spec : SpecId.t) : list Address.t :=
    let numbers := if Impl_SpecId.is_enabled_in spec SpecId.OSAKA then
        List.seq 1 17 ++ [256%nat]
      else if Impl_SpecId.is_enabled_in spec SpecId.PRAGUE then List.seq 1 17
      else if Impl_SpecId.is_enabled_in spec SpecId.CANCUN then List.seq 1 10
      else if Impl_SpecId.is_enabled_in spec SpecId.ISTANBUL then List.seq 1 9
      else if Impl_SpecId.is_enabled_in spec SpecId.BYZANTIUM then List.seq 1 8
      else List.seq 1 4 in
    List.map (fun number => {| Address.value := Z.of_nat number |}) numbers.

  Definition contains (spec : SpecId.t) (address : Address.t) : bool :=
    List.existsb (fun entry => Z.eqb address.(Address.value) entry.(Address.value)) (addresses spec).

  Definition output (cost : u64) (bytes : list u8) : PrecompileResult.t :=
    Result.Ok (Impl_PrecompileOutput.new cost (Impl_Bytes.copy_from_slice bytes)).

  (** The existing cryptographic kernels use mathematical integers internally.
      Only this adapter converts their byte vectors and costs to Rust types. *)
  Definition integer_output (cost : u64) (bytes : list Z) : PrecompileResult.t :=
    output cost (List.map (fun byte => {| Integer.value := byte |}) bytes).

  Definition linear (base word_cost : u64) (input : list u8) (limit : u64)
      (hash : list Z -> list Z) : PrecompileResult.t :=
    let words : u64 := {| Integer.value := (Z.of_nat (List.length input) + 31) / 32 |} in
    let cost := BinOp.Wrap.add base (BinOp.Wrap.mul word_cost words) in
    if Z.ltb limit.(Integer.value) cost.(Integer.value) then Result.Err PrecompileError.OutOfGas
    else integer_output cost (hash (List.map Integer.value input)).

  Definition modexp (spec : SpecId.t) (input : list u8) (limit : u64) : PrecompileResult.t :=
    let run := if Impl_SpecId.is_enabled_in spec SpecId.OSAKA then Modexp.run_osaka else
      if Impl_SpecId.is_enabled_in spec SpecId.BERLIN then Modexp.run_berlin else Modexp.run_byzantium in
    match run (List.map Integer.value input) limit.(Integer.value) with
    | Modexp.Result.Success cost bytes => integer_output {| Integer.value := cost |} bytes
    | Modexp.Result.OutOfGas => Result.Err PrecompileError.OutOfGas
    | Modexp.Result.InvalidLength => Result.Err PrecompileError.ModexpEip7823LimitSize
    end.

  Definition blake2 (input : list u8) (limit : u64) : PrecompileResult.t :=
    match Blake2.run (List.map Integer.value input) limit.(Integer.value) with
    | Blake2.Result.Success cost bytes => integer_output {| Integer.value := cost |} bytes
    | Blake2.Result.OutOfGas => Result.Err PrecompileError.OutOfGas
    | Blake2.Result.WrongLength => Result.Err PrecompileError.Blake2WrongLength
    | Blake2.Result.WrongFinalIndicatorFlag => Result.Err PrecompileError.Blake2WrongFinalIndicatorFlag
    end.

  Definition bn254 (spec : SpecId.t) (multiply : bool) (input : list u8) (limit : u64) : PrecompileResult.t :=
    let istanbul := Impl_SpecId.is_enabled_in spec SpecId.ISTANBUL in
    let cost : u64 := if multiply then (if istanbul then 6000 else 40000) else (if istanbul then 150 else 500) in
    let run := if multiply then Bn254.run_mul else Bn254.run_add in
    match run (List.map Integer.value input) cost.(Integer.value) limit.(Integer.value) with
    | Bn254.Result.Success cost bytes => integer_output {| Integer.value := cost |} bytes
    | Bn254.Result.OutOfGas => Result.Err PrecompileError.OutOfGas
    | Bn254.Result.InvalidPoint Bn254.Error.FieldPointNotAMember => Result.Err PrecompileError.Bn254FieldPointNotAMember
    | Bn254.Result.InvalidPoint Bn254.Error.AffineGFailedToCreate => Result.Err PrecompileError.Bn254AffineGFailedToCreate
    end.

  Definition bn254_pairing (spec : SpecId.t) (input : list u8) (limit : u64) : PrecompileResult.t :=
    let istanbul := Impl_SpecId.is_enabled_in spec SpecId.ISTANBUL in
    let base : u64 := if istanbul then 45000 else 100000 in
    let pair : u64 := if istanbul then 34000 else 80000 in
    match Bn254PairingRun.run base.(Integer.value) pair.(Integer.value) (List.map Integer.value input) limit.(Integer.value) with
    | Bn254PairingRun.Result.Success cost bytes => integer_output {| Integer.value := cost |} bytes
    | Bn254PairingRun.Result.OutOfGas => Result.Err PrecompileError.OutOfGas
    | Bn254PairingRun.Result.InvalidLength => Result.Err PrecompileError.Bn254PairLength
    | Bn254PairingRun.Result.InvalidField => Result.Err PrecompileError.Bn254FieldPointNotAMember
    | Bn254PairingRun.Result.InvalidPoint => Result.Err PrecompileError.Bn254AffineGFailedToCreate
    end.

  (** [None] is retained from a cryptographic evaluator if it cannot finish;
      the provider must propagate it as an incomplete execution. *)
  Definition execute (spec : SpecId.t) (address : Address.t) (input : list u8) (limit : u64)
      : option PrecompileResult.t :=
    let address := address.(Address.value) in
    if Z.eqb address 1 then Some (linear 3000 0 input limit Secp256k1.output) else
    if Z.eqb address 2 then Some (linear 60 12 input limit Sha256.hash) else
    if Z.eqb address 3 then Some (linear 600 120 input limit (fun input => List.repeat 0 12 ++ Ripemd160.hash input)) else
    if Z.eqb address 4 then Some (linear 15 3 input limit (fun input => input)) else
    if Z.eqb address 5 then Some (modexp spec input limit) else
    if Z.eqb address 6 then Some (bn254 spec false input limit) else
    if Z.eqb address 7 then Some (bn254 spec true input limit) else
    if Z.eqb address 8 then Some (bn254_pairing spec input limit) else
    if Z.eqb address 9 then Some (blake2 input limit) else
    if Z.eqb address 10 then kzg_point_evaluation.run input limit else
    if Z.eqb address 11 then g1_add.g1_add input limit else
    if Z.eqb address 12 then g1_msm.g1_msm input limit else
    if Z.eqb address 13 then g2_add.g2_add input limit else
    if Z.eqb address 14 then g2_msm.g2_msm input limit else
    if Z.eqb address 15 then pairing.pairing input limit else
    if Z.eqb address 16 then map_fp_to_g1.map_fp_to_g1 input limit else
    if Z.eqb address 17 then map_fp2_to_g2.map_fp2_to_g2 input limit else
    if Z.eqb address 256 then secp256r1.p256_verify_osaka input limit else None.
End EthereumPrecompiles.

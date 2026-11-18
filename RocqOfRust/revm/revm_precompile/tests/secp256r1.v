From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.secp256r1.
Require Import simulate.RocqOfRust.
Import ListNotations.

Module Secp256r1Test.
  Definition zero_byte : u8 := {| Integer.value := 0 |}.

  Definition empty_output (cost : u64) : option PrecompileResult.t :=
    Some (Result.Ok (Impl_PrecompileOutput.new cost
      alloy_primitives.bytes.simulate.mod.Impl_Bytes.new)).

  Example osaka_empty_exact_gas :
    secp256r1.p256_verify_osaka [] {| Integer.value := 6900 |} =
      empty_output {| Integer.value := 6900 |}.
  Proof. reflexivity. Qed.

  Example osaka_empty_below_gas :
    secp256r1.p256_verify_osaka [] {| Integer.value := 6899 |} =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. reflexivity. Qed.

  Example osaka_long_input :
    secp256r1.p256_verify_osaka (List.repeat zero_byte 256)
      {| Integer.value := 6900 |} = empty_output {| Integer.value := 6900 |}.
  Proof. reflexivity. Qed.

  Example osaka_short_input :
    secp256r1.p256_verify_osaka (List.repeat zero_byte 159)
      {| Integer.value := 6900 |} = empty_output {| Integer.value := 6900 |}.
  Proof. reflexivity. Qed.

  Example osaka_one_byte_over :
    secp256r1.p256_verify_osaka (List.repeat zero_byte 161)
      {| Integer.value := 6900 |} = empty_output {| Integer.value := 6900 |}.
  Proof. reflexivity. Qed.

  Example osaka_zero_signature_returns_empty :
    secp256r1.p256_verify_osaka (List.repeat zero_byte 160)
      {| Integer.value := 6900 |} = empty_output {| Integer.value := 6900 |}.
  Proof. reflexivity. Qed.

  Example osaka_oog_precedes_signature_verification :
    secp256r1.p256_verify_osaka (List.repeat zero_byte 160)
      {| Integer.value := 6899 |} = Some (Result.Err PrecompileError.OutOfGas).
  Proof. reflexivity. Qed.

  Example pre_osaka_exact_gas :
    secp256r1.p256_verify [] {| Integer.value := 3450 |} =
      empty_output {| Integer.value := 3450 |}.
  Proof. reflexivity. Qed.

  Example pre_osaka_below_gas :
    secp256r1.p256_verify [] {| Integer.value := 3449 |} =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. reflexivity. Qed.

  Example osaka_does_not_use_old_price :
    secp256r1.p256_verify_osaka [] {| Integer.value := 3450 |} =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. reflexivity. Qed.

  Example osaka_excess_gas_preserves_charge :
    secp256r1.p256_verify_osaka [] {| Integer.value := 10000 |} =
      empty_output {| Integer.value := 6900 |}.
  Proof. reflexivity. Qed.
End Secp256r1Test.

Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.

(** Executable gas and input-length paths of secp256r1.rs. The outer option
    marks unsupported cryptographic verification, not a Rust precompile error.
    Exactly 160-byte inputs remain unsupported when sufficient gas is supplied.
    Rust integer and byte validity bounds are assumed, as for the linked types. *)
Module secp256r1.
  Definition P256VERIFY_ADDRESS : u64 := {| Integer.value := 256 |}.

  Definition P256VERIFY_BASE_GAS_FEE : u64 := {| Integer.value := 3450 |}.

  Definition P256VERIFY_BASE_GAS_FEE_OSAKA : u64 := {| Integer.value := 6900 |}.

  Definition verify_impl (input : list u8) : option bool :=
    if Nat.eqb (List.length input) 160 then None else Some false.

  Definition p256_verify_inner (input : list u8) (gas_limit gas_cost : u64)
      : option PrecompileResult.t :=
    if Z.ltb gas_limit.(Integer.value) gas_cost.(Integer.value)
    then Some (Result.Err PrecompileError.OutOfGas)
    else
      match verify_impl input with
      | Some false => Some (Result.Ok
          (Impl_PrecompileOutput.new gas_cost alloy_primitives.bytes.simulate.mod.Impl_Bytes.new))
      | Some true | None => None
      end.

  Definition p256_verify (input : list u8) (gas_limit : u64)
      : option PrecompileResult.t :=
    p256_verify_inner input gas_limit P256VERIFY_BASE_GAS_FEE.

  Definition p256_verify_osaka (input : list u8) (gas_limit : u64)
      : option PrecompileResult.t :=
    p256_verify_inner input gas_limit P256VERIFY_BASE_GAS_FEE_OSAKA.
End secp256r1.

Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import p256.simulate.ecdsa.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.

(** Executable secp256r1.rs precompile and P256 verification provider.
    The provider models reduced field/scalar arithmetic; it does not establish
    correspondence with Rust limb operations or a cryptographic correctness proof. *)
Module secp256r1.
  Definition P256VERIFY_ADDRESS : u64 := {| Integer.value := 256 |}.

  Definition P256VERIFY_BASE_GAS_FEE : u64 := {| Integer.value := 3450 |}.

  Definition P256VERIFY_BASE_GAS_FEE_OSAKA : u64 := {| Integer.value := 6900 |}.

  Definition verify_signature (msg sig pk : list u8) : option unit :=
    P256Ecdsa.verify_signature msg sig pk.

  Definition verify_impl (input : list u8) : bool :=
    if negb (Nat.eqb (List.length input) 160) then false else
    let msg := List.firstn 32 input in
    let sig := List.firstn 64 (List.skipn 32 input) in
    let pk := List.skipn 96 input in
    match verify_signature msg sig pk with
    | Some tt => true
    | None => false
    end.

  Definition p256_verify_inner (input : list u8) (gas_limit gas_cost : u64)
      : option PrecompileResult.t :=
    if Z.ltb gas_limit.(Integer.value) gas_cost.(Integer.value)
    then Some (Result.Err PrecompileError.OutOfGas)
    else
      let result := if verify_impl input then
        alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
          (List.repeat ({| Integer.value := 0 |} : u8) 31 ++
           ({| Integer.value := 1 |} : u8) :: nil)%list
        else alloy_primitives.bytes.simulate.mod.Impl_Bytes.new in
      Some (Result.Ok (Impl_PrecompileOutput.new gas_cost result)).

  Definition p256_verify (input : list u8) (gas_limit : u64)
      : option PrecompileResult.t :=
    p256_verify_inner input gas_limit P256VERIFY_BASE_GAS_FEE.

  Definition p256_verify_osaka (input : list u8) (gas_limit : u64)
      : option PrecompileResult.t :=
    p256_verify_inner input gas_limit P256VERIFY_BASE_GAS_FEE_OSAKA.
End secp256r1.

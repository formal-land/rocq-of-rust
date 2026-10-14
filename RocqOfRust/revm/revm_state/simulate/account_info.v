From Stdlib Require Import List ZArith.

Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_bytecode.links.bytecode.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context_interface.links.journaled_state.

Module Impl_AccountInfo.
  Definition set_balance (self : AccountInfo.t) (balance : aliases.U256.t) : AccountInfo.t :=
    self <| AccountInfo.balance := balance |>.

  Definition set_nonce (self : AccountInfo.t) (nonce : u64) : AccountInfo.t :=
    self <| AccountInfo.nonce := nonce |>.

  Definition set_code_hash (self : AccountInfo.t) (code_hash : aliases.B256.t) : AccountInfo.t :=
    self <| AccountInfo.code := None |> <| AccountInfo.code_hash := code_hash |>.

  Definition set_code (self : AccountInfo.t) (code : Bytecode.t) : AccountInfo.t :=
    self <| AccountInfo.code_hash := Impl_Bytecode.hash_slow code |>
      <| AccountInfo.code := Some code |>.

  Definition set_code_and_hash (self : AccountInfo.t) (code : Bytecode.t)
      (code_hash : aliases.B256.t) : AccountInfo.t :=
    self <| AccountInfo.code_hash := code_hash |> <| AccountInfo.code := Some code |>.
End Impl_AccountInfo.

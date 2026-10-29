From Stdlib Require Import List ZArith.

Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_bytecode.links.bytecode.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_primitives.simulate.lib.
Require Import ruint.links.lib.

Module Impl_Default_for_AccountInfo.
  Definition default : AccountInfo.t := {|
    AccountInfo.balance := {| Uint.value := 0 |};
    AccountInfo.nonce := 0;
    AccountInfo.code_hash := KECCAK_EMPTY;
    AccountInfo.code := Some {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice nil |};
  |}.
End Impl_Default_for_AccountInfo.

Module Impl_AccountInfo.
  Definition is_empty_code_hash (self : AccountInfo.t) : bool :=
    Z.eqb (FixedBytes.to_Z self.(AccountInfo.code_hash)) (FixedBytes.to_Z KECCAK_EMPTY).

  Definition is_empty (self : AccountInfo.t) : bool :=
    let code_empty := is_empty_code_hash self ||
      Z.eqb (FixedBytes.to_Z self.(AccountInfo.code_hash)) 0 in
    code_empty && Z.eqb self.(AccountInfo.balance).(Uint.value) 0 &&
      (self.(AccountInfo.nonce) =i 0).

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

Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.common.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

(** gas/calc.rs transaction helpers, separated from instruction costs to keep
    recompilation of the transaction port independent of opcode proofs. *)
Module InitialTxGas.
  Definition get_tokens_in_calldata (input : list u8) (is_istanbul : bool) : u64 :=
    let zero_len : u64 := {| Integer.value := Z.of_nat (List.length
      (List.filter (fun byte => Z.eqb byte.(Integer.value) 0) input)) |} in
    let input_len : u64 := {| Integer.value := Z.of_nat (List.length input) |} in
    let non_zero_len := BinOp.Wrap.sub input_len zero_len in
    BinOp.Wrap.add zero_len (BinOp.Wrap.mul non_zero_len (if is_istanbul then 4 else 17)).

  Definition calc_tx_floor_cost (tokens : u64) : u64 :=
    BinOp.Wrap.add (BinOp.Wrap.mul tokens 10) 21000.

  Definition calculate_initial_tx_gas (spec : SpecId.t) (input : list u8) (is_create : bool)
      (access_list_accounts access_list_storages authorization_list_num : u64) : InitialAndFloorGas.t :=
    let tokens := get_tokens_in_calldata input (Impl_SpecId.is_enabled_in spec SpecId.ISTANBUL) in
    let gas := BinOp.Wrap.mul tokens 4 in
    let gas := BinOp.Wrap.add gas (BinOp.Wrap.mul access_list_accounts 2400) in
    let gas := BinOp.Wrap.add gas (BinOp.Wrap.mul access_list_storages 1900) in
    let gas := BinOp.Wrap.add gas
      (if is_create && Impl_SpecId.is_enabled_in spec SpecId.HOMESTEAD then 53000 else 21000) in
    let gas := if is_create && Impl_SpecId.is_enabled_in spec SpecId.SHANGHAI then
      BinOp.Wrap.add gas (initcode_cost {| Integer.value := Z.of_nat (List.length input) |}) else gas in
    if Impl_SpecId.is_enabled_in spec SpecId.PRAGUE then {|
      InitialAndFloorGas.initial_gas := BinOp.Wrap.add gas (BinOp.Wrap.mul authorization_list_num 25000);
      InitialAndFloorGas.floor_gas := calc_tx_floor_cost tokens |}
    else {| InitialAndFloorGas.initial_gas := gas; InitialAndFloorGas.floor_gas := 0 |}.

  Definition calculate_initial_tx_gas_for_tx (tx : TxEnv.t) (spec : SpecId.t) : InitialAndFloorGas.t :=
    let '(accounts, storages) := if Z.eqb tx.(TxEnv.tx_type).(Integer.value) 0 then
        ((0 : u64), (0 : u64))
      else List.fold_left (fun '(accounts, storages) item =>
        (BinOp.Wrap.add accounts 1, BinOp.Wrap.add storages
          {| Integer.value := Z.of_nat (List.length item.(AccessListItem.storage_keys)) |}))
        tx.(TxEnv.access_list) ((0 : u64), (0 : u64)) in
    calculate_initial_tx_gas spec tx.(TxEnv.data).(Bytes.value).(bytes.Bytes.value)
      (match tx.(TxEnv.kind) with TxKind.Create => true | TxKind.Call _ => false end)
      accounts storages {| Integer.value := Z.of_nat (List.length tx.(TxEnv.authorization_list)) |}.
End InitialTxGas.

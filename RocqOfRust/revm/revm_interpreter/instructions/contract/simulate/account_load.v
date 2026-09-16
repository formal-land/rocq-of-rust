Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.links.bytes.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import simulate.RocqOfRust.

Definition new_account_cost (is_spurious_dragon transfers_value : bool) : u64 :=
  if negb is_spurious_dragon || transfers_value then NEWACCOUNT else 0.

Definition loaded_bytecode (account : AccountInfoLoad.t) : Bytecode.t :=
  match account.(AccountInfoLoad.account) with
  | Cow.Owned info =>
      match info.(AccountInfo.code) with
      | Some code => code
      | None => {| Bytecode.original_bytes := Impl_Bytes.new |}
      end
  | Cow.Borrowed _ =>
      {| Bytecode.original_bytes := account_info_load_original_bytes account |}
  end.

(** This projection assumes bytes from a valid native raw-bytecode constructor.
    The byte-only model does not represent a forced legacy EF0100 encoding. *)
Definition delegated_address (code : Bytecode.t) : option Address.t :=
  match code.(Bytecode.original_bytes)
    .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) with
  | magic0 :: magic1 :: version :: address =>
      if (magic0.(Integer.value) =? 239) &&
         (magic1.(Integer.value) =? 1) &&
         (version.(Integer.value) =? 0) &&
         Nat.eqb (List.length address) 20 then
        Some {| Address.value :=
          List.fold_left
            (fun (n : Z) (byte : u8) => Z.add (Z.mul 256 n) byte.(Integer.value))
            address 0 |}
      else None
  | _ => None
  end.

Definition load_account_delegated
    {H : Set} `{Link H}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (host : H) (spec : SpecId.t) (remaining_gas : u64)
    (address : Address.t) (transfers_value create_empty_account : bool) :
    Result.t (u64 * Bytecode.t * aliases.B256.t) LoadError.t * H :=
  let is_berlin := Impl_SpecId.is_enabled_in spec SpecId.BERLIN in
  let skip_cold := is_berlin &&
    (remaining_gas.(Integer.value) <? COLD_ACCOUNT_ACCESS_COST_ADDITIONAL.(Integer.value)) in
  let '(result, host) :=
    IHost.(Host.load_account_info_skip_cold_load) host address true skip_cold in
  match result with
  | Result.Err error => (Result.Err error, host)
  | Result.Ok account =>
      let cost : u64 := if is_berlin && account.(AccountInfoLoad.is_cold)
        then COLD_ACCOUNT_ACCESS_COST_ADDITIONAL else 0 in
      let code := loaded_bytecode account in
      let hash := account_info_load_code_hash account in
      if create_empty_account && account.(AccountInfoLoad.is_empty) then
        (Result.Ok
          (cost +i new_account_cost
            (Impl_SpecId.is_enabled_in spec SpecId.SPURIOUS_DRAGON)
            transfers_value, code, hash), host)
      else
        match delegated_address code with
        | None => (Result.Ok (cost, code, hash), host)
        | Some delegate =>
            let cost := cost +i WARM_STORAGE_READ_COST in
            if remaining_gas.(Integer.value) <? cost.(Integer.value) then
              (Result.Err LoadError.ColdLoadSkipped, host)
            else
              let skip_cold := remaining_gas.(Integer.value) <?
                (cost +i COLD_ACCOUNT_ACCESS_COST_ADDITIONAL).(Integer.value) in
              let '(result, host) := IHost.(Host.load_account_info_skip_cold_load)
                host delegate true skip_cold in
              match result with
              | Result.Err error => (Result.Err error, host)
              | Result.Ok delegate =>
                  let cost := if delegate.(AccountInfoLoad.is_cold)
                    then cost +i COLD_ACCOUNT_ACCESS_COST_ADDITIONAL else cost in
                  (Result.Ok (cost, loaded_bytecode delegate,
                    account_info_load_code_hash delegate), host)
              end
        end
  end.

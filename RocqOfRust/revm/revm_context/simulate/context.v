Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.local.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_state.simulate.account_info.
Require Import ruint.links.lib.

(** Default Ethereum context types, with the database and its error generic. *)
Module Context.
  Record t (DB Error : Set) : Set := {
    block : BlockEnv.t;
    tx : TxEnv.t;
    cfg : CfgEnv.t;
    journaled_state : Journal.t DB;
    chain : unit;
    local : LocalContext.t;
    error : Result.t unit (ContextError.t Error);
  }.

  Arguments block {DB Error}.

  Arguments tx {DB Error}.

  Arguments cfg {DB Error}.

  Arguments journaled_state {DB Error}.

  Arguments chain {DB Error}.

  Arguments local {DB Error}.

  Arguments error {DB Error}.
End Context.

Module Impl_Context.
  Definition new {DB Error : Set} (database : DB) (spec : SpecId.t) : Context.t DB Error := {|
    Context.block := Impl_Default_for_BlockEnv.default;
    Context.tx := Impl_Default_for_TxEnv.default;
    Context.cfg := Impl_CfgEnv.new_with_spec spec;
    Context.journaled_state := Impl_Journal.set_spec_id (Impl_Journal.new database) spec;
    Context.chain := tt;
    Context.local := Impl_LocalContext.new;
    Context.error := Result.Ok tt;
  |}.

  Definition set_tx {DB Error : Set} (self : Context.t DB Error) (tx : TxEnv.t) : Context.t DB Error :=
    self <| Context.tx := tx |>.

  Definition set_block {DB Error : Set} (self : Context.t DB Error) (block : BlockEnv.t) : Context.t DB Error :=
    self <| Context.block := block |>.
End Impl_Context.

Module Impl_Host_for_Context.
  Definition basefee {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    {| Uint.value := self.(Context.block).(BlockEnv.basefee).(Integer.value) |}.

  Definition blob_gasprice {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    {| Uint.value := match Impl_Block_for_BlockEnv.blob_gasprice self.(Context.block) with
      | Some price => price.(Integer.value) | None => 0 end |}.

  Definition gas_limit {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    {| Uint.value := self.(Context.block).(BlockEnv.gas_limit).(Integer.value) |}.

  Definition difficulty {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    self.(Context.block).(BlockEnv.difficulty).

  Definition prevrandao {DB Error : Set} (self : Context.t DB Error) : option aliases.U256.t :=
    option_map (fun hash => {| Uint.value := FixedBytes.to_Z hash |}) self.(Context.block).(BlockEnv.prevrandao).

  Definition block_number {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    self.(Context.block).(BlockEnv.number).

  Definition timestamp {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    self.(Context.block).(BlockEnv.timestamp).

  Definition beneficiary {DB Error : Set} (self : Context.t DB Error) : Address.t :=
    self.(Context.block).(BlockEnv.beneficiary).

  Definition chain_id {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    {| Uint.value := self.(Context.cfg).(CfgEnv.chain_id).(Integer.value) |}.

  Definition effective_gas_price {DB Error : Set} (self : Context.t DB Error) : aliases.U256.t :=
    {| Uint.value := (Transaction.Fees.effective_gas_price self.(Context.tx)
      {| Integer.value := self.(Context.block).(BlockEnv.basefee).(Integer.value) |}).(Integer.value) |}.

  Definition caller {DB Error : Set} (self : Context.t DB Error) : Address.t := self.(Context.tx).(TxEnv.caller).

  Definition blob_hash {DB Error : Set} (self : Context.t DB Error) (number : usize) : option aliases.U256.t :=
    if negb (Z.eqb self.(Context.tx).(TxEnv.tx_type).(Integer.value) 3) then None else
    let hashes := self.(Context.tx).(TxEnv.blob_hashes) in
    if Z.ltb number.(Integer.value) (Z.of_nat (List.length hashes)) then
      option_map (fun hash => {| Uint.value := FixedBytes.to_Z hash |})
        (List.nth_error hashes (Z.to_nat number.(Integer.value)))
    else None.

  Definition max_initcode_size {DB Error : Set} (self : Context.t DB Error) : usize :=
    Impl_CfgEnv.max_initcode_size self.(Context.cfg).

  Definition block_hash {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (requested_number : u64) : option aliases.B256.t * Context.t DB Error :=
    let journal := self.(Context.journaled_state) in
    let '(result, database) := Database.block_hash journal.(Journal.database) requested_number in
    let self := self <| Context.journaled_state := journal <| Journal.database := database |> |> in
    match result with
    | Result.Ok hash => (Some hash, self)
    | Result.Err error => (None, self <| Context.error := Result.Err (ContextError.Db error) |>)
    end.

  Definition tload {DB Error : Set} (self : Context.t DB Error) (address : Address.t) (index : aliases.U256.t) :=
    Impl_Journal.tload self.(Context.journaled_state) address index.

  Definition tstore {DB Error : Set} (self : Context.t DB Error) (address : Address.t) (index value : aliases.U256.t) :=
    self <| Context.journaled_state := Impl_Journal.tstore self.(Context.journaled_state) address index value |>.

  Definition log {DB Error : Set} (self : Context.t DB Error) (log : Log.t LogData.t) :=
    self <| Context.journaled_state := Impl_Journal.log self.(Context.journaled_state) log |>.

  (** The repeated Rust map_err closure: cold skips leave the context error
      alone; database failures keep their concrete error for the handler. *)
  Definition finish_load {DB Error A : Set} (self : Context.t DB Error)
      (result : Result.t A (JournalLoadError.t Error) * Journal.t DB)
      : Result.t A LoadError.t * Context.t DB Error :=
    let '(result, journal) := result in
    let self := self <| Context.journaled_state := journal |> in
    match result with
    | Result.Ok value => (Result.Ok value, self)
    | Result.Err JournalLoadError.ColdLoadSkipped => (Result.Err LoadError.ColdLoadSkipped, self)
    | Result.Err (JournalLoadError.DBError error) =>
      (Result.Err LoadError.DBError, self <| Context.error := Result.Err (ContextError.Db error) |>)
    end.

  Definition selfdestruct {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address target : Address.t) (skip_cold_load : bool) :=
    option_map (finish_load self)
      (Impl_Journal.selfdestruct self.(Context.journaled_state) address target skip_cold_load).

  Definition sstore_skip_cold_load {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t) (key value : aliases.U256.t) (skip_cold_load : bool) :=
    option_map (finish_load self)
      (Impl_Journal.sstore_skip_cold_load self.(Context.journaled_state) address key value skip_cold_load).

  Definition sload_skip_cold_load {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t) (key : aliases.U256.t) (skip_cold_load : bool) :=
    option_map (finish_load self)
      (Impl_Journal.sload_skip_cold_load self.(Context.journaled_state) address key skip_cold_load).

  Definition load_account_info_skip_cold_load {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t) (load_code skip_cold_load : bool) :=
    finish_load self
      (Impl_Journal.load_account_info_skip_cold_load self.(Context.journaled_state) address load_code skip_cold_load).
  (** Default methods of context_interface/host.rs. This context always returns
      owned account observations. A borrowed observation is an invariant failure. *)
  Definition balance {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t)
      : option (option (StateLoad.t aliases.U256.t) * Context.t DB Error) :=
    let '(result, self) := load_account_info_skip_cold_load self address false false in
    match result with
    | Result.Err _ => Some (None, self)
    | Result.Ok load => match load.(AccountInfoLoad.account) with
        | Cow.Owned info => Some (Some {| StateLoad.data := info.(AccountInfo.balance);
            StateLoad.is_cold := load.(AccountInfoLoad.is_cold) |}, self)
        | Cow.Borrowed _ => None
        end
    end.

  Definition load_account_code {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t)
      : option (option (StateLoad.t Bytes.t) * Context.t DB Error) :=
    let '(result, self) := load_account_info_skip_cold_load self address true false in
    match result with
    | Result.Err _ => Some (None, self)
    | Result.Ok load => match load.(AccountInfoLoad.account) with
        | Cow.Owned info => Some (Some {| StateLoad.data := match info.(AccountInfo.code) with
            | Some code => code.(Bytecode.original_bytes) | None => Impl_Bytes.new end;
            StateLoad.is_cold := load.(AccountInfoLoad.is_cold) |}, self)
        | Cow.Borrowed _ => None
        end
    end.

  Definition load_account_code_hash {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t)
      : option (option (StateLoad.t aliases.B256.t) * Context.t DB Error) :=
    let '(result, self) := load_account_info_skip_cold_load self address false false in
    match result with
    | Result.Err _ => Some (None, self)
    | Result.Ok load => match load.(AccountInfoLoad.account) with
        | Cow.Owned info => Some (Some {| StateLoad.data :=
            if Impl_AccountInfo.is_empty info then FixedBytes.from_Z 0 else info.(AccountInfo.code_hash);
            StateLoad.is_cold := load.(AccountInfoLoad.is_cold) |}, self)
        | Cow.Borrowed _ => None
        end
    end.

  Definition load_account_delegated {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t)
      : option (option (StateLoad.t AccountLoad.t) * Context.t DB Error) :=
    let '(result, self) := load_account_info_skip_cold_load self address true false in
    match result with
    | Result.Err _ => Some (None, self)
    | Result.Ok load => match load.(AccountInfoLoad.account) with
        | Cow.Borrowed _ => None
        | Cow.Owned info =>
          let account_load := {| StateLoad.data := {|
            AccountLoad.is_delegate_account_cold := None;
            AccountLoad.is_empty := load.(AccountInfoLoad.is_empty) |};
            StateLoad.is_cold := load.(AccountInfoLoad.is_cold) |} in
          let delegate := match info.(AccountInfo.code) with
            | Some code => Impl_Bytecode.delegated_address code | None => None end in
          match delegate with
          | None => Some (Some account_load, self)
          | Some delegate =>
            let '(result, self) := load_account_info_skip_cold_load self delegate true false in
            match result with
            | Result.Err _ => Some (None, self)
            | Result.Ok delegate_load => Some (Some (account_load <| StateLoad.data := {|
                AccountLoad.is_delegate_account_cold := Some delegate_load.(AccountInfoLoad.is_cold);
                AccountLoad.is_empty := delegate_load.(AccountInfoLoad.is_empty) |} |>), self)
            end
          end
        end
    end.

  Definition sload {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t) (key : aliases.U256.t) :=
    option_map (fun '(result, self) =>
      (match result with Result.Ok value => Some value | Result.Err _ => None end, self))
      (sload_skip_cold_load self address key false).

  Definition sstore {DB Error : Set} `{Database.C DB Error}
      (self : Context.t DB Error) (address : Address.t) (key value : aliases.U256.t) :=
    option_map (fun '(result, self) =>
      (match result with Result.Ok value => Some value | Result.Err _ => None end, self))
      (sstore_skip_cold_load self address key value false).
End Impl_Host_for_Context.

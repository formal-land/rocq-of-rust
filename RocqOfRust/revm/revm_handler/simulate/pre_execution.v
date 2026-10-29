Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import lib.simulate.lib.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_context_interface.transaction.simulate.eip7702.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import revm.revm_primitives.simulate.eip7702.
Require Import revm.revm_state.simulate.lib.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.

Module PreExecution.
  Definition code_allows_transaction (code : Bytecode.t) : bool :=
    Impl_Bytecode.is_empty code ||
      match Impl_Bytecode.delegated_address code with Some _ => true | None => false end.

  Definition validate_account_nonce_and_code (info : AccountInfo.t) (tx_nonce : u64)
      (is_nonce_check_disabled : bool) : Result.t unit InvalidTransaction.t :=
    if negb (match info.(AccountInfo.code) with None => true | Some code => code_allows_transaction code end)
    then Result.Err InvalidTransaction.RejectCallerWithCode
    else if is_nonce_check_disabled then Result.Ok tt else
    match Z.compare tx_nonce.(Integer.value) info.(AccountInfo.nonce).(Integer.value) with
    | Gt => Result.Err (InvalidTransaction.NonceTooHigh tx_nonce info.(AccountInfo.nonce))
    | Lt => Result.Err (InvalidTransaction.NonceTooLow tx_nonce info.(AccountInfo.nonce))
    | Eq => Result.Ok tt
    end.

  (** Default Cargo features keep the balance and EIP-3607 checks enabled. *)
  Definition calculate_caller_fee (balance : aliases.U256.t) (tx : TxEnv.t) (block : BlockEnv.t)
      : option (Result.t aliases.U256.t InvalidTransaction.t) :=
    match Transaction.Fees.ensure_enough_balance tx balance with
    | Result.Err error => Some (Result.Err error)
    | Result.Ok _ =>
      let blob_price := match Impl_Block_for_BlockEnv.blob_gasprice block with Some price => price | None => 0 end in
      match Transaction.Fees.effective_balance_spending tx
        {| Integer.value := block.(BlockEnv.basefee).(Integer.value) |} blob_price with
      | Result.Err _ => None (* Rust expect: effective spending cannot exceed the checked maximum. *)
      | Result.Ok spending =>
        let gas_spending := Impl_Uint.wrapping_sub spending tx.(TxEnv.value) in
        Some (Result.Ok {| Uint.value := Z.max 0 (balance.(Uint.value) - gas_spending.(Uint.value)) |})
      end
    end.

  Definition validate_against_state_and_deduct_caller {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) : option (Result.t unit (EVMError.t Error) * Context.t DB Error) :=
    match Impl_Journal.load_account_mut_optional_code ctx.(Context.journaled_state) ctx.(Context.tx).(TxEnv.caller) true with
    | None => None
    | Some (result, journal) =>
      let ctx := ctx <| Context.journaled_state := journal |> in
      match result with
      | Result.Err error => Some (Result.Err (EVMError.Database error), ctx)
      | Result.Ok (caller, _) =>
        match validate_account_nonce_and_code caller.(JournaledAccount.account).(Account.info)
          ctx.(Context.tx).(TxEnv.nonce) ctx.(Context.cfg).(CfgEnv.disable_nonce_check) with
        | Result.Err error => Some (Result.Err (EVMError.Transaction error), ctx)
        | Result.Ok _ =>
          match calculate_caller_fee (Impl_JournaledAccount.balance caller) ctx.(Context.tx) ctx.(Context.block) with
          | None => None
          | Some (Result.Err error) => Some (Result.Err (EVMError.Transaction error), ctx)
          | Some (Result.Ok balance) =>
            let caller := Impl_JournaledAccount.set_balance caller balance in
            let caller := match ctx.(Context.tx).(TxEnv.kind) with
              | TxKind.Call _ => snd (Impl_JournaledAccount.bump_nonce caller)
              | TxKind.Create => caller
              end in
            option_map (fun journal => (Result.Ok tt, ctx <| Context.journaled_state := journal |>))
              (Impl_Journal.store_account journal caller)
          end
        end
      end
    end.

  Definition extend_storage_keys (keys more : list aliases.U256.t) : list aliases.U256.t :=
    List.fold_left (fun keys key =>
      if List.existsb (fun old => Z.eqb key.(Uint.value) old.(Uint.value)) keys then keys else key :: keys) more keys.

  Fixpoint extend_access_list (address : Address.t) (keys : list aliases.U256.t)
      (entries : list (Address.t * list aliases.U256.t)) : list (Address.t * list aliases.U256.t) :=
    match entries with
    | [] => [(address, extend_storage_keys [] keys)]
    | (old_address, old_keys) :: rest =>
      if Z.eqb address.(Address.value) old_address.(Address.value) then
        (address, extend_storage_keys old_keys keys) :: rest
      else (old_address, old_keys) :: extend_access_list address keys rest
    end.

  Definition access_list_map (items : list AccessListItem.t) : list (Address.t * list aliases.U256.t) :=
    List.fold_left (fun entries item => extend_access_list item.(AccessListItem.address)
      (List.map (fun key => {| Uint.value := FixedBytes.to_Z key |}) item.(AccessListItem.storage_keys)) entries) items [].

  Definition load_accounts {DB Error : Set} (ctx : Context.t DB Error)
      (precompile_addresses : list Address.t) : Context.t DB Error :=
    let spec := ctx.(Context.cfg).(CfgEnv.spec) in
    let journal := Impl_Journal.set_spec_id ctx.(Context.journaled_state) spec in
    (* The pure provider supplies the list for this spec; refreshing the same
       set has no observable effect, so no mutable precompile cache is needed. *)
    let journal := Impl_Journal.warm_precompiles journal precompile_addresses in
    let journal := if Impl_SpecId.is_enabled_in spec SpecId.SHANGHAI then
      Impl_Journal.warm_coinbase_account journal ctx.(Context.block).(BlockEnv.beneficiary) else journal in
    let journal := if Z.eqb ctx.(Context.tx).(TxEnv.tx_type).(Integer.value) 0 then journal else
      Impl_Journal.warm_access_list journal (access_list_map ctx.(Context.tx).(TxEnv.access_list)) in
    ctx <| Context.journaled_state := journal |>.

  Definition apply_authorization {DB Error Authorization : Set} `{Database.C DB Error} `{AuthorizationTr.C Authorization}
      (chain_id : u64) (authorization : Authorization) (journal : Journal.t DB)
      : option (Result.t bool Error * Journal.t DB) :=
    let auth_chain_id := (AuthorizationTr.chain_id authorization).(Uint.value) in
    if negb (Z.eqb auth_chain_id 0 || Z.eqb auth_chain_id chain_id.(Integer.value)) ||
      Z.eqb (AuthorizationTr.nonce authorization).(Integer.value) (2 ^ 64 - 1) then
      Some (Result.Ok false, journal)
    else match AuthorizationTr.authority authorization with
    | None => Some (Result.Ok false, journal)
    | Some authority =>
      match Impl_Journal.load_account_mut_optional_code journal authority true with
      | None => None
      | Some (Result.Err error, journal) => Some (Result.Err error, journal)
      | Some (Result.Ok (account, _), journal) =>
        let info := account.(JournaledAccount.account).(Account.info) in
        if negb (match info.(AccountInfo.code) with None => true | Some code => code_allows_transaction code end) ||
          negb (Z.eqb (AuthorizationTr.nonce authorization).(Integer.value) info.(AccountInfo.nonce).(Integer.value)) then
          Some (Result.Ok false, journal)
        else
          let refund := negb (Impl_Account.is_empty account.(JournaledAccount.account) &&
            Impl_Account.is_loaded_as_not_existing_not_touched account.(JournaledAccount.account)) in
          let account := Impl_JournaledAccount.delegate account (AuthorizationTr.address authorization) in
          option_map (fun journal => (Result.Ok refund, journal)) (Impl_Journal.store_account journal account)
      end
    end.

  Fixpoint apply_authorizations {DB Error Authorization : Set} `{Database.C DB Error} `{AuthorizationTr.C Authorization}
      (chain_id : u64) (authorizations : list Authorization) (refunded_accounts : u64) (journal : Journal.t DB)
      : option (Result.t u64 Error * Journal.t DB) :=
    match authorizations with
    | [] => Some (Result.Ok (BinOp.Wrap.mul refunded_accounts (BinOp.Wrap.sub PER_EMPTY_ACCOUNT_COST PER_AUTH_BASE_COST)), journal)
    | auth :: rest =>
      match apply_authorization chain_id auth journal with
      | None => None
      | Some (Result.Err error, journal) => Some (Result.Err error, journal)
      | Some (Result.Ok refund, journal) =>
        apply_authorizations chain_id rest (if refund then BinOp.Wrap.add refunded_accounts 1 else refunded_accounts) journal
      end
    end.

  Definition apply_eip7702_auth_list {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) : option (Result.t u64 (EVMError.t Error) * Context.t DB Error) :=
    if negb (Z.eqb ctx.(Context.tx).(TxEnv.tx_type).(Integer.value) 4) then Some (Result.Ok (0 : u64), ctx) else
    match apply_authorizations ctx.(Context.cfg).(CfgEnv.chain_id) ctx.(Context.tx).(TxEnv.authorization_list)
      0 ctx.(Context.journaled_state) with
    | None => None
    | Some (result, journal) =>
      Some (match result with Result.Ok gas => Result.Ok gas | Result.Err error => Result.Err (EVMError.Database error) end,
        ctx <| Context.journaled_state := journal |>)
    end.
End PreExecution.

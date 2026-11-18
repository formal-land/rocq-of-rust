Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.log.links.mod.
Require Import alloc.vec.links.mod.
Require Import alloc.links.raw_vec.
Require Import revm.revm_handler.simulate.eest_types.
Require Import revm.revm_handler.simulate.handler.
Require Import revm.revm_handler.simulate.precompile_provider.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.block.links.blob.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

(** JSON/EEST boundary. Fixture records are converted to the typed
    Context/Handler path and finalized accounts are converted back here. *)
Module EestContext.
  Definition bytes (values : list Z) :=
    Impl_Bytes.copy_from_slice (List.map (fun value => {| Integer.value := value |}) values).

  Definition bytecode (values : list Z) : revm.revm_bytecode.links.bytecode.Bytecode.t :=
    {| revm.revm_bytecode.links.bytecode.Bytecode.original_bytes := bytes values |}.

  Definition account_info (account : EestTypes.Account.t) : AccountInfo.t := {|
    AccountInfo.balance := {| Uint.value := account.(EestTypes.Account.balance) |};
    AccountInfo.nonce := {| Integer.value := account.(EestTypes.Account.nonce) |};
    AccountInfo.code_hash := FixedBytes.from_Z account.(EestTypes.Account.code_hash);
    AccountInfo.code := Some (bytecode account.(EestTypes.Account.code));
  |}.

  #[global] Instance database : Database.C EestTypes.Input.t unit := {|
    Database.basic input address := (Result.Ok (option_map account_info
      (EestTypes.find_account address.(Address.value) input.(EestTypes.Input.accounts))), input);
    Database.code_by_hash input hash := (Result.Ok (bytecode (match List.find
      (fun account => Z.eqb account.(EestTypes.Account.code_hash) (FixedBytes.to_Z hash))
      input.(EestTypes.Input.accounts) with
      | Some account => account.(EestTypes.Account.code) | None => [] end)), input);
    Database.storage input address key := (Result.Ok {| Uint.value := match
      EestTypes.find_account address.(Address.value) input.(EestTypes.Input.accounts) with
      | None => 0
      | Some account => match EestTypes.lookup_z key.(Uint.value) account.(EestTypes.Account.storage) with
          | None => 0 | Some value => value end
      end |}, input);
    Database.block_hash input number :=
      let block := input.(EestTypes.Input.block) in
      (match EestTypes.lookup_z number.(Integer.value) block.(EestTypes.Block.hashes) with
      | Some hash => Result.Ok (FixedBytes.from_Z hash)
      | None => if block.(EestTypes.Block.use_state_test_hashes) then
          Result.Ok (FixedBytes.from_Z (EestTypes.state_test_block_hash number.(Integer.value)))
        else Result.Err tt
      end, input);
  |}.

  Definition transaction (tx : TransactionAccounting.Transaction.t) : TxEnv.t := {|
    TxEnv.tx_type := {| Integer.value := tx.(TransactionAccounting.Transaction.tx_type) |};
    TxEnv.caller := {| Address.value := tx.(TransactionAccounting.Transaction.caller) |};
    TxEnv.gas_limit := {| Integer.value := tx.(TransactionAccounting.Transaction.gas_limit) |};
    TxEnv.gas_price := TransactionAccounting.fixture_gas_price {| Uint.value := tx.(TransactionAccounting.Transaction.gas_price) |};
    TxEnv.kind := match tx.(TransactionAccounting.Transaction.target) with
      | Some target => TxKind.Call {| Address.value := target |} | None => TxKind.Create end;
    TxEnv.value := {| Uint.value := tx.(TransactionAccounting.Transaction.value) |};
    TxEnv.data := bytes tx.(TransactionAccounting.Transaction.data);
    TxEnv.nonce := {| Integer.value := tx.(TransactionAccounting.Transaction.nonce) |};
    TxEnv.chain_id := option_map (fun value => {| Integer.value := value |}) tx.(TransactionAccounting.Transaction.chain_id);
    TxEnv.access_list := List.map (fun '(address, keys) => {|
      AccessListItem.address := {| Address.value := address |};
      AccessListItem.storage_keys := List.map FixedBytes.from_Z keys |}) tx.(TransactionAccounting.Transaction.access_list);
    TxEnv.gas_priority_fee := option_map (fun value => {| Integer.value := value |}) tx.(TransactionAccounting.Transaction.max_priority_fee);
    TxEnv.blob_hashes := List.map FixedBytes.from_Z tx.(TransactionAccounting.Transaction.blob_hashes);
    TxEnv.max_fee_per_blob_gas := {| Integer.value := tx.(TransactionAccounting.Transaction.max_fee_per_blob_gas) |};
    TxEnv.authorization_list := tx.(TransactionAccounting.Transaction.authorization_list);
  |}.

  Definition context (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t) (input : EestTypes.Input.t)
      : Context.t EestTypes.Input.t unit :=
    let ctx := Impl_Context.new input spec in
    let block := input.(EestTypes.Input.block) in
    ctx <| Context.tx := transaction tx |>
      <| Context.cfg := ctx.(Context.cfg) <| CfgEnv.chain_id := {| Integer.value := input.(EestTypes.Input.chain_id) |} |>
        <| CfgEnv.max_blobs_per_tx := option_map (fun value => {| Integer.value := value |}) input.(EestTypes.Input.max_blobs_per_tx) |> |>
      <| Context.block := {|
        BlockEnv.number := {| Uint.value := block.(EestTypes.Block.number) |};
        BlockEnv.beneficiary := {| Address.value := block.(EestTypes.Block.coinbase) |};
        BlockEnv.timestamp := {| Uint.value := block.(EestTypes.Block.timestamp) |};
        BlockEnv.gas_limit := {| Integer.value := block.(EestTypes.Block.gas_limit) |};
        BlockEnv.basefee := {| Integer.value := block.(EestTypes.Block.base_fee) |};
        BlockEnv.difficulty := {| Uint.value := block.(EestTypes.Block.difficulty) |};
        BlockEnv.prevrandao := option_map FixedBytes.from_Z block.(EestTypes.Block.previous_randao);
        BlockEnv.blob_excess_gas_and_price := option_map (fun excess => {|
          BlobExcessGasAndPrice.excess_blob_gas := {| Integer.value := excess |};
          BlobExcessGasAndPrice.blob_gasprice := {| Integer.value := block.(EestTypes.Block.blob_base_fee) |} |})
          input.(EestTypes.Input.excess_blob_gas);
      |} |>.

  Definition store_slot (storage : list (Z * Z)) (entry : aliases.U256.t * EvmStorageSlot.t) :=
    let '(key, slot) := entry in
    let storage := List.filter (fun entry => negb (Z.eqb (fst entry) key.(Uint.value))) storage in
    let value := slot.(EvmStorageSlot.present_value).(Uint.value) in
    if Z.eqb value 0 then storage else (key.(Uint.value), value) :: storage.

  Definition commit_account (spec : SpecId.t) (accounts : list EestTypes.Account.t)
      (entry : Address.t * Account.t) : list EestTypes.Account.t :=
    let '(address, account) := entry in
    if negb (Impl_Account.is_touched account) then accounts else
    let previous := EestTypes.account_at address.(Address.value) accounts in
    let accounts := List.filter (fun old => negb (Z.eqb old.(EestTypes.Account.address) address.(Address.value))) accounts in
    if Impl_Account.is_selfdestructed account ||
      (Impl_SpecId.is_enabled_in spec SpecId.SPURIOUS_DRAGON && Impl_Account.is_empty account) then accounts else
    let info := account.(Account.info) in
    {| EestTypes.Account.address := address.(Address.value);
      EestTypes.Account.balance := info.(AccountInfo.balance).(Uint.value);
      EestTypes.Account.nonce := info.(AccountInfo.nonce).(Integer.value);
      EestTypes.Account.code_hash := FixedBytes.to_Z info.(AccountInfo.code_hash);
      EestTypes.Account.code := match info.(AccountInfo.code) with
        | None => previous.(EestTypes.Account.code)
        | Some code => List.map Integer.value code.(revm.revm_bytecode.links.bytecode.Bytecode.original_bytes)
            .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)
        end;
      EestTypes.Account.storage := List.fold_left store_slot account.(Account.storage)
        (if Impl_Account.is_created account then [] else previous.(EestTypes.Account.storage));
      EestTypes.Account.transient_storage := [];
    |} :: accounts.

  Definition accounts (ctx : Context.t EestTypes.Input.t unit) :=
    (* A zero storage value denotes an absent trie entry, including in an
       untouched fixture account. Rejected transactions retain the original input. *)
    List.map (fun account => account <| EestTypes.Account.storage :=
      List.filter (fun slot => negb (Z.eqb (snd slot) 0)) account.(EestTypes.Account.storage) |>)
      (List.fold_left (commit_account ctx.(Context.cfg).(CfgEnv.spec))
        ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state)
        ctx.(Context.journaled_state).(Journal.database).(EestTypes.Input.accounts)).

  Definition log (log : Log.t LogData.t) : EestTypes.EvmLog.t := {|
    EestTypes.EvmLog.address := log.(Log.address).(Address.value);
    EestTypes.EvmLog.topics := List.map Uint.value log.(Log.data).(LogData.topics).(Vec.buf).(RawVec.value);
    EestTypes.EvmLog.data := List.map Integer.value log.(Log.data).(LogData.data)
      .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value);
  |}.

  Definition halt_status (reason : HaltReason.t) : InstructionResult.t :=
    match reason with
    | HaltReason.OutOfGas reason => match reason with
        | OutOfGasError.Basic => InstructionResult.OutOfGas
        | OutOfGasError.MemoryLimit => InstructionResult.MemoryLimitOOG
        | OutOfGasError.Memory => InstructionResult.MemoryOOG
        | OutOfGasError.Precompile => InstructionResult.PrecompileOOG
        | OutOfGasError.InvalidOperand => InstructionResult.InvalidOperandOOG
        | OutOfGasError.ReentrancySentry => InstructionResult.ReentrancySentryOOG end
    | HaltReason.OpcodeNotFound => InstructionResult.OpcodeNotFound
    | HaltReason.InvalidFEOpcode => InstructionResult.InvalidFEOpcode
    | HaltReason.InvalidJump => InstructionResult.InvalidJump
    | HaltReason.NotActivated => InstructionResult.NotActivated
    | HaltReason.StackUnderflow => InstructionResult.StackUnderflow
    | HaltReason.StackOverflow => InstructionResult.StackOverflow
    | HaltReason.OutOfOffset => InstructionResult.OutOfOffset
    | HaltReason.CreateCollision => InstructionResult.CreateCollision
    | HaltReason.PrecompileError | HaltReason.PrecompileErrorWithContext _ => InstructionResult.PrecompileError
    | HaltReason.NonceOverflow => InstructionResult.NonceOverflow
    | HaltReason.CreateContractSizeLimit => InstructionResult.CreateContractSizeLimit
    | HaltReason.CreateContractStartingWithEF => InstructionResult.CreateContractStartingWithEF
    | HaltReason.CreateInitCodeSizeLimit => InstructionResult.CreateInitCodeSizeLimit
    | HaltReason.OverflowPayment => InstructionResult.OverflowPayment
    | HaltReason.StateChangeDuringStaticCall => InstructionResult.StateChangeDuringStaticCall
    | HaltReason.CallNotAllowedInsideStatic => InstructionResult.CallNotAllowedInsideStatic
    | HaltReason.OutOfFunds => InstructionResult.OutOfFunds
    | HaltReason.CallTooDeep => InstructionResult.CallTooDeep
    end.

  Definition settlement (ctx : Context.t EestTypes.Input.t unit) (used refunded : u64)
      : TransactionAccounting.Settlement.t :=
    let tx := ctx.(Context.tx) in
    let basefee := ctx.(Context.block).(BlockEnv.basefee) in
    let price := transaction.Transaction.Fees.effective_gas_price tx {| Integer.value := basefee.(Integer.value) |} in
    let remaining := tx.(TxEnv.gas_limit).(Integer.value) - used.(Integer.value) - refunded.(Integer.value) in
    {| TransactionAccounting.Settlement.gas_remaining := remaining;
      TransactionAccounting.Settlement.gas_refunded := refunded.(Integer.value);
      TransactionAccounting.Settlement.gas_used := used.(Integer.value);
      TransactionAccounting.Settlement.caller_reimbursement := (remaining + refunded.(Integer.value)) * price.(Integer.value);
      TransactionAccounting.Settlement.beneficiary_reward := used.(Integer.value) *
        (price.(Integer.value) - if Impl_SpecId.is_enabled_in ctx.(Context.cfg).(CfgEnv.spec) SpecId.LONDON then basefee.(Integer.value) else 0);
      TransactionAccounting.Settlement.base_fee_burn := if Impl_SpecId.is_enabled_in ctx.(Context.cfg).(CfgEnv.spec) SpecId.LONDON
        then used.(Integer.value) * basefee.(Integer.value) else 0;
      TransactionAccounting.Settlement.blob_fee_burn := if Z.eqb tx.(TxEnv.tx_type).(Integer.value) 3 then
        Z.of_nat (List.length tx.(TxEnv.blob_hashes)) * 131072 *
          match Impl_Block_for_BlockEnv.blob_gasprice ctx.(Context.block) with Some price => price.(Integer.value) | None => 0 end
        else 0;
    |}.

  Definition completed (ctx : Context.t EestTypes.Input.t unit) (result : ExecutionResult.t) (gas : Gas.t) : EestTypes.Result.t :=
    let '(status, data, logs) := match result with
      | ExecutionResult.Success reason _ _ logs output =>
          (match reason with SuccessReason.Stop => InstructionResult.Stop | SuccessReason.Return => InstructionResult.Return
            | SuccessReason.SelfDestruct => InstructionResult.SelfDestruct end,
          Output.into_data output, logs)
      | ExecutionResult.Revert _ data => (InstructionResult.Revert, data, [])
      | ExecutionResult.Halt reason _ => (halt_status reason, Impl_Bytes.new, [])
      end in
    EestTypes.Result.Completed {|
      EestTypes.Output.status := status;
      EestTypes.Output.gas := settlement ctx (Impl_Gas.used gas) (cast_integer IntegerKind.U64 gas.(Gas.refunded));
      EestTypes.Output.data := List.map Integer.value data.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value);
      EestTypes.Output.accounts := accounts ctx;
      EestTypes.Output.logs := List.map log logs;
    |}.

  Definition rejected (error : EVMError.t unit) : EestTypes.Result.t :=
    let reject := EestTypes.Result.Rejected in
    match error with
    | EVMError.Header InvalidHeader.PrevrandaoNotSet => reject EestTypes.Rejection.PrevrandaoNotSet
    | EVMError.Header InvalidHeader.ExcessBlobGasNotSet => reject EestTypes.Rejection.ExcessBlobGasNotSet
    | EVMError.Database _ | EVMError.Custom _ => EestTypes.Result.Incomplete
    | EVMError.Transaction error => match error with
      | InvalidTransaction.InvalidChainId => reject EestTypes.Rejection.InvalidChainId
      | InvalidTransaction.MissingChainId => reject EestTypes.Rejection.MissingChainId
      | InvalidTransaction.RejectCallerWithCode => reject EestTypes.Rejection.RejectCallerWithCode
      | InvalidTransaction.NonceTooHigh _ _ => reject EestTypes.Rejection.NonceTooHigh
      | InvalidTransaction.NonceTooLow _ _ => reject EestTypes.Rejection.NonceTooLow
      | InvalidTransaction.LackOfFundForMaxFee _ _ => reject EestTypes.Rejection.LackOfFunds
      | InvalidTransaction.OverflowPaymentInTransaction => reject (EestTypes.Rejection.Gas TransactionAccounting.GasError.PaymentOverflow)
      | InvalidTransaction.CallGasCostMoreThanGasLimit available required => reject
          (EestTypes.Rejection.Gas (TransactionAccounting.GasError.IntrinsicGasTooHigh required.(Integer.value) available.(Integer.value)))
      | InvalidTransaction.GasFloorMoreThanGasLimit required available => reject
          (EestTypes.Rejection.Gas (TransactionAccounting.GasError.FloorGasTooHigh required.(Integer.value) available.(Integer.value)))
      | error => match TransactionAccounting.reject_environment error with
          | TransactionAccounting.Result.Rejected reason => reject (EestTypes.Rejection.Gas reason)
          | _ => EestTypes.Result.Incomplete
          end
      end
    end.

  Definition input_valid (input : EestTypes.Input.t) : bool :=
    let block := input.(EestTypes.Input.block) in
    (* Block number/timestamp are U256 in Rust. Reuse the remaining wire checks. *)
    EestTypes.input_valid (input <| EestTypes.Input.block := block
      <| EestTypes.Block.number := 0 |> <| EestTypes.Block.timestamp := 0 |> |>) &&
    TransactionAccounting.bounded 256 block.(EestTypes.Block.number) &&
    TransactionAccounting.bounded 256 block.(EestTypes.Block.timestamp) &&
    TransactionAccounting.block_fields_valid {|
      TransactionAccounting.Block.gas_limit := block.(EestTypes.Block.gas_limit);
      TransactionAccounting.Block.base_fee := block.(EestTypes.Block.base_fee);
      TransactionAccounting.Block.blob_base_fee := block.(EestTypes.Block.blob_base_fee);
    |}.

  Definition run (fuel : nat) (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t)
      (input : EestTypes.Input.t) : EestTypes.Result.t :=
    if negb (input_valid input && TransactionAccounting.transaction_fields_valid tx) then EestTypes.Result.Malformed else
    match Handler.run_with_gas fuel (EthPrecompiles.warm_addresses spec) (context spec tx input) with
    | None => EestTypes.Result.Incomplete
    | Some (Result.Err error, _) => rejected error
    | Some (Result.Ok (result, gas), ctx) => completed ctx result gas
    end.
End EestContext.

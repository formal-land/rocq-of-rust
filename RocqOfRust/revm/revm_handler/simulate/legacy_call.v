From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.simulate.pre_execution.
Require Import revm.revm_handler.simulate.post_execution.
Require Import revm.revm_handler.simulate.validation.
Require Import revm.revm_context_interface.simulate.result.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_handler.simulate.handler.
Require Import revm.revm_context_interface.transaction.simulate.alloy_types.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.create_frame.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import simulate.RocqOfRust.

#[local] Existing Instance TransactionAccounting.fee_fields.

Import ListNotations.
Open Scope Z_scope.

(** Ordinary legacy, EIP-2930, EIP-1559 EIP-4844 and EIP-7702 transactions on Cancun, Prague and Osaka, including nested
    calls and creation through the concrete frame runner. The caller and block
    context are supplied normalized inputs. Top-level SHA256, RIPEMD160, identity
    and MODEXP use the existing precompile frame implementation. Signature
    decoding and other precompiles remain separate boundaries.
    Code hashes are supplied by the normalized database input; only their numeric
    bounds are checked here. The concrete host/runner has no native journal or
    handler correspondence proof. *)
Module LegacyCall.
  Module Input.
    Record t : Set := {
      chain_id : Z;
      block : StatefulHost.Environment.Block.t;
      excess_blob_gas : option Z;
      max_blobs_per_tx : option Z;
      accounts : list StatefulHost.Account.t;
    }.
  End Input.

  Module Rejection.
    Inductive t : Set :=
    | Gas (reason : TransactionAccounting.GasError.t)
    | PrevrandaoNotSet
    | ExcessBlobGasNotSet
    | InvalidChainId
    | MissingChainId
    | RejectCallerWithCode
    | NonceTooLow
    | NonceTooHigh
    | NonceOverflow
    | LackOfFunds.
  End Rejection.

  Module Gap.
    Inductive t : Set :=
    | Accounting (reason : TransactionAccounting.UnsupportedReason.t)
    | TopLevelPrecompile
    | Delegation.
  End Gap.

  Module Output.
    Record t : Set := {
      status : InstructionResult.t;
      gas : TransactionAccounting.Settlement.t;
      data : list Z;
      accounts : list StatefulHost.Account.t;
      logs : list StatefulHost.EvmLog.t;
    }.
  End Output.

  Module Result.
    Inductive t : Set :=
    | Completed (output : Output.t)
    | Rejected (reason : Rejection.t)
    | Unsupported (reason : Gap.t)
    | Malformed
    | Incomplete.
  End Result.

  Fixpoint distinct (values : list Z) : bool :=
    match values with
    | [] => true
    | value :: rest => negb (List.existsb (Z.eqb value) rest) && distinct rest
    end.

  Definition account_valid (account : StatefulHost.Account.t) : bool :=
    TransactionAccounting.bounded 160 account.(StatefulHost.Account.address) &&
    TransactionAccounting.bounded 256 account.(StatefulHost.Account.balance) &&
    TransactionAccounting.bounded 64 account.(StatefulHost.Account.nonce) &&
    TransactionAccounting.bounded 256 account.(StatefulHost.Account.code_hash) &&
    List.forallb (TransactionAccounting.bounded 8) account.(StatefulHost.Account.code) &&
    List.forallb (fun slot => TransactionAccounting.bounded 256 (fst slot) &&
      TransactionAccounting.bounded 256 (snd slot)) account.(StatefulHost.Account.storage) &&
    distinct (List.map fst account.(StatefulHost.Account.storage)) &&
    match account.(StatefulHost.Account.transient_storage) with
    | [] => true
    | _ => false
    end.

  Definition input_valid (input : Input.t) : bool :=
    TransactionAccounting.bounded 64 input.(Input.chain_id) &&
    TransactionAccounting.bounded 160 input.(Input.block).(StatefulHost.Environment.Block.coinbase) &&
    TransactionAccounting.bounded 64 input.(Input.block).(StatefulHost.Environment.Block.number) &&
    TransactionAccounting.bounded 64 input.(Input.block).(StatefulHost.Environment.Block.timestamp) &&
    TransactionAccounting.bounded 256 input.(Input.block).(StatefulHost.Environment.Block.difficulty) &&
    TransactionAccounting.bounded 128 input.(Input.block).(StatefulHost.Environment.Block.blob_base_fee) &&
    List.forallb (fun entry => TransactionAccounting.bounded 64 (fst entry) &&
      TransactionAccounting.bounded 256 (snd entry)) input.(Input.block).(StatefulHost.Environment.Block.hashes) &&
    (match input.(Input.block).(StatefulHost.Environment.Block.previous_randao) with
     | None => true
     | Some value => TransactionAccounting.bounded 256 value
     end) &&
    (match input.(Input.excess_blob_gas) with
     | None => true
     | Some value => TransactionAccounting.bounded 64 value
     end) &&
    TransactionAccounting.blob_limit_valid input.(Input.max_blobs_per_tx) &&
    List.forallb account_valid input.(Input.accounts) &&
    distinct (List.map StatefulHost.Account.address input.(Input.accounts)).

  Definition account_at (address : Z) (accounts : list StatefulHost.Account.t) :=
    match StatefulHost.find_account address accounts with
    | Some account => account
    | None => StatefulHost.empty_account address
    end.

  Definition is_delegation (code : list Z) : bool :=
    match code with
    | 239 :: 1 :: 0 :: address => Nat.eqb (List.length address) 20
    | _ => false
    end.

  Definition empty (account : StatefulHost.Account.t) : bool :=
    (account.(StatefulHost.Account.balance) =? 0) &&
    (account.(StatefulHost.Account.nonce) =? 0) &&
    ((account.(StatefulHost.Account.code_hash) =? 0) ||
     (account.(StatefulHost.Account.code_hash) =? StatefulHost.empty_code_hash)).

  Definition finish_accounts (touched : list Z) (host : StatefulHost.t) :=
    let host := StatefulHost.finalize_selfdestructs host in
    List.map (fun account => account
      <| StatefulHost.Account.storage := List.filter (fun slot => negb (snd slot =? 0))
           account.(StatefulHost.Account.storage) |>
      <| StatefulHost.Account.transient_storage := [] |>)
      (List.filter (fun account => negb
        (Impl_SpecId.is_enabled_in host.(StatefulHost.spec_id) SpecId.SPURIOUS_DRAGON &&
         List.existsb (Z.eqb account.(StatefulHost.Account.address)) touched && empty account))
        host.(StatefulHost.accounts)).

  Definition classify (status : InstructionResult.t) : option TransactionAccounting.FrameStatus.t :=
    match status with
    | InstructionResult.Stop | InstructionResult.Return | InstructionResult.SelfDestruct =>
      Some TransactionAccounting.FrameStatus.Success
    | InstructionResult.Revert => Some TransactionAccounting.FrameStatus.Revert
    | InstructionResult.Continue | InstructionResult.CallOrCreate
    | InstructionResult.ReturnContract | InstructionResult.FatalExternalError => None
    | _ => Some TransactionAccounting.FrameStatus.Halt
    end.

  Definition execute_with_runner
      (run_frame : bool -> nat -> StatefulHost.t -> list CallRunner.Pending.t -> CallFrame.state ->
        option (InterpreterAction.t * CallFrame.state))
      (fuel : nat) (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t)
      (input : Input.t) (target : option Z) (initial : TransactionAccounting.InitialGas.t) : Result.t :=
    let sender := account_at tx.(TransactionAccounting.Transaction.caller) input.(Input.accounts) in
    (* Native bump_nonce touches the caller but leaves u64::MAX unchanged;
       transaction pre-execution ignores its boolean result. *)
    let bump_nonce := match target with
      | Some _ => sender.(StatefulHost.Account.nonce) <? 2 ^ 64 - 1
      | None => false
      end in
    let sender := CreateFrame.with_nonce
      (StatefulHost.account_with_balance sender
        (sender.(StatefulHost.Account.balance) - initial.(TransactionAccounting.InitialGas.upfront_fee)))
      (sender.(StatefulHost.Account.nonce) +
        if bump_nonce then 1 else 0) in
    let host_input : StatefulHost.Input.t := {|
      StatefulHost.Input.block := input.(Input.block);
      StatefulHost.Input.transaction := {|
        StatefulHost.Environment.Transaction.chain_id := input.(Input.chain_id);
        StatefulHost.Environment.Transaction.gas_price := TransactionAccounting.effective_gas_price tx
          input.(Input.block).(StatefulHost.Environment.Block.base_fee);
        StatefulHost.Environment.Transaction.blob_hashes :=
          if tx.(TransactionAccounting.Transaction.tx_type) =? 3 then
            tx.(TransactionAccounting.Transaction.blob_hashes) else [];
      |};
      StatefulHost.Input.call := {|
        StatefulHost.Environment.Call.caller := tx.(TransactionAccounting.Transaction.caller);
      |};
      StatefulHost.Input.state := input.(Input.accounts);
    |} in
    let host := (StatefulHost.make host_input) <| StatefulHost.spec_id := spec |> in
    let host := StatefulHost.with_accounts host
      (StatefulHost.update_account tx.(TransactionAccounting.Transaction.caller) (fun _ => sender)
        host.(StatefulHost.accounts)) in
    let host := StatefulHost.append_change host
      (StatefulHost.Change.Balance tx.(TransactionAccounting.Transaction.caller) sender.(StatefulHost.Account.balance)) in
    let host := if bump_nonce then StatefulHost.append_change host
      (StatefulHost.Change.Nonce tx.(TransactionAccounting.Transaction.caller) sender.(StatefulHost.Account.nonce))
      else host in
    let host := StatefulHost.touch_account host tx.(TransactionAccounting.Transaction.caller) in
    let host := List.fold_left StatefulHost.warm_account
      (tx.(TransactionAccounting.Transaction.caller) ::
       (if Impl_SpecId.is_enabled_in spec SpecId.SHANGHAI then
          [input.(Input.block).(StatefulHost.Environment.Block.coinbase)] else []) ++
       (match target with Some address => [address] | None => [] end) ++
       PrecompileFrame.addresses spec) host in
    let host := if tx.(TransactionAccounting.Transaction.tx_type) =? 0 then host else
      StatefulHost.warm_access_list host tx.(TransactionAccounting.Transaction.access_list) in
    let '(authorization_refund, host) := pre_execution.apply_eip7702_auth_list
      {| Integer.value := tx.(TransactionAccounting.Transaction.tx_type) |}
      {| Integer.value := input.(Input.chain_id) |}
      tx.(TransactionAccounting.Transaction.authorization_list) host in
    let result := match target with
      | None =>
        let parent := interpreter_with_spec_id
          (make_interpreter_with_bytecode [] {| Stack.value := [] |}) spec in
        let inputs : CreateInputs.t := {|
          CreateInputs.caller := StatefulHost.rust_address tx.(TransactionAccounting.Transaction.caller);
          CreateInputs.scheme := CreateScheme.Create;
          CreateInputs.value := StatefulHost.rust_word tx.(TransactionAccounting.Transaction.value);
          CreateInputs.init_code := Impl_Bytes.copy_from_slice
            (List.map StatefulHost.rust_byte tx.(TransactionAccounting.Transaction.data));
          CreateInputs.gas_limit := {| Integer.value := initial.(TransactionAccounting.InitialGas.execution) |};
        |} in
        match CreateFrame.prepare parent host 0 inputs with
        | None => None
        | Some (CreateFrame.Immediate output host) =>
          Some (InterpreterAction.Return output,
            {| InstructionContext.State.interpreter := parent;
               InstructionContext.State.host := host |})
        | Some (CreateFrame.Child address checkpoint state) =>
          match run_frame false fuel checkpoint [] state with
          | Some (InterpreterAction.Return output, state) =>
            let '(output, host) := CreateFrame.finish address checkpoint
              (InstructionContext.State.host _ _ _ state) output in
            Some (InterpreterAction.Return output,
              {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
                 InstructionContext.State.host := host |})
          | _ => None
          end
        end
      | Some target =>
        let '(code, host) := handler.first_frame_input target host in
        let code := if PrecompileFrame.enabled spec target then [] else code in
        let checkpoint := host in
        let '(error, host) := CallFrame.transfer host tx.(TransactionAccounting.Transaction.caller)
          target tx.(TransactionAccounting.Transaction.value) in
        let interpreter := interpreter_with_spec_id
          (make_interpreter_with_bytecode (List.map StatefulHost.rust_byte code)
            {| Stack.value := [] |}) spec in
        let interpreter := interpreter
          <| @Interpreter.gas WIRE _ WIRE_types _ := interpreter.(Interpreter.gas)
            <| Gas.limit := {| Integer.value := initial.(TransactionAccounting.InitialGas.execution) |} |>
            <| Gas.remaining := {| Integer.value := initial.(TransactionAccounting.InitialGas.execution) |} |> |>
          <| @Interpreter.input WIRE _ WIRE_types _ := {|
            revm.revm_interpreter.tests.interpreter_types.Input.target_address := StatefulHost.rust_address target;
            revm.revm_interpreter.tests.interpreter_types.Input.caller_address := StatefulHost.rust_address tx.(TransactionAccounting.Transaction.caller);
            revm.revm_interpreter.tests.interpreter_types.Input.call_value := StatefulHost.rust_word tx.(TransactionAccounting.Transaction.value);
            revm.revm_interpreter.tests.interpreter_types.Input.input := CallInput.Bytes
              (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
                (List.map StatefulHost.rust_byte tx.(TransactionAccounting.Transaction.data)));
          |} |> in
        let state : CallFrame.state := {|
          InstructionContext.State.interpreter := interpreter;
          InstructionContext.State.host := host;
        |} in
        match error with
          | Some InstructionResult.OverflowPayment =>
              (* Native source-debit persistence is outside snapshot rollback. *)
              None
          | Some status => Some (InterpreterAction.Return (CallFrame.result status interpreter),
              {| InstructionContext.State.interpreter := interpreter;
                 InstructionContext.State.host := StatefulHost.rollback checkpoint host |})
          | None =>
              let precompile := PrecompileFrame.run target interpreter in
              if PrecompileFrame.is_precompile spec target &&
                (match precompile with None => true | Some _ => false end)
              then None else
              let interpreter := match precompile with
                | Some output => interpreter
                    <| @Interpreter.bytecode WIRE _ WIRE_types _ := interpreter.(Interpreter.bytecode)
                      <| Bytecode.action := Some (InterpreterAction.Return output) |> |>
                | None => interpreter
                end in
              run_frame false fuel checkpoint []
                {| InstructionContext.State.interpreter := interpreter;
                   InstructionContext.State.host := InstructionContext.State.host _ _ _ state |}
          end
      end in
    match result with
    | Some (InterpreterAction.Return output, state) =>
      match classify output.(InterpreterResult.result) with
      | None => Result.Incomplete
      | Some status =>
        let block := {|
          TransactionAccounting.Block.gas_limit := input.(Input.block).(StatefulHost.Environment.Block.gas_limit);
          TransactionAccounting.Block.base_fee := input.(Input.block).(StatefulHost.Environment.Block.base_fee);
          TransactionAccounting.Block.blob_base_fee := input.(Input.block).(StatefulHost.Environment.Block.blob_base_fee);
        |} in
        match TransactionAccounting.settle_with_authorization_refund authorization_refund spec tx block {|
          TransactionAccounting.FrameGas.status := status;
          TransactionAccounting.FrameGas.remaining := output.(InterpreterResult.gas).(Gas.remaining).(Integer.value);
          TransactionAccounting.FrameGas.refunded := output.(InterpreterResult.gas).(Gas.refunded).(Integer.value);
        |} with
        | TransactionAccounting.Result.Ready gas =>
          let host := InstructionContext.State.host _ _ _ state in
          let settled_gas := (Impl_Gas.new
            {| Integer.value := tx.(TransactionAccounting.Transaction.gas_limit) |})
            <| Gas.remaining := {| Integer.value := gas.(TransactionAccounting.Settlement.gas_remaining) |} |>
            <| Gas.refunded := {| Integer.value := gas.(TransactionAccounting.Settlement.gas_refunded) |} |> in
          let basefee : u64 := {| Integer.value := block.(TransactionAccounting.Block.base_fee) |} in
          let host := post_execution.reimburse_caller tx basefee
            (StatefulHost.rust_address tx.(TransactionAccounting.Transaction.caller))
            settled_gas (StatefulHost.rust_word 0) host in
          let coinbase := input.(Input.block).(StatefulHost.Environment.Block.coinbase) in
          let host := post_execution.reward_beneficiary tx basefee
            (StatefulHost.rust_address coinbase) spec settled_gas host in
          let touched := host.(StatefulHost.touched_accounts) in
          Result.Completed {|
            Output.status := output.(InterpreterResult.result);
            Output.gas := gas;
            Output.data := match status with
              | TransactionAccounting.FrameStatus.Halt => []
              | _ => List.map Integer.value output.(InterpreterResult.output)
                  .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)
              end;
            Output.accounts := finish_accounts touched host;
            Output.logs := host.(StatefulHost.logs);
          |}
        | _ => Result.Malformed
        end
      end
    | _ => Result.Incomplete
    end.

  Definition execute := execute_with_runner CallRunner.execute_with_finalization.

  Definition validate_header (spec : SpecId.t)
      (previous_randao : option aliases.B256.t) (excess_blob_gas : option u64)
      : option Rejection.t :=
    let block : validation.BlockFields.t := {|
      validation.BlockFields.basefee := 0;
      validation.BlockFields.gas_limit := 0;
      validation.BlockFields.blob_gasprice := 0;
      validation.BlockFields.prevrandao := previous_randao;
      validation.BlockFields.blob_excess_gas := excess_blob_gas;
    |} in
    match validation.validate_header spec block with
    | core.links.result.Result.Err InvalidHeader.PrevrandaoNotSet => Some Rejection.PrevrandaoNotSet
    | core.links.result.Result.Err InvalidHeader.ExcessBlobGasNotSet => Some Rejection.ExcessBlobGasNotSet
    | core.links.result.Result.Ok _ => None
    end.

  Definition validate_chain_id (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t)
      (chain_id : u64) : option Rejection.t :=
    let cfg := (TransactionAccounting.validation_config spec None)
      <| validation.CfgFields.chain_id := chain_id |>
      <| validation.CfgFields.tx_chain_id_check := true |> in
    match validation.validate_chain_id
      {| Integer.value := tx.(TransactionAccounting.Transaction.tx_type) |}
      (option_map (fun value => {| Integer.value := value |}) tx.(TransactionAccounting.Transaction.chain_id)) cfg with
    | core.links.result.Result.Err InvalidTransaction.InvalidChainId => Some Rejection.InvalidChainId
    | core.links.result.Result.Err InvalidTransaction.MissingChainId => Some Rejection.MissingChainId
    | _ => None
    end.

  Definition run_with_runner
      (run_frame : bool -> nat -> StatefulHost.t -> list CallRunner.Pending.t -> CallFrame.state ->
        option (InterpreterAction.t * CallFrame.state))
      (fuel : nat) (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t)
      (input : Input.t) : Result.t :=
    if negb (match spec with SpecId.FRONTIER | SpecId.HOMESTEAD | SpecId.TANGERINE |
      SpecId.SPURIOUS_DRAGON | SpecId.BYZANTIUM | SpecId.PETERSBURG | SpecId.ISTANBUL | SpecId.BERLIN | SpecId.LONDON | SpecId.MERGE | SpecId.SHANGHAI |
      SpecId.CANCUN | SpecId.PRAGUE | SpecId.OSAKA => true | _ => false end) then
      Result.Unsupported (Gap.Accounting (TransactionAccounting.UnsupportedReason.Fork spec))
    else if negb (input_valid input) then Result.Malformed else
    match validate_header spec
      (option_map FixedBytes.from_Z input.(Input.block).(StatefulHost.Environment.Block.previous_randao))
      (option_map (fun value => {| Integer.value := value |}) input.(Input.excess_blob_gas)) with
    | Some reason => Result.Rejected reason
    | None =>
        match validate_chain_id spec tx {| Integer.value := input.(Input.chain_id) |} with
        | Some reason => Result.Rejected reason
        | None =>
        let block := {|
          TransactionAccounting.Block.gas_limit := input.(Input.block).(StatefulHost.Environment.Block.gas_limit);
          TransactionAccounting.Block.base_fee := input.(Input.block).(StatefulHost.Environment.Block.base_fee);
          TransactionAccounting.Block.blob_base_fee := input.(Input.block).(StatefulHost.Environment.Block.blob_base_fee);
        |} in
        match TransactionAccounting.prepare_gas_with_blob_limit spec tx block input.(Input.max_blobs_per_tx) with
        | TransactionAccounting.Result.Malformed _ => Result.Malformed
        | TransactionAccounting.Result.Unsupported reason => Result.Unsupported (Gap.Accounting reason)
        | TransactionAccounting.Result.Rejected reason => Result.Rejected (Rejection.Gas reason)
        | TransactionAccounting.Result.Ready initial =>
            let sender := account_at tx.(TransactionAccounting.Transaction.caller) input.(Input.accounts) in
            if negb (Nat.eqb (List.length sender.(StatefulHost.Account.code)) 0) &&
              negb (is_delegation sender.(StatefulHost.Account.code)) then
              Result.Rejected Rejection.RejectCallerWithCode
            else if tx.(TransactionAccounting.Transaction.nonce) <? sender.(StatefulHost.Account.nonce) then
              Result.Rejected Rejection.NonceTooLow
            else if sender.(StatefulHost.Account.nonce) <? tx.(TransactionAccounting.Transaction.nonce) then
              Result.Rejected Rejection.NonceTooHigh
            else match TransactionAccounting.maximum_payment tx with
            | core.links.result.Result.Err _ =>
              Result.Rejected (Rejection.Gas TransactionAccounting.GasError.PaymentOverflow)
            | core.links.result.Result.Ok maximum_payment =>
              if negb (TransactionAccounting.bounded 256 initial.(TransactionAccounting.InitialGas.upfront_fee)) then
                Result.Rejected (Rejection.Gas TransactionAccounting.GasError.PaymentOverflow)
              else if sender.(StatefulHost.Account.balance) <? maximum_payment then
                Result.Rejected Rejection.LackOfFunds
              else match tx.(TransactionAccounting.Transaction.target) with
              | None => execute_with_runner run_frame fuel spec tx input None initial
              | Some target =>
                if PrecompileFrame.is_precompile spec target &&
                  negb (PrecompileFrame.supported target) then
                  Result.Unsupported Gap.TopLevelPrecompile
                else execute_with_runner run_frame fuel spec tx input (Some target) initial
              end
            end
        end
        end
    end.

  Definition run := run_with_runner CallRunner.execute_with_finalization.
End LegacyCall.

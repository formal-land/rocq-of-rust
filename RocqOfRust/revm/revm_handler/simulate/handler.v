Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloc.links.boxed.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.local.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_handler.simulate.evm.
Require Import revm.revm_handler.simulate.frame.
Require Import revm.revm_handler.simulate.frame_data.
Require Import revm.revm_handler.simulate.pre_execution.
Require Import revm.revm_handler.simulate.post_execution.
Require Import revm.revm_handler.simulate.validation.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.initial_tx.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_result.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import revm.revm_state.simulate.lib.
Require Import ruint.links.lib.


Module Handler.
  Definition validate_env {DB Error : Set} (ctx : Context.t DB Error) : Result.t unit (EVMError.t Error) :=
    let tx := ctx.(Context.tx) in
    let cfg := ctx.(Context.cfg) in
    let block := ctx.(Context.block) in
    let extra := {|
      validation.TxFields.chain_id := tx.(TxEnv.chain_id);
      validation.TxFields.kind := tx.(TxEnv.kind);
      validation.TxFields.input_length := {| Integer.value := Z.of_nat (List.length tx.(TxEnv.data).(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)) |};
      validation.TxFields.authorization_list_len := {| Integer.value := Z.of_nat (List.length tx.(TxEnv.authorization_list)) |} |} in
    let cfg_fields := {|
      validation.CfgFields.chain_id := cfg.(CfgEnv.chain_id);
      validation.CfgFields.tx_chain_id_check := cfg.(CfgEnv.tx_chain_id_check);
      validation.CfgFields.tx_gas_limit_cap := Impl_CfgEnv.tx_gas_limit_cap cfg;
      validation.CfgFields.is_base_fee_check_disabled := false;
      validation.CfgFields.is_priority_fee_check_disabled := false;
      validation.CfgFields.is_block_gas_limit_disabled := false;
      validation.CfgFields.max_blobs_per_tx := cfg.(CfgEnv.max_blobs_per_tx);
      validation.CfgFields.max_initcode_size := Impl_CfgEnv.max_initcode_size cfg |} in
    let block_fields := {|
      validation.BlockFields.basefee := block.(BlockEnv.basefee);
      validation.BlockFields.gas_limit := block.(BlockEnv.gas_limit);
      validation.BlockFields.blob_gasprice := match Impl_Block_for_BlockEnv.blob_gasprice block with Some price => price | None => 0 end;
      validation.BlockFields.prevrandao := block.(BlockEnv.prevrandao);
      validation.BlockFields.blob_excess_gas := Impl_Block_for_BlockEnv.blob_excess_gas block |} in
    match validation.validate_env tx extra cfg_fields block_fields cfg.(CfgEnv.spec) with
    | Result.Ok _ => Result.Ok tt
    | Result.Err (validation.EnvironmentError.Header error) => Result.Err (EVMError.Header error)
    | Result.Err (validation.EnvironmentError.Transaction error) => Result.Err (EVMError.Transaction error)
    end.

  Definition validate_initial_tx_gas {DB Error : Set} (ctx : Context.t DB Error)
      : Result.t InitialAndFloorGas.t (EVMError.t Error) :=
    let gas := InitialTxGas.calculate_initial_tx_gas_for_tx ctx.(Context.tx) ctx.(Context.cfg).(CfgEnv.spec) in
    let limit := ctx.(Context.tx).(TxEnv.gas_limit) in
    if Z.ltb limit.(Integer.value) gas.(InitialAndFloorGas.initial_gas).(Integer.value) then
      Result.Err (EVMError.Transaction (InvalidTransaction.CallGasCostMoreThanGasLimit limit gas.(InitialAndFloorGas.initial_gas)))
    else if Impl_SpecId.is_enabled_in ctx.(Context.cfg).(CfgEnv.spec) SpecId.PRAGUE &&
      Z.ltb limit.(Integer.value) gas.(InitialAndFloorGas.floor_gas).(Integer.value) then
      Result.Err (EVMError.Transaction (InvalidTransaction.GasFloorMoreThanGasLimit gas.(InitialAndFloorGas.floor_gas) limit))
    else Result.Ok gas.

  Definition validate {DB Error : Set} (ctx : Context.t DB Error) :=
    match validate_env ctx with Result.Err error => Result.Err error | Result.Ok _ => validate_initial_tx_gas ctx end.

  Definition pre_execution {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) (precompile_addresses : list Address.t)
      : option (Result.t u64 (EVMError.t Error) * Context.t DB Error) :=
    match PreExecution.validate_against_state_and_deduct_caller ctx with
    | None => None
    | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
    | Some (Result.Ok _, ctx) => PreExecution.apply_eip7702_auth_list (PreExecution.load_accounts ctx precompile_addresses)
    end.

  Definition create_init_frame (tx : TxEnv.t) (bytecode : option (revm.revm_bytecode.links.bytecode.Bytecode.t * aliases.B256.t))
      (gas_limit : u64) : FrameInput.t :=
    match tx.(TxEnv.kind) with
    | TxKind.Call target => FrameInput.Call {| Box.value := {|
        CallInputs.input := CallInput.Bytes tx.(TxEnv.data);
        CallInputs.gas_limit := gas_limit;
        CallInputs.target_address := target;
        CallInputs.bytecode_address := target;
        CallInputs.known_bytecode := option_map (fun '(code, hash) => (hash, code)) bytecode;
        CallInputs.caller := tx.(TxEnv.caller);
        CallInputs.value := CallValue.Transfer tx.(TxEnv.value);
        CallInputs.scheme := CallScheme.Call;
        CallInputs.is_static := false;
        CallInputs.return_memory_offset := {| Range.start := (0 : usize); Range.end_ := (0 : usize) |} |} |}
    | TxKind.Create => FrameInput.Create {| Box.value := {|
        CreateInputs.caller := tx.(TxEnv.caller);
        CreateInputs.scheme := CreateScheme.Create;
        CreateInputs.value := tx.(TxEnv.value);
        CreateInputs.init_code := tx.(TxEnv.data);
        CreateInputs.gas_limit := gas_limit |} |}
    end.

  Definition load_code {DB Error : Set} `{Database.C DB Error} (ctx : Context.t DB Error) (address : Address.t)
      : option (Result.t (revm.revm_bytecode.links.bytecode.Bytecode.t * aliases.B256.t) (EVMError.t Error) * Context.t DB Error) :=
    match Impl_Journal.load_account_with_code ctx.(Context.journaled_state) address with
    | None => None
    | Some (result, journal) =>
      Some (match result with
        | Result.Err error => Result.Err (EVMError.Database error)
        | Result.Ok (account, _) => Result.Ok
          (match account.(Account.info).(AccountInfo.code) with Some code => code
            | None => {| revm.revm_bytecode.links.bytecode.Bytecode.original_bytes := Impl_Bytes.new |} end,
            account.(Account.info).(AccountInfo.code_hash))
        end, ctx <| Context.journaled_state := journal |>)
    end.

  Definition first_frame_input {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) (gas_limit : u64)
      : option (Result.t FrameInit.t (EVMError.t Error) * Context.t DB Error) :=
    let memory := {| Memory.value := []; Memory.shared_buffer := ctx.(Context.local).(LocalContext.shared_memory_buffer) |} in
    let bytecode := match ctx.(Context.tx).(TxEnv.kind) with
      | TxKind.Create => Some (Result.Ok None, ctx)
      | TxKind.Call target =>
        match load_code ctx target with
        | None => None
        | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
        | Some (Result.Ok (code, hash), ctx) =>
          match Impl_Bytecode.delegated_address code with
          | None => Some (Result.Ok (Some (code, hash)), ctx)
          | Some delegate =>
            match load_code ctx delegate with
            | None => None
            | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
            | Some (Result.Ok code, ctx) => Some (Result.Ok (Some code), ctx)
            end
          end
        end
      end in
    match bytecode with
    | None => None
    | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
    | Some (Result.Ok code, ctx) => Some (Result.Ok {| FrameInit.depth := 0; FrameInit.memory := memory;
        FrameInit.frame_input := create_init_frame ctx.(Context.tx) code gas_limit |}, ctx)
    end.

  Definition last_frame_result {DB Error : Set} (ctx : Context.t DB Error) (result : FrameResult.t) : FrameResult.t :=
    FrameResult.map_interpreter_result (fun output =>
      let remaining := output.(InterpreterResult.gas).(Gas.remaining) in
      let refunded := output.(InterpreterResult.gas).(Gas.refunded) in
      let gas := Impl_Gas.new_spent ctx.(Context.tx).(TxEnv.gas_limit) in
      let gas := if Impl_InstructionResult.is_ok_or_revert output.(InterpreterResult.result)
        then Impl_Gas.erase_cost gas remaining else gas in
      let gas := if Impl_InstructionResult.is_ok output.(InterpreterResult.result)
        then Impl_Gas.record_refund gas refunded else gas in
      output <| InterpreterResult.gas := gas |>) result.

  Definition execution {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (fuel : nat) (ctx : Context.t DB Error) (initial : InitialAndFloorGas.t)
      : option (Result.t FrameResult.t (EVMError.t Error) * Context.t DB Error) :=
    let gas_limit := BinOp.Wrap.sub ctx.(Context.tx).(TxEnv.gas_limit) initial.(InitialAndFloorGas.initial_gas) in
    match first_frame_input ctx gas_limit with
    | None => None
    | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
    | Some (Result.Ok input, ctx) =>
      match ExecutionLoop.run_exec_loop fuel {| Evm.ctx := ctx; Evm.frame_stack := [] |} input with
      | None => None
      | Some (Result.Err error, evm, _) => Some (Result.Err (EVMError.from_context error), evm.(Evm.ctx))
      | Some (Result.Ok result, evm, _) => Some (Result.Ok (last_frame_result evm.(Evm.ctx) result), evm.(Evm.ctx))
      end
    end.

  Definition post_execution {DB Error : Set} `{Database.C DB Error} (ctx : Context.t DB Error)
      (result : FrameResult.t) (initial : InitialAndFloorGas.t) (eip7702_refund : i64)
      : option (Result.t FrameResult.t (EVMError.t Error) * Context.t DB Error) :=
    let result := FrameResult.map_interpreter_result (fun output =>
      output <| InterpreterResult.gas := PostExecution.eip7623_check_gas_floor
        (PostExecution.refund ctx.(Context.cfg).(CfgEnv.spec) output.(InterpreterResult.gas) eip7702_refund) initial |>) result in
    let gas := (FrameResult.into_interpreter_result result).(InterpreterResult.gas) in
    match PostExecution.reimburse_caller ctx gas {| Uint.value := 0 |} with
    | None => None
    | Some (Result.Err error, ctx) => Some (Result.Err (EVMError.Database error), ctx)
    | Some (Result.Ok _, ctx) =>
      match PostExecution.reward_beneficiary ctx gas with
      | None => None
      | Some (Result.Err error, ctx) => Some (Result.Err (EVMError.Database error), ctx)
      | Some (Result.Ok _, ctx) => Some (Result.Ok result, ctx)
      end
    end.

  Definition execution_result {DB Error : Set} (ctx : Context.t DB Error) (result : FrameResult.t)
      : option (Result.t ExecutionResult.t (EVMError.t Error) * Context.t DB Error) :=
    let ctx' := ctx <| Context.error := Result.Ok tt |> in
    match ctx.(Context.error) with
    | Result.Err error => Some (Result.Err (EVMError.from_context error), ctx')
    | Result.Ok _ =>
      match PostExecution.output ctx' result with
      | None => None
      | Some (result, ctx) => Some (Result.Ok result, ctx
          <| Context.journaled_state := Impl_Journal.commit_tx ctx.(Context.journaled_state) |>
          <| Context.local := Impl_LocalContext.clear ctx.(Context.local) |>)
      end
    end.

  Definition run_without_catch_error_with_gas {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (fuel : nat) (precompile_addresses : list Address.t) (ctx : Context.t DB Error)
      : option (Result.t (ExecutionResult.t * Gas.t) (EVMError.t Error) * Context.t DB Error) :=
    match validate ctx with
    | Result.Err error => Some (Result.Err error, ctx)
    | Result.Ok initial =>
      match pre_execution ctx precompile_addresses with
      | None => None
      | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
      | Some (Result.Ok eip7702_refund, ctx) =>
        match execution fuel ctx initial with
        | None => None
        | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
        | Some (Result.Ok result, ctx) =>
          match post_execution ctx result initial (cast_integer IntegerKind.I64 eip7702_refund) with
          | None => None
          | Some (Result.Err error, ctx) => Some (Result.Err error, ctx)
          | Some (Result.Ok result, ctx) =>
            let gas := (FrameResult.into_interpreter_result result).(InterpreterResult.gas) in
            option_map (fun '(output, ctx) =>
              (match output with
               | Result.Ok output => Result.Ok (output, gas)
               | Result.Err error => Result.Err error
               end, ctx)) (execution_result ctx result)
          end
        end
      end
    end.

  Definition discard_gas {DB Error : Set}
      (output : Result.t (ExecutionResult.t * Gas.t) (EVMError.t Error) * Context.t DB Error) :=
    let '(result, ctx) := output in
    (match result with
     | Result.Ok (result, _) => Result.Ok result
     | Result.Err error => Result.Err error
     end, ctx).

  Definition run_without_catch_error {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (fuel : nat) (precompile_addresses : list Address.t) (ctx : Context.t DB Error)
      : option (Result.t ExecutionResult.t (EVMError.t Error) * Context.t DB Error) :=
    option_map discard_gas (run_without_catch_error_with_gas fuel precompile_addresses ctx).

  Definition catch_error {DB Error : Set} (ctx : Context.t DB Error) (error : EVMError.t Error)
      : option (Result.t ExecutionResult.t (EVMError.t Error) * Context.t DB Error) :=
    option_map (fun journal => (Result.Err error, ctx <| Context.journaled_state := journal |>
      <| Context.local := Impl_LocalContext.clear ctx.(Context.local) |>))
      (Impl_Journal.discard_tx ctx.(Context.journaled_state)).

  Definition run_with_gas {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (fuel : nat) (precompile_addresses : list Address.t) (ctx : Context.t DB Error)
      : option (Result.t (ExecutionResult.t * Gas.t) (EVMError.t Error) * Context.t DB Error) :=
    match run_without_catch_error_with_gas fuel precompile_addresses ctx with
    | None => None
    | Some (Result.Err error, ctx) =>
        option_map (fun '(_, ctx) => (Result.Err error, ctx)) (catch_error ctx error)
    | Some (Result.Ok result, ctx) => Some (Result.Ok result, ctx)
    end.

  Definition run {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (fuel : nat) (precompile_addresses : list Address.t) (ctx : Context.t DB Error)
      : option (Result.t ExecutionResult.t (EVMError.t Error) * Context.t DB Error) :=
    match run_without_catch_error fuel precompile_addresses ctx with
    | None => None
    | Some (Result.Err error, ctx) => catch_error ctx error
    | Some (Result.Ok result, ctx) => Some (Result.Ok result, ctx)
    end.
End Handler.

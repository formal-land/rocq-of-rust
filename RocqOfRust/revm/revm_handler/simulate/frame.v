Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import alloc.links.boxed.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address_creation.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_handler.simulate.frame_data.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import revm.revm_interpreter.simulate.eth_interpreter.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_result.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import ruint.links.lib.


Module ItemOrResult.
  Inductive t (Item Result : Set) : Set :=
  | Item (item : Item)
  | Result (result : Result).

  Arguments Item {Item Result}.

  Arguments Result {Item Result}.
End ItemOrResult.

Module FrameInit.
  Record t : Set := {
    depth : usize;
    memory : Memory.t;
    frame_input : FrameInput.t;
  }.
End FrameInit.

Module EthFrame.
  Record t : Set := {
    data : FrameData.t;
    input : FrameInput.t;
    depth : usize;
    checkpoint : JournalCheckpoint.t;
    interpreter : EthInterpreter.t;
    is_finished : bool;
  }.
End EthFrame.

(** Explicit mutable receiver: DB/context updates survive a provider error.
    [None] is an evaluator/invariant failure, not an EVM result. *)
Module PrecompileProvider.
  Class C (DB Error : Set) : Type := {
    run : Context.t DB Error -> Memory.t -> CallInputs.t ->
      option (Result.t (option InterpreterResult.t) string * Context.t DB Error);
  }.
End PrecompileProvider.

Module Impl_EthFrame.
  Definition clear (data : FrameData.t) (input : FrameInput.t) (depth : usize)
      (memory : Memory.t) (code : alloy_primitives.bytes.links.mod.Bytes.t) (inputs : InputsImpl.t)
      (is_static : bool) (spec_id : SpecId.t) (gas_limit : u64)
      (checkpoint : JournalCheckpoint.t) : EthFrame.t := {|
    EthFrame.data := data;
    EthFrame.input := input;
    EthFrame.depth := depth;
    EthFrame.checkpoint := checkpoint;
    EthFrame.interpreter := Impl_EthInterpreter.new memory code inputs is_static spec_id gas_limit;
    EthFrame.is_finished := false;
  |}.

  Definition initial_result (status : InstructionResult.t) (gas_limit : u64) : InterpreterResult.t := {|
    InterpreterResult.result := status;
    InterpreterResult.gas := Impl_Gas.new gas_limit;
    InterpreterResult.output := Impl_Bytes.new;
  |}.

  Definition call_result (inputs : CallInputs.t) (status : InstructionResult.t) : FrameResult.t :=
    FrameResult.Call (CallOutcome.new (initial_result status inputs.(CallInputs.gas_limit))
      inputs.(CallInputs.return_memory_offset)).

  Definition finish_call_init {DB Error : Set} (ctx : Context.t DB Error)
      (depth : usize) (memory : Memory.t) (inputs : CallInputs.t)
      (checkpoint : JournalCheckpoint.t) (code : revm.revm_bytecode.links.bytecode.Bytecode.t)
      : ItemOrResult.t EthFrame.t FrameResult.t * Context.t DB Error :=
    let code := code.(revm.revm_bytecode.links.bytecode.Bytecode.original_bytes) in
    if Nat.eqb (List.length code.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)) 0 then
      (ItemOrResult.Result (call_result inputs InstructionResult.Stop),
        ctx <| Context.journaled_state := Impl_Journal.checkpoint_commit ctx.(Context.journaled_state) |>)
    else
      let input := {| InputsImpl.target_address := inputs.(CallInputs.target_address);
        InputsImpl.bytecode_address := Some inputs.(CallInputs.bytecode_address);
        InputsImpl.caller_address := inputs.(CallInputs.caller);
        InputsImpl.input := inputs.(CallInputs.input);
        InputsImpl.call_value := match inputs.(CallInputs.value) with
          | CallValue.Transfer value | CallValue.Apparent value => value end |} in
      (ItemOrResult.Item (clear
        (FrameData.Call {| CallFrame.return_memory_range := inputs.(CallInputs.return_memory_offset) |})
        (FrameInput.Call {| Box.value := inputs |}) depth memory code input
        inputs.(CallInputs.is_static) ctx.(Context.cfg).(CfgEnv.spec)
        inputs.(CallInputs.gas_limit) checkpoint), ctx).

  Definition make_call_frame {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (ctx : Context.t DB Error) (depth : usize) (memory : Memory.t) (inputs : CallInputs.t)
      : option (Result.t (ItemOrResult.t EthFrame.t FrameResult.t) (ContextError.t Error) * Context.t DB Error) :=
    if Z.ltb 1024 depth.(Integer.value) then
      Some (Result.Ok (ItemOrResult.Result (call_result inputs InstructionResult.CallTooDeep)), ctx)
    else
      let '(checkpoint, journal) := Impl_Journal.checkpoint ctx.(Context.journaled_state) in
      let transfer := match inputs.(CallInputs.value) with
        | CallValue.Transfer value => Impl_Journal.transfer_loaded journal
            inputs.(CallInputs.caller) inputs.(CallInputs.target_address) value
        | CallValue.Apparent _ => Some (None, journal)
        end in
      match transfer with
      | None => None
      | Some (transfer_error, journal) =>
        let ctx := ctx <| Context.journaled_state := journal |> in
        match transfer_error with
        | Some error => option_map (fun journal =>
            (Result.Ok (ItemOrResult.Result (call_result inputs (Impl_InstructionResult.from_transfer_error error))),
              ctx <| Context.journaled_state := journal |>))
            (Impl_Journal.checkpoint_revert journal checkpoint)
        | None =>
          match PrecompileProvider.run ctx memory inputs with
          | None => None
          | Some (Result.Err error, ctx) => Some (Result.Err (ContextError.Custom error), ctx)
          | Some (Result.Ok (Some output), ctx) =>
            let journal := ctx.(Context.journaled_state) in
            let success := Impl_InstructionResult.is_ok output.(InterpreterResult.result) in
            if negb success && negb (Z.leb 0 checkpoint.(JournalCheckpoint.log_i).(Integer.value) &&
              Z.leb checkpoint.(JournalCheckpoint.log_i).(Integer.value) (Z.of_nat (List.length (Impl_Journal.logs journal))))
            then None else
            let logs := if success then [] else
              List.skipn (Z.to_nat checkpoint.(JournalCheckpoint.log_i).(Integer.value)) (Impl_Journal.logs journal) in
            let journal := if success then Some (Impl_Journal.checkpoint_commit journal)
              else Impl_Journal.checkpoint_revert journal checkpoint in
            option_map (fun journal => (Result.Ok (ItemOrResult.Result (FrameResult.Call {|
              CallOutcome.result := output;
              CallOutcome.memory_offset := inputs.(CallInputs.return_memory_offset);
              CallOutcome.was_precompile_called := true;
              CallOutcome.precompile_call_logs := logs |})), ctx <| Context.journaled_state := journal |>)) journal
          | Some (Result.Ok None, ctx) =>
            match inputs.(CallInputs.known_bytecode) with
            | Some (_, code) => let '(frame, ctx) := finish_call_init ctx depth memory inputs checkpoint code in
                Some (Result.Ok frame, ctx)
            | None =>
              match Impl_Journal.load_account_with_code ctx.(Context.journaled_state) inputs.(CallInputs.bytecode_address) with
              | None => None
              | Some (result, journal) =>
                let ctx := ctx <| Context.journaled_state := journal |> in
                match result with
                | Result.Err error => Some (Result.Err (ContextError.Db error), ctx)
                | Result.Ok (account, _) =>
                  let code := match account.(Account.info).(AccountInfo.code) with
                    | Some code => code | None => {| revm.revm_bytecode.links.bytecode.Bytecode.original_bytes := Impl_Bytes.new |} end in
                  let '(frame, ctx) := finish_call_init ctx depth memory inputs checkpoint code in
                  Some (Result.Ok frame, ctx)
                end
              end
            end
          end
        end
      end.

  Definition make_create_frame {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) (depth : usize) (memory : Memory.t) (inputs : CreateInputs.t)
      : option (Result.t (ItemOrResult.t EthFrame.t FrameResult.t) (ContextError.t Error) * Context.t DB Error) :=
    let return_error status ctx := Some (Result.Ok (ItemOrResult.Result (FrameResult.Create {|
      CreateOutcome.result := initial_result status inputs.(CreateInputs.gas_limit);
      CreateOutcome.address := None |})), ctx) in
    if Z.ltb 1024 depth.(Integer.value) then return_error InstructionResult.CallTooDeep ctx else
    match Impl_Journal.load_account_mut_optional_code ctx.(Context.journaled_state) inputs.(CreateInputs.caller) false with
    | None => None
    | Some (result, journal) =>
      let ctx := ctx <| Context.journaled_state := journal |> in
      match result with
      | Result.Err error => Some (Result.Err (ContextError.Db error), ctx)
      | Result.Ok (caller_info, _) =>
        if Z.ltb (Impl_JournaledAccount.balance caller_info).(Uint.value) inputs.(CreateInputs.value).(Uint.value) then
          return_error InstructionResult.OutOfFunds ctx
        else
          let old_nonce := Impl_JournaledAccount.nonce caller_info in
          let '(bumped, caller_info) := Impl_JournaledAccount.bump_nonce caller_info in
          match Impl_Journal.store_account journal caller_info with
          | None => None
          | Some journal =>
            let ctx := ctx <| Context.journaled_state := journal |> in
            if negb bumped then return_error InstructionResult.Return ctx else
            let code := {| revm.revm_bytecode.links.bytecode.Bytecode.original_bytes := inputs.(CreateInputs.init_code) |} in
            let address := match inputs.(CreateInputs.scheme) with
              | CreateScheme.Create => Impl_AddressCreation.create inputs.(CreateInputs.caller) old_nonce
              | CreateScheme.Create2 salt => Impl_AddressCreation.create2 inputs.(CreateInputs.caller)
                  (FixedBytes.from_Z salt.(Uint.value)) (Impl_Bytecode.hash_slow code)
              end in
            match Impl_Journal.load_account journal address with
            | None => None
            | Some (result, journal) =>
              let ctx := ctx <| Context.journaled_state := journal |> in
              match result with
              | Result.Err error => Some (Result.Err (ContextError.Db error), ctx)
              | Result.Ok _ =>
                let spec := ctx.(Context.cfg).(CfgEnv.spec) in
                match Impl_Journal.create_account_checkpoint journal inputs.(CreateInputs.caller)
                  address inputs.(CreateInputs.value) spec with
                | None => None
                | Some (result, journal) =>
                  let ctx := ctx <| Context.journaled_state := journal |> in
                  match result with
                  | Result.Err error => return_error (Impl_InstructionResult.from_transfer_error error) ctx
                  | Result.Ok checkpoint =>
                    let interpreter_input := {| InputsImpl.target_address := address;
                      InputsImpl.bytecode_address := None;
                      InputsImpl.caller_address := inputs.(CreateInputs.caller);
                      InputsImpl.input := CallInput.Bytes Impl_Bytes.new;
                      InputsImpl.call_value := inputs.(CreateInputs.value) |} in
                    Some (Result.Ok (ItemOrResult.Item (clear
                      (FrameData.Create {| CreateFrame.created_address := address |})
                      (FrameInput.Create {| Box.value := inputs |}) depth memory inputs.(CreateInputs.init_code)
                      interpreter_input false spec inputs.(CreateInputs.gas_limit) checkpoint)), ctx)
                  end
                end
              end
            end
          end
      end
    end.

  Definition init_with_context {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (ctx : Context.t DB Error) (init : FrameInit.t)
      : option (Result.t (ItemOrResult.t EthFrame.t FrameResult.t) (ContextError.t Error) * Context.t DB Error) :=
    match init.(FrameInit.frame_input) with
    | FrameInput.Call inputs => make_call_frame ctx init.(FrameInit.depth) init.(FrameInit.memory) inputs.(Box.value)
    | FrameInput.Create inputs => make_create_frame ctx init.(FrameInit.depth) init.(FrameInit.memory) inputs.(Box.value)
    | FrameInput.Empty => None
    end.

  Definition return_create {DB : Set} (journal : Journal.t DB) (checkpoint : JournalCheckpoint.t)
      (output : InterpreterResult.t) (address : Address.t) (max_code_size : usize)
      (spec_id : SpecId.t) : option (InterpreterResult.t * Journal.t DB) :=
    let fail status := option_map (fun journal => (output <| InterpreterResult.result := status |>, journal))
      (Impl_Journal.checkpoint_revert journal checkpoint) in
    if negb (Impl_InstructionResult.is_ok output.(InterpreterResult.result)) then
      option_map (fun journal => (output, journal)) (Impl_Journal.checkpoint_revert journal checkpoint)
    else
      let code := output.(InterpreterResult.output).(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
      if Impl_SpecId.is_enabled_in spec_id SpecId.LONDON &&
          (match code with [] => false | byte :: _ => Z.eqb byte.(Integer.value) 239 end) then
        fail InstructionResult.CreateContractStartingWithEF
      else if Impl_SpecId.is_enabled_in spec_id SpecId.SPURIOUS_DRAGON &&
          Z.ltb max_code_size.(Integer.value) (Z.of_nat (List.length code)) then
        fail InstructionResult.CreateContractSizeLimit
      else
        let deposit := BinOp.Wrap.mul ({| Integer.value := Z.of_nat (List.length code) |} : u64) 200 in
        let gas := Impl_Gas.record_cost output.(InterpreterResult.gas) deposit in
        let result := match gas with
          | Some gas => Some (output <| InterpreterResult.gas := gas |>)
          | None => if Impl_SpecId.is_enabled_in spec_id SpecId.HOMESTEAD then None
              else Some (output <| InterpreterResult.output := Impl_Bytes.new |>)
          end in
        match result with
        | None => fail InstructionResult.OutOfGas
        | Some output =>
          let journal := Impl_Journal.checkpoint_commit journal in
          let code := {| revm.revm_bytecode.links.bytecode.Bytecode.original_bytes := output.(InterpreterResult.output) |} in
          option_map (fun journal => (output <| InterpreterResult.result := InstructionResult.Return |>, journal))
            (Impl_Journal.set_code_with_hash journal address code (Impl_Bytecode.hash_slow code))
        end.

  Definition process_next_action {DB Error : Set} (self : EthFrame.t) (ctx : Context.t DB Error)
      (action : InterpreterAction.t)
      : option (ItemOrResult.t FrameInit.t FrameResult.t * Context.t DB Error) :=
    match action with
    | InterpreterAction.NewFrame input => Some (ItemOrResult.Item {|
        FrameInit.depth := BinOp.Wrap.add self.(EthFrame.depth) 1;
        FrameInit.memory := Impl_EthInterpreter.new_child_context self.(EthFrame.interpreter).(EthInterpreter.memory);
        FrameInit.frame_input := input |}, ctx)
    | InterpreterAction.Return output =>
      let journal := ctx.(Context.journaled_state) in
      match self.(EthFrame.data) with
      | FrameData.Call frame =>
        let journal := if Impl_InstructionResult.is_ok output.(InterpreterResult.result)
          then Some (Impl_Journal.checkpoint_commit journal)
          else Impl_Journal.checkpoint_revert journal self.(EthFrame.checkpoint) in
        option_map (fun journal =>
          (ItemOrResult.Result (FrameResult.Call (CallOutcome.new output frame.(CallFrame.return_memory_range))),
            ctx <| Context.journaled_state := journal |>)) journal
      | FrameData.Create frame =>
        option_map (fun '(output, journal) =>
          (ItemOrResult.Result (FrameResult.Create {| CreateOutcome.result := output;
            CreateOutcome.address := Some frame.(CreateFrame.created_address) |}),
            ctx <| Context.journaled_state := journal |>))
          (return_create journal self.(EthFrame.checkpoint) output frame.(CreateFrame.created_address)
            (Impl_CfgEnv.max_code_size ctx.(Context.cfg)) ctx.(Context.cfg).(CfgEnv.spec))
      end
    end.

  Definition return_result {DB Error : Set} (self : EthFrame.t) (ctx : Context.t DB Error)
      (result : FrameResult.t)
      : option (Result.t EthFrame.t (ContextError.t Error) * Context.t DB Error) :=
    let ctx' := ctx <| Context.error := Result.Ok tt |> in
    match ctx.(Context.error) with
    | Result.Err error => Some (Result.Err error, ctx')
    | Result.Ok _ =>
      let interpreter := self.(EthFrame.interpreter) in
      let output := FrameResult.into_interpreter_result result in
      match output.(InterpreterResult.result) with
      | InstructionResult.FatalExternalError => None
      | status =>
        let success := Impl_InstructionResult.is_ok status in
        let return_gas := Impl_InstructionResult.is_ok_or_revert status in
        let gas := if return_gas then Impl_Gas.erase_cost interpreter.(EthInterpreter.gas)
          output.(InterpreterResult.gas).(Gas.remaining) else interpreter.(EthInterpreter.gas) in
        let gas := if success then Impl_Gas.record_refund gas output.(InterpreterResult.gas).(Gas.refunded) else gas in
        let interpreter := interpreter <| EthInterpreter.gas := gas |> in
        let interpreter := match result with
          | FrameResult.Call outcome =>
            let bytes := output.(InterpreterResult.output).(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
            let range := outcome.(CallOutcome.memory_offset) in
            let length := BinOp.Wrap.sub range.(Range.end_) range.(Range.start) in
            let count := Z.min length.(Integer.value) (Z.of_nat (List.length bytes)) in
            let memory := if return_gas then Memory.set interpreter.(EthInterpreter.memory) range.(Range.start)
              (List.firstn (Z.to_nat count) bytes) else interpreter.(EthInterpreter.memory) in
            let '(_, stack) := StackTrait.push interpreter.(EthInterpreter.stack) {| Uint.value := if success then 1 else 0 |} in
            interpreter <| EthInterpreter.return_data := output.(InterpreterResult.output) |>
              <| EthInterpreter.stack := stack |> <| EthInterpreter.memory := memory |>
          | FrameResult.Create outcome =>
            let return_data := match status with InstructionResult.Revert => output.(InterpreterResult.output)
              | _ => Impl_Bytes.new end in
            let value := if success then match outcome.(CreateOutcome.address) with
              | Some address => address.(Address.value) | None => 0 end else 0 in
            let '(_, stack) := StackTrait.push interpreter.(EthInterpreter.stack) {| Uint.value := value |} in
            interpreter <| EthInterpreter.return_data := return_data |> <| EthInterpreter.stack := stack |>
          end in
        Some (Result.Ok (self <| EthFrame.interpreter := interpreter |>), ctx')
      end
    end.
End Impl_EthFrame.

Require Import simulate.RocqOfRust.
Require Import core.links.result.
Require Import revm.revm_context.simulate.local.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_handler.simulate.frame_data.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.gas.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.add.
Require Import revm.revm_interpreter.links.gas.
Require Import ruint.links.lib.

Module PostExecution.
  Definition eip7623_check_gas_floor (gas : Gas.t)
      (init_and_floor_gas : InitialAndFloorGas.t) : Gas.t :=
    if Impl_Gas.spent_sub_refunded gas <i init_and_floor_gas.(InitialAndFloorGas.floor_gas)
    then Impl_Gas.set_refund
      (Impl_Gas.set_spent gas init_and_floor_gas.(InitialAndFloorGas.floor_gas)) 0
    else gas.

  Definition refund (spec : SpecId.t) (gas : Gas.t) (eip7702_refund : i64) : Gas.t :=
    Impl_Gas.set_final_refund (Impl_Gas.record_refund gas eip7702_refund)
      (Impl_SpecId.is_enabled_in spec SpecId.LONDON).

  Definition caller_reimbursement {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (basefee : u64) (gas : Gas.t) (additional_refund : aliases.U256.t)
      : aliases.U256.t :=
    let effective_gas_price := Transaction.Fees.effective_gas_price tx
      {| Integer.value := basefee.(Integer.value) |} in
    let remaining := Impl_Gas.remaining gas +i
      ({| Integer.value := (Impl_Gas.refunded gas).(Integer.value) mod 2 ^ 64 |} : u64) in
    let reimbursement := effective_gas_price *is
      ({| Integer.value := remaining.(Integer.value) |} : u128) in
    Impl_Uint.wrapping_add {| Uint.value := reimbursement.(Integer.value) |} additional_refund.

  Definition reimburse_caller {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) (gas : Gas.t) (additional_refund : aliases.U256.t)
      : option (Result.t unit Error * Context.t DB Error) :=
    let amount := caller_reimbursement ctx.(Context.tx)
      ctx.(Context.block).(BlockEnv.basefee) gas additional_refund in
    option_map (fun '(result, journal) => (result, ctx <| Context.journaled_state := journal |>))
      (Impl_Journal.balance_incr ctx.(Context.journaled_state) ctx.(Context.tx).(TxEnv.caller) amount).

  Definition beneficiary_reward {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (basefee : u64) (spec : SpecId.t) (gas : Gas.t) : aliases.U256.t :=
    let basefee : u128 := {| Integer.value := basefee.(Integer.value) |} in
    let effective_gas_price := Transaction.Fees.effective_gas_price tx basefee in
    let coinbase_gas_price := if Impl_SpecId.is_enabled_in spec SpecId.LONDON
      then effective_gas_price -is basefee else effective_gas_price in
    let reward := coinbase_gas_price *i
      ({| Integer.value := (Impl_Gas.used gas).(Integer.value) |} : u128) in
    {| Uint.value := reward.(Integer.value) |}.

  Definition reward_beneficiary {DB Error : Set} `{Database.C DB Error}
      (ctx : Context.t DB Error) (gas : Gas.t) : option (Result.t unit Error * Context.t DB Error) :=
    let amount := beneficiary_reward ctx.(Context.tx)
      ctx.(Context.block).(BlockEnv.basefee) ctx.(Context.cfg).(CfgEnv.spec) gas in
    option_map (fun '(result, journal) => (result, ctx <| Context.journaled_state := journal |>))
      (Impl_Journal.balance_incr ctx.(Context.journaled_state) ctx.(Context.block).(BlockEnv.beneficiary) amount).

  Definition halt_reason (status : InstructionResult.t) : option HaltReason.t :=
    match status with
    | InstructionResult.OutOfGas => Some (HaltReason.OutOfGas OutOfGasError.Basic)
    | InstructionResult.MemoryOOG => Some (HaltReason.OutOfGas OutOfGasError.Memory)
    | InstructionResult.MemoryLimitOOG => Some (HaltReason.OutOfGas OutOfGasError.MemoryLimit)
    | InstructionResult.PrecompileOOG => Some (HaltReason.OutOfGas OutOfGasError.Precompile)
    | InstructionResult.InvalidOperandOOG => Some (HaltReason.OutOfGas OutOfGasError.InvalidOperand)
    | InstructionResult.ReentrancySentryOOG => Some (HaltReason.OutOfGas OutOfGasError.ReentrancySentry)
    | InstructionResult.OpcodeNotFound => Some HaltReason.OpcodeNotFound
    | InstructionResult.CallNotAllowedInsideStatic => Some HaltReason.CallNotAllowedInsideStatic
    | InstructionResult.StateChangeDuringStaticCall => Some HaltReason.StateChangeDuringStaticCall
    | InstructionResult.InvalidFEOpcode => Some HaltReason.InvalidFEOpcode
    | InstructionResult.InvalidJump => Some HaltReason.InvalidJump
    | InstructionResult.NotActivated => Some HaltReason.NotActivated
    | InstructionResult.StackUnderflow => Some HaltReason.StackUnderflow
    | InstructionResult.StackOverflow => Some HaltReason.StackOverflow
    | InstructionResult.OutOfOffset => Some HaltReason.OutOfOffset
    | InstructionResult.CreateCollision => Some HaltReason.CreateCollision
    | InstructionResult.OverflowPayment => Some HaltReason.OverflowPayment
    | InstructionResult.PrecompileError => Some HaltReason.PrecompileError
    | InstructionResult.NonceOverflow => Some HaltReason.NonceOverflow
    | InstructionResult.CreateContractSizeLimit => Some HaltReason.CreateContractSizeLimit
    | InstructionResult.CreateContractStartingWithEF => Some HaltReason.CreateContractStartingWithEF
    | InstructionResult.CreateInitCodeSizeLimit => Some HaltReason.CreateInitCodeSizeLimit
    | InstructionResult.CallTooDeep => Some HaltReason.CallTooDeep
    | InstructionResult.OutOfFunds => Some HaltReason.OutOfFunds
    | _ => None
    end.

  Definition output {DB Error : Set} (ctx : Context.t DB Error) (result : FrameResult.t)
      : option (ExecutionResult.t * Context.t DB Error) :=
    let interpreter_result := FrameResult.into_interpreter_result result in
    let gas := interpreter_result.(InterpreterResult.gas) in
    let gas_used := Impl_Gas.used gas in
    let gas_refunded : u64 := {| Integer.value := gas.(Gas.refunded).(Integer.value) mod 2 ^ 64 |} in
    let output := match result with
      | FrameResult.Call outcome => Output.Call outcome.(CallOutcome.result).(InterpreterResult.output)
      | FrameResult.Create outcome => Output.Create outcome.(CreateOutcome.result).(InterpreterResult.output) outcome.(CreateOutcome.address)
      end in
    let '(logs, journal) := Impl_Journal.take_logs ctx.(Context.journaled_state) in
    let ctx := ctx <| Context.journaled_state := journal |> in
    let success reason := Some (ExecutionResult.Success reason gas_used gas_refunded logs output, ctx) in
    match interpreter_result.(InterpreterResult.result) with
    | InstructionResult.Stop => success SuccessReason.Stop
    | InstructionResult.Return => success SuccessReason.Return
    | InstructionResult.SelfDestruct => success SuccessReason.SelfDestruct
    | InstructionResult.Revert | InstructionResult.CreateInitCodeStartingEF00 | InstructionResult.InvalidEOFInitCode =>
        Some (ExecutionResult.Revert gas_used (Output.into_data output), ctx)
    | InstructionResult.PrecompileError =>
        let '(message, local) := Impl_LocalContext.take_precompile_error_context ctx.(Context.local) in
        Some (ExecutionResult.Halt (match message with Some message => HaltReason.PrecompileErrorWithContext message
          | None => HaltReason.PrecompileError end) gas_used, ctx <| Context.local := local |>)
    | status => option_map (fun reason => (ExecutionResult.Halt reason gas_used, ctx)) (halt_reason status)
    end.

End PostExecution.

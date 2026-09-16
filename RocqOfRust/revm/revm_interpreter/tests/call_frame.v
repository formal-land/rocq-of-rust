From Stdlib Require Import List ZArith.

Require Import alloc.links.boxed.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import core.ops.links.range.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module CallFrame.
  Definition state : Set := InstructionContext.State.t StatefulHost.t WIRE WIRE_types.
  Definition machine : Set := Interpreter.t WIRE WIRE_types.

  Definition gas_returned (result : InstructionResult.t) : bool :=
    StatefulFrame.successful result ||
    match result with
    | InstructionResult.Revert | InstructionResult.CallTooDeep
    | InstructionResult.OutOfFunds | InstructionResult.InvalidEOFInitCode
    | InstructionResult.CreateInitCodeStartingEF00
    | InstructionResult.InvalidExtDelegateCallTarget => true
    | _ => false
    end.

  Definition result (status : InstructionResult.t) (interpreter : machine) :=
    {| InterpreterResult.result := status;
       InterpreterResult.output := Impl_Bytes.new;
       InterpreterResult.gas := interpreter.(Interpreter.gas) |}.

  Definition resume (parent : machine) (range : Range.t usize)
      (output : InterpreterResult.t) : machine :=
    let success := StatefulFrame.successful output.(InterpreterResult.result) in
    let return_gas := gas_returned output.(InterpreterResult.result) in
    let gas := if return_gas then
      Impl_Gas.erase_cost parent.(Interpreter.gas)
        output.(InterpreterResult.gas).(Gas.remaining)
      else parent.(Interpreter.gas) in
    let gas := if success then Impl_Gas.record_refund gas
      output.(InterpreterResult.gas).(Gas.refunded) else gas in
    let bytes := output.(InterpreterResult.output)
      .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
    let len := Z.min (range.(Range.end_).(Integer.value) - range.(Range.start).(Integer.value))
      (Z.of_nat (List.length bytes)) in
    let memory := if return_gas && (0 <? len) then
      Memory.set parent.(Interpreter.memory) range.(Range.start)
        (List.firstn (Z.to_nat len) bytes)
      else parent.(Interpreter.memory) in
    parent
      <| @Interpreter.bytecode WIRE _ WIRE_types _ :=
        parent.(Interpreter.bytecode) <| Bytecode.action := None |> |>
      <| @Interpreter.stack WIRE _ WIRE_types _ :=
        {| Stack.value := {| Uint.value := if success then 1 else 0 |} ::
          parent.(Interpreter.stack).(Stack.value) |} |>
      <| @Interpreter.gas WIRE _ WIRE_types _ := gas |>
      <| @Interpreter.memory WIRE _ WIRE_types _ := memory |>
      <| @Interpreter.return_data WIRE _ WIRE_types _ := output.(InterpreterResult.output) |>.

  Definition child (parent : machine) (inputs : CallInputs.t)
      (code : list u8) : machine :=
    let input := match inputs.(CallInputs.input) with
      | CallInput.Bytes data => data
      | CallInput.SharedBuffer range =>
          let len := range.(Range.end_).(Integer.value) - range.(Range.start).(Integer.value) in
          if len =? 0 then Impl_Bytes.new else
            Impl_Bytes.copy_from_slice
              (Memory.slice parent.(Interpreter.memory) range.(Range.start)
                {| Integer.value := len |})
      end in
    let value := match inputs.(CallInputs.value) with
      | CallValue.Transfer value | CallValue.Apparent value => value end in
    let interpreter := make_interpreter_with_bytecode code {| Stack.value := [] |} in
    interpreter
      <| @Interpreter.runtime_flag WIRE _ WIRE_types _ := parent.(Interpreter.runtime_flag) |>
      <| @Interpreter.gas WIRE _ WIRE_types _ :=
        interpreter.(Interpreter.gas)
          <| Gas.limit := inputs.(CallInputs.gas_limit) |>
          <| Gas.remaining := inputs.(CallInputs.gas_limit) |> |>
      <| @Interpreter.input WIRE _ WIRE_types _ :=
        {| Input.target_address := inputs.(CallInputs.target_address);
           Input.caller_address := inputs.(CallInputs.caller);
           Input.call_value := value;
           Input.input := CallInput.Bytes input |} |>.

  Definition balance (host : StatefulHost.t) (address : Z) : Z :=
    match StatefulHost.find_account address host.(StatefulHost.accounts) with
    | Some account => account.(StatefulHost.Account.balance)
    | None => 0
    end.

  Definition transfer (host : StatefulHost.t) (from to value : Z) :
      option InstructionResult.t * StatefulHost.t :=
    let source := balance host from in
    let target := balance host to in
    if source <? value then (Some InstructionResult.OutOfFunds, host)
    else if (from =? to) || (value =? 0) then (None, host)
    else if 2 ^ 256 <=? target + value then
      (Some InstructionResult.OverflowPayment, host)
    else
      let accounts := StatefulHost.update_account from
        (fun account => StatefulHost.account_with_balance account (source - value))
        host.(StatefulHost.accounts) in
      let accounts := StatefulHost.update_account to
        (fun account => StatefulHost.account_with_balance account (target + value)) accounts in
      let host := StatefulHost.with_accounts host accounts in
      let host := StatefulHost.append_change host (StatefulHost.Change.Balance from (source - value)) in
      (None, StatefulHost.append_change host (StatefulHost.Change.Balance to (target + value))).

  Module Pending.
    Record t : Set := {
      parent : machine;
      output_range : Range.t usize;
      checkpoint : StatefulHost.t;
    }.
  End Pending.
End CallFrame.

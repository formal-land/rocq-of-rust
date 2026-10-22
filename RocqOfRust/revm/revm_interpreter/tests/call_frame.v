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
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
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
    let value := match inputs.(CallInputs.value) with
      | CallValue.Transfer value | CallValue.Apparent value => value end in
    let interpreter := make_interpreter_with_bytecode code {| Stack.value := [] |} in
    (* Each frame's ranges are local to its parent's memory. Retain that
       immutable buffer for input reads; the child starts with empty local memory. *)
    interpreter
      <| @Interpreter.memory WIRE _ WIRE_types _ :=
        interpreter.(Interpreter.memory)
          <| Memory.shared_buffer := parent.(Interpreter.memory).(Memory.value) |> |>
      <| @Interpreter.runtime_flag WIRE _ WIRE_types _ :=
        parent.(Interpreter.runtime_flag)
          <| RuntimeFlags.is_static := inputs.(CallInputs.is_static) |> |>
      <| @Interpreter.gas WIRE _ WIRE_types _ :=
        interpreter.(Interpreter.gas)
          <| Gas.limit := inputs.(CallInputs.gas_limit) |>
          <| Gas.remaining := inputs.(CallInputs.gas_limit) |> |>
      <| @Interpreter.input WIRE _ WIRE_types _ :=
        {| Input.target_address := inputs.(CallInputs.target_address);
           Input.caller_address := inputs.(CallInputs.caller);
           Input.call_value := value;
           Input.input := inputs.(CallInputs.input) |} |>.

  Definition balance (host : StatefulHost.t) (address : Z) : Z :=
    match StatefulHost.find_account address host.(StatefulHost.accounts) with
    | Some account => account.(StatefulHost.Account.balance)
    | None => 0
    end.

  (** Match transfer_loaded's touch order. Same-address transfers never touch;
      distinct zero-value transfers touch only the destination. Error callers
      must roll back this returned host, preserving the address-3 exception. *)
  Definition transfer (host : StatefulHost.t) (from to value : Z) :
      option InstructionResult.t * StatefulHost.t :=
    let source := balance host from in
    let target := balance host to in
    if from =? to then
      (if source <? value then Some InstructionResult.OutOfFunds else None, host)
    else if value =? 0 then
      (* Loaded missing accounts become persistent on a pre-EIP-161 touch. *)
      let host := if Impl_SpecId.is_enabled_in host.(StatefulHost.spec_id) SpecId.SPURIOUS_DRAGON
        then host else StatefulHost.with_accounts host
          (StatefulHost.update_account to (fun account => account) host.(StatefulHost.accounts)) in
      (None, StatefulHost.touch_account host to)
    else
      let host := StatefulHost.touch_account host from in
      if source <? value then (Some InstructionResult.OutOfFunds, host)
      else
        let host := StatefulHost.touch_account host to in
        if 2 ^ 256 <=? target + value then
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

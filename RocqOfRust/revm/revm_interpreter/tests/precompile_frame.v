From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import simulate.RocqOfRust.

Open Scope Z_scope.

Module PrecompileFrame.
  (** Identity gas and output follow revm_precompile/identity.rs and
      calc_linear_cost_u32; status and failure gas follow precompile_provider.rs.
      The child has already materialized either shared or owned call input. *)
  Definition identity_cost (input : list u8) : Z :=
    15 + 3 * ((Z.of_nat (List.length input) + 31) / 32).

  Definition identity (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let cost := identity_cost input.(alloy_primitives.bytes.links.mod.Bytes.value)
      .(bytes.Bytes.value) in
    let gas := child.(Interpreter.gas) in
    if gas.(Gas.remaining).(Integer.value) <? cost then
      CallFrame.result InstructionResult.PrecompileOOG child
    else
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := input;
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}.
End PrecompileFrame.

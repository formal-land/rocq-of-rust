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
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.ripemd160.
Require Import revm.revm_precompile.simulate.sha256.
Require Import simulate.RocqOfRust.

Open Scope Z_scope.

Module PrecompileFrame.
  (** Gas and output follow revm_precompile/{identity,hash}.rs; status and
      failure gas follow precompile_provider.rs. Children already own input. *)
  Definition linear_cost (base word : Z) (input : list u8) : Z :=
    (base + word * ((Z.of_nat (List.length input) + 31) / 32)) mod (2 ^ 64).

  Definition identity_cost := linear_cost 15 3.
  Definition sha256_cost := linear_cost 60 12.
  Definition ripemd160_cost := linear_cost 600 120.

  Definition complete (cost_of : list u8 -> Z)
      (output_of : alloy_primitives.bytes.links.mod.Bytes.t ->
        alloy_primitives.bytes.links.mod.Bytes.t)
      (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let cost := cost_of input.(alloy_primitives.bytes.links.mod.Bytes.value)
      .(bytes.Bytes.value) in
    let gas := child.(Interpreter.gas) in
    if gas.(Gas.remaining).(Integer.value) <? cost then
      CallFrame.result InstructionResult.PrecompileOOG child
    else
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := output_of input;
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}.

  Definition identity := complete identity_cost (fun input => input).

  Definition sha256 := complete sha256_cost (fun input =>
    Impl_Bytes.copy_from_slice
      (List.map (fun byte => {| Integer.value := byte |})
        (Sha256.hash (List.map Integer.value
          input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))))).

  Definition ripemd160 := complete ripemd160_cost (fun input =>
    Impl_Bytes.copy_from_slice
      (List.map (fun byte => {| Integer.value := byte |})
        (List.repeat 0 12 ++ Ripemd160.hash (List.map Integer.value
          input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))))).

  Definition modexp (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let gas := child.(Interpreter.gas) in
    match Modexp.run_berlin
      (List.map Integer.value
        input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
      gas.(Gas.remaining).(Integer.value) with
    | Modexp.Result.Success cost output =>
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := Impl_Bytes.copy_from_slice
           (List.map (fun byte => {| Integer.value := byte |}) output);
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}
    | Modexp.Result.OutOfGas => CallFrame.result InstructionResult.PrecompileOOG child
    | Modexp.Result.InvalidLength => CallFrame.result InstructionResult.PrecompileError child
    end.

  Definition supported (address : Z) : bool :=
    (address =? 2) || (address =? 3) || (address =? 4) || (address =? 5).

  Definition run (address : Z) (child : CallFrame.machine) : option InterpreterResult.t :=
    if address =? 2 then Some (sha256 child) else
    if address =? 3 then Some (ripemd160 child) else
    if address =? 4 then Some (identity child) else
    if address =? 5 then Some (modexp child) else None.
End PrecompileFrame.

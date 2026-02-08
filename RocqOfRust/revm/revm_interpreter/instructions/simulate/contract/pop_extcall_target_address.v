Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_interpreter.instructions.links.contract.pop_extcall_target_address.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

(** Check if the first [n] bytes of a [FixedBytes] are all zero. *)
Definition has_leading_zeros {N : usize} (x : FixedBytes.t N) (n : nat) : bool :=
  let bytes := ArrayPairs.to_list x.(FixedBytes.value).(array.value) in
  List.forallb (fun b => b.(Integer.value) =? 0) (List.firstn n bytes).

Definition pop_extcall_target_address
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    option Address.t * Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter 1
    (fun interpreter => (None, interpreter)) (fun arr interpreter =>
  let '⟬ target_address ⟭ := arr.(array.value) in
  let target_address := Impl_From_U256_for_FixedBytes_32.from target_address in
  if negb (has_leading_zeros target_address 12) then
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.InvalidEXTCALLTarget in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    (None, interpreter)
  else
    (Some (Impl_Address.from_word target_address), interpreter)
  ).

Lemma pop_extcall_target_address_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f
      (run_pop_extcall_target_address run_InterpreterTypes_for_WIRE ref_interpreter)
      (interpreter :: stack)%stack 🌲
    let result := pop_extcall_target_address interpreter in
    (
      Output.Success (fst result),
      (snd result :: stack)%stack
    )
  }}.
Proof.
Admitted.

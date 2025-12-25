Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.ops.links.range.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Parameter get_memory_input_and_out_ranges :
  forall
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types},
  Interpreter.t WIRE WIRE_types ->
  option (Bytes.t * Range.t Usize.t) *
  Interpreter.t WIRE WIRE_types.

Lemma get_memory_input_and_out_ranges_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f (
      run_get_memory_input_and_out_ranges run_InterpreterTypes_for_WIRE ref_interpreter
    )
    (interpreter :: stack)%stack 🌲
    let result_interpreter := get_memory_input_and_out_ranges interpreter in
    (
      Output.Success (fst result_interpreter),
      (snd result_interpreter :: stack)%stack
    )
  }}.
Proof.
Admitted.
Global Opaque run_get_memory_input_and_out_ranges.

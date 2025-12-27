Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.ops.links.range.
Require Import revm.revm_context_interface.links.journaled_state.
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

Parameter calc_call_gas :
  forall
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types},
  Interpreter.t WIRE WIRE_types ->
  AccountLoad.t ->
  bool ->
  U64.t ->
  option U64.t * Interpreter.t WIRE WIRE_types.

Lemma calc_call_gas_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (account_load : AccountLoad.t)
    (has_transfer : bool)
    (local_gas_limit : U64.t)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f (
      run_calc_call_gas
        run_InterpreterTypes_for_WIRE
        ref_interpreter
        account_load
        has_transfer
        local_gas_limit
    )
    (interpreter :: stack)%stack 🌲
    let result_interpreter := calc_call_gas interpreter account_load has_transfer local_gas_limit in
    (
      Output.Success (fst result_interpreter),
      (snd result_interpreter :: stack)%stack
    )
  }}.
Proof.
Admitted.

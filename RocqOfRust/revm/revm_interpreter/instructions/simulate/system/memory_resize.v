Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.system.memory_resize.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Definition memory_resize
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (memory_offset : aliases.U256.t)
    (len : usize) :
    option usize * Interpreter.t WIRE WIRE_types :=
  let cost :=
    match calc.copy_cost_verylow len with
    | Some cost => cost
    | None => {| Integer.value := 0 |}
    end in
  gas_macro interpreter cost
    (fun interpreter => (None, interpreter))
    (fun interpreter =>
      if len =? 0 then
        (None, interpreter)
      else
        as_usize_or_fail_ret_macro interpreter memory_offset None
          (fun interpreter => (None, interpreter))
          (fun memory_offset interpreter =>
            resize_memory_macro interpreter memory_offset len
              (fun interpreter => (None, interpreter))
              (fun interpreter => (Some memory_offset, interpreter))
          )
    ).

Lemma memory_resize_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (memory_offset : aliases.U256.t)
    (len : usize) :
  let ref_interpreter := make_ref 0 in
  exists (result : option usize) (stack' : Stack.t),
    {{
      SimulateM.eval_f
        (run_memory_resize run_InterpreterTypes_for_WIRE ref_interpreter memory_offset len)
        [interpreter]%stack 🌲
      (
        Output.Success result,
        stack'
      )
    }}.
Admitted.

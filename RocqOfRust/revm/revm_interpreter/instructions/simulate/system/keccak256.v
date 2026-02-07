Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.system.keccak256.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import ruint.links.lib.

Definition keccak256
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter 1
    id
    (fun arr top interpreter =>
      let '{| ArrayPair.x := offset |} := arr.(array.value) in
      let len_word := top.(RefStub.projection) interpreter.(Interpreter.stack) in
      as_usize_or_fail_macro interpreter len_word None
        id
        (fun len interpreter =>
          let _from := as_usize_saturated_macro offset in
          let cost :=
            match calc.keccak256_cost len with
            | Some cost => cost
            | None => {| Integer.value := 0 |}
            end in
          gas_macro interpreter cost
            id
            (fun interpreter =>
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  {| Uint.value := 0 |} in
              interpreter <| Interpreter.stack := stack |>
            )
        )
    ).

Lemma keccak256_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  exists stack' : Stack.t,
    {{
      SimulateM.eval_f
        (run_keccak256 run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        stack'
      )
    }}.
Admitted.

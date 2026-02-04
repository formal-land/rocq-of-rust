Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.stack.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Definition pop
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.BASE id (fun interpreter =>
  popn_macro interpreter {| Integer.value := 1 |} id (fun _arr interpreter =>
    interpreter
  )).

Lemma pop_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_pop run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        pop interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition push0
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.SHANGHAI id (fun interpreter =>
  gas_macro interpreter constants.BASE id (fun interpreter =>
    let '(_, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.push)
        interpreter.(Interpreter.stack) Impl_Uint.ZERO in
    interpreter <| Interpreter.stack := stack |>
  )).

Lemma push0_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_push0 run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        push0 interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition cast_slice_to_u256 (imm : list u8) : aliases.U256.t :=
  {| Uint.value :=
    List.fold_left (fun (acc : Z) (byte : u8) => Z.add (Z.mul acc 256) byte.(Integer.value)) imm 0
  |}.

Definition push
    (N : usize)
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    let '(_, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.push)
        interpreter.(Interpreter.stack) Impl_Uint.ZERO in
    let interpreter := interpreter <| Interpreter.stack := stack |> in
    popn_top_macro interpreter {| Integer.value := 0 |} id (fun _arr top interpreter =>
      let slice :=
        IInterpreterTypes.(InterpreterTypes.Immediates_for_Bytecode).(Immediates.read_slice) N in
      let imm := slice.(RefStub.projection) interpreter.(Interpreter.bytecode) in
      let top_value := top.(RefStub.projection) interpreter.(Interpreter.stack) in
      let new_value := cast_slice_to_u256 imm in
      let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) new_value in
      let interpreter := interpreter <| Interpreter.stack := stack |> in
      let bytecode :=
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.relative_jump)
          interpreter.(Interpreter.bytecode) {| Integer.value := N.(Integer.value) |} in
      interpreter <| Interpreter.bytecode := bytecode |>
    )
  ).

Lemma push_eq
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_push N run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        push N interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition dup
    (N : usize)
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    let '(success, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.dup)
        interpreter.(Interpreter.stack) N in
    let interpreter := interpreter <| Interpreter.stack := stack |> in
    if success then
      interpreter
    else
      let control :=
        IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
          interpreter.(Interpreter.control)
          instruction_result.InstructionResult.StackOverflow in
      interpreter <| Interpreter.control := control |>
  ).

Lemma dup_eq
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_dup N run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        dup N interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition swap
    (N : usize)
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    let '(success, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.exchange)
        interpreter.(Interpreter.stack) {| Integer.value := 0 |} N in
    let interpreter := interpreter <| Interpreter.stack := stack |> in
    if success then
      interpreter
    else
      let control :=
        IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
          interpreter.(Interpreter.control)
          instruction_result.InstructionResult.StackOverflow in
      interpreter <| Interpreter.control := control |>
  ).

Lemma swap_eq
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_swap N run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        swap N interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition require_eof_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let is_eof :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_eof)
      interpreter.(Interpreter.runtime_flag) in
  if is_eof then
    k interpreter
  else
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.NotActivated in
    let interpreter := interpreter <| Interpreter.control := control |> in
    k_exit interpreter.

Definition dupn
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  require_eof_macro interpreter id (fun interpreter =>
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    let imm :=
      IInterpreterTypes.(InterpreterTypes.Immediates_for_Bytecode).(Immediates.read_u8)
        interpreter.(Interpreter.bytecode) in
    let n := {| Integer.value := imm.(Integer.value) + 1 |} in
    let '(success, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.dup)
        interpreter.(Interpreter.stack) n in
    let interpreter := interpreter <| Interpreter.stack := stack |> in
    let interpreter :=
      if success then
        interpreter
      else
        let control :=
          IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
            interpreter.(Interpreter.control)
            instruction_result.InstructionResult.StackOverflow in
        interpreter <| Interpreter.control := control |> in
    let bytecode :=
      IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.relative_jump)
        interpreter.(Interpreter.bytecode) {| Integer.value := 1 |} in
    interpreter <| Interpreter.bytecode := bytecode |>
  )).

Lemma dupn_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_dupn run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        dupn interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition swapn
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  require_eof_macro interpreter id (fun interpreter =>
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    let imm :=
      IInterpreterTypes.(InterpreterTypes.Immediates_for_Bytecode).(Immediates.read_u8)
        interpreter.(Interpreter.bytecode) in
    let n := {| Integer.value := imm.(Integer.value) + 1 |} in
    let '(success, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.exchange)
        interpreter.(Interpreter.stack) {| Integer.value := 0 |} n in
    let interpreter := interpreter <| Interpreter.stack := stack |> in
    let interpreter :=
      if success then
        interpreter
      else
        let control :=
          IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
            interpreter.(Interpreter.control)
            instruction_result.InstructionResult.StackOverflow in
        interpreter <| Interpreter.control := control |> in
    let bytecode :=
      IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.relative_jump)
        interpreter.(Interpreter.bytecode) {| Integer.value := 1 |} in
    interpreter <| Interpreter.bytecode := bytecode |>
  )).

Lemma swapn_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_swapn run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        swapn interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition exchange
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  require_eof_macro interpreter id (fun interpreter =>
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    let imm :=
      IInterpreterTypes.(InterpreterTypes.Immediates_for_Bytecode).(Immediates.read_u8)
        interpreter.(Interpreter.bytecode) in
    let n := {| Integer.value := Z.shiftr imm.(Integer.value) 4 + 1 |} in
    let m := {| Integer.value := Z.land imm.(Integer.value) 15 + 1 |} in
    let '(success, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.exchange)
        interpreter.(Interpreter.stack) n m in
    let interpreter := interpreter <| Interpreter.stack := stack |> in
    let interpreter :=
      if success then
        interpreter
      else
        let control :=
          IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
            interpreter.(Interpreter.control)
            instruction_result.InstructionResult.StackOverflow in
        interpreter <| Interpreter.control := control |> in
    let bytecode :=
      IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.relative_jump)
        interpreter.(Interpreter.bytecode) {| Integer.value := 1 |} in
    interpreter <| Interpreter.bytecode := bytecode |>
  )).

Lemma exchange_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_exchange run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        exchange interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

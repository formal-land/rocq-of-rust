Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.extcodecopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition extcodecopy
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter 4 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '⟬ address_u256; memory_offset_u256; code_offset_u256; len_u256 ⟭ := arr.(array.value) in
    let address := Impl_IntoAddress_for_U256.into_address address_u256 in
    let '(code_opt, host) := IHost.(Host.code) host address in
    match code_opt with
    | None =>
      let control :=
        IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
          interpreter.(Interpreter.control)
          instruction_result.InstructionResult.FatalExternalError in
      (interpreter <| Interpreter.control := control |>, host)
    | Some code =>
      as_usize_or_fail_ret_macro interpreter len_u256 None
        (fun interpreter => (interpreter, host))
        (fun len interpreter =>
          let '(code, load) := Impl_Eip7702CodeLoad.into_components code in
          let spec_id :=
            IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
              interpreter.(Interpreter.runtime_flag) in
          gas_or_fail_macro interpreter
            (calc.extcodecopy_cost spec_id len load)
            (fun interpreter => (interpreter, host))
            (fun interpreter =>
              if i[len] =? 0 then
                (interpreter, host)
              else
                as_usize_or_fail_ret_macro interpreter memory_offset_u256 None
                  (fun interpreter => (interpreter, host))
                  (fun memory_offset interpreter =>
                    let code_offset := as_usize_saturated_macro code_offset_u256 in
                    resize_memory_macro interpreter memory_offset len
                      (fun interpreter => (interpreter, host))
                      (fun interpreter =>
                        let memory :=
                          IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data)
                            interpreter.(Interpreter.memory)
                            memory_offset
                            code_offset
                            len
                            code.(Bytes.value).(bytes.Bytes.value) in
                        (interpreter <| Interpreter.memory := memory |>, host)
                      )
                  )
            )
        )
    end
  ).

Lemma extcodecopy_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    `{IHost : !Host.C H H_types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let result := extcodecopy interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodecopy run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.

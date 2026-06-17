Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.simulate.bytes.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.extcodesize.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition extcodesize
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0 (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
  let address :=
    Impl_IntoAddress_for_U256.into_address
      (top.(RefStub.projection) interpreter.(Interpreter.stack)) in
  let '(code_opt, host) := IHost.(Host.code) host address in
  match code_opt with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some code =>
    let '(code, load) := Impl_Eip7702CodeLoad.into_components code in
    let spec_id :=
      IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
        interpreter.(Interpreter.runtime_flag) in
    gas_macro interpreter
      (if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
        calc.warm_cold_cost_with_delegation load
      else if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
        700
      else
        20)
      (fun interpreter => (interpreter, host))
      (fun interpreter =>
  let size : aliases.U256.t := Impl_Uint.from (Impl_Bytes.len code.(Bytes.value)) in
  let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) size in
  (interpreter <| Interpreter.stack := stack |>, host))
  end).

Lemma extcodesize_eq
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
  let result := extcodesize interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodesize run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Opaque Impl_Eip7702CodeLoad.into_components.
  with_strategy transparent [run_extcodesize] unfold extcodesize, run_extcodesize; cbn.
  popn_top_macro_eq InterpreterTypesEq.
  s. {
    apply Impl_IntoAddress_for_U256.into_address_eq.
  }
  s. {
    apply HostEq.
  }
  destruct _.(Host.code) as [[code|] ?host]; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  s. {
    apply Impl_Eip7702CodeLoad.into_components_eq.
  }
  destruct Impl_Eip7702CodeLoad.into_components as [?code ?load]; cbn.
  unfold gas_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct Impl_SpecId.is_enabled_in; cbn.
  { gas_macro_eq ltac:(s; [apply calc.warm_cold_cost_with_delegation_eq |]).
    s. {
      apply simulate.mod.Impl_Deref_for_Bytes.Eq.I.
    }
    s. {
      s_apply Impl_Bytes.len_eq.
    }
    s. {
      s_apply Impl_Uint.from_eq.
    }
    s.
  }
  { s. {
      s_apply Impl_SpecId.is_enabled_in_eq.
    }
    destruct Impl_SpecId.is_enabled_in; cbn.
    { gas_macro_eq idtac.
      s. {
        apply simulate.mod.Impl_Deref_for_Bytes.Eq.I.
      }
      s. {
        s_apply Impl_Bytes.len_eq.
      }
      s. {
        s_apply Impl_Uint.from_eq.
      }
      s.
    }
    { gas_macro_eq idtac.
      s. {
        apply simulate.mod.Impl_Deref_for_Bytes.Eq.I.
      }
      s. {
        s_apply Impl_Bytes.len_eq.
      }
      s. {
        s_apply Impl_Uint.from_eq.
      }
      s.
    }
  }
Transparent Impl_Eip7702CodeLoad.into_components.
Qed.

Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.cfg.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.block_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition chainid
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.ISTANBUL (fun interpreter => (interpreter, host)) (fun interpreter =>
  gas_macro interpreter constants.BASE (fun interpreter => (interpreter, host)) (fun interpreter =>
  let cfg := IHost.(Host.CfgGetter_for_Self).(CfgGetter.cfg).(RefStub.projection) host in
  let chain_id := IHost.(Host.CfgGetter_for_Self).(CfgGetter.Cfg_for_Cfg).(Cfg.chain_id) cfg in
  push_macro interpreter
    {| Uint.value := i[chain_id] |}
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  (interpreter, host)
  ))).

Lemma chainid_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H H_types)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_chainid run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      ([interpreter; host]%stack) 🌲
    (
      Output.Success tt,
      let '(interpreter, host) := chainid interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_chainid] unfold chainid, run_chainid; cbn.
  check_macro_eq InterpreterTypesEq.
  gas_macro_eq idtac.
  s. {
    apply HostEq.
  }
  s. {
    s_apply HostEq.
  }
  s. {
    s_apply Impl_Uint.from_eq.
  }
  push_macro_eq InterpreterTypesEq.
  s.
Qed.

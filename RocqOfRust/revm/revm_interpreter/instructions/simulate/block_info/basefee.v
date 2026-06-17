Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.block_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition basefee
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.LONDON (fun interpreter => (interpreter, host)) (fun interpreter =>
  gas_macro interpreter constants.BASE (fun interpreter => (interpreter, host)) (fun interpreter =>
  let block :=
    IHost.(Host.BlockGetter_for_Self).(BlockGetter.block).(RefStub.projection) host in
  let basefee :=
    IHost.(Host.BlockGetter_for_Self).(BlockGetter.Block_for_Block).(Block.basefee) block in
  push_macro interpreter
    {| Uint.value := i[basefee] |}
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  (interpreter, host)
  ))).

Lemma basefee_eq
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
      (run_basefee run_InterpreterTypes_for_WIRE ref_interpreter run_Host_for_H ref_host)
      ([interpreter; host]%stack) 🌲
    (
      Output.Success tt,
      let '(interpreter, host) := basefee interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_basefee] unfold basefee, run_basefee; cbn.
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

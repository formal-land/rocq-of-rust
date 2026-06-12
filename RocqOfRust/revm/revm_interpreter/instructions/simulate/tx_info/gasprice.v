Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.tx_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition gasprice
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  gas_macro interpreter constants.BASE (fun interpreter => (interpreter, host)) (fun interpreter =>
  let block :=
    IHost.(Host.BlockGetter_for_Self).(BlockGetter.block).(RefStub.projection) host in
  let basefee :=
    IHost.(Host.BlockGetter_for_Self).(BlockGetter.Block_for_Block).(Block.basefee) block in
  let tx :=
    IHost.(Host.TransactionGetter_for_Self).(TransactionGetter.tx).(RefStub.projection) host in
  let price :=
    IHost.(Host.TransactionGetter_for_Self).(TransactionGetter.Transaction_for_Transaction)
      .(Transaction.effective_gas_price) tx (M.cast_integer IntegerKind.U128 basefee) in
  push_macro interpreter
    (Impl_Uint.from price)
    (fun interpreter => (interpreter, host))
    (fun interpreter => (interpreter, host))
  ).

Lemma gasprice_eq
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
  let result := gasprice interpreter host in
  {{
    SimulateM.eval_f
      (run_gasprice run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.

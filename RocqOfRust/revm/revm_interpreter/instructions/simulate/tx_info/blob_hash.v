Require Import simulate.RocqOfRust.
Require Import core.convert.simulate.mod.
Require Import core.links.cmp.
Require Import revm.revm_context_interface.transaction.links.transaction_type.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.tx_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.lib.

Definition blob_hash
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    `{Into.C
      H_types.(Host.Types.TransactionTypes).(Transaction.Types.TransactionType)
      TransactionType.t}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.CANCUN (fun interpreter => (interpreter, host)) (fun interpreter =>
  gas_macro interpreter constants.VERYLOW (fun interpreter => (interpreter, host)) (fun interpreter =>
  popn_top_macro interpreter 0 (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
    let index := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let _i := as_usize_saturated_macro index in
    let tx :=
      IHost.(Host.TransactionGetter_for_Self).(TransactionGetter.tx).(RefStub.projection) host in
    let tx_type :=
      Into.into
        (IHost.(Host.TransactionGetter_for_Self).(TransactionGetter.Transaction_for_Transaction)
          .(Transaction.tx_type) tx) in
    let value :=
      if PartialEq.eq tx_type TransactionType.Eip4844 then
        index
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) value in
    (
      interpreter <| Interpreter.stack := stack |>,
      host
    )
  ))).

Lemma blob_hash_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (IHost : Host.C H H_types)
    `{Into.C
      H_types.(Host.Types.TransactionTypes).(Transaction.Types.TransactionType)
      TransactionType.t}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  {{
    SimulateM.eval_f
      (run_blob_hash run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let '(interpreter, host) := blob_hash interpreter host in
      [interpreter; host]%stack
    )
  }}.
Admitted.

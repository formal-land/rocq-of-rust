Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.block_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Definition difficulty
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  gas_macro interpreter constants.BASE (fun interpreter => (interpreter, host)) (fun interpreter =>
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let block :=
    IHost.(Host.BlockGetter_for_Self).(BlockGetter.block).(RefStub.projection) host in
  let is_merge := Impl_SpecId.is_enabled_in spec_id SpecId.MERGE in
  let value :=
    if is_merge then
      match IHost.(Host.BlockGetter_for_Self).(BlockGetter.Block_for_Block).(Block.prevrandao) block with
      | Some prevrandao => Impl_IntoU256_for_B256.into_u256 prevrandao
      | None => Impl_Uint.ZERO
      end
    else
      IHost.(Host.BlockGetter_for_Self).(BlockGetter.Block_for_Block).(Block.difficulty) block
  in
  push_macro interpreter value (fun interpreter => (interpreter, host)) (fun interpreter =>
  (interpreter, host)
  )).

Lemma difficulty_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H H_types)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (prevrandao : FixedBytes.t 32)
    (H_prevrandao :
      IHost.(Host.BlockGetter_for_Self).(BlockGetter.Block_for_Block).(Block.prevrandao)
        (IHost.(Host.BlockGetter_for_Self).(BlockGetter.block).(RefStub.projection) host) =
      Some prevrandao
    ) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_difficulty run_Host_for_H run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; host]%stack) 🌲
    (
      Output.Success tt,
      let '(interpreter, host) := difficulty interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_difficulty] unfold difficulty, run_difficulty; cbn.
  gas_macro_eq idtac.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct Impl_SpecId.is_enabled_in; cbn.
  { s. {
      apply HostEq.
    }
    s. {
      s_apply HostEq.
    }
    s. {
      apply Impl_Option.unwrap_eq.
      exact H_prevrandao.
    }
    s. {
      apply Impl_IntoU256_for_B256.into_u256_eq.
    }
    rewrite H_prevrandao.
    push_macro_eq InterpreterTypesEq.
    s.
  }
  { s. {
      apply HostEq.
    }
    s. {
      s_apply HostEq.
    }
    push_macro_eq InterpreterTypesEq.
    s.
  }
Qed.

Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import core.convert.links.mod.
Require Import core.links.default.
Require Import core.links.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.block.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.instructions.block_info.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_context_interface.links.cfg.
Require Import ruint.links.from.

(*
pub fn chainid<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    check!(context.interpreter, ISTANBUL);
    //gas!(context.interpreter, gas::BASE);
    push!(context.interpreter, context.host.chain_id());
}
*)
Instance run_chainid
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.chainid [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply Impl_Interpreter.run_halt_not_activated. }
  { eapply (@Host.run_chain_id
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_chain_id H _ method_chain_id)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_chainid.

(*
pub fn coinbase<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    //gas!(context.interpreter, gas::BASE);
    push!(
        context.interpreter,
        context.host.beneficiary().into_word().into()
    );
}
*)
Instance run_coinbase
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.coinbase [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  (* NOTE: used for resolving dependency issue for `core::convert::Into::into` *)
  destruct (Impl_Into_for_From_T.run Impl_From_FixedBytes_32_for_U256.run).
  run_symbolic.
  { eapply (@Host.run_beneficiary
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_beneficiary H _ method_beneficiary)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_coinbase.

(*
pub fn timestamp<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    //gas!(context.interpreter, gas::BASE);
    push!(context.interpreter, context.host.timestamp());
}
*)
Instance run_timestamp
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.timestamp [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply (@Host.run_timestamp
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_timestamp H _ method_timestamp)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_timestamp.

(*
pub fn block_number<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    //gas!(context.interpreter, gas::BASE);
    push!(context.interpreter, context.host.block_number());
}
*)
Instance run_block_number
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.block_number [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply (@Host.run_block_number
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_block_number H _ method_block_number)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_block_number.

(*
pub fn difficulty<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    //gas!(context.interpreter, gas::BASE);
    if context
        .interpreter
        .runtime_flag
        .spec_id()
        .is_enabled_in(MERGE)
    {
        // Unwrap is safe as this fields is checked in validation handler.
        push!(context.interpreter, context.host.prevrandao().unwrap());
    } else {
        push!(context.interpreter, context.host.difficulty());
    }
}
*)
Instance run_difficulty
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.difficulty [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply (@Host.run_prevrandao
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_prevrandao H _ method_prevrandao)
      (Ref.cast_to Pointer.Kind.Ref sub_ref3)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
  { eapply (@Host.run_difficulty
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_difficulty H _ method_difficulty)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_difficulty.

(*
pub fn gaslimit<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    //gas!(context.interpreter, gas::BASE);
    push!(context.interpreter, context.host.gas_limit());
}
*)
Instance run_gaslimit
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.gaslimit [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply (@Host.run_gas_limit
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_gas_limit H _ method_gas_limit)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_gaslimit.

(*
pub fn basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    check!(context.interpreter, LONDON);
    //gas!(context.interpreter, gas::BASE);
    push!(context.interpreter, context.host.basefee());
}
*)
Instance run_basefee
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.basefee [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply Impl_Interpreter.run_halt_not_activated. }
  { eapply (@Host.run_basefee
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_basefee H _ method_basefee)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_basefee.

(*
pub fn blob_basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    check!(context.interpreter, CANCUN);
    //gas!(context.interpreter, gas::BASE);
    push!(context.interpreter, context.host.blob_gasprice());
}
*)
Instance run_blob_basefee
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.block_info.blob_basefee [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  run_symbolic.
  { eapply Impl_Interpreter.run_halt_not_activated. }
  { eapply (@Host.run_blob_gasprice
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_blob_gasprice H _ method_blob_gasprice)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  { eapply Impl_Interpreter.run_halt_overflow. }
Defined.
Global Opaque run_blob_basefee.

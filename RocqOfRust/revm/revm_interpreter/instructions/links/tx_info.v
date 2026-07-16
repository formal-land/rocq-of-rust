Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.default.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.slice.links.index.
Require Import core.slice.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.transaction.
Require Import revm.revm_context_interface.transaction.links.transaction_type.
Require Import revm.revm_interpreter.instructions.tx_info.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Module Impl_Default_for_U256.
  Definition Self : Set := aliases.U256.t.

  Instance run_default :
    Run.Trait
      (ruint.lib.Impl_core_default_Default_for_ruint_Uint_BITS_LIMBS.default
        (Value.Integer IntegerKind.Usize 256)
        (Value.Integer IntegerKind.Usize 4))
      [] [] []
      Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  Instance method_default : Default.Method_default Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply ruint.lib.Impl_core_default_Default_for_ruint_Uint_BITS_LIMBS.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Default.Run Self := {}.
End Impl_Default_for_U256.
Export (hints) Impl_Default_for_U256.

(*
pub fn gasprice<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
)
*)
Instance run_gasprice
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.tx_info.gasprice [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  destruct run_TransactionGetter_for_Self.
  destruct run_Transaction_for_Transaction.
  run_symbolic.
  { eapply (@Host.run_effective_gas_price
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_effective_gas_price H _ method_effective_gas_price)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  Unshelve.
  all: try typeclasses eauto.
Defined.
Global Opaque run_gasprice.

(*
pub fn origin<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
)
*)
Instance run_origin
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.tx_info.origin [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  destruct run_TransactionGetter_for_Self.
  destruct run_Transaction_for_Transaction.
  run_symbolic.
  { eapply (@Host.run_caller
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_caller H _ method_caller)
      (Ref.cast_to Pointer.Kind.Ref sub_ref1)). }
  Unshelve.
  all: eapply Impl_Address.run_into_word.
Defined.
Global Opaque run_origin.

(*
pub fn blob_hash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
)
*)
Instance run_blob_hash
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.tx_info.blob_hash [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  destruct run_TransactionGetter_for_Self.
  destruct run_Transaction_for_Transaction.
  destruct Impl_TryFrom_u64_for_usize.run.
  run_symbolic.
  { eapply (@Host.run_blob_hash
      ('&mut H)
      _
      (@Impl_Host_for_RefMut.method_blob_hash H _ method_blob_hash)). }
  Unshelve.
  all: eapply Impl_Option.run_unwrap_or_default.
  Unshelve.
  all: typeclasses eauto.
Defined.
Global Opaque run_blob_hash.

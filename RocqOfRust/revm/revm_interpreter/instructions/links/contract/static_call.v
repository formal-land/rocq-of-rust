Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.links.boxed.
Require Import alloc.links.slice.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.utils.links.mod.
Require Import bytes.links.bytes.
Require Import core.convert.links.mod.
Require Import core.fmt.links.mod.
Require Import core.links.borrow.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.ops.links.control_flow.
Require Import core.ops.links.range.
Require Import core.slice.links.iter.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.instructions.contract.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.bytes.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn static_call<WIRE: InterpreterTypes, H: Host + ?Sized>(
    mut context: InstructionContext<'_, H, WIRE>,
)
*)
Instance run_static_call
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.contract.static_call [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct (TryFrom_Uint_for_u64.method_try_from (BITS := {| Integer.value := 256 |}) (LIMBS := {| Integer.value := 4 |})).
  run_symbolic.
  { eapply Impl_Interpreter.run_halt_not_activated. }
  {
    eapply (@Impl_Box.run_new CallInputs.t CallInputs.IsLink {|
      CallInputs.bytecode_address := value15;
      CallInputs.caller := value_inter2;
      CallInputs.gas_limit := value12;
      CallInputs.input := CallInput.SharedBuffer value11;
      CallInputs.is_static := true;
      CallInputs.known_bytecode := Some (value16, value17);
      CallInputs.return_memory_offset := value19;
      CallInputs.scheme := CallScheme.StaticCall;
      CallInputs.target_address := value13;
      CallInputs.value := CallValue.Transfer value18;
    |}).
  }
  { eapply Impl_Interpreter.run_halt_underflow. }
Defined.
Global Opaque run_static_call.

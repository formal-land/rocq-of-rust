Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.instructions.links.system.common.

Instance run_address
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    instructions.system.address [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct (Impl_Into_for_From_T.run Impl_From_FixedBytes_32_for_U256.run).
  run_symbolic.
Defined.
Global Opaque run_address.

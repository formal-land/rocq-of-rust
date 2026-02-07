Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.instructions.links.system.common.

Instance run_codecopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    instructions.system.codecopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_MemoryTrait_for_Memory.
  destruct run_LegacyBytecode_for_Bytecode.
  destruct Impl_TryFrom_u64_for_usize.run.
  run_symbolic.
Defined.
Global Opaque run_codecopy.

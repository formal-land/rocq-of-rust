Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.instructions.links.system.common.

Instance run_memory_resize
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types}
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (memory_offset : aliases.U256.t)
  (len : usize) :
  Run.Trait
    instructions.system.memory_resize [] [ Φ WIRE ] [ φ interpreter; φ memory_offset; φ len ]
    (option usize).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_MemoryTrait_for_Memory.
  run_symbolic.
Defined.
Global Opaque run_memory_resize.

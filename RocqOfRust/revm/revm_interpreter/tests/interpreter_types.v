(** Compatibility exports for existing instruction tests. *)
Require Export revm.revm_interpreter.simulate.eth_types.

Module Stack := eth_types.Stack.

Module Memory := eth_types.Memory.

Module MemorySlice := eth_types.MemorySlice.

Module Bytecode := eth_types.Bytecode.

Module Control := eth_types.Control.

Module Input := eth_types.Input.

Module Immediates := eth_types.Immediates.

Module LegacyBytecode := eth_types.LegacyBytecode.

Module Jumps := eth_types.Jumps.

Module EofData := eth_types.EofData.

Module EofContainer := eth_types.EofContainer.

Module InputTraits := eth_types.InputTraits.

Module StackTrait := eth_types.StackTrait.

Module LoopControl := eth_types.LoopControl.

Module RuntimeFlag := eth_types.RuntimeFlag.

Module MemoryTrait := eth_types.MemoryTrait.

Module SubRoutineStack := eth_types.SubRoutineStack.

Module ReturnData := eth_types.ReturnData.

Module InterpreterTypes := eth_types.InterpreterTypes.

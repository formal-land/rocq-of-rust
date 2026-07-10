Require Import links.RocqOfRust.
Require Import revm_interpreter.interpreter.links.shared_memory.
Require Import revm_interpreter.interpreter.links.stack.
Require Import revm_interpreter.links.gas.
Require Import revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.interpreter_action.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.interpreter.

(*
pub struct Interpreter<WIRE: InterpreterTypes> {
    pub bytecode: WIRE::Bytecode,
    pub gas: Gas,
    pub stack: WIRE::Stack,
    pub return_data: WIRE::ReturnData,
    pub memory: WIRE::Memory,
    pub input: WIRE::Input,
    pub sub_routine: WIRE::SubRoutineStack,
    pub control: WIRE::Control,
    pub runtime_flag: WIRE::RuntimeFlag,
    pub extend: WIRE::Extend,
}
*)
Module Interpreter.
  RocqOfRustLinkInterpreterTypesRecordNoValueArgs
    "revm_interpreter::interpreter::Interpreter" [ WIRE ] WIRE_types := {
    bytecode : WIRE_types.(InterpreterTypes.Types.Bytecode);
    gas : Gas.t;
    stack : WIRE_types.(InterpreterTypes.Types.Stack);
    return_data : WIRE_types.(InterpreterTypes.Types.ReturnData);
    memory : WIRE_types.(InterpreterTypes.Types.Memory);
    input : WIRE_types.(InterpreterTypes.Types.Input);
    sub_routine : WIRE_types.(InterpreterTypes.Types.SubRoutineStack);
    control : WIRE_types.(InterpreterTypes.Types.Control);
    runtime_flag : WIRE_types.(InterpreterTypes.Types.RuntimeFlag);
    extend : WIRE_types.(InterpreterTypes.Types.Extend)
  }.
End Interpreter.

#[export] Existing Instance Interpreter.IsLink.

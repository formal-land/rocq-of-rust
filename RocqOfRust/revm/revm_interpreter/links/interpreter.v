Require Import links.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.array.
Require Import revm_interpreter.interpreter.links.shared_memory.
Require Import revm_interpreter.interpreter.links.stack.
Require Import revm_interpreter.links.gas.
Require Import revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.interpreter_action.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.links.table.
Require Import revm_interpreter.interpreter.

Require Export revm.revm_interpreter.links.interpreter_Interpreter.
Require Export revm.revm_interpreter.links.interpreter_InterpreterResult.

(* impl<IW: InterpreterTypes> Interpreter<IW> { *)
Module Impl_Interpreter.
  Definition Self
    (IW : Set) `{Link IW}
    {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
    (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types) :
    Set :=
    Interpreter.t IW IW_types.

  (*
  pub(crate) fn step<FN, H: Host>(&mut self, instruction_table: &[FN; 256], host: &mut H)
  where
      FN: CustomInstruction<Wire = IW, Host = H>,
  *)
  Instance run_step
      (IW H FN : Set) `{Link IW} `{Link H} `{Link FN}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      {run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H}
      (self : '&mut (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : '& (array.t FN {| Integer.value := 256 |}))
      (host : '&mut H) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.step (Φ IW))
        []
        [ Φ FN; Φ H ]
        [ φ self; φ instruction_table; φ host ]
      unit.
  Proof.
    constructor.
    destruct run_CustomInstruction_for_FN.
    run_symbolic.
  Defined.
  Global Opaque run_step.

   (* pub fn halt(&mut self, result: InstructionResult) *)
  Instance run_halt
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      (self : '&mut (Self IW run_InterpreterTypes_for_IW))
      (result : InstructionResult.t) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.halt (Φ IW))
      [] [] [φ self; φ result]
      unit.
  Proof.
    constructor.
    destruct run_InterpreterTypes_for_IW.
    destruct run_LoopControl_for_Bytecode.
    run_symbolic.
  Defined.
  Global Opaque run_halt.

  (* pub fn halt_underflow(&mut self) *)
  Instance run_halt_underflow
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      (self : '&mut (Self IW run_InterpreterTypes_for_IW)) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.halt_underflow (Φ IW))
      [] [] [φ self]
      unit.
    Proof.
    constructor.
    run_symbolic.
    eapply (@run_halt IW H IW_types H0 run_InterpreterTypes_for_IW).
  Defined.

  Global Opaque run_halt_underflow.

  (* pub fn halt_overflow(&mut self) *)
  Instance run_halt_overflow
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      (self : '&mut (Self IW run_InterpreterTypes_for_IW)) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.halt_overflow (Φ IW))
      [] [] [φ self]
      unit.
  Proof.
    constructor.
    run_symbolic.
    eapply (@run_halt IW H IW_types H0 run_InterpreterTypes_for_IW).
  Defined.
  Global Opaque run_halt_overflow.

  (* pub fn halt_memory_oog(&mut self) *)
  Instance run_halt_memory_oog
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      (self : '&mut (Self IW run_InterpreterTypes_for_IW)) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.halt_memory_oog (Φ IW))
      [] [] [φ self]
      unit.
  Proof.
    constructor.
    run_symbolic.
    eapply (@run_halt IW H IW_types H0 run_InterpreterTypes_for_IW).
  Defined.
  Global Opaque run_halt_memory_oog.

  (* (*
  pub fn run<FN, H: Host>(
      &mut self,
      instruction_table: &[FN; 256],
      host: &mut H,
  ) -> InterpreterAction
  where
      FN: CustomInstruction<Wire = IW, Host = H>,
  *)
  Instance run_run
      (IW H FN : Set) `{Link IW} `{Link H} `{Link FN}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      {run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H}
      (self : '&mut (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : '& (array.t FN {| Integer.value := 256 |}))
      (host : '&mut H) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.run (Φ IW))
        []
        [ Φ FN; Φ H ]
        [ φ self; φ instruction_table; φ host ]
      InterpreterAction.t.
  Proof.
    constructor.
    destruct run_InterpreterTypes_for_IW eqn:?.
    destruct run_LoopControl_for_Control.
    run_symbolic.
    (* now eapply run_step.
  Defined. *)
  Admitted.
  Global Opaque run_run. *)
End Impl_Interpreter.
Export (hints) Impl_Interpreter.

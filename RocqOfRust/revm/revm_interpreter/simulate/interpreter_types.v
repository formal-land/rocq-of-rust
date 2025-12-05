Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_specification.links.hardfork.

Module Stack.
  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Type := {
    (* fn popn_top<const POPN: usize>(&mut self) -> Option<([U256; POPN], &mut U256)>; *)
    popn_top :
      forall
        (POPN : Usize.t)
        (self : WIRE_types.(InterpreterTypes.Types.Stack)),
      option (
        array.t aliases.U256.t POPN *
        RefStub.t WIRE_types.(InterpreterTypes.Types.Stack) aliases.U256.t
      ) *
      WIRE_types.(InterpreterTypes.Types.Stack);
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      popn_top
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.t)
          (POPN : Usize.t) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_StackTrait_for_Stack).(StackTrait.popn_top).(TraitMethod.run)
              POPN
              ref_self
            )
            (interpreter :: stack_rest)%stack 🌲
          let (result, self) := I.(popn_top) POPN interpreter.(Interpreter.stack) in
          let result :=
            match result with
            | Some (a, stub) => Some (a, RefStub.apply ref_self stub)
            | None => None
            end in
          (
            Output.Success result,
            (interpreter <| Interpreter.stack := self |> :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End Stack.

Module Loop.
 Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Set := {
    (* fn set_instruction_result(&mut self, result: InstructionResult); *)
    set_instruction_result :
      forall
        (self : WIRE_types.(InterpreterTypes.Types.Control))
        (result : InstructionResult.t),
      WIRE_types.(InterpreterTypes.Types.Control);
    (* fn gas(&mut self) -> &mut Gas; *)
    gas : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      set_instruction_result
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.t)
          (result : InstructionResult.t) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_interpreter.(Ref.core)
              Interpreter.SubPointer.get_control
        |} in
        let control' :=
          I.(set_instruction_result) interpreter.(Interpreter.control) result in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_LoopControl_for_Control).(LoopControl.set_instruction_result).(TraitMethod.run)
              ref_self
              result
            )
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.control := control' |> :: stack_rest)%stack
          )
        }};
      gas
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.t) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_interpreter.(Ref.core)
              Interpreter.SubPointer.get_control
        |} in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_LoopControl_for_Control).(LoopControl.gas).(TraitMethod.run)
              ref_self
            )
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(gas)),
            (interpreter :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End Loop.

Module SRuntimeFlag.
  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Set := {
    is_static : forall (self : WIRE_types.(InterpreterTypes.Types.RuntimeFlag)), bool;
    is_eof : forall (self : WIRE_types.(InterpreterTypes.Types.RuntimeFlag)), bool;
    is_eof_init : forall (self : WIRE_types.(InterpreterTypes.Types.RuntimeFlag)), bool;
    spec_id : forall (self : WIRE_types.(InterpreterTypes.Types.RuntimeFlag)), SpecId.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      is_static
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.t) :
        let ref_core_interpreter := make_ref_core 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_core_interpreter
              Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_static).(TraitMethod.run)
              ref_self
            )
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(is_static) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
      is_eof
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_core_interpreter := make_ref_core 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_core_interpreter
              Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_eof).(TraitMethod.run)
              ref_self
            )
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(is_eof) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
      is_eof_init
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_core_interpreter := make_ref_core 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_core_interpreter
              Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_eof_init).(TraitMethod.run)
              ref_self
            )
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(is_eof_init) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
      spec_id
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_core_interpreter := make_ref_core 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_core_interpreter
              Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id).(TraitMethod.run)
              ref_self
            )
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(spec_id) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End SRuntimeFlag.

Module InterpreterTypes.
  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Type := {
    Stack : Stack.C WIRE_types;
    Loop : Loop.C WIRE_types;
    RuntimeFlag : SRuntimeFlag.C WIRE_types;
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      Stack : Stack.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE I.(Stack);
      Loop : Loop.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE I.(Loop);
      RuntimeFlag : SRuntimeFlag.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE I.(RuntimeFlag);
    }.
  End Eq.
End InterpreterTypes.

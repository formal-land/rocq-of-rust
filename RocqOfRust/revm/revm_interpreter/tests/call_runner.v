From Stdlib Require Import List ZArith.

Require Import alloc.links.boxed.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.simulate.step.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module CallRunner.
  Definition supported_opcode (opcode : Z) : bool :=
    ((0 <=? opcode) && (opcode <=? 11)) ||
    ((16 <=? opcode) && (opcode <=? 30)) ||
    ((95 <=? opcode) && (opcode <=? 159)) ||
    List.existsb (Z.eqb opcode)
      [48; 49; 51; 52; 53; 54; 55; 57; 59; 60; 61; 62; 63;
       65; 66; 67; 68; 69; 70; 71; 72; 74;
       80; 81; 82; 83; 84; 85; 86; 87; 89; 90; 91; 92; 93;
       241; 242; 243; 244; 250; 253].

  Definition table := FragmentInstructionTable.table
    (H := StatefulHost.t) (H_types := StatefulHost.host_types)
    (run_host := run_Host_for_StatefulHost) run_InterpreterTypes_for_WIRE.

  (** Fuel bounds all instructions and frame transitions together. Unsupported
      precompiles, call schemes and missing instructions remain incomplete. *)
  Fixpoint execute (fuel : nat) (checkpoint : StatefulHost.t)
      (parents : list CallFrame.Pending.t) (state : CallFrame.state) :
      option (InterpreterAction.t * CallFrame.state) :=
    match fuel with
    | O => None
    | S fuel =>
      let interpreter := InstructionContext.State.interpreter _ _ _ state in
      let host := InstructionContext.State.host _ _ _ state in
      let action := match interpreter.(Interpreter.bytecode).(Bytecode.action) with
        | Some action => Some action
        | None => if bytecode_is_not_end interpreter.(Interpreter.bytecode)
          then None else Some (InterpreterAction.Return
            (CallFrame.result InstructionResult.Stop interpreter))
        end in
      match action with
      | None =>
          let opcode := List.nth
            (Z.to_nat interpreter.(Interpreter.bytecode).(Bytecode.pc).(Integer.value))
            interpreter.(Interpreter.bytecode).(Bytecode.code) (0 : u8) in
          if negb (supported_opcode opcode.(Integer.value)) then None else
          match InterpreterDispatch.step_result_stateful InterpreterTypes.I table state with
          | InterpreterStep.Result.MissingInstruction => None
          | InterpreterStep.Result.OutOfGas state
          | InterpreterStep.Result.Success state => execute fuel checkpoint parents state
          end
      | Some (InterpreterAction.Return output) =>
          match output.(InterpreterResult.result) with
          | InstructionResult.FatalExternalError => None
          | _ =>
            let host := if StatefulFrame.successful output.(InterpreterResult.result)
              then host else checkpoint in
            match parents with
            | [] => Some (InterpreterAction.Return output,
                {| InstructionContext.State.interpreter := interpreter;
                   InstructionContext.State.host := host |})
            | parent :: parents =>
                execute fuel parent.(CallFrame.Pending.checkpoint) parents
                  {| InstructionContext.State.interpreter :=
                       CallFrame.resume parent.(CallFrame.Pending.parent)
                         parent.(CallFrame.Pending.output_range) output;
                     InstructionContext.State.host := host |}
            end
          end
      | Some (InterpreterAction.NewFrame (FrameInput.Call boxed)) =>
          let inputs := boxed.(Box.value) in
          let address := inputs.(CallInputs.bytecode_address).(Address.value) in
          let max_precompile := if Impl_SpecId.is_enabled_in
            interpreter.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) SpecId.PRAGUE then 17 else 10 in
          if (1 <=? address) && (address <=? max_precompile) then None else
          let supported := match inputs.(CallInputs.scheme), inputs.(CallInputs.value) with
            | CallScheme.Call, CallValue.Transfer _
            | CallScheme.CallCode, CallValue.Transfer _
            | CallScheme.DelegateCall, CallValue.Apparent _ => true
            | CallScheme.StaticCall, CallValue.Transfer value =>
                inputs.(CallInputs.is_static) && Z.eqb value.(Uint.value) 0
            | _, _ => false
            end in
          if negb supported then None else
          match inputs.(CallInputs.known_bytecode) with
          | Some (_, code) =>
              let child := CallFrame.child interpreter inputs
                code.(revm.revm_bytecode.links.bytecode.Bytecode.original_bytes)
                  .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
              let '(error, next_host) :=
                if Nat.ltb 1024 (S (List.length parents)) then
                  (Some InstructionResult.CallTooDeep, host)
                else match inputs.(CallInputs.value) with
                  | CallValue.Transfer value =>
                      CallFrame.transfer host inputs.(CallInputs.caller).(Address.value)
                        inputs.(CallInputs.target_address).(Address.value) value.(Uint.value)
                  | CallValue.Apparent _ => (None, host)
                  end in
              match error with
              | Some error =>
                  execute fuel checkpoint parents
                    {| InstructionContext.State.interpreter := CallFrame.resume interpreter
                         inputs.(CallInputs.return_memory_offset) (CallFrame.result error child);
                       InstructionContext.State.host := host |}
              | None =>
                  execute fuel host
                    ({| CallFrame.Pending.parent := interpreter;
                        CallFrame.Pending.output_range := inputs.(CallInputs.return_memory_offset);
                        CallFrame.Pending.checkpoint := checkpoint |} :: parents)
                    {| InstructionContext.State.interpreter := child;
                       InstructionContext.State.host := next_host |}
              end
          | None => None
          end
      | Some _ => None
      end
    end.

  Definition run (fuel : nat) (state : CallFrame.state) :=
    match (InstructionContext.State.interpreter _ _ _ state)
      .(Interpreter.runtime_flag).(RuntimeFlags.spec_id) with
    | SpecId.CANCUN | SpecId.PRAGUE =>
        execute fuel (InstructionContext.State.host _ _ _ state) [] state
    | _ => None
    end.
End CallRunner.

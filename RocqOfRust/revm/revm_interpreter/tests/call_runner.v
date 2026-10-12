From Stdlib Require Import Lia List ZArith.

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
Require Import revm.revm_interpreter.tests.create_frame.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.precompile_frame.
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
      [32; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63;
       64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74;
       80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94;
       160; 161; 162; 163; 164; 240; 241; 242; 243; 244; 245; 250; 253; 254; 255].

  (** Unassigned legacy bytes in revm_bytecode/opcode.rs. They execute the
      table's zero-gas unknown handler rather than an incomplete instruction. *)
  Definition undefined_legacy_opcode (opcode : Z) : bool :=
    ((12 <=? opcode) && (opcode <=? 15)) || (opcode =? 31) ||
    ((33 <=? opcode) && (opcode <=? 47)) ||
    ((75 <=? opcode) && (opcode <=? 79)) ||
    ((165 <=? opcode) && (opcode <=? 239)) ||
    ((246 <=? opcode) && (opcode <=? 249)) ||
    ((251 <=? opcode) && (opcode <=? 252)).

  Definition table := FragmentInstructionTable.table
    (H := StatefulHost.t) (H_types := StatefulHost.host_types)
    (run_host := run_Host_for_StatefulHost) run_InterpreterTypes_for_WIRE.

  (** Looking up the current byte once avoids traversing the entire bytecode
      on every step just to decide whether execution has reached its end.
      The negative-pc branch preserves the old [Z.to_nat] behavior. *)
  Definition opcode_at_pc (bytecode : Bytecode.t) : option u8 :=
    let pc := bytecode.(Bytecode.pc).(Integer.value) in
    if pc <? 0 then
      Some (List.nth 0 bytecode.(Bytecode.code) (0 : u8))
    else List.nth_error bytecode.(Bytecode.code) (Z.to_nat pc).

  Lemma opcode_at_pc_eq (bytecode : Bytecode.t) :
    opcode_at_pc bytecode =
    if bytecode_is_not_end bytecode then
      Some (List.nth
        (Z.to_nat bytecode.(Bytecode.pc).(Integer.value))
        bytecode.(Bytecode.code) (0 : u8))
    else None.
  Proof.
    unfold opcode_at_pc, bytecode_is_not_end.
    set (pc := bytecode.(Bytecode.pc).(Integer.value)).
    set (code := bytecode.(Bytecode.code)).
    destruct (pc <? 0) eqn:H_negative.
    - apply Z.ltb_lt in H_negative.
      assert (H_pc : Z.to_nat pc = O) by lia.
      assert (H_end : pc <? Z.of_nat (List.length code) = true) by
        (apply Z.ltb_lt; lia).
      rewrite H_pc, H_end.
      reflexivity.
    - apply Z.ltb_ge in H_negative.
      destruct (List.nth_error code (Z.to_nat pc)) eqn:H_opcode.
      + assert (H_present : (Z.to_nat pc < List.length code)%nat).
        { apply (proj1 (List.nth_error_Some code (Z.to_nat pc))).
          congruence. }
        assert (H_end : pc <? Z.of_nat (List.length code) = true) by
          (apply Z.ltb_lt; lia).
        rewrite H_end.
        now rewrite (List.nth_error_nth code (Z.to_nat pc) (0 : u8) H_opcode).
      + assert (H_absent : (List.length code <= Z.to_nat pc)%nat).
        { apply (proj1 (List.nth_error_None code (Z.to_nat pc))).
          exact H_opcode. }
        assert (H_end : pc <? Z.of_nat (List.length code) = false) by
          (apply Z.ltb_ge; lia).
        now rewrite H_end.
  Qed.

  Module Pending.
    Inductive t : Set :=
    | Call (frame : CallFrame.Pending.t)
    | Create (parent : CallFrame.machine) (address : Z) (checkpoint : StatefulHost.t).
  End Pending.

  (** Fuel bounds all instructions and frame transitions together. Unsupported
      precompiles, call schemes and missing instructions remain incomplete. *)
  Fixpoint execute_with_step
      (step : CallFrame.state -> InterpreterStep.Result.t StatefulHost.t WIRE WIRE_types)
      (finalize : bool) (fuel : nat) (checkpoint : StatefulHost.t)
      (parents : list Pending.t) (state : CallFrame.state) :
      option (InterpreterAction.t * CallFrame.state) :=
    match fuel with
    | O => None
    | S fuel =>
      let interpreter := InstructionContext.State.interpreter _ _ _ state in
      let host := InstructionContext.State.host _ _ _ state in
      let opcode := opcode_at_pc interpreter.(Interpreter.bytecode) in
      let action := match interpreter.(Interpreter.bytecode).(Bytecode.action) with
        | Some action => Some action
        | None => match opcode with
          | Some _ => None
          | None => Some (InterpreterAction.Return
              (CallFrame.result InstructionResult.Stop interpreter))
          end
        end in
      match action with
      | None =>
          match opcode with
          | None => None
          | Some opcode =>
            if negb (supported_opcode opcode.(Integer.value) ||
              undefined_legacy_opcode opcode.(Integer.value)) then None else
            match step state with
            | InterpreterStep.Result.MissingInstruction => None
            | InterpreterStep.Result.OutOfGas state
            | InterpreterStep.Result.Success state => execute_with_step step finalize fuel checkpoint parents state
            end
          end
      | Some (InterpreterAction.Return output) =>
          match output.(InterpreterResult.result) with
          | InstructionResult.FatalExternalError => None
          | _ =>
            let host := if StatefulFrame.successful output.(InterpreterResult.result)
              then host else StatefulHost.rollback checkpoint host in
            match parents with
            | [] => Some (InterpreterAction.Return output,
                {| InstructionContext.State.interpreter := interpreter;
                   InstructionContext.State.host :=
                     if finalize && StatefulFrame.successful output.(InterpreterResult.result)
                     then StatefulHost.finalize_selfdestructs host else host |})
            | Pending.Call parent :: parents =>
                execute_with_step step finalize fuel parent.(CallFrame.Pending.checkpoint) parents
                  {| InstructionContext.State.interpreter :=
                       CallFrame.resume parent.(CallFrame.Pending.parent)
                         parent.(CallFrame.Pending.output_range) output;
                     InstructionContext.State.host := host |}
            | Pending.Create parent address parent_checkpoint :: parents =>
                let '(output, host) := CreateFrame.finish address checkpoint host output in
                execute_with_step step finalize fuel parent_checkpoint parents
                  {| InstructionContext.State.interpreter :=
                       CreateFrame.resume parent (Some address) output;
                     InstructionContext.State.host := host |}
            end
          end
      | Some (InterpreterAction.NewFrame (FrameInput.Call boxed)) =>
          let inputs := boxed.(Box.value) in
          let address := inputs.(CallInputs.bytecode_address).(Address.value) in
          if PrecompileFrame.is_precompile
            interpreter.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address &&
            negb (PrecompileFrame.supported address)
          then None else
          let supported := match inputs.(CallInputs.scheme), inputs.(CallInputs.value) with
            | CallScheme.Call, CallValue.Transfer _
            | CallScheme.CallCode, CallValue.Transfer _
            | CallScheme.DelegateCall, CallValue.Apparent _ => true
            | CallScheme.StaticCall, CallValue.Transfer value =>
                inputs.(CallInputs.is_static) && Z.eqb value.(Uint.value) 0
            | _, _ => false
            end in
          if negb supported then None else
          let code := if PrecompileFrame.enabled
            interpreter.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address
            then Some [] else
            match inputs.(CallInputs.known_bytecode) with
            | Some (_, code) => Some
                code.(revm.revm_bytecode.links.bytecode.Bytecode.original_bytes)
                  .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)
            | None => None
            end in
          match code with
          | Some code =>
              let child := CallFrame.child interpreter inputs code in
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
              | Some InstructionResult.OverflowPayment =>
                  (* Native transfer_loaded leaves an unjournaled source debit
                     on overflow; snapshot rollback cannot model that edge. *)
                  None
              | Some error =>
                  execute_with_step step finalize fuel checkpoint parents
                    {| InstructionContext.State.interpreter := CallFrame.resume interpreter
                         inputs.(CallInputs.return_memory_offset) (CallFrame.result error child);
                       InstructionContext.State.host := StatefulHost.rollback host next_host |}
              | None =>
                  let precompile := PrecompileFrame.run address child in
                  if PrecompileFrame.is_precompile
                    interpreter.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address &&
                    (match precompile with None => true | Some _ => false end)
                  then None else
                  let child := match precompile with
                    | Some output => child
                        <| @Interpreter.bytecode WIRE _ WIRE_types _ :=
                          child.(Interpreter.bytecode) <| Bytecode.action :=
                            Some (InterpreterAction.Return output) |> |>
                    | None => child
                    end in
                  execute_with_step step finalize fuel host
                    (Pending.Call {| CallFrame.Pending.parent := interpreter;
                        CallFrame.Pending.output_range := inputs.(CallInputs.return_memory_offset);
                        CallFrame.Pending.checkpoint := checkpoint |} :: parents)
                    {| InstructionContext.State.interpreter := child;
                       InstructionContext.State.host := next_host |}
              end
          | None => None
          end
      | Some (InterpreterAction.NewFrame (FrameInput.Create boxed)) =>
          match CreateFrame.prepare interpreter host (S (List.length parents)) boxed.(Box.value) with
          | None => None
          | Some (CreateFrame.Immediate output host) =>
              execute_with_step step finalize fuel checkpoint parents
                {| InstructionContext.State.interpreter := CreateFrame.resume interpreter None output;
                   InstructionContext.State.host := host |}
          | Some (CreateFrame.Child address child_checkpoint child) =>
              execute_with_step step finalize fuel child_checkpoint
                (Pending.Create interpreter address checkpoint :: parents) child
          end
      | Some _ => None
      end
    end.

  Definition execute_with_finalization (finalize : bool) (fuel : nat)
      (checkpoint : StatefulHost.t) (parents : list Pending.t) (state : CallFrame.state) :=
    execute_with_step
      (InterpreterDispatch.step_result_stateful InterpreterTypes.I table)
      finalize fuel checkpoint parents state.

  Definition execute (fuel : nat) (checkpoint : StatefulHost.t)
      (parents : list Pending.t) (state : CallFrame.state) :=
    execute_with_finalization true fuel checkpoint parents state.

  Definition run (fuel : nat) (state : CallFrame.state) :=
    match (InstructionContext.State.interpreter _ _ _ state)
      .(Interpreter.runtime_flag).(RuntimeFlags.spec_id) with
    | SpecId.FRONTIER | SpecId.HOMESTEAD | SpecId.TANGERINE |
      SpecId.SPURIOUS_DRAGON | SpecId.BYZANTIUM | SpecId.PETERSBURG | SpecId.ISTANBUL | SpecId.BERLIN | SpecId.LONDON | SpecId.MERGE | SpecId.SHANGHAI
    | SpecId.CANCUN | SpecId.PRAGUE | SpecId.OSAKA =>
        let interpreter := InstructionContext.State.interpreter _ _ _ state in
        let host := (InstructionContext.State.host _ _ _ state)
          <| StatefulHost.spec_id := interpreter.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) |> in
        execute fuel host []
          {| InstructionContext.State.interpreter := interpreter;
             InstructionContext.State.host := host |}
    | _ => None
    end.
End CallRunner.

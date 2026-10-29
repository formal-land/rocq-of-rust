Require Import simulate.RocqOfRust.
Require Import revm.revm_handler.simulate.eest_context.
Require Import revm.revm_handler.simulate.eest_types.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.tests.transaction_cases.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_primitives.links.hardfork.

Require Import core.links.result.
Require Import core.ops.links.range.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import revm.revm_handler.simulate.handler.
Require Import revm.revm_handler.simulate.frame_data.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.gas.simulate.calc.

Module Test.
  Example stop_applies_value_nonce_and_exact_fees :
    TransactionCases.observation (EestContext.run 100 SpecId.OSAKA TransactionCases.tx (TransactionCases.input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Example reverted_storage_is_not_committed_to_fixture_database :
    TransactionCases.observation (EestContext.run 100 SpecId.OSAKA TransactionCases.tx
      (TransactionCases.input [95; 95; 85; 95; 95; 253])) =
    Some (InstructionResult.Revert, 26008, 1, 739920, 0, 156048, 1).
  Proof. vm_compute. reflexivity. Qed.

  Example successful_storage_clear_removes_slot_and_applies_refund :
    match EestContext.run 100 SpecId.OSAKA TransactionCases.tx (TransactionCases.input [95; 95; 85; 0]) with
    | EestTypes.Result.Completed output => Some
        (output.(EestTypes.Output.gas).(TransactionAccounting.Settlement.gas_used),
         output.(EestTypes.Output.gas).(TransactionAccounting.Settlement.gas_refunded),
         (EestTypes.account_at 42 output.(EestTypes.Output.accounts)).(EestTypes.Account.storage),
         (EestTypes.account_at 100 output.(EestTypes.Output.accounts)).(EestTypes.Account.balance))
    | _ => None
    end = Some (21204, 4800, [], 787953).
  Proof. vm_compute. reflexivity. Qed.

  Example u256_block_number_is_preserved_by_fixture_boundary :
    let input := TransactionCases.input [0] in
    let input := input <| EestTypes.Input.block := input.(EestTypes.Input.block)
      <| EestTypes.Block.number := 2 ^ 200 |> |> in
    match EestContext.run 100 SpecId.OSAKA TransactionCases.tx input with
    | EestTypes.Result.Completed _ => true | _ => false
    end = true.
  Proof. vm_compute. reflexivity. Qed.

  Example untouched_zero_storage_is_absent_from_fixture_output :
    let input := TransactionCases.input [0] in
    let input := input <| EestTypes.Input.accounts :=
      List.map (fun account => if Z.eqb account.(EestTypes.Account.address) 77 then
        account <| EestTypes.Account.storage := [(0, 0); (1, 2)] |> else account)
        input.(EestTypes.Input.accounts) |> in
    match EestContext.run 100 SpecId.OSAKA TransactionCases.tx input with
    | EestTypes.Result.Completed output => Some
        (EestTypes.account_at 77 output.(EestTypes.Output.accounts)).(EestTypes.Account.storage)
    | _ => None
    end = Some [(1, 2)].
  Proof. vm_compute. reflexivity. Qed.
  (* Start at the post-execution boundary with an applied authorization refund.
     ExecutionResult drops that refund for both failure variants. *)
  Definition failed_authorization_gas (status : InstructionResult.t) (remaining floor : u64) :=
    let ctx := EestContext.context SpecId.OSAKA
      (TransactionCases.tx <| TransactionAccounting.Transaction.gas_limit := 100000 |>)
      (TransactionCases.input [0]) in
    let frame := FrameResult.Call (CallOutcome.new
      {| InterpreterResult.result := status;
         InterpreterResult.output := Impl_Bytes.new;
         InterpreterResult.gas := Impl_Gas.erase_cost (Impl_Gas.new_spent 100000) remaining |}
      {| Range.start := (0 : usize); Range.end_ := (0 : usize) |}) in
    match Handler.post_execution ctx frame
      {| InitialAndFloorGas.initial_gas := 46000; InitialAndFloorGas.floor_gas := floor |} 12500 with
    | Some (Result.Ok frame, ctx) =>
        let gas := (FrameResult.into_interpreter_result frame).(InterpreterResult.gas) in
        match Handler.execution_result ctx frame with
        | Some (Result.Ok result, ctx) =>
            match EestContext.completed ctx result gas with
            | EestTypes.Result.Completed output =>
                let gas := output.(EestTypes.Output.gas) in
                Some (output.(EestTypes.Output.status),
                  gas.(TransactionAccounting.Settlement.gas_remaining),
                  gas.(TransactionAccounting.Settlement.gas_refunded),
                  gas.(TransactionAccounting.Settlement.gas_used),
                  gas.(TransactionAccounting.Settlement.caller_reimbursement))
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end.

  Example exceptional_halt_preserves_authorization_refund :
    failed_authorization_gas InstructionResult.OutOfGas 0 21000 =
    Some (InstructionResult.OutOfGas, 0, 12500, 87500, 125000).
  Proof. vm_compute. reflexivity. Qed.

  Example revert_preserves_authorization_refund_and_remaining_gas :
    failed_authorization_gas InstructionResult.Revert 20000 21000 =
    Some (InstructionResult.Revert, 20000, 12500, 67500, 325000).
  Proof. vm_compute. reflexivity. Qed.

  Example reverted_authorization_refund_is_capped :
    failed_authorization_gas InstructionResult.Revert 50000 21000 =
    Some (InstructionResult.Revert, 50000, 10000, 40000, 600000).
  Proof. vm_compute. reflexivity. Qed.

  Example reverted_authorization_refund_respects_gas_floor :
    failed_authorization_gas InstructionResult.Revert 50000 45000 =
    Some (InstructionResult.Revert, 55000, 0, 45000, 550000).
  Proof. vm_compute. reflexivity. Qed.
End Test.

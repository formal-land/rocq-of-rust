Require Import simulate.RocqOfRust.
Require Import revm.revm_handler.simulate.eest_context.
Require Import revm.revm_handler.simulate.eest_types.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.tests.transaction_cases.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_primitives.links.hardfork.

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
End Test.

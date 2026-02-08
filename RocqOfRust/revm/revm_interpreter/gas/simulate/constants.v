Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.gas.links.constants.

Definition ZERO : u64 := 0.
Definition BASE : u64 := 2.
Definition VERYLOW : u64 := 3.
Definition DATA_LOADN_GAS : u64 := 3.
Definition CONDITION_JUMP_GAS : u64 := 4.
Definition RETF_GAS : u64 := 3.
Definition DATA_LOAD_GAS : u64 := 4.
Definition LOW : u64 := 5.
Definition MID : u64 := 8.
Definition HIGH : u64 := 10.
Definition JUMPDEST : u64 := 1.
Definition SELFDESTRUCT : i64 := 24000.
Definition CREATE : u64 := 32000.
Definition CALLVALUE : u64 := 9000.
Definition NEWACCOUNT : u64 := 25000.
Definition EXP : u64 := 10.
Definition MEMORY : u64 := 3.
Definition LOG : u64 := 375.
Definition LOGDATA : u64 := 8.
Definition LOGTOPIC : u64 := 375.
Definition KECCAK256 : u64 := 30.
Definition KECCAK256WORD : u64 := 6.
Definition COPY : u64 := 3.
Definition BLOCKHASH : u64 := 20.
Definition CODEDEPOSIT : u64 := 200.
Definition ISTANBUL_SLOAD_GAS : u64 := 800.
Definition SSTORE_SET : u64 := 20000.
Definition SSTORE_RESET : u64 := 5000.
Definition REFUND_SSTORE_CLEARS : i64 := 15000.
Definition TRANSACTION_ZERO_DATA : u64 := 4.
Definition TRANSACTION_NON_ZERO_DATA_INIT : u64 := 16.
Definition TRANSACTION_NON_ZERO_DATA_FRONTIER : u64 := 68.
Definition EOF_CREATE_GAS : u64 := 32000.
Definition ACCESS_LIST_ADDRESS : u64 := 2400.
Definition ACCESS_LIST_STORAGE_KEY : u64 := 1900.
Definition COLD_SLOAD_COST : u64 := 2100.
Definition COLD_ACCOUNT_ACCESS_COST : u64 := 2600.
Definition WARM_STORAGE_READ_COST : u64 := 100.
Definition WARM_SSTORE_RESET : u64 := 2900. (* SSTORE_RESET - COLD_SLOAD_COST = 5000 - 2100 *)
Definition INITCODE_WORD_COST : u64 := 2.
Definition CALL_STIPEND : u64 := 2300.
Definition MIN_CALLEE_GAS : u64 := 2300. (* = CALL_STIPEND *)

Lemma ZERO_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_ZERO stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw ZERO), stack) }}.
Proof. p. Qed.

Lemma BASE_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_BASE stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw BASE), stack) }}.
Proof. p. Qed.

Lemma VERYLOW_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_VERYLOW stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw VERYLOW), stack) }}.
Proof. p. Qed.

Lemma DATA_LOADN_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_DATA_LOADN_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw DATA_LOADN_GAS), stack) }}.
Proof. p. Qed.

Lemma CONDITION_JUMP_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_CONDITION_JUMP_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw CONDITION_JUMP_GAS), stack) }}.
Proof. p. Qed.

Lemma RETF_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_RETF_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw RETF_GAS), stack) }}.
Proof. p. Qed.

Lemma DATA_LOAD_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_DATA_LOAD_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw DATA_LOAD_GAS), stack) }}.
Proof. p. Qed.

Lemma LOW_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_LOW stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw LOW), stack) }}.
Proof. p. Qed.

Lemma MID_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_MID stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw MID), stack) }}.
Proof. p. Qed.

Lemma HIGH_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_HIGH stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw HIGH), stack) }}.
Proof. p. Qed.

Lemma JUMPDEST_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_JUMPDEST stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw JUMPDEST), stack) }}.
Proof. p. Qed.

Lemma SELFDESTRUCT_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_SELFDESTRUCT stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw SELFDESTRUCT), stack) }}.
Proof. p. Qed.

Lemma CREATE_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_CREATE stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw CREATE), stack) }}.
Proof. p. Qed.

Lemma CALLVALUE_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_CALLVALUE stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw CALLVALUE), stack) }}.
Proof. p. Qed.

Lemma NEWACCOUNT_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_NEWACCOUNT stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw NEWACCOUNT), stack) }}.
Proof. p. Qed.

Lemma EXP_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_EXP stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw EXP), stack) }}.
Proof. p. Qed.

Lemma MEMORY_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_MEMORY stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw MEMORY), stack) }}.
Proof. p. Qed.

Lemma LOG_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_LOG stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw LOG), stack) }}.
Proof. p. Qed.

Lemma LOGDATA_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_LOGDATA stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw LOGDATA), stack) }}.
Proof. p. Qed.

Lemma LOGTOPIC_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_LOGTOPIC stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw LOGTOPIC), stack) }}.
Proof. p. Qed.

Lemma KECCAK256_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_KECCAK256 stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw KECCAK256), stack) }}.
Proof. p. Qed.

Lemma KECCAK256WORD_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_KECCAK256WORD stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw KECCAK256WORD), stack) }}.
Proof. p. Qed.

Lemma COPY_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_COPY stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw COPY), stack) }}.
Proof. p. Qed.

Lemma BLOCKHASH_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_BLOCKHASH stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw BLOCKHASH), stack) }}.
Proof. p. Qed.

Lemma CODEDEPOSIT_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_CODEDEPOSIT stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw CODEDEPOSIT), stack) }}.
Proof. p. Qed.

Lemma ISTANBUL_SLOAD_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_ISTANBUL_SLOAD_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw ISTANBUL_SLOAD_GAS), stack) }}.
Proof. p. Qed.

Lemma SSTORE_SET_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_SSTORE_SET stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw SSTORE_SET), stack) }}.
Proof. p. Qed.

Lemma SSTORE_RESET_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_SSTORE_RESET stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw SSTORE_RESET), stack) }}.
Proof. p. Qed.

Lemma REFUND_SSTORE_CLEARS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_REFUND_SSTORE_CLEARS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw REFUND_SSTORE_CLEARS), stack) }}.
Proof. p. Qed.

Lemma TRANSACTION_ZERO_DATA_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_TRANSACTION_ZERO_DATA stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw TRANSACTION_ZERO_DATA), stack) }}.
Proof. p. Qed.

Lemma TRANSACTION_NON_ZERO_DATA_INIT_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_TRANSACTION_NON_ZERO_DATA_INIT stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw TRANSACTION_NON_ZERO_DATA_INIT), stack) }}.
Proof. p. Qed.

Lemma TRANSACTION_NON_ZERO_DATA_FRONTIER_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_TRANSACTION_NON_ZERO_DATA_FRONTIER stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw TRANSACTION_NON_ZERO_DATA_FRONTIER), stack) }}.
Proof. p. Qed.

Lemma EOF_CREATE_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_EOF_CREATE_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw EOF_CREATE_GAS), stack) }}.
Proof. p. Qed.

Lemma ACCESS_LIST_ADDRESS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_ACCESS_LIST_ADDRESS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw ACCESS_LIST_ADDRESS), stack) }}.
Proof. p. Qed.

Lemma ACCESS_LIST_STORAGE_KEY_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_ACCESS_LIST_STORAGE_KEY stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw ACCESS_LIST_STORAGE_KEY), stack) }}.
Proof. p. Qed.

Lemma COLD_SLOAD_COST_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_COLD_SLOAD_COST stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw COLD_SLOAD_COST), stack) }}.
Proof. p. Qed.

Lemma COLD_ACCOUNT_ACCESS_COST_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_COLD_ACCOUNT_ACCESS_COST stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw COLD_ACCOUNT_ACCESS_COST), stack) }}.
Proof. p. Qed.

Lemma WARM_STORAGE_READ_COST_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_WARM_STORAGE_READ_COST stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw WARM_STORAGE_READ_COST), stack) }}.
Proof. p. Qed.

Lemma WARM_SSTORE_RESET_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_WARM_SSTORE_RESET stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw WARM_SSTORE_RESET), stack) }}.
Proof. s. Qed.

Lemma INITCODE_WORD_COST_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_INITCODE_WORD_COST stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw INITCODE_WORD_COST), stack) }}.
Proof. p. Qed.

Lemma CALL_STIPEND_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_CALL_STIPEND stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw CALL_STIPEND), stack) }}.
Proof. p. Qed.

Lemma MIN_CALLEE_GAS_eq (stack : Stack.t) :
  {{ SimulateM.eval_f run_MIN_CALLEE_GAS stack 🌲
     (Output.Success (Ref.immediate Pointer.Kind.Raw MIN_CALLEE_GAS), stack) }}.
Proof. s. Qed.

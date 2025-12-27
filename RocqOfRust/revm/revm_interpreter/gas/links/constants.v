(* Generated *)
Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import revm_interpreter.gas.constants.

Instance run_ZERO :
  Run.Trait
    gas.constants.value_ZERO [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ZERO.

Instance run_BASE :
  Run.Trait
    gas.constants.value_BASE [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_BASE.

Instance run_VERYLOW :
  Run.Trait
    gas.constants.value_VERYLOW [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_VERYLOW.

Instance run_DATA_LOADN_GAS :
  Run.Trait
    gas.constants.value_DATA_LOADN_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DATA_LOADN_GAS.

Instance run_CONDITION_JUMP_GAS :
  Run.Trait
    gas.constants.value_CONDITION_JUMP_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CONDITION_JUMP_GAS.

Instance run_RETF_GAS :
  Run.Trait
    gas.constants.value_RETF_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_RETF_GAS.

Instance run_DATA_LOAD_GAS :
  Run.Trait
    gas.constants.value_DATA_LOAD_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DATA_LOAD_GAS.

Instance run_LOW :
  Run.Trait
    gas.constants.value_LOW [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOW.

Instance run_MID :
  Run.Trait
    gas.constants.value_MID [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MID.

Instance run_HIGH :
  Run.Trait
    gas.constants.value_HIGH [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_HIGH.

Instance run_JUMPDEST :
  Run.Trait
    gas.constants.value_JUMPDEST [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_JUMPDEST.

Instance run_SELFDESTRUCT :
  Run.Trait
    gas.constants.value_SELFDESTRUCT [] [] []
    (Ref.t Pointer.Kind.Raw I64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_SELFDESTRUCT.

Instance run_CREATE :
  Run.Trait
    gas.constants.value_CREATE [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CREATE.

Instance run_CALLVALUE :
  Run.Trait
    gas.constants.value_CALLVALUE [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CALLVALUE.

Instance run_NEWACCOUNT :
  Run.Trait
    gas.constants.value_NEWACCOUNT [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_NEWACCOUNT.

Instance run_EXP :
  Run.Trait
    gas.constants.value_EXP [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_EXP.

Instance run_MEMORY :
  Run.Trait
    gas.constants.value_MEMORY [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MEMORY.

Instance run_LOG :
  Run.Trait
    gas.constants.value_LOG [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOG.

Instance run_LOGDATA :
  Run.Trait
    gas.constants.value_LOGDATA [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOGDATA.

Instance run_LOGTOPIC :
  Run.Trait
    gas.constants.value_LOGTOPIC [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOGTOPIC.

Instance run_KECCAK256 :
  Run.Trait
    gas.constants.value_KECCAK256 [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_KECCAK256.

Instance run_KECCAK256WORD :
  Run.Trait
    gas.constants.value_KECCAK256WORD [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_KECCAK256WORD.

Instance run_COPY :
  Run.Trait
    gas.constants.value_COPY [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COPY.

Instance run_BLOCKHASH :
  Run.Trait
    gas.constants.value_BLOCKHASH [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_BLOCKHASH.

Instance run_CODEDEPOSIT :
  Run.Trait
    gas.constants.value_CODEDEPOSIT [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CODEDEPOSIT.

Instance run_ISTANBUL_SLOAD_GAS :
  Run.Trait
    gas.constants.value_ISTANBUL_SLOAD_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ISTANBUL_SLOAD_GAS.

Instance run_SSTORE_SET :
  Run.Trait
    gas.constants.value_SSTORE_SET [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_SSTORE_SET.

Instance run_SSTORE_RESET :
  Run.Trait
    gas.constants.value_SSTORE_RESET [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_SSTORE_RESET.

Instance run_REFUND_SSTORE_CLEARS :
  Run.Trait
    gas.constants.value_REFUND_SSTORE_CLEARS [] [] []
    (Ref.t Pointer.Kind.Raw I64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_REFUND_SSTORE_CLEARS.

Instance run_TRANSACTION_ZERO_DATA :
  Run.Trait
    gas.constants.value_TRANSACTION_ZERO_DATA [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_TRANSACTION_ZERO_DATA.

Instance run_TRANSACTION_NON_ZERO_DATA_INIT :
  Run.Trait
    gas.constants.value_TRANSACTION_NON_ZERO_DATA_INIT [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_TRANSACTION_NON_ZERO_DATA_INIT.

Instance run_TRANSACTION_NON_ZERO_DATA_FRONTIER :
  Run.Trait
    gas.constants.value_TRANSACTION_NON_ZERO_DATA_FRONTIER [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_TRANSACTION_NON_ZERO_DATA_FRONTIER.

Instance run_EOF_CREATE_GAS :
  Run.Trait
    gas.constants.value_EOF_CREATE_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_EOF_CREATE_GAS.

Instance run_ACCESS_LIST_ADDRESS :
  Run.Trait
    gas.constants.value_ACCESS_LIST_ADDRESS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ACCESS_LIST_ADDRESS.

Instance run_ACCESS_LIST_STORAGE_KEY :
  Run.Trait
    gas.constants.value_ACCESS_LIST_STORAGE_KEY [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ACCESS_LIST_STORAGE_KEY.

Instance run_COLD_SLOAD_COST :
  Run.Trait
    gas.constants.value_COLD_SLOAD_COST [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COLD_SLOAD_COST.

Instance run_COLD_ACCOUNT_ACCESS_COST :
  Run.Trait
    gas.constants.value_COLD_ACCOUNT_ACCESS_COST [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COLD_ACCOUNT_ACCESS_COST.

Instance run_WARM_STORAGE_READ_COST :
  Run.Trait
    gas.constants.value_WARM_STORAGE_READ_COST [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_WARM_STORAGE_READ_COST.

Instance run_WARM_SSTORE_RESET :
  Run.Trait
    gas.constants.value_WARM_SSTORE_RESET [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_WARM_SSTORE_RESET.

Instance run_INITCODE_WORD_COST :
  Run.Trait
    gas.constants.value_INITCODE_WORD_COST [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_INITCODE_WORD_COST.

Instance run_CALL_STIPEND :
  Run.Trait
    gas.constants.value_CALL_STIPEND [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CALL_STIPEND.

Instance run_MIN_CALLEE_GAS :
  Run.Trait
    gas.constants.value_MIN_CALLEE_GAS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MIN_CALLEE_GAS.

(* Generated *)
Require Import links.RocqOfRust.
Require Import revm_interpreter.gas.constants.

Instance run_ZERO :
  Run.Trait
    gas.constants.value_ZERO [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ZERO.

Instance run_BASE :
  Run.Trait
    gas.constants.value_BASE [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_BASE.

Instance run_VERYLOW :
  Run.Trait
    gas.constants.value_VERYLOW [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_VERYLOW.

Instance run_DATA_LOADN_GAS :
  Run.Trait
    gas.constants.value_DATA_LOADN_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DATA_LOADN_GAS.

Instance run_CONDITION_JUMP_GAS :
  Run.Trait
    gas.constants.value_CONDITION_JUMP_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CONDITION_JUMP_GAS.

Instance run_RETF_GAS :
  Run.Trait
    gas.constants.value_RETF_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_RETF_GAS.

Instance run_DATA_LOAD_GAS :
  Run.Trait
    gas.constants.value_DATA_LOAD_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DATA_LOAD_GAS.

Instance run_LOW :
  Run.Trait
    gas.constants.value_LOW [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOW.

Instance run_MID :
  Run.Trait
    gas.constants.value_MID [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MID.

Instance run_HIGH :
  Run.Trait
    gas.constants.value_HIGH [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_HIGH.

Instance run_JUMPDEST :
  Run.Trait
    gas.constants.value_JUMPDEST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_JUMPDEST.

Instance run_SELFDESTRUCT_REFUND :
  Run.Trait
    gas.constants.value_SELFDESTRUCT_REFUND [] [] []
    ('* i64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_SELFDESTRUCT_REFUND.

Instance run_CREATE :
  Run.Trait
    gas.constants.value_CREATE [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CREATE.

Instance run_CALLVALUE :
  Run.Trait
    gas.constants.value_CALLVALUE [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CALLVALUE.

Instance run_NEWACCOUNT :
  Run.Trait
    gas.constants.value_NEWACCOUNT [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_NEWACCOUNT.

Instance run_EXP :
  Run.Trait
    gas.constants.value_EXP [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_EXP.

Instance run_MEMORY :
  Run.Trait
    gas.constants.value_MEMORY [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MEMORY.

Instance run_LOG :
  Run.Trait
    gas.constants.value_LOG [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOG.

Instance run_LOGDATA :
  Run.Trait
    gas.constants.value_LOGDATA [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOGDATA.

Instance run_LOGTOPIC :
  Run.Trait
    gas.constants.value_LOGTOPIC [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_LOGTOPIC.

Instance run_KECCAK256 :
  Run.Trait
    gas.constants.value_KECCAK256 [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_KECCAK256.

Instance run_KECCAK256WORD :
  Run.Trait
    gas.constants.value_KECCAK256WORD [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_KECCAK256WORD.

Instance run_COPY :
  Run.Trait
    gas.constants.value_COPY [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COPY.

Instance run_BLOCKHASH :
  Run.Trait
    gas.constants.value_BLOCKHASH [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_BLOCKHASH.

Instance run_CODEDEPOSIT :
  Run.Trait
    gas.constants.value_CODEDEPOSIT [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CODEDEPOSIT.

Instance run_ISTANBUL_SLOAD_GAS :
  Run.Trait
    gas.constants.value_ISTANBUL_SLOAD_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ISTANBUL_SLOAD_GAS.

Instance run_SSTORE_SET :
  Run.Trait
    gas.constants.value_SSTORE_SET [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_SSTORE_SET.

Instance run_SSTORE_RESET :
  Run.Trait
    gas.constants.value_SSTORE_RESET [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_SSTORE_RESET.

Instance run_REFUND_SSTORE_CLEARS :
  Run.Trait
    gas.constants.value_REFUND_SSTORE_CLEARS [] [] []
    ('* i64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_REFUND_SSTORE_CLEARS.

Instance run_STANDARD_TOKEN_COST :
  Run.Trait
    gas.constants.value_STANDARD_TOKEN_COST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_STANDARD_TOKEN_COST.

Instance run_NON_ZERO_BYTE_DATA_COST :
  Run.Trait
    gas.constants.value_NON_ZERO_BYTE_DATA_COST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_NON_ZERO_BYTE_DATA_COST.

Instance run_NON_ZERO_BYTE_MULTIPLIER :
  Run.Trait
    gas.constants.value_NON_ZERO_BYTE_MULTIPLIER [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_NON_ZERO_BYTE_MULTIPLIER.

Instance run_NON_ZERO_BYTE_DATA_COST_ISTANBUL :
  Run.Trait
    gas.constants.value_NON_ZERO_BYTE_DATA_COST_ISTANBUL [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_NON_ZERO_BYTE_DATA_COST_ISTANBUL.

Instance run_NON_ZERO_BYTE_MULTIPLIER_ISTANBUL :
  Run.Trait
    gas.constants.value_NON_ZERO_BYTE_MULTIPLIER_ISTANBUL [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_NON_ZERO_BYTE_MULTIPLIER_ISTANBUL.

Instance run_TOTAL_COST_FLOOR_PER_TOKEN :
  Run.Trait
    gas.constants.value_TOTAL_COST_FLOOR_PER_TOKEN [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_TOTAL_COST_FLOOR_PER_TOKEN.

Instance run_EOF_CREATE_GAS :
  Run.Trait
    gas.constants.value_EOF_CREATE_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_EOF_CREATE_GAS.

Instance run_ACCESS_LIST_ADDRESS :
  Run.Trait
    gas.constants.value_ACCESS_LIST_ADDRESS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ACCESS_LIST_ADDRESS.

Instance run_ACCESS_LIST_STORAGE_KEY :
  Run.Trait
    gas.constants.value_ACCESS_LIST_STORAGE_KEY [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ACCESS_LIST_STORAGE_KEY.

Instance run_COLD_SLOAD_COST :
  Run.Trait
    gas.constants.value_COLD_SLOAD_COST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COLD_SLOAD_COST.

Instance run_COLD_ACCOUNT_ACCESS_COST :
  Run.Trait
    gas.constants.value_COLD_ACCOUNT_ACCESS_COST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COLD_ACCOUNT_ACCESS_COST.

Instance run_WARM_STORAGE_READ_COST :
  Run.Trait
    gas.constants.value_WARM_STORAGE_READ_COST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_WARM_STORAGE_READ_COST.

Instance run_COLD_ACCOUNT_ACCESS_COST_ADDITIONAL :
  Run.Trait
    gas.constants.value_COLD_ACCOUNT_ACCESS_COST_ADDITIONAL [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COLD_ACCOUNT_ACCESS_COST_ADDITIONAL.

Instance run_COLD_SLOAD_COST_ADDITIONAL :
  Run.Trait
    gas.constants.value_COLD_SLOAD_COST_ADDITIONAL [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_COLD_SLOAD_COST_ADDITIONAL.

Instance run_WARM_SSTORE_RESET :
  Run.Trait
    gas.constants.value_WARM_SSTORE_RESET [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_WARM_SSTORE_RESET.

Instance run_INITCODE_WORD_COST :
  Run.Trait
    gas.constants.value_INITCODE_WORD_COST [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_INITCODE_WORD_COST.

Instance run_CALL_STIPEND :
  Run.Trait
    gas.constants.value_CALL_STIPEND [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_CALL_STIPEND.

Instance run_MIN_CALLEE_GAS :
  Run.Trait
    gas.constants.value_MIN_CALLEE_GAS [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MIN_CALLEE_GAS.
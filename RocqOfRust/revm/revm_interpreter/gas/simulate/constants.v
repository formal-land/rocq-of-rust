Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.gas.links.constants.

(*
pub const ZERO: u64 = 0;
pub const BASE: u64 = 2;

pub const VERYLOW: u64 = 3;
pub const DATA_LOADN_GAS: u64 = 3;

pub const CONDITION_JUMP_GAS: u64 = 4;
pub const RETF_GAS: u64 = 3;
pub const DATA_LOAD_GAS: u64 = 4;

pub const LOW: u64 = 5;
pub const MID: u64 = 8;
pub const HIGH: u64 = 10;
pub const JUMPDEST: u64 = 1;
pub const SELFDESTRUCT: i64 = 24000;
pub const CREATE: u64 = 32000;
pub const CALLVALUE: u64 = 9000;
pub const NEWACCOUNT: u64 = 25000;
pub const EXP: u64 = 10;
pub const MEMORY: u64 = 3;
pub const LOG: u64 = 375;
pub const LOGDATA: u64 = 8;
pub const LOGTOPIC: u64 = 375;
pub const KECCAK256: u64 = 30;
pub const KECCAK256WORD: u64 = 6;
pub const COPY: u64 = 3;
pub const BLOCKHASH: u64 = 20;
pub const CODEDEPOSIT: u64 = 200;

/// EIP-1884: Repricing for trie-size-dependent opcodes
pub const ISTANBUL_SLOAD_GAS: u64 = 800;
pub const SSTORE_SET: u64 = 20000;
pub const SSTORE_RESET: u64 = 5000;
pub const REFUND_SSTORE_CLEARS: i64 = 15000;

pub const TRANSACTION_ZERO_DATA: u64 = 4;
pub const TRANSACTION_NON_ZERO_DATA_INIT: u64 = 16;
pub const TRANSACTION_NON_ZERO_DATA_FRONTIER: u64 = 68;

pub const EOF_CREATE_GAS: u64 = 32000;

// Berlin eip2929 constants
pub const ACCESS_LIST_ADDRESS: u64 = 2400;
pub const ACCESS_LIST_STORAGE_KEY: u64 = 1900;
pub const COLD_SLOAD_COST: u64 = 2100;
pub const COLD_ACCOUNT_ACCESS_COST: u64 = 2600;
pub const WARM_STORAGE_READ_COST: u64 = 100;
pub const WARM_SSTORE_RESET: u64 = SSTORE_RESET - COLD_SLOAD_COST;

/// EIP-3860 : Limit and meter initcode
pub const INITCODE_WORD_COST: u64 = 2;

pub const CALL_STIPEND: u64 = 2300;
pub const MIN_CALLEE_GAS: u64 = CALL_STIPEND;
*)

Definition ZERO : u64 :=
  {| Integer.value := 0 |}.
Definition BASE : u64 :=
  {| Integer.value := 2 |}.

Definition VERYLOW : u64 :=
  {| Integer.value := 3 |}.
Definition DATA_LOADN_GAS : u64 :=
  {| Integer.value := 3 |}.

Definition CONDITION_JUMP_GAS : u64 :=
  {| Integer.value := 4 |}.
Definition RETF_GAS : u64 :=
  {| Integer.value := 3 |}.
Definition DATA_LOAD_GAS : u64 :=
  {| Integer.value := 4 |}.

Definition LOW : u64 :=
  {| Integer.value := 5 |}.
Definition MID : u64 :=
  {| Integer.value := 8 |}.
Definition HIGH : u64 :=
  {| Integer.value := 10 |}.
Definition JUMPDEST : u64 :=
  {| Integer.value := 1 |}.
Definition SELFDESTRUCT : i64 :=
  {| Integer.value := 24000 |}.
Definition CREATE : u64 :=
  {| Integer.value := 32000 |}.
Definition CALLVALUE : u64 :=
  {| Integer.value := 9000 |}.
Definition NEWACCOUNT : u64 :=
  {| Integer.value := 25000 |}.
Definition EXP : u64 :=
  {| Integer.value := 10 |}.
Definition MEMORY : u64 :=
  {| Integer.value := 3 |}.
Definition LOG : u64 :=
  {| Integer.value := 375 |}.
Definition LOGDATA : u64 :=
  {| Integer.value := 8 |}.
Definition LOGTOPIC : u64 :=
  {| Integer.value := 375 |}.
Definition KECCAK256 : u64 :=
  {| Integer.value := 30 |}.
Definition KECCAK256WORD : u64 :=
  {| Integer.value := 6 |}.
Definition COPY : u64 :=
  {| Integer.value := 3 |}.
Definition BLOCKHASH : u64 :=
  {| Integer.value := 20 |}.
Definition CODEDEPOSIT : u64 :=
  {| Integer.value := 200 |}.

Definition ISTANBUL_SLOAD_GAS : u64 :=
  {| Integer.value := 800 |}.
Definition SSTORE_SET : u64 :=
  {| Integer.value := 20000 |}.
Definition SSTORE_RESET : u64 :=
  {| Integer.value := 5000 |}.
Definition REFUND_SSTORE_CLEARS : i64 :=
  {| Integer.value := 15000 |}.

Definition TRANSACTION_ZERO_DATA : u64 :=
  {| Integer.value := 4 |}.
Definition TRANSACTION_NON_ZERO_DATA_INIT : u64 :=
  {| Integer.value := 16 |}.
Definition TRANSACTION_NON_ZERO_DATA_FRONTIER : u64 :=
  {| Integer.value := 68 |}.

Definition EOF_CREATE_GAS : u64 :=
  {| Integer.value := 32000 |}.

Definition ACCESS_LIST_ADDRESS : u64 :=
  {| Integer.value := 2400 |}.
Definition ACCESS_LIST_STORAGE_KEY : u64 :=
  {| Integer.value := 1900 |}.
Definition COLD_SLOAD_COST : u64 :=
  {| Integer.value := 2100 |}.
Definition COLD_ACCOUNT_ACCESS_COST : u64 :=
  {| Integer.value := 2600 |}.
Definition WARM_STORAGE_READ_COST : u64 :=
  {| Integer.value := 100 |}.
Definition WARM_SSTORE_RESET : u64 :=
  {| Integer.value := SSTORE_RESET.(Integer.value) - COLD_SLOAD_COST.(Integer.value) |}.

Definition INITCODE_WORD_COST : u64 :=
  {| Integer.value := 2 |}.

Definition CALL_STIPEND : u64 :=
  {| Integer.value := 2300 |}.
Definition MIN_CALLEE_GAS : u64 :=
  {| Integer.value := CALL_STIPEND.(Integer.value) |}.

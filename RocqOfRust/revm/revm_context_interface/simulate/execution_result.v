Require Import simulate.RocqOfRust.
From Stdlib Require Import String.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.result.

Module EVMError.
  Inductive t (Error : Set) : Set :=
  | Transaction (error : InvalidTransaction.t)
  | Header (error : InvalidHeader.t)
  | Database (error : Error)
  | Custom (error : string).

  Arguments Transaction {Error}.
  Arguments Header {Error}.
  Arguments Database {Error}.
  Arguments Custom {Error}.

  Definition from_context {Error : Set} (error : ContextError.t Error) : t Error :=
    match error with ContextError.Db error => Database error | ContextError.Custom error => Custom error end.
End EVMError.

Module SuccessReason.
  Inductive t : Set := Stop | Return | SelfDestruct.
End SuccessReason.

Module OutOfGasError.
  Inductive t : Set := Basic | MemoryLimit | Memory | Precompile | InvalidOperand | ReentrancySentry.
End OutOfGasError.

Module HaltReason.
  Inductive t : Set :=
  | OutOfGas (error : OutOfGasError.t)
  | OpcodeNotFound | InvalidFEOpcode | InvalidJump | NotActivated
  | StackUnderflow | StackOverflow | OutOfOffset | CreateCollision
  | PrecompileError | PrecompileErrorWithContext (message : string)
  | NonceOverflow | CreateContractSizeLimit | CreateContractStartingWithEF | CreateInitCodeSizeLimit
  | OverflowPayment | StateChangeDuringStaticCall | CallNotAllowedInsideStatic | OutOfFunds | CallTooDeep.
End HaltReason.

Module Output.
  Inductive t : Set :=
  | Call (data : Bytes.t)
  | Create (data : Bytes.t) (address : option Address.t).

  Definition into_data (self : t) : Bytes.t :=
    match self with Call data | Create data _ => data end.
End Output.

Module ExecutionResult.
  Inductive t : Set :=
  | Success (reason : SuccessReason.t) (gas_used gas_refunded : u64)
      (logs : list (Log.t LogData.t)) (output : Output.t)
  | Revert (gas_used : u64) (output : Bytes.t)
  | Halt (reason : HaltReason.t) (gas_used : u64).
End ExecutionResult.

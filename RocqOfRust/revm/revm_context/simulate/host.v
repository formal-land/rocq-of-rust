Require Import simulate.RocqOfRust.
From Stdlib Require Import String.
Require Import core.links.result.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.host_runtime.
Require Import revm.revm_database_interface.simulate.lib.

Module ContextHost.
  (** A Rust unwrap failure is retained as a context error, so the handler must
      reject execution as an internal failure rather than report EVM success. *)
  Definition invariant_failure {DB Error : Set} (self : Context.t DB Error) : Context.t DB Error :=
    self <| Context.error := Result.Err (ContextError.Custom "journal invariant failure") |>.

  Definition finish_option {DB Error A : Set} (self : Context.t DB Error)
      (result : option (option A * Context.t DB Error)) : option A * Context.t DB Error :=
    match result with Some result => result | None => (None, invariant_failure self) end.

  Definition finish_result {DB Error A : Set} (self : Context.t DB Error)
      (result : option (Result.t A LoadError.t * Context.t DB Error))
      : Result.t A LoadError.t * Context.t DB Error :=
    match result with
    | Some result => result
    | None => (Result.Err LoadError.DBError, invariant_failure self)
    end.

  #[global] Instance methods {DB Error : Set} `{Database.C DB Error}
      : HostRuntime.C (Context.t DB Error) := {|
    HostRuntime.load_account_info_skip_cold_load := Impl_Host_for_Context.load_account_info_skip_cold_load;
    HostRuntime.load_account_code self address := finish_option self (Impl_Host_for_Context.load_account_code self address);
    HostRuntime.block_hash := Impl_Host_for_Context.block_hash;
    HostRuntime.max_initcode_size self := (Impl_Host_for_Context.max_initcode_size self, self);
    HostRuntime.beneficiary self := (Impl_Host_for_Context.beneficiary self, self);
    HostRuntime.block_number self := (Impl_Host_for_Context.block_number self, self);
    HostRuntime.timestamp self := (Impl_Host_for_Context.timestamp self, self);
    HostRuntime.gas_limit self := (Impl_Host_for_Context.gas_limit self, self);
    HostRuntime.chain_id self := (Impl_Host_for_Context.chain_id self, self);
    HostRuntime.basefee self := (Impl_Host_for_Context.basefee self, self);
    HostRuntime.blob_gasprice self := (Impl_Host_for_Context.blob_gasprice self, self);
    HostRuntime.effective_gas_price self := (Impl_Host_for_Context.effective_gas_price self, self);
    HostRuntime.caller self := (Impl_Host_for_Context.caller self, self);
    HostRuntime.blob_hash self number := (Impl_Host_for_Context.blob_hash self number, self);
    HostRuntime.difficulty self := (Impl_Host_for_Context.difficulty self, self);
    HostRuntime.prevrandao self := (Impl_Host_for_Context.prevrandao self, self);
    HostRuntime.balance self address := finish_option self (Impl_Host_for_Context.balance self address);
    HostRuntime.sload self address key := finish_option self (Impl_Host_for_Context.sload self address key);
    HostRuntime.sload_skip_cold_load self address key skip_cold_load :=
      finish_result self (Impl_Host_for_Context.sload_skip_cold_load self address key skip_cold_load);
    HostRuntime.sstore self address key value := finish_option self (Impl_Host_for_Context.sstore self address key value);
    HostRuntime.sstore_skip_cold_load self address key value skip_cold_load :=
      finish_result self (Impl_Host_for_Context.sstore_skip_cold_load self address key value skip_cold_load);
    HostRuntime.tload self address key := (Impl_Host_for_Context.tload self address key, self);
    HostRuntime.tstore := Impl_Host_for_Context.tstore;
    HostRuntime.log := Impl_Host_for_Context.log;
    HostRuntime.selfdestruct self address target skip_cold_load :=
      finish_result self (Impl_Host_for_Context.selfdestruct self address target skip_cold_load);
  |}.
End ContextHost.

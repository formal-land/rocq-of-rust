Require Import simulate.RocqOfRust.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

(** CfgEnv<SpecId> with the default Cargo features used by the checked-in
    translation. Optional validation-disabling features are not enabled. *)
Module CfgEnv.
  Record t : Set := {
    chain_id : u64;
    tx_chain_id_check : bool;
    spec : SpecId.t;
    limit_contract_code_size : option usize;
    limit_contract_initcode_size : option usize;
    disable_nonce_check : bool;
    max_blobs_per_tx : option u64;
    blob_base_fee_update_fraction : option u64;
    tx_gas_limit_cap : option u64;
  }.
End CfgEnv.

Module Impl_CfgEnv.
  Definition new_with_spec (spec : SpecId.t) : CfgEnv.t := {|
    CfgEnv.chain_id := 1;
    CfgEnv.tx_chain_id_check := true;
    CfgEnv.spec := spec;
    CfgEnv.limit_contract_code_size := None;
    CfgEnv.limit_contract_initcode_size := None;
    CfgEnv.disable_nonce_check := false;
    CfgEnv.max_blobs_per_tx := None;
    CfgEnv.blob_base_fee_update_fraction := None;
    CfgEnv.tx_gas_limit_cap := None;
  |}.

  Definition new : CfgEnv.t := new_with_spec SpecId.PRAGUE.

  Definition blob_base_fee_update_fraction (self : CfgEnv.t) : u64 :=
    match self.(CfgEnv.blob_base_fee_update_fraction) with
    | Some fraction => fraction
    | None => if Impl_SpecId.is_enabled_in self.(CfgEnv.spec) SpecId.PRAGUE then 5007716 else 3338477
    end.

  Definition tx_gas_limit_cap (self : CfgEnv.t) : u64 :=
    match self.(CfgEnv.tx_gas_limit_cap) with
    | Some cap => cap
    | None => if Impl_SpecId.is_enabled_in self.(CfgEnv.spec) SpecId.OSAKA
        then 16777216 else {| Integer.value := 2 ^ 64 - 1 |}
    end.

  Definition max_code_size (self : CfgEnv.t) : usize :=
    match self.(CfgEnv.limit_contract_code_size) with Some size => size | None => 24576 end.

  Definition max_initcode_size (self : CfgEnv.t) : usize :=
    match self.(CfgEnv.limit_contract_initcode_size) with
    | Some size => size
    | None => match self.(CfgEnv.limit_contract_code_size) with
        | Some size => BinOp.Saturating.mul size 2
        | None => 49152
        end
    end.

  Definition with_chain_id (self : CfgEnv.t) (chain_id : u64) : CfgEnv.t :=
    self <| CfgEnv.chain_id := chain_id |>.

  Definition with_spec (self : CfgEnv.t) (spec : SpecId.t) : CfgEnv.t := self <| CfgEnv.spec := spec |>.
End Impl_CfgEnv.

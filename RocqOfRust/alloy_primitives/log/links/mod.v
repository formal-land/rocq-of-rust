Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.mod.
Require Import core.links.option.
Require Import ruint.links.lib.

(*
pub struct Log<T = LogData> {
    pub address: Address,
    pub data: T,
}
*)
Module Log.
  RocqOfRustLinkGenericRecord "alloy_primitives::log::Log" [ T ] := {
    address : Address.t;
    data : T
  }.
End Log.
Export (hints) Log.

(*
pub struct LogData {
    topics: Vec<B256>,
    pub data: Bytes,
}
*)
Module LogData.
  RocqOfRustLinkRecord "alloy_primitives::log::LogData" := {
    topics : (Vec.t aliases.U256.t Global.t);
    data : Bytes.t
  }.
End LogData.
Export (hints) LogData.

Module Impl_LogData.
  Definition Self : Set :=
    LogData.t.

  (* pub fn new(topics: Vec<B256>, data: Bytes) -> Option<Self> *)
  Instance run_new (topics : Vec.t aliases.B256.t Global.t) (data : Bytes.t) :
    Run.Trait log.Impl_alloy_primitives_log_LogData.new [] [] [φ topics; φ data]
    (option Self).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new.
End Impl_LogData.
Export (hints) Impl_LogData.

Require Import links.RocqOfRust.
Require Import revm.revm_primitives.links.hardfork.

Module RuntimeFlags.
  RocqOfRustLinkRecord "revm_interpreter::interpreter::runtime_flags::RuntimeFlags" := {
    is_static : bool;
    spec_id : SpecId.t;
  }.

  Definition non_static (spec : SpecId.t) : t := {|
    is_static := false;
    spec_id := spec;
  |}.

End RuntimeFlags.
Export (hints) RuntimeFlags.

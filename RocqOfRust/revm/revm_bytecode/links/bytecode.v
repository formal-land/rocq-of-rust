Require Import links.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import revm.revm_bytecode.bytecode.

Module Bytecode.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::bytecode::Bytecode";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::bytecode::Bytecode").
  Proof.
    eapply OfTy.Make with (A := t); reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Bytecode.
Export (hints) Bytecode.

Module Impl_Bytecode.
  Definition Self : Set :=
    Bytecode.t.

  Instance run_original_bytes (self : '& Self) :
    Run.Trait
      bytecode.Impl_revm_bytecode_bytecode_Bytecode.original_bytes
      [] [] [ φ self ]
      alloy_primitives.bytes.links.mod.Bytes.t.
  Admitted.
  Global Opaque run_original_bytes.
End Impl_Bytecode.
Export (hints) Impl_Bytecode.

(* Module Bytecode.
  Inductive t : Set :=
  | LegacyAnalyzed
    (_ : revm_bytecode.legacy.links.analyzed.LegacyAnalyzedBytecode.t)
  | Eof
    (_ : alloc.links.sync.Arc.t revm_bytecode.links.eof.Eof.t alloc.links.alloc.Global.t)
  | Eip7702
    (_ : revm_bytecode.links.eip7702.Eip7702Bytecode.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "bytecode::Bytecode";
    φ x :=
      match x with
      | LegacyAnalyzed γ0 =>
        Value.StructTuple "bytecode::Bytecode::LegacyAnalyzed" [
          φ γ0
        ]
      | Eof γ0 =>
        Value.StructTuple "bytecode::Bytecode::Eof" [
          φ γ0
        ]
      | Eip7702 γ0 =>
        Value.StructTuple "bytecode::Bytecode::Eip7702" [
          φ γ0
        ]
      end
  }.
End Bytecode. *)

Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.links.result.
Require Import core.links.option.
Require Import revm.revm_bytecode.eof.links.header.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_bytecode.links.eof.
Require Import core.slice.links.mod.

Require Export revm.revm_bytecode.eof.links.body_EofBody.

Module body.
  Module eof.
    Module body.
      Module Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.
        Definition clone : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::clone".

        Axiom Implements :
          M.IsTraitInstance
            "core::clone::Clone"
            [] []
            (Ty.path "revm_bytecode::eof::body::EofBody")
            [ ("clone", InstanceField.Method clone) ].
      End Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.

      Module Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.
        Definition default : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::default".

        Axiom Implements :
          M.IsTraitInstance
            "core::default::Default"
            [] []
            (Ty.path "revm_bytecode::eof::body::EofBody")
            [ ("default", InstanceField.Method default) ].
      End Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.

      Module Impl_revm_bytecode_eof_body_EofBody.
        Definition code : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::code".

        Definition encode : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::encode".

        Definition into_eof : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::into_eof".

        Definition eof_code_section_start : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::eof_code_section_start".

        Definition decode : PolymorphicFunction.t :=
          fun _ _ _ => M.impossible "revm_bytecode::eof::body::EofBody::decode".
      End Impl_revm_bytecode_eof_body_EofBody.
    End body.
  End eof.
End body.

Module Impl_Clone_for_EofBody.
  Definition Self : Set :=
    EofBody.t.

  Instance run_clone (self : '& Self) :
    Run.Trait body.eof.body.Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.clone
      [] [] [φ self]
      Self.
  Proof.
  Admitted.

  Instance method_clone : Clone.Method_clone Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Clone.Run Self := {}.
End Impl_Clone_for_EofBody.
Export (hints) Impl_Clone_for_EofBody.

Module Impl_Default_for_EofBody.
  Definition Self : Set :=
    EofBody.t.

  Instance run_default :
    Run.Trait body.eof.body.Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.default
      [] [] []
      Self.
  Proof.
  Admitted.

  Instance method_default : Default.Method_default Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Default.Run Self := {}.
End Impl_Default_for_EofBody.
Export (hints) Impl_Default_for_EofBody.

Module Impl_EofBody.
  Definition Self : Set := EofBody.t.

  (*
    pub fn code(&self, index: usize) -> Option<Bytes>
  *)
  Instance run_code (self : '& Self) (index : usize) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.code [] [] [φ self; φ index] (option Bytes.t).
  Proof.
    constructor.
    (* destruct (vec.links.mod.Impl_Index_for_Vec_T_A.run usize usize Global.t usize).
    destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := usize) (A := Global.t)). *)
    run_symbolic.
  Admitted.
  Global Opaque run_code.

  (*
    pub fn encode(&self, buffer: &mut Vec<u8>)
  *)
  Instance run_encode (self : '& Self) (buffer : '*mut (Vec.t u8 Global.t)) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.encode [] [] [φ self; φ buffer] unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_encode.

  (*
    pub fn into_eof(self) -> Eof
  *)
  Instance run_into_eof (self : Self) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.into_eof [] [] [φ self] Eof.t.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_into_eof.

  (*
    pub fn eof_code_section_start(&self, idx: usize) -> Option<usize> 
  *)
  Instance run_eof_code_section_start (self : '& Self) (idx : usize) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.eof_code_section_start [] [] [φ self; φ idx] (option usize).
  Proof.
    constructor.
    (* destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := usize) (A := Global.t)).
    destruct deref. *)
    run_symbolic.
  Admitted.
  Global Opaque run_eof_code_section_start.

  (*
    pub fn decode(input: &Bytes, header: &EofHeader) -> Result<Self, EofDecodeError>
  *)
  Instance run_decode (input : '& Bytes.t) (header : '& EofHeader.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.decode [] [] [φ input; φ header] (Result.t EofBody.t EofDecodeError.t).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_decode.
End Impl_EofBody.

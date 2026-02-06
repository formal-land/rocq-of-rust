Require Import links.RocqOfRust.
Require Import core.default.

(*
    pub trait Default: Sized {
        // Required method
        fn default() -> Self;
    }
*)
Module Default.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::default::Default";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_default (Self : Set) `{Link Self} : Set := {
    default : PolymorphicFunction.t;
    default_is_method :: IsTraitMethod.C (trait Self) "default" default;
    run_default :: Run.Trait default [] [] [] Self;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_default :: Method_default Self;
  }.
End Default.
Export (hints) Default.

Module Impl_Default_for_unit.
  Definition Self : Set := unit.

  Instance run_default :
    Run.Trait default.Impl_core_default_Default_for_Tuple_.default [] [] [] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_default.

  Instance method_default : Default.Method_default Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply default.Impl_core_default_Default_for_Tuple_.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Default.Run Self := {}.
End Impl_Default_for_unit.
Export (hints) Impl_Default_for_unit.

Module Impl_Default_for_bool.
  Definition Self : Set := bool.

  Instance run_default :
    Run.Trait default.Impl_core_default_Default_for_bool.default [] [] [] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_default.

  Instance method_default : Default.Method_default Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply default.Impl_core_default_Default_for_bool.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Default.Run Self := {}.
End Impl_Default_for_bool.
Export (hints) Impl_Default_for_bool.

Module Impl_Default_for_char.
  (* TODO *)
End Impl_Default_for_char.
Export (hints) Impl_Default_for_char.

Module Impl_Default_for_integer.
  Definition Self (kind : IntegerKind.t) : Set :=
    Integer.t kind.

  Definition method_of_ingeter_kind (kind : IntegerKind.t) :=
    match kind with
    | IntegerKind.I8 => default.Impl_core_default_Default_for_i8.default
    | IntegerKind.I16 => default.Impl_core_default_Default_for_i16.default
    | IntegerKind.I32 => default.Impl_core_default_Default_for_i32.default
    | IntegerKind.I64 => default.Impl_core_default_Default_for_i64.default
    | IntegerKind.I128 => default.Impl_core_default_Default_for_i128.default
    | IntegerKind.Isize => default.Impl_core_default_Default_for_isize.default
    | IntegerKind.U8 => default.Impl_core_default_Default_for_u8.default
    | IntegerKind.U16 => default.Impl_core_default_Default_for_u16.default
    | IntegerKind.U32 => default.Impl_core_default_Default_for_u32.default
    | IntegerKind.U64 => default.Impl_core_default_Default_for_u64.default
    | IntegerKind.U128 => default.Impl_core_default_Default_for_u128.default
    | IntegerKind.Usize => default.Impl_core_default_Default_for_usize.default
    end.

  Instance run_default (kind : IntegerKind.t) :
    Run.Trait (method_of_ingeter_kind kind) [] [] [] (Self kind).
  Proof.
    constructor.
    destruct kind; run_symbolic.
  Defined.
  Global Opaque run_default.

  Definition implements_of_integer_kind (kind : IntegerKind.t) :
      IsTraitInstance "core::default::Default"
        []
        []
        (Φ (Self kind))
        [("default", InstanceField.Method (method_of_ingeter_kind kind))] :=
    match kind with
    | IntegerKind.I8 => default.Impl_core_default_Default_for_i8.Implements
    | IntegerKind.I16 => default.Impl_core_default_Default_for_i16.Implements
    | IntegerKind.I32 => default.Impl_core_default_Default_for_i32.Implements
    | IntegerKind.I64 => default.Impl_core_default_Default_for_i64.Implements
    | IntegerKind.I128 => default.Impl_core_default_Default_for_i128.Implements
    | IntegerKind.Isize => default.Impl_core_default_Default_for_isize.Implements
    | IntegerKind.U8 => default.Impl_core_default_Default_for_u8.Implements
    | IntegerKind.U16 => default.Impl_core_default_Default_for_u16.Implements
    | IntegerKind.U32 => default.Impl_core_default_Default_for_u32.Implements
    | IntegerKind.U64 => default.Impl_core_default_Default_for_u64.Implements
    | IntegerKind.U128 => default.Impl_core_default_Default_for_u128.Implements
    | IntegerKind.Usize => default.Impl_core_default_Default_for_usize.Implements
    end.

  Instance method_default (kind : IntegerKind.t) : Default.Method_default (Self kind).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply implements_of_integer_kind. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (kind : IntegerKind.t) : Default.Run (Self kind) := {}.
End Impl_Default_for_integer.
Export (hints) Impl_Default_for_integer.

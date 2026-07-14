Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter_Interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

(*
pub struct Instruction<W, H> {
    fn_: fn(InstructionContext<'_, H, W>),
    static_gas: u64,
}
*)
Module Instruction.
  Record t
      (W H : Set) `{Link W} `{Link H}
      (W_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks W_types} :
      Set := {
    fn_ : Function1.t (InstructionContext.t H W W_types) unit;
    static_gas : u64;
  }.
  Arguments t _ _ {_ _} _ {_}.

  Global Instance IsLink
      (W H : Set) `{Link W} `{Link H}
      (W_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks W_types} :
      Link (t W H W_types) := {
    Φ := Ty.apply
      (Ty.path "revm_interpreter::instructions::Instruction")
      []
      [Φ W; Φ H];
    φ x :=
      let '{| fn_ := fn_; static_gas := static_gas |} := x in
      Value.StructRecord
        "revm_interpreter::instructions::Instruction"
        []
        [Φ W; Φ H]
        [
          ("fn_", φ fn_);
          ("static_gas", φ static_gas)
        ];
  }.

  Definition of_ty
      (wire host : Ty.t)
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (wire_of_ty : OfTy.t wire)
      (host_of_ty : OfTy.t host) :
    InterpreterTypes.Run (OfTy.get_Set wire_of_ty) WIRE_types ->
    OfTy.t
      (Ty.apply
        (Ty.path "revm_interpreter::instructions::Instruction")
        []
        [wire; host]).
  Proof.
    intros.
    destruct wire_of_ty as [WireT].
    destruct host_of_ty as [HostT].
    eapply OfTy.Make with (A := t WireT HostT WIRE_types).
    subst.
    reflexivity.
  Defined.
  Smpl Add (unshelve eapply of_ty; [smpl of_ty | smpl of_ty | auto]) : of_ty.

  Module SubPointer.
    Definition get_fn
        {W H : Set} `{Link W} `{Link H}
        {W_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks W_types} :
      SubPointer.Runner.t
        (t W H W_types)
        (Pointer.Index.StructRecord
          "revm_interpreter::instructions::Instruction"
          "fn_") :=
      {|
        SubPointer.Runner.projection x :=
          let '{| fn_ := fn_ |} := x in Some fn_;
        SubPointer.Runner.injection x y :=
          let '{| static_gas := static_gas |} := x in
          Some {| fn_ := y; static_gas := static_gas |};
      |}.

    Lemma get_fn_is_valid
        {W H : Set} `{Link W} `{Link H}
        {W_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks W_types} :
      SubPointer.Runner.Valid.t
        (get_fn (W := W) (H := H) (W_types := W_types)).
    Proof. now constructor. Qed.
    Smpl Add apply get_fn_is_valid : run_sub_pointer.

    Definition get_static_gas
        {W H : Set} `{Link W} `{Link H}
        {W_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks W_types} :
      SubPointer.Runner.t
        (t W H W_types)
        (Pointer.Index.StructRecord
          "revm_interpreter::instructions::Instruction"
          "static_gas") :=
      {|
        SubPointer.Runner.projection x :=
          let '{| static_gas := static_gas |} := x in Some static_gas;
        SubPointer.Runner.injection x y :=
          let '{| fn_ := fn_ |} := x in
          Some {| fn_ := fn_; static_gas := y |};
      |}.

    Lemma get_static_gas_is_valid
        {W H : Set} `{Link W} `{Link H}
        {W_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks W_types} :
      SubPointer.Runner.Valid.t
        (get_static_gas (W := W) (H := H) (W_types := W_types)).
    Proof. now constructor. Qed.
    Smpl Add apply get_static_gas_is_valid : run_sub_pointer.
  End SubPointer.
End Instruction.

(*
pub trait CustomInstruction {
    type Wire: InterpreterTypes;
    type Host;

    fn exec(&self, interpreter: &mut Interpreter<Self::Wire>, host: &mut Self::Host);

    fn from_base(instruction: Instruction<Self::Wire, Self::Host>) -> Self;
}
*)
Module CustomInstruction.
  Definition trait (Self Wire Host : Set) `{Link Self} `{Link Wire} `{Link Host} :
      TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::table::CustomInstruction";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_exec
      (Self : Set) `{Link Self}
      (Wire : Set) `{Link Wire}
      (Wire_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks Wire_types}
      (Host : Set) `{Link Host} :
      Set := {
    exec : PolymorphicFunction.t;
    exec_is_method :: IsTraitMethod.C (trait Self Wire Host) "exec" exec;
    run_exec (self : '& Self) (interpreter : '&mut (Interpreter.t Wire Wire_types)) (host : '&mut Host) ::
      Run.Trait exec [] [] [ φ self; φ interpreter; φ host ] unit;
  }.

  Class Method_from_base
      (Self : Set) `{Link Self}
      (Wire : Set) `{Link Wire}
      (Wire_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks Wire_types}
      (Host : Set) `{Link Host} :
      Set := {
    from_base : PolymorphicFunction.t;
    from_base_is_method :: IsTraitMethod.C (trait Self Wire Host) "from_base" from_base;
    run_from_base (instruction : '& (Instruction.t Wire Host Wire_types)) ::
      Run.Trait from_base [] [] [ φ instruction ] ('& Self);
  }.

  Class Run
      (Self : Set) `{Link Self}
      (Wire : Set) `{Link Wire}
      (Wire_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks Wire_types}
      (Host : Set) `{Link Host} : Set := {
    Wire_IsAssociated :
      IsTraitAssociatedType
      "revm_interpreter::table::CustomInstruction" [] [] (Φ Self)
      "Wire" (Φ Wire);
    run_InterpreterTypes_for_Wire :: InterpreterTypes.Run Wire Wire_types;
    Host_IsAssociated :
      IsTraitAssociatedType
      "revm_interpreter::table::CustomInstruction" [] [] (Φ Self)
      "Host" (Φ Host);
    method_exec :: Method_exec Self Wire Wire_types Host;
    method_from_base :: Method_from_base Self Wire Wire_types Host;
  }.
End CustomInstruction.
Export (hints) CustomInstruction.

Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.links.interpreter_Interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.table.

(*
pub type Instruction<W, H> = for<'a> fn(&'a mut Interpreter<W>, &'a mut H);
*)
Module Instruction.
  Definition t
      (W H : Set) `{Link W} `{Link H}
      (W_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks W_types} :
      Set :=
    Function2.t
      ('&mut (Interpreter.t W W_types))
      ('&mut H)
      unit.
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

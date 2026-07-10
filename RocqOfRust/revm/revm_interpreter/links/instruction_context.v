Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.links.interpreter_Interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instruction_context.

  Module InstructionContext.
  Record t
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Set := {
    interpreter : '&mut (Interpreter.t WIRE WIRE_types);
    host : '&mut H;
  }.
  Arguments t _ _ {_} {_} _ {_}.

  Global Instance IsLink
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Link (t H WIRE WIRE_types) := {
    Φ := Ty.apply
      (Ty.path "revm_interpreter::instruction_context::InstructionContext")
      []
      [Φ H; Φ WIRE];
    φ x :=
      Value.StructRecord
        "revm_interpreter::instruction_context::InstructionContext"
        []
        [Φ H; Φ WIRE]
        [
          ("interpreter", φ x.(interpreter));
          ("host", φ x.(host))
        ];
  }.

  Definition of_ty
      (host wire : Ty.t)
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (host_of_ty : OfTy.t host)
      (wire_of_ty : OfTy.t wire) :
    InterpreterTypes.Run (OfTy.get_Set wire_of_ty) WIRE_types ->
    OfTy.t
      (Ty.apply
        (Ty.path "revm_interpreter::instruction_context::InstructionContext")
        []
        [host; wire]).
  Proof.
    intros.
    destruct host_of_ty as [HostT].
    destruct wire_of_ty as [WIRE].
    eapply OfTy.Make with (A := t HostT WIRE WIRE_types).
    subst.
    reflexivity.
   Defined.
  Smpl Add (unshelve eapply of_ty; [smpl of_ty | smpl of_ty | auto]) : of_ty.

  Module SubPointer.
    Definition get_interpreter
        {H WIRE : Set} `{Link H} `{Link WIRE}
        {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      SubPointer.Runner.t
        (t H WIRE WIRE_types)
        (Pointer.Index.StructRecord
          "revm_interpreter::instruction_context::InstructionContext"
          "interpreter") :=
      {|
        SubPointer.Runner.projection x := Some x.(interpreter);
        SubPointer.Runner.injection x y := Some (x <| interpreter := y |>);
      |}.

  Lemma get_interpreter_is_valid
        {H WIRE : Set} `{Link H} `{Link WIRE}
        {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      SubPointer.Runner.Valid.t
        (get_interpreter (H := H) (WIRE := WIRE) (WIRE_types := WIRE_types)).
    Proof. now constructor. Qed.
    Smpl Add apply get_interpreter_is_valid : run_sub_pointer.

  Definition get_host
        {H WIRE : Set} `{Link H} `{Link WIRE}
        {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      SubPointer.Runner.t
        (t H WIRE WIRE_types)
        (Pointer.Index.StructRecord
          "revm_interpreter::instruction_context::InstructionContext"
          "host") :=
      {|
        SubPointer.Runner.projection x := Some x.(host);
        SubPointer.Runner.injection x y := Some (x <| host := y |>);
      |}.

  Lemma get_host_is_valid
        {H WIRE : Set} `{Link H} `{Link WIRE}
        {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      SubPointer.Runner.Valid.t
        (get_host (H := H) (WIRE := WIRE) (WIRE_types := WIRE_types)).
    Proof. now constructor. Qed.
    Smpl Add apply get_host_is_valid : run_sub_pointer.
  End SubPointer.
End InstructionContext.

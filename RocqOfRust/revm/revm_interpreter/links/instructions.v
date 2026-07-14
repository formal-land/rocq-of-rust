Require Import links.RocqOfRust.
Require Import core.links.array.
Require Import revm.revm_bytecode.links.opcode.
Require Import revm.revm_interpreter.instructions.arithmetic.
Require Import revm.revm_interpreter.instructions.control.
Require Import revm.revm_interpreter.instructions.host.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.links.control.stop.
Require Import revm.revm_interpreter.instructions.links.control.unknown.
(* NOTE: WARNING: there might be future conflicts between the two `Host`s *)
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.host.balance.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.
Require Import revm.revm_interpreter.instructions.

Definition instruction_table_discriminant
    {WIRE H : Set} `{Link WIRE} `{Link H} :
    PolymorphicFunction.t :=
  fun ε τ α =>
    match ε, τ, α with
    | [], [], [] =>
      let table_ty :=
        Ty.apply
          (Ty.path "array")
          [ Value.Integer IntegerKind.Usize 256 ]
          [ Ty.apply (Ty.path "revm_interpreter::instructions::Instruction") [] [ Φ WIRE; Φ H ] ] in
      LowM.Let table_ty
        (instructions.instruction_table_impl [] [ Φ WIRE; Φ H ] [])
        (fun table =>
          match table with
          | inl table => M.alloc table_ty table
          | inr error => LowM.Pure (inr error)
          end)
    | _, _, _ => M.impossible "wrong number of arguments"
    end.

Global Instance Instance_IsFunction_instruction_table_discriminant
    {WIRE H : Set} `{Link WIRE} `{Link H} :
  M.IsFunction.C
    "revm_interpreter::instructions::instruction_table_discriminant"
    (@instruction_table_discriminant WIRE H _ _).
Admitted.

Lemma run_instruction_table_impl_for_discriminant
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types) :
  {{
    instructions.instruction_table_impl [] [ Φ WIRE; Φ H ] []
    🔽
    '* (array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}),
    array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}
  }}.
Admitted.

Instance run_instruction_table_discriminant
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types) :
  Run.Trait
    (@instruction_table_discriminant WIRE H _ _)
    [] [] []
    ('* (array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |})).
Proof.
  constructor.
  change (instruction_table_discriminant [] [] []) with
    (let table_ty :=
      Ty.apply
        (Ty.path "array")
        [ Value.Integer IntegerKind.Usize 256 ]
        [ Ty.apply (Ty.path "revm_interpreter::instructions::Instruction") [] [ Φ WIRE; Φ H ] ] in
    LowM.Let table_ty
      (instructions.instruction_table_impl [] [ Φ WIRE; Φ H ] [])
      (fun table =>
        match table with
        | inl table => M.alloc table_ty table
        | inr error => LowM.Pure (inr error)
        end)).
  unshelve eapply Run.Let.
  { eapply array.of_ty with (length := {| Integer.value := 256 |}).
    { reflexivity. }
    {
      pose (wire_of_ty := @OfTy.Make (Φ WIRE) WIRE H0 eq_refl).
      pose (host_of_ty := @OfTy.Make (Φ H) H H1 eq_refl).
      exact (Instruction.of_ty
        (Φ WIRE) (Φ H) wire_of_ty host_of_ty run_InterpreterTypes_for_WIRE).
    }
  }
  {
    change
      {{
        instructions.instruction_table_impl [] [ Φ WIRE; Φ H ] [] 🔽
        '* (array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}),
        array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}
      }}.
    exact (run_instruction_table_impl_for_discriminant
      (WIRE := WIRE)
      (H := H)
      (WIRE_types := WIRE_types)
      run_InterpreterTypes_for_WIRE).
  }
  { cbn.
    intros [table | []]; run_symbolic. }
Defined.
Global Opaque run_instruction_table_discriminant.

(*
pub const fn instruction_table<WIRE: InterpreterTypes, H: Host + ?Sized>(
) -> [crate::table::Instruction<WIRE, H>; 256]
*)
Instance run_instruction_table
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types) 
    (run_Host_for_H : Host.Run H H_types)
    :
  Run.Trait
    instructions.instruction_table [] [ Φ WIRE; Φ H ] []
    (array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}).
Proof.
  constructor.
  run_symbolic; cbn.
  { typeclasses eauto. }
Defined.
Global Opaque run_instruction_table.

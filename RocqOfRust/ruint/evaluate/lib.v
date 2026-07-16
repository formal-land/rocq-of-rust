Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import ruint.lib.

Definition run_nlimbs (bits : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    Translated.Runtime.empty
    30
    (nlimbs [] [] [Value.Integer IntegerKind.Usize bits]).

Definition run_mask (bits : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    Translated.Runtime.empty
    100
    (mask [] [] [Value.Integer IntegerKind.Usize bits]).

Definition is_integer
    (kind : IntegerKind.t)
    (expected : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done (inl (Value.Integer actual_kind actual)) =>
    andb (IntegerKind.eqb actual_kind kind) (Z.eqb actual expected)
  | _ => false
  end.

Definition check_nlimbs (case : Z * Z) : bool :=
  let '(bits, expected) := case in
  is_integer IntegerKind.Usize expected (run_nlimbs bits).

Definition check_mask (case : Z * Z) : bool :=
  let '(bits, expected) := case in
  is_integer IntegerKind.U64 expected (run_mask bits).

Definition nlimbs_cases : list (Z * Z) :=
  [
    (0, 0);
    (1, 1);
    (63, 1);
    (64, 1);
    (65, 2);
    (127, 2);
    (128, 2);
    (129, 3);
    (255, 4);
    (256, 4);
    (257, 5)
  ].

Definition mask_cases : list (Z * Z) :=
  [
    (0, 0);
    (1, 1);
    (2, 3);
    (7, 127);
    (8, 255);
    (32, 4294967295);
    (63, 9223372036854775807);
    (64, 18446744073709551615);
    (65, 1)
  ].

Fixpoint first_failed_mask
    (cases : list (Z * Z)) :
    option (Z * Translated.Execution.t) :=
  match cases with
  | [] => None
  | (bits, expected) :: cases =>
    let result := run_mask bits in
    if is_integer IntegerKind.U64 expected result then
      first_failed_mask cases
    else
      Some (bits, result)
  end.

Definition first_failure : option (Z * Translated.Execution.t) :=
  if List.forallb check_nlimbs nlimbs_cases then
    first_failed_mask mask_cases
  else
    Some (-1, Translated.Execution.Unsupported "nlimbs case failed").

Parameter assert_none : option (Z * Translated.Execution.t) -> unit.

Definition main : unit :=
  assert_none first_failure.

Extract Constant assert_none =>
  "(function
    | None -> ()
    | Some (bits, Translated.Execution.Unsupported message) ->
      failwith
        (""ruint arithmetic stopped at "" ^ Big_int_Z.string_of_big_int bits ^
          "": "" ^ Pstring.to_string message)
    | Some (bits, Translated.Execution.OutOfFuel) ->
      failwith (""ruint arithmetic ran out of fuel at "" ^ Big_int_Z.string_of_big_int bits)
    | Some (bits, Translated.Execution.Done (Inl (Value.Integer (_, actual)))) ->
      failwith
        (""ruint arithmetic failed at "" ^ Big_int_Z.string_of_big_int bits ^
          "" with "" ^ Big_int_Z.string_of_big_int actual)
    | Some (bits, Translated.Execution.Done _) ->
      failwith
        (""ruint arithmetic returned a non-integer at "" ^ Big_int_Z.string_of_big_int bits))".

Set Extraction Output Directory "evaluate/extracted".
Extraction "ruint.ml" main.

Require Import RocqOfRust.RocqOfRust.
Require Import core.convert.num.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import ruint.algorithms.mod.
Require Import ruint.algorithms.ops.
Require Import ruint.lib.

Definition runtime : Translated.Runtime.t :=
  Translated.Runtime.of_tables
    []
    [
      ("core::convert::From",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "from",
        convert.num.Impl_core_convert_From_u64_for_u128.from);
      ("ruint::algorithms::DoubleWord",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "low",
        algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.low);
      ("ruint::algorithms::DoubleWord",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "high",
        algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.high);
      ("ruint::algorithms::DoubleWord",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "split",
        algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.split)
    ].

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

Definition run_adc (lhs rhs carry : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.ops.adc
      []
      []
      [
        Value.Integer IntegerKind.U64 lhs;
        Value.Integer IntegerKind.U64 rhs;
        Value.Integer IntegerKind.U64 carry
      ]).

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

Definition is_u64_pair
    (expected_low expected_high : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done
      (inl
        (Value.Tuple
          [
            Value.Integer IntegerKind.U64 low;
            Value.Integer IntegerKind.U64 high
          ])) =>
    andb (Z.eqb low expected_low) (Z.eqb high expected_high)
  | _ => false
  end.

Definition check_adc (case : (Z * Z * Z) * (Z * Z)) : bool :=
  let '((lhs, rhs, carry), (expected_low, expected_high)) := case in
  is_u64_pair expected_low expected_high (run_adc lhs rhs carry).

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

Definition adc_cases : list ((Z * Z * Z) * (Z * Z)) :=
  [
    ((1, 2, 3), (6, 0));
    ((18446744073709551615, 1, 0), (0, 1));
    ((18446744073709551615, 18446744073709551615, 1),
      (18446744073709551615, 1))
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

Fixpoint first_failed_adc
    (cases : list ((Z * Z * Z) * (Z * Z)))
    (index : Z) :
    option (Z * Translated.Execution.t) :=
  match cases with
  | [] => None
  | ((lhs, rhs, carry), (expected_low, expected_high)) :: cases =>
    let result := run_adc lhs rhs carry in
    if is_u64_pair expected_low expected_high result then
      first_failed_adc cases (index + 1)
    else
      Some (index, result)
  end.

Definition first_failure : option (Z * Translated.Execution.t) :=
  if List.forallb check_nlimbs nlimbs_cases then
    match first_failed_mask mask_cases with
    | Some failure => Some failure
    | None => first_failed_adc adc_cases 0
    end
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
        (""ruint arithmetic returned an unexpected value at "" ^
          Big_int_Z.string_of_big_int bits))".

Set Extraction Output Directory "evaluate/extracted".
Extraction "ruint.ml" main.

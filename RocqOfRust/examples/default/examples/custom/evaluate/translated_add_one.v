Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.
Require Import examples.default.examples.custom.add_one.

From Stdlib Require Import extraction.Extraction.
From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.
From Stdlib Require Import extraction.ExtrOcamlZInt.
From Stdlib Require Import extraction.ExtrOCamlPString.

Definition run_add_one : Translated.Execution.t :=
  Translated.Evaluate.eval
    20
    (add_one
      nil
      nil
      (cons (Value.Integer IntegerKind.U32 41) nil)).

Definition run_add_one_is_42 : bool :=
  match run_add_one with
  | Translated.Execution.Done (inl (Value.Integer IntegerKind.U32 42)) => true
  | _ => false
  end.

Parameter assert_true : bool -> unit.

Definition main : unit :=
  assert_true run_add_one_is_42.

Extraction Language OCaml.

Extract Constant Ty.t => "unit".
Extract Constant Ty.path => "(fun _ -> ())".
Extract Constant Translated.Evaluate.closure_body =>
  "(fun value ->
    match value with
    | Value.Closure (ExistS (_, body)) ->
      Some ((Obj.magic body : Value.t list -> m))
    | _ -> None)".
Extract Constant assert_true =>
  "(fun value -> if value then () else failwith ""expected add_one(41) = 42"")".

Set Extraction Output Directory "evaluate/extracted".
Extraction "translated_add_one.ml" main.

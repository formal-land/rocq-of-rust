Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.

From Stdlib Require Export extraction.Extraction.
From Stdlib Require Export extraction.ExtrOcamlBasic.
From Stdlib Require Export extraction.ExtrOcamlNatInt.
From Stdlib Require Export extraction.ExtrOcamlZInt.
From Stdlib Require Export extraction.ExtrOCamlPString.

Extraction Language OCaml.

Extract Constant Ty.t => "Pstring.t".
Extract Constant Ty.path => "(fun path -> path)".
Extract Constant Translated.ty_eqb =>
  "(fun left right ->
    String.equal (Pstring.to_string left) (Pstring.to_string right))".
Extract Constant Ty.tuple =>
  "(fun types ->
    Pstring.unsafe_of_string
      (""("" ^ String.concat "","" (Stdlib.List.map Pstring.to_string types) ^ "")""))".
Extract Constant Translated.Stack.address_to_nat =>
  "(fun address -> Some (Obj.magic address : int))".
Extract Constant Translated.Evaluate.closure_body =>
  "(fun value ->
    match value with
    | Value.Closure (ExistS (_, body)) ->
      Some ((Obj.magic body : Value.t list -> m))
    | _ -> None)".

type field = {
  field_name : string;
  field_ty : string;
}

type variant_payload =
  | TuplePayload of field list
  | RecordPayload of field list

type variant = {
  name : string;
  rust_name : string;
  payload : variant_payload;
}

type command =
  | EnumDecl of {
      path : string;
      variants : variant list;
    }
  | RecordDecl of {
      path : string;
      fields : field list;
    }

exception Error of string

let user_error message = raise (Error message)

let compare_field (a : field) (b : field) = String.compare a.field_name b.field_name

let sorted_fields (fields : field list) = List.sort compare_field fields

let validate_unique what names =
  let seen = Hashtbl.create 17 in
  List.iter
    (fun name ->
      if Hashtbl.mem seen name then
        user_error ("duplicate " ^ what ^ " `" ^ name ^ "`");
      Hashtbl.add seen name ())
    names

let validate_fields (fields : field list) =
  validate_unique "field" (List.map (fun (field : field) -> field.field_name) fields)

let validate_variant (variant : variant) =
  match variant.payload with
  | TuplePayload fields | RecordPayload fields -> validate_fields fields

let validate = function
  | RecordDecl { fields; _ } -> validate_fields fields
  | EnumDecl { variants; _ } ->
      validate_unique "variant" (List.map (fun variant -> variant.name) variants);
      List.iter validate_variant variants

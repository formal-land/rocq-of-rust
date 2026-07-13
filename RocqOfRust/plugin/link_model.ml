(* Small AST shared by the vernac command parser and the renderer.  It is
   intentionally textual: types are kept as Rocq source fragments because the
   plugin generates vernacular definitions, not kernel terms directly. *)

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

type record_layout =
  | StructRecord of string
  | StructTuple of string
  | Tuple

type command =
  | EnumDecl of {
      path : string;
      type_params : string list;
      variants : variant list;
    }
  | RecordDecl of {
      layout : record_layout;
      type_params : string list;
      fields : field list;
    }
  | InterpreterTypesRecordDecl of {
      path : string;
      type_params : string list;
      interpreter_types_param : string;
      use_value_type_args : bool;
      fields : field list;
    }

exception Error of string

let user_error (message : string) : 'a = raise (Error message)

let compare_field (a : field) (b : field) : int =
  String.compare a.field_name b.field_name

let sorted_fields (fields : field list) : field list =
  List.sort compare_field fields

(* Catch duplicate names before rendering, so failures point to the compact
   command rather than to a generated definition later in the file. *)
let validate_unique (what : string) (names : string list) : unit =
  let seen = Hashtbl.create 17 in
  List.iter
    (fun name ->
      if Hashtbl.mem seen name then
        user_error ("duplicate " ^ what ^ " `" ^ name ^ "`");
      Hashtbl.add seen name ())
    names

let validate_fields (fields : field list) : unit =
  validate_unique "field" (List.map (fun (field : field) -> field.field_name) fields)

let validate_variant (variant : variant) : unit =
  match variant.payload with
  | TuplePayload fields | RecordPayload fields -> validate_fields fields

let validate (command : command) : unit =
  match command with
  | RecordDecl { type_params; fields; _ } ->
      validate_unique "type parameter" type_params;
      validate_fields fields
  | InterpreterTypesRecordDecl { type_params; interpreter_types_param; fields; _ } ->
      validate_unique "type parameter" (interpreter_types_param :: type_params);
      validate_fields fields
  | EnumDecl { type_params; variants; _ } ->
      validate_unique "type parameter" type_params;
      validate_unique "variant" (List.map (fun variant -> variant.name) variants);
      List.iter validate_variant variants

open Link_model

(* Render compact link declarations into ordinary Rocq sentences.  The plugin
   interprets these sentences immediately, while tests inspect the resulting
   definitions with Print. *)

let quote (s : string) : string = Printf.sprintf "%S" s

let indent (prefix : string) (lines : string list) : string list =
  List.map (fun line -> if line = "" then line else prefix ^ line) lines

let join_lines (lines : string list) : string = String.concat "\n" lines

let semicolon_list (render : 'a -> string) (values : 'a list) : string list =
  let rec aux = function
    | [] -> []
    | [ value ] -> [ render value ]
    | value :: rest -> (render value ^ ";") :: aux rest
  in
  aux values

let path_ty (path : string) : string = "Ty.path " ^ quote path

let ty_args (args : string list) : string =
  match args with
  | [] -> "[]"
  | _ -> "[ " ^ String.concat "; " args ^ " ]"

let path_ty_with_args (path : string) (args : string list) : string =
  match args with
  | [] -> path_ty path
  | _ -> "Ty.apply (" ^ path_ty path ^ ") [] " ^ ty_args args

let type_param_binders (type_params : string list) : string =
  String.concat " " (List.map (fun param -> "(" ^ param ^ " : Set)") type_params)

let type_param_link_binders (type_params : string list) : string =
  String.concat " " (List.map (fun param -> "{H_" ^ param ^ " : Link " ^ param ^ "}") type_params)

let type_param_ty_args (type_params : string list) : string =
  ty_args (List.map (fun param -> "Φ " ^ param) type_params)

let type_param_of_ty_args (type_params : string list) : string =
  ty_args (List.map (fun param -> param ^ "'") type_params)

let type_app (type_params : string list) : string =
  match type_params with
  | [] -> "t"
  | _ -> "(t " ^ String.concat " " type_params ^ ")"

let type_app_of_ty (type_params : string list) : string =
  match type_params with
  | [] -> "t"
  | _ ->
      "(t "
      ^ String.concat " " (List.map (fun param -> "H_" ^ param ^ ".(OfTy.A)") type_params)
      ^ ")"

let field_ty_for_of_ty (type_params : string list) (field_ty : string) : string =
  if List.exists (( = ) field_ty) type_params then
    "H_" ^ field_ty ^ ".(OfTy.A)"
  else
    field_ty

let variant_path (path : string) (variant : variant) : string =
  path ^ "::" ^ variant.rust_name

(* Constructor patterns and values use the user-written field order, matching
   the generated Rocq constructor arguments. *)
let constructor_pattern (variant : variant) : string =
  match variant.payload with
  | TuplePayload fields | RecordPayload fields ->
      String.concat " " (variant.name :: List.map (fun (field : field) -> field.field_name) fields)

let constructor_value ?(type_args = []) (variant : variant) (fields : field list) : string =
  let constructor =
    match type_args with
    | [] -> variant.name
    | _ -> "@" ^ variant.name ^ " " ^ String.concat " " (List.map (fun arg -> "(" ^ arg ^ ")") type_args)
  in
  match fields with
  | [] -> constructor
  | _ ->
      String.concat "\n"
        (constructor
         :: List.map
              (fun field -> "      H_" ^ field.field_name ^ ".(OfValueWith.value)")
              fields)

let render_inductive (type_params : string list) (variants : variant list) : string list =
  let header =
    match type_params with
    | [] -> "Inductive t : Set :="
    | _ -> "Inductive t " ^ type_param_binders type_params ^ " : Set :="
  in
  [ header ]
  @ List.map
      (fun variant ->
        let fields =
          match variant.payload with
          | TuplePayload fields | RecordPayload fields -> fields
        in
        "  | " ^ variant.name
        ^ String.concat ""
            (List.map
               (fun field -> " (" ^ field.field_name ^ " : " ^ field.field_ty ^ ")")
               fields))
      variants
  @ [ "." ]

let render_constructor_arguments (type_params : string list) (variant : variant) : string list =
  match type_params with
  | [] -> []
  | _ ->
      let fields =
        match variant.payload with
        | TuplePayload fields | RecordPayload fields -> fields
      in
      let implicit_params = String.concat " " (List.map (fun param -> "{" ^ param ^ "}") type_params) in
      let field_names = String.concat " " (List.map (fun field -> field.field_name) fields) in
      let suffix =
        if field_names = "" then
          implicit_params
        else
          implicit_params ^ " " ^ field_names
      in
      [ "Arguments " ^ variant.name ^ " " ^ suffix ^ "." ]

let render_record_decl (fields : field list) : string list =
  [ "Record t : Set := {" ]
  @ List.map (fun field -> "  " ^ field.field_name ^ " : " ^ field.field_ty ^ ";") fields
  @ [ "}." ]

let render_record_value
    ?(type_args = "[]") (path : string) (fields : field list) (value_of : field -> string) : string list =
  [ "Value.StructRecord " ^ quote path ^ " [] " ^ type_args ^ " [" ]
  @ indent "  "
      (semicolon_list
         (fun field -> "(" ^ quote field.field_name ^ ", " ^ value_of field ^ ")")
         fields)
  @ [ "]" ]

(* StructRecord values are rendered in sorted field-name order, matching the
   existing Jinja convention and keeping output stable. *)
let render_variant_value (path : string) (type_params : string list) (variant : variant) : string =
  let vpath = variant_path path variant in
  let type_args = type_param_ty_args type_params in
  match variant.payload with
  | TuplePayload fields ->
      "Value.StructTuple " ^ quote vpath ^ " [] " ^ type_args ^ " ["
      ^ String.concat "; " (List.map (fun field -> "φ " ^ field.field_name) fields)
      ^ "]"
  | RecordPayload fields ->
      join_lines
        (render_record_value ~type_args vpath (sorted_fields fields)
           (fun field -> "φ " ^ field.field_name))

let render_enum_link (path : string) (type_params : string list) (variants : variant list) : string list =
  let instance_head =
    match type_params with
    | [] -> "Instance IsLink : Link t := {"
    | _ ->
        "Instance IsLink "
        ^ type_param_binders type_params ^ " "
        ^ type_param_link_binders type_params
        ^ " : Link " ^ type_app type_params ^ " := {"
  in
  [ instance_head;
    "  Φ := " ^ path_ty_with_args path (List.map (fun param -> "Φ " ^ param) type_params) ^ ";";
    "  φ x :=";
    "    match x with" ]
  @ List.concat
      (List.map
         (fun variant ->
           [ "    | " ^ constructor_pattern variant ^ " =>" ]
           @ indent "        "
               (String.split_on_char '\n' (render_variant_value path type_params variant)))
         variants)
  @ [ "    end";
      "}." ]

let render_record_link (path : string) (fields : field list) : string list =
  [ "Instance IsLink : Link t := {";
    "  Φ := " ^ path_ty path ^ ";";
    "  φ x :=" ]
  @ indent "    "
      (render_record_value path (sorted_fields fields)
         (fun field -> "φ x.(" ^ field.field_name ^ ")"))
  @ [ "}." ]

let render_of_ty (path : string) : string list =
  [ "Instance IsOfTy : OfTy.C (" ^ path_ty path ^ ") := {";
    "  A := t;";
    "  eq := eq_refl;";
    "}." ]

let render_enum_of_ty (path : string) (type_params : string list) : string list =
  match type_params with
  | [] -> render_of_ty path
  | _ ->
      let params =
        List.map
          (fun param -> "(" ^ param ^ "' : Ty.t) {H_" ^ param ^ " : OfTy.C " ^ param ^ "'}")
          type_params
      in
      [ "Instance IsOfTy" ]
      @ List.map (fun param -> "    " ^ param) params
      @ [ "    : OfTy.C ("
          ^ path_ty_with_args path (List.map (fun param -> param ^ "'") type_params)
          ^ ") := {";
          "  A := " ^ type_app_of_ty type_params ^ ";";
          "  eq := ltac:(sauto lq: on);";
          "}." ]

let render_enum_inductive_of_ty (path : string) (type_params : string list) : string list =
  match type_params with
  | [] -> []
  | _ ->
      let ty_params = List.map (fun param -> param ^ "'") type_params in
      let intros = List.map (fun param -> "[" ^ param ^ "]") type_params in
      [ "Definition of_ty " ^ String.concat " " ty_params ^ " :";
        "  "
        ^ String.concat " -> "
            (List.map
               (fun param -> "OfTy.t " ^ param)
               ty_params
             @ [ "OfTy.t ("
                 ^ path_ty_with_args path ty_params
                 ^ ")" ])
        ^ " :=";
        "  ltac:(intros " ^ String.concat " " intros
        ^ "; eapply OfTy.Make with (A := " ^ type_app type_params
        ^ "); subst; reflexivity).";
        "Smpl Add eapply of_ty : of_ty." ]

let render_instance_params ?(type_params = []) ?(use_of_ty = false) (fields : field list) : string list =
  List.map
    (fun field ->
      let field_ty =
        if use_of_ty then
          field_ty_for_of_ty type_params field.field_ty
        else
          field.field_ty
      in
      "    (" ^ field.field_name ^ "' : Value.t) {H_" ^ field.field_name
      ^ " : OfValueWith.C (" ^ field_ty ^ ") " ^ field.field_name ^ "'}")
    fields

let render_value_fields ?(type_args = "[]") (path : string) (fields : field list) : string list =
  render_record_value ~type_args path fields (fun (field : field) -> field.field_name ^ "'")

(* Record constructors still receive fields in declaration order; only the
   StructRecord value used for matching is sorted. *)
let render_record_of_value
    (kind : [ `Plain | `With ]) (path : string) (fields : field list) : string list =
  let sorted = sorted_fields fields in
  let head =
    match kind with
    | `With -> "Instance IsOfValueWith"
    | `Plain -> "Instance IsOfValue"
  in
  let class_head =
    match kind with
    | `With -> "OfValueWith.C t"
    | `Plain -> "OfValue.C"
  in
  [ head ]
  @ render_instance_params sorted
  @ [ "    :";
      "  " ^ class_head ^ " (" ]
  @ indent "    " (render_value_fields path sorted)
  @ [ "  ) := {";
      "  value := Build_t" ]
  @ List.map
      (fun field -> "    H_" ^ field.field_name ^ ".(OfValueWith.value)")
      fields
  @ [ "  ;";
      "  eq := ltac:(sauto lq: on);";
      "}." ]

let render_enum_of_value
    (kind : [ `Plain | `With ]) (path : string) (type_params : string list) (variant : variant) : string list =
  let fields =
    match variant.payload with
    | TuplePayload fields -> fields
    | RecordPayload fields -> sorted_fields fields
  in
  let constructor_fields =
    match variant.payload with
    | TuplePayload fields | RecordPayload fields -> fields
  in
  let vpath = variant_path path variant in
  let head =
    match kind with
    | `With -> "Instance IsOfValueWith_" ^ variant.name
    | `Plain -> "Instance IsOfValue_" ^ variant.name
  in
  let class_head =
    match kind with
    | `With -> "OfValueWith.C " ^ type_app type_params
    | `Plain -> "OfValue.C"
  in
  let params =
    match kind with
    | `With ->
        (match type_params with
         | [] -> []
         | _ ->
             [ "    "
               ^ type_param_binders type_params
               ^ " "
               ^ type_param_link_binders type_params ])
    | `Plain ->
        List.map
          (fun param -> "    (" ^ param ^ "' : Ty.t) {H_" ^ param ^ " : OfTy.C " ^ param ^ "'}")
          type_params
  in
  let type_args =
    match kind with
    | `With -> type_param_ty_args type_params
    | `Plain -> type_param_of_ty_args type_params
  in
  let constructor_type_args =
    match kind with
    | `With -> type_params
    | `Plain -> List.map (fun param -> "H_" ^ param ^ ".(OfTy.A)") type_params
  in
  let of_value_body_prefix =
    match kind with
    | `With -> []
    | `Plain -> [ "  A := " ^ type_app_of_ty type_params ^ ";" ]
  in
  let no_field_eq =
    match kind, type_params with
    | `Plain, _ :: _ -> "ltac:(sauto lq: on)"
    | _ -> "eq_refl"
  in
  let value_lines =
    match variant.payload with
    | TuplePayload fields ->
        [ "Value.StructTuple " ^ quote vpath ^ " [] " ^ type_args ^ " ["
          ^ String.concat "; " (List.map (fun (field : field) -> field.field_name ^ "'") fields)
          ^ "]" ]
    | RecordPayload fields -> render_value_fields ~type_args vpath (sorted_fields fields)
  in
  if fields = [] then
    [ head ]
    @ params
    @ [ "    :";
      "  " ^ class_head ^ " (Value.StructTuple " ^ quote vpath ^ " [] " ^ type_args ^ " []) := {" ]
    @ of_value_body_prefix
    @ [ "  value := " ^ constructor_value ~type_args:constructor_type_args variant [] ^ ";";
      "  eq := " ^ no_field_eq ^ ";";
      "}." ]
  else
    [ head ]
    @ params
    @ render_instance_params ~type_params ~use_of_ty:(kind = `Plain) fields
    @ [ "    :";
        "  " ^ class_head ^ " (" ]
    @ indent "    " value_lines
    @ [ "  ) := {" ]
    @ of_value_body_prefix
    @ [ "  value := " ^ constructor_value ~type_args:constructor_type_args variant constructor_fields;
        "  ;";
        "  eq := ltac:(sauto lq: on);";
        "}." ]

(* SubPointer proofs are emitted as proof terms with ltac:(...), because the
   plugin interprets complete vernacular sentences rather than entering proof
   mode for generated tactic commands. *)
let render_record_subpointer (path : string) (field : field) : string list =
  let get = "get_" ^ field.field_name in
  [ "Definition " ^ get ^ " : SubPointer.Runner.t t";
    "  (Pointer.Index.StructRecord " ^ quote path ^ " " ^ quote field.field_name ^ ") :=";
    "{|";
    "  SubPointer.Runner.projection x := Datatypes.Some x.(" ^ field.field_name ^ ");";
    "  SubPointer.Runner.injection x y := Datatypes.Some (x <| " ^ field.field_name ^ " := y |>);";
    "|}.";
    "";
    "Definition " ^ get ^ "_is_valid :";
    "  SubPointer.Runner.Valid.t " ^ get ^ " :=";
    "  ltac:(now constructor).";
    "Smpl Add apply " ^ get ^ "_is_valid : run_sub_pointer." ]

let render_enum_subpointer
    (path : string) (type_params : string list) (variant : variant) (index : int) (field : field) : string list =
  let vpath = variant_path path variant in
  let is_record =
    match variant.payload with
    | RecordPayload _ -> true
    | TuplePayload _ -> false
  in
  let index_expr =
    if is_record then
      "Pointer.Index.StructRecord " ^ quote vpath ^ " " ^ quote field.field_name
    else
      "Pointer.Index.StructTuple " ^ quote vpath ^ " " ^ string_of_int index
  in
  let get =
    if is_record then
      "get_" ^ variant.name ^ "_" ^ field.field_name
    else
      "get_" ^ variant.name ^ "_" ^ string_of_int index
  in
  let fields =
    match variant.payload with
    | TuplePayload fields | RecordPayload fields -> fields
  in
  let projection_pattern = constructor_pattern variant in
  let injection_pattern =
    String.concat " "
      (variant.name
       :: List.mapi
            (fun i f -> if i = index then "_" else f.field_name)
            fields)
  in
  let injected =
    String.concat " "
      (variant.name
       :: List.mapi
            (fun i f -> if i = index then "y" else f.field_name)
            fields)
  in
  let definition_head =
    match type_params with
    | [] -> "Definition " ^ get ^ " : SubPointer.Runner.t t"
    | _ ->
        "Definition " ^ get ^ " "
        ^ type_param_binders type_params ^ " "
        ^ type_param_link_binders type_params
        ^ " : SubPointer.Runner.t " ^ type_app type_params
  in
  let get_applied =
    match type_params with
    | [] -> get
    | _ -> "(" ^ get ^ " " ^ String.concat " " type_params ^ ")"
  in
  let validity_head =
    match type_params with
    | [] -> "Definition " ^ get ^ "_is_valid :"
    | _ ->
        "Definition " ^ get ^ "_is_valid "
        ^ type_param_binders type_params ^ " "
        ^ type_param_link_binders type_params
        ^ " :"
  in
  [ definition_head;
    "  (" ^ index_expr ^ ") :=";
    "{|";
    "  SubPointer.Runner.projection x :=";
    "    match x with";
    "    | " ^ projection_pattern ^ " => Datatypes.Some " ^ field.field_name;
    "    | _ => Datatypes.None";
    "    end;";
    "  SubPointer.Runner.injection x y :=";
    "    match x with";
    "    | " ^ injection_pattern ^ " => Datatypes.Some (" ^ injected ^ ")";
    "    | _ => Datatypes.None";
    "    end;";
    "|}.";
    "";
    validity_head;
    "  SubPointer.Runner.Valid.t " ^ get_applied ^ " :=";
    "  ltac:(constructor; intros; destruct a; try reflexivity; discriminate).";
    "Smpl Add apply " ^ get ^ "_is_valid : run_sub_pointer." ]

let render_subpointer_module (body : string list) : string list =
  [ "Module SubPointer." ] @ indent "  " body @ [ "End SubPointer." ]

(* Top-level renderers validate first so all downstream functions can assume a
   well-formed declaration. *)
let render_record (path : string) (fields : field list) : string list =
  validate (RecordDecl { path; fields });
  render_record_decl fields
  @ [ "" ]
  @ render_record_link path fields
  @ [ "" ]
  @ render_of_ty path
  @ [ "" ]
  @ render_record_of_value `With path fields
  @ [ "" ]
  @ render_record_of_value `Plain path fields
  @ [ "" ]
  @ render_subpointer_module
      (List.concat
         (List.mapi
            (fun i field ->
              let lines = render_record_subpointer path field in
              if i = List.length fields - 1 then lines else lines @ [ "" ])
            fields))

let render_enum (path : string) (type_params : string list) (variants : variant list) : string list =
  validate (EnumDecl { path; type_params; variants });
  render_inductive type_params variants
  @ List.concat (List.map (render_constructor_arguments type_params) variants)
  @ [ "" ]
  @ render_enum_link path type_params variants
  @ [ "" ]
  @ render_enum_of_ty path type_params
  @ [ "" ]
  @ render_enum_inductive_of_ty path type_params
  @ [ "" ]
  @ List.concat
      (List.map
         (fun variant ->
           render_enum_of_value `With path type_params variant
           @ [ "" ]
           @ render_enum_of_value `Plain path type_params variant
           @ [ "" ])
         variants)
  @ render_subpointer_module
      (List.concat
         (List.map
            (fun variant ->
              let fields =
                match variant.payload with
                | TuplePayload fields | RecordPayload fields -> fields
              in
              List.concat
                (List.mapi
                   (fun i field -> render_enum_subpointer path type_params variant i field @ [ "" ])
                   fields))
            variants))

let render (command : command) : string list =
  match command with
  | RecordDecl { path; fields } -> render_record path fields
  | EnumDecl { path; type_params; variants } -> render_enum path type_params variants

open Link_model

let quote s = Printf.sprintf "%S" s

let indent prefix lines =
  List.map (fun line -> if line = "" then line else prefix ^ line) lines

let join_lines lines = String.concat "\n" lines

let semicolon_list render values =
  let rec aux = function
    | [] -> []
    | [ value ] -> [ render value ]
    | value :: rest -> (render value ^ ";") :: aux rest
  in
  aux values

let path_ty path = "Ty.path " ^ quote path

let variant_path path variant = path ^ "::" ^ variant.rust_name

let constructor_pattern variant =
  match variant.payload with
  | TuplePayload fields | RecordPayload fields ->
      String.concat " " (variant.name :: List.map (fun (field : field) -> field.field_name) fields)

let constructor_value variant fields =
  match fields with
  | [] -> variant.name
  | _ ->
      String.concat "\n"
        (variant.name
         :: List.map
              (fun field -> "      H_" ^ field.field_name ^ ".(OfValueWith.value)")
              fields)

let render_inductive variants =
  [ "Inductive t : Set :=" ]
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

let render_record_decl fields =
  [ "Record t : Set := {" ]
  @ List.map (fun field -> "  " ^ field.field_name ^ " : " ^ field.field_ty ^ ";") fields
  @ [ "}." ]

let render_record_value path fields value_of =
  [ "Value.StructRecord " ^ quote path ^ " [] [] [" ]
  @ indent "  "
      (semicolon_list
         (fun field -> "(" ^ quote field.field_name ^ ", " ^ value_of field ^ ")")
         fields)
  @ [ "]" ]

let render_variant_value path variant =
  let vpath = variant_path path variant in
  match variant.payload with
  | TuplePayload fields ->
      "Value.StructTuple " ^ quote vpath ^ " [] [] ["
      ^ String.concat "; " (List.map (fun field -> "φ " ^ field.field_name) fields)
      ^ "]"
  | RecordPayload fields ->
      join_lines
        (render_record_value vpath (sorted_fields fields)
           (fun field -> "φ " ^ field.field_name))

let render_enum_link path variants =
  [ "Instance IsLink : Link t := {";
    "  Φ := " ^ path_ty path ^ ";";
    "  φ x :=";
    "    match x with" ]
  @ List.concat
      (List.map
         (fun variant ->
           [ "    | " ^ constructor_pattern variant ^ " =>" ]
           @ indent "        "
               (String.split_on_char '\n' (render_variant_value path variant)))
         variants)
  @ [ "    end";
      "}." ]

let render_record_link path fields =
  [ "Instance IsLink : Link t := {";
    "  Φ := " ^ path_ty path ^ ";";
    "  φ x :=" ]
  @ indent "    "
      (render_record_value path (sorted_fields fields)
         (fun field -> "φ x.(" ^ field.field_name ^ ")"))
  @ [ "}." ]

let render_of_ty path =
  [ "Instance IsOfTy : OfTy.C (" ^ path_ty path ^ ") := {";
    "  A := t;";
    "  eq := eq_refl;";
    "}." ]

let render_instance_params fields =
  List.map
    (fun field ->
      "    (" ^ field.field_name ^ "' : Value.t) {H_" ^ field.field_name
      ^ " : OfValueWith.C (" ^ field.field_ty ^ ") " ^ field.field_name ^ "'}")
    fields

let render_value_fields path fields =
  render_record_value path fields (fun (field : field) -> field.field_name ^ "'")

let render_record_of_value kind path fields =
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

let render_enum_of_value kind path variant =
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
    | `With -> "OfValueWith.C t"
    | `Plain -> "OfValue.C"
  in
  let value_lines =
    match variant.payload with
    | TuplePayload fields ->
        [ "Value.StructTuple " ^ quote vpath ^ " [] [] ["
          ^ String.concat "; " (List.map (fun (field : field) -> field.field_name ^ "'") fields)
          ^ "]" ]
    | RecordPayload fields -> render_value_fields vpath (sorted_fields fields)
  in
  if fields = [] then
    [ head ^ " :";
      "  " ^ class_head ^ " (Value.StructTuple " ^ quote vpath ^ " [] [] []) := {";
      "  value := " ^ variant.name ^ ";";
      "  eq := eq_refl;";
      "}." ]
  else
    [ head ]
    @ render_instance_params fields
    @ [ "    :";
        "  " ^ class_head ^ " (" ]
    @ indent "    " value_lines
    @ [ "  ) := {";
        "  value := " ^ constructor_value variant constructor_fields;
        "  ;";
        "  eq := ltac:(sauto lq: on);";
        "}." ]

let render_record_subpointer path field =
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

let render_enum_subpointer path variant index field =
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
  [ "Definition " ^ get ^ " : SubPointer.Runner.t t";
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
    "Definition " ^ get ^ "_is_valid :";
    "  SubPointer.Runner.Valid.t " ^ get ^ " :=";
    "  ltac:(constructor; intros; destruct a; try reflexivity; discriminate).";
    "Smpl Add apply " ^ get ^ "_is_valid : run_sub_pointer." ]

let render_subpointer_module body =
  [ "Module SubPointer." ] @ indent "  " body @ [ "End SubPointer." ]

let render_record path fields =
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

let render_enum path variants =
  validate (EnumDecl { path; variants });
  render_inductive variants
  @ [ "" ]
  @ render_enum_link path variants
  @ [ "" ]
  @ render_of_ty path
  @ [ "" ]
  @ List.concat
      (List.map
         (fun variant ->
           render_enum_of_value `With path variant
           @ [ "" ]
           @ render_enum_of_value `Plain path variant
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
                   (fun i field -> render_enum_subpointer path variant i field @ [ "" ])
                   fields))
            variants))

let render = function
  | RecordDecl { path; fields } -> render_record path fields
  | EnumDecl { path; variants } -> render_enum path variants

let render_text command = join_lines (render command) ^ "\n"

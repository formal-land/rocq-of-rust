let () : unit = Mltop.add_known_module "rocqofrust_link_plugin"

open Procq
open Stdarg
open Pp

(* Register two vernacular commands:
   - RocqOfRustLinkRecord
   - RocqOfRustLinkEnum
   They parse a compact declaration, render ordinary Rocq sentences, then
   interpret those sentences at the command location. *)

let plugin_name : string = "rocqofrust_link_plugin"

let string_of_id (id : Names.Id.t) : string = Names.Id.to_string id

(* The command grammar accepts normal Rocq constr syntax for field types.  We
   keep the pretty-printed source form so the renderer can emit definitions
   through the regular vernacular parser. *)
let string_of_constr_expr (expr : Constrexpr.constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Pp.string_of_ppcmds (Ppconstr.pr_constr_expr env sigma expr)

let user_err (message : string) : 'a = CErrors.user_err (Pp.str message)

let convert_error (f : 'a -> 'b) (x : 'a) : 'b =
  try f x with
  | Link_model.Error message -> user_err message

let token (s : string) : ('a, Gramlib.Grammar.norec, string) Procq.Symbol.t =
  Symbol.token (terminal s)

(* Separators are generic grammar symbols.  Their phantom result type is fixed
   by the list parser that consumes them. *)
let semi : (Link_model.field list, Gramlib.Grammar.norec, unit) Procq.Symbol.t =
  Symbol.rules
    [ Rules.make
        (Rule.next_norec Rule.stop (token ";"))
        (fun _ _loc -> ())
    ]

let comma : (Link_model.field list, Gramlib.Grammar.norec, unit) Procq.Symbol.t =
  Symbol.rules
    [ Rules.make
        (Rule.next_norec Rule.stop (token ","))
        (fun _ _loc -> ())
    ]

let comma_type_param : (string list, Gramlib.Grammar.norec, unit) Procq.Symbol.t =
  Symbol.rules
    [ Rules.make
        (Rule.next_norec Rule.stop (token ","))
        (fun _ _loc -> ())
    ]

let pr_field (field : Link_model.field) : Pp.t =
  Pp.str field.Link_model.field_name ++ Pp.str " : " ++ Pp.str field.field_ty

let pr_field_list (fields : Link_model.field list) : Pp.t =
  Pp.str "{"
  ++ Pp.prlist_with_sep Pp.pr_semicolon pr_field fields
  ++ Pp.str "}"

let pr_type_params (type_params : string list) : Pp.t =
  Pp.str "["
  ++ Pp.prlist_with_sep Pp.pr_comma Pp.str type_params
  ++ Pp.str "]"

(* Field grammar: [name : type]. *)
let (wit_link_field, link_field) :
    Link_model.field Genarg.vernac_genarg_type * Link_model.field Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_field"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules
          [
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next Rule.stop (Symbol.nterm Prim.ident))
                    (token ":"))
                 (Symbol.nterm Constr.constr))
              (fun ty _ name _loc ->
                { Link_model.field_name = string_of_id name;
                  field_ty = string_of_constr_expr ty;
                });
          ];
      arg_printer = (fun _env _sigma -> pr_field);
    }

(* Shared grammar for semicolon-separated field lists without delimiters. *)
let (wit_link_fields, link_fields) :
    Link_model.field list Genarg.vernac_genarg_type * Link_model.field list Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_fields"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules
          [
            Production.make
              (Rule.next_norec Rule.stop
                 (Symbol.list1sep (Symbol.nterm link_field) semi true))
              (fun fields _loc -> fields);
          ];
      arg_printer =
        (fun _env _sigma fields ->
          Pp.prlist_with_sep Pp.pr_semicolon pr_field fields);
    }

let (wit_link_type_params, link_type_params) :
    string list Genarg.vernac_genarg_type * string list Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_type_params"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules
          [
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next Rule.stop (token "["))
                    (Symbol.list1sep (Symbol.nterm Prim.ident) comma_type_param true))
                 (token "]"))
              (fun _ params _ _loc -> List.map string_of_id params);
          ];
      arg_printer = (fun _env _sigma -> pr_type_params);
    }

let (wit_link_ident, link_ident) :
    Names.Id.t Genarg.vernac_genarg_type * Names.Id.t Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_ident"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules
          [
            Production.make
              (Rule.next Rule.stop (Symbol.nterm Prim.ident))
              (fun name _loc -> name);
          ];
      arg_printer = (fun _env _sigma id -> Pp.str (string_of_id id));
    }

(* Delimited field lists are reused for record declarations and record-like
   enum variants. *)
let fields_between
    (open_token : string) (close_token : string) : Link_model.field list Procq.Production.t =
  Production.make
    (Rule.next
       (Rule.next
          (Rule.next Rule.stop (token open_token))
          (Symbol.nterm link_fields))
       (token close_token))
    (fun _ fields _ _loc -> fields)

let (wit_link_record_fields, link_record_fields) :
    Link_model.field list Genarg.vernac_genarg_type * Link_model.field list Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_record_fields"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules [ fields_between "{" "}" ];
      arg_printer = (fun _env _sigma -> pr_field_list);
    }

(* Tuple payloads accept either semicolon or comma separators to make compact
   declarations convenient in both record-like and tuple-like styles. *)
let (wit_link_tuple_fields, link_tuple_fields) :
    Link_model.field list Genarg.vernac_genarg_type * Link_model.field list Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_tuple_fields"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules
          [
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next Rule.stop (token "("))
                    (Symbol.list1sep (Symbol.nterm link_field) semi true))
                 (token ")"))
              (fun _ fields _ _loc -> fields);
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next Rule.stop (token "("))
                    (Symbol.list1sep (Symbol.nterm link_field) comma true))
                 (token ")"))
              (fun _ fields _ _loc -> fields);
          ];
      arg_printer = (fun _env _sigma fields ->
        Pp.str "("
        ++ Pp.prlist_with_sep Pp.pr_semicolon pr_field fields
        ++ Pp.str ")");
    }

let variant
    (name : Names.Id.t) (rust_name : string) (payload : Link_model.variant_payload) :
    Link_model.variant =
  { Link_model.name = string_of_id name;
    rust_name;
    payload;
  }

let variant_default
    (name : Names.Id.t) (payload : Link_model.variant_payload) : Link_model.variant =
  variant name (string_of_id name) payload

(* Variant grammar always starts with [|].  The optional [as "RustName"] keeps
   the Rocq constructor name independent from the Rust path component. *)
let (wit_link_variant, link_variant) :
    Link_model.variant Genarg.vernac_genarg_type * Link_model.variant Procq.Entry.t =
  Vernacextend.vernac_argument_extend ~plugin:plugin_name ~name:"rocqofrust_link_variant"
    {
      Vernacextend.arg_parsing =
        Vernacextend.Arg_rules
          [
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next
                       (Rule.next
                          (Rule.next Rule.stop (token "|"))
                          (Symbol.nterm Prim.ident))
                       (token "as"))
                    (Symbol.nterm Prim.string))
                 (Symbol.nterm link_record_fields))
              (fun fields rust_name _ name _ _loc ->
                variant name rust_name (Link_model.RecordPayload fields));
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next
                       (Rule.next
                          (Rule.next Rule.stop (token "|"))
                          (Symbol.nterm Prim.ident))
                       (token "as"))
                    (Symbol.nterm Prim.string))
                 (Symbol.nterm link_tuple_fields))
              (fun fields rust_name _ name _ _loc ->
                variant name rust_name (Link_model.TuplePayload fields));
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next Rule.stop (token "|"))
                    (Symbol.nterm Prim.ident))
                 (Symbol.nterm link_record_fields))
              (fun fields name _ _loc ->
                variant_default name (Link_model.RecordPayload fields));
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next Rule.stop (token "|"))
                    (Symbol.nterm Prim.ident))
                 (Symbol.nterm link_tuple_fields))
              (fun fields name _ _loc ->
                variant_default name (Link_model.TuplePayload fields));
            Production.make
              (Rule.next
                 (Rule.next
                    (Rule.next
                       (Rule.next Rule.stop (token "|"))
                       (Symbol.nterm Prim.ident))
                    (token "as"))
                 (Symbol.nterm Prim.string))
              (fun rust_name _ name _ _loc ->
                variant name rust_name (Link_model.TuplePayload []));
            Production.make
              (Rule.next
                 (Rule.next Rule.stop (token "|"))
                 (Symbol.nterm Prim.ident))
              (fun name _ _loc ->
                variant_default name (Link_model.TuplePayload []));
          ];
      arg_printer = (fun _env _sigma variant ->
        Pp.str variant.Link_model.name);
    }

(* The renderer returns lines, not sentences.  Grouping by final dots keeps
   multiline definitions intact before calling Rocq's vernacular parser. *)
let parse_vernac (sentence : string) : Vernacexpr.vernac_control =
  match Procq.parse_string (Pvernac.main_entry None) sentence with
  | Some command -> command
  | None -> user_err ("empty generated Rocq sentence: " ^ sentence)

let line_ends_sentence (line : string) : bool =
  let line = String.trim line in
  let len = String.length line in
  len > 0 && line.[len - 1] = '.'

let generated_sentences (lines : string list) : string list =
  let rec loop sentences pending = function
    | [] -> (
        match pending with
        | [] -> List.rev sentences
        | _ ->
            user_err
              ("generated Rocq sentence is missing a final dot: "
              ^ String.concat "\n" (List.rev pending)))
    | line :: rest ->
        if pending = [] && String.trim line = "" then
          loop sentences [] rest
        else
          let pending = line :: pending in
          if line_ends_sentence line then
            loop (String.concat "\n" (List.rev pending) :: sentences) [] rest
          else
            loop sentences pending rest
  in
  loop [] [] lines

(* Interpret generated sentences in the current vernacular state so the compact
   command behaves as if the expanded definitions had been written inline. *)
let interp_vernac (sentence : string) : unit =
  try
    let command = parse_vernac sentence in
    let st = Vernacstate.freeze_full_state () in
    let st = Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~verbosely:false ~st command in
    Vernacstate.unfreeze_full_state st
  with exn ->
    user_err
      ("error while interpreting generated Rocq sentence:\n"
      ^ sentence ^ "\n\n" ^ Printexc.to_string exn)

let run_generated (command : Link_model.command) : unit =
  convert_error Link_render.render command
  |> generated_sentences
  |> List.iter interp_vernac

let command_typed_vernac (command : Link_model.command) : Vernactypes.typed_vernac =
  Vernactypes.vtdefault (fun () -> run_generated command)

(* Top-level record command.  Braces live in the command grammar rather than in
   a custom nonterminal so the vernacular parser recognizes the command head
   reliably after [:=]. *)
let () : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command:"RocqOfRustLinkRecord"
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "RocqOfRustLinkRecord",
              Vernacextend.TyNonTerminal
                ( Extend.TUentry (Genarg.get_arg_tag wit_string),
                  Vernacextend.TyTerminal
                    ( ":=",
                      Vernacextend.TyTerminal
                        ( "{",
                          Vernacextend.TyNonTerminal
                            ( Extend.TUentry (Genarg.get_arg_tag wit_link_fields),
                              Vernacextend.TyTerminal ("}", Vernacextend.TyNil) ) ) ) ) ),
          (fun path fields ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac
              (Link_model.RecordDecl
                 { layout = Link_model.StructRecord path; type_params = []; fields })),
          None );
    ]

(* Rust tuple-struct command.  This handles structs such as [OpCode(u8)] whose
   link type has a path but whose value uses [Value.StructTuple]. *)
let () : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command:"RocqOfRustLinkTupleStruct"
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "RocqOfRustLinkTupleStruct",
              Vernacextend.TyNonTerminal
                ( Extend.TUentry (Genarg.get_arg_tag wit_string),
                  Vernacextend.TyTerminal
                    ( ":=",
                      Vernacextend.TyTerminal
                        ( "{",
                          Vernacextend.TyNonTerminal
                            ( Extend.TUentry (Genarg.get_arg_tag wit_link_fields),
                              Vernacextend.TyTerminal ("}", Vernacextend.TyNil) ) ) ) ) ),
          (fun path fields ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac
              (Link_model.RecordDecl
                 { layout = Link_model.StructTuple path; type_params = []; fields })),
          None );
    ]

(* Plain tuple-value command.  This handles helper records whose link type is a
   [Ty.tuple] and whose values are [Value.Tuple], without a Rust path. *)
let () : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command:"RocqOfRustLinkTupleRecord"
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "RocqOfRustLinkTupleRecord",
              Vernacextend.TyTerminal
                ( ":=",
                  Vernacextend.TyTerminal
                    ( "{",
                      Vernacextend.TyNonTerminal
                        ( Extend.TUentry (Genarg.get_arg_tag wit_link_fields),
                          Vernacextend.TyTerminal ("}", Vernacextend.TyNil) ) ) ) ),
          (fun fields ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac
              (Link_model.RecordDecl
                 { layout = Link_model.Tuple; type_params = []; fields })),
          None );
    ]

(* Generic record command.  This handles Rust structs such as [Foo<T>] whose
   link type is represented with [Ty.apply] and whose StructRecord values carry
   type arguments. *)
let () : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command:"RocqOfRustLinkGenericRecord"
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "RocqOfRustLinkGenericRecord",
              Vernacextend.TyNonTerminal
                ( Extend.TUentry (Genarg.get_arg_tag wit_string),
                  Vernacextend.TyNonTerminal
                    ( Extend.TUentry (Genarg.get_arg_tag wit_link_type_params),
                      Vernacextend.TyTerminal
                        ( ":=",
                          Vernacextend.TyTerminal
                            ( "{",
                              Vernacextend.TyNonTerminal
                                ( Extend.TUentry (Genarg.get_arg_tag wit_link_fields),
                                  Vernacextend.TyTerminal ("}", Vernacextend.TyNil) ) ) ) ) ) ),
          (fun path type_params fields ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac
              (Link_model.RecordDecl
                 { layout = Link_model.StructRecord path; type_params; fields })),
          None );
    ]

let interpreter_types_record_command
    ~(command : string)
    ~(use_value_type_args : bool) : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( command,
              Vernacextend.TyNonTerminal
                ( Extend.TUentry (Genarg.get_arg_tag wit_string),
                  Vernacextend.TyNonTerminal
                    ( Extend.TUentry (Genarg.get_arg_tag wit_link_type_params),
                      Vernacextend.TyNonTerminal
                        ( Extend.TUentry (Genarg.get_arg_tag wit_link_ident),
                          Vernacextend.TyTerminal
                            ( ":=",
                              Vernacextend.TyTerminal
                                ( "{",
                                  Vernacextend.TyNonTerminal
                                    ( Extend.TUentry (Genarg.get_arg_tag wit_link_fields),
                                      Vernacextend.TyTerminal ("}", Vernacextend.TyNil) ) ) ) ) ) ) ),
          (fun path type_params interpreter_types_param fields ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac
              (Link_model.InterpreterTypesRecordDecl
                 {
                   path;
                   type_params;
                   interpreter_types_param = string_of_id interpreter_types_param;
                   use_value_type_args;
                   fields;
                 })),
          None );
    ]

let () : unit =
  interpreter_types_record_command
    ~command:"RocqOfRustLinkInterpreterTypesRecord"
    ~use_value_type_args:true

let () : unit =
  interpreter_types_record_command
    ~command:"RocqOfRustLinkInterpreterTypesRecordNoValueArgs"
    ~use_value_type_args:false

(* Top-level enum command.  The body is a nonempty list of variant entries,
   each beginning with [|], just like an Inductive declaration. *)
let () : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command:"RocqOfRustLinkEnum"
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "RocqOfRustLinkEnum",
              Vernacextend.TyNonTerminal
                ( Extend.TUentry (Genarg.get_arg_tag wit_string),
                  Vernacextend.TyTerminal
                    ( ":=",
                      Vernacextend.TyNonTerminal
                        ( Extend.TUlist1
                            (Extend.TUentry (Genarg.get_arg_tag wit_link_variant)),
                          Vernacextend.TyNil ) ) ) ),
          (fun path variants ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac (Link_model.EnumDecl { path; type_params = []; variants })),
          None );
    ]

(* Generic enum command.  This handles Rust enums such as [Foo<T>] whose link
   type is represented with [Ty.apply] and type arguments on each variant
   value. *)
let () : unit =
  Vernacextend.static_vernac_extend
    ~plugin:(Some plugin_name)
    ~command:"RocqOfRustLinkGenericEnum"
    ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
    [
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "RocqOfRustLinkGenericEnum",
              Vernacextend.TyNonTerminal
                ( Extend.TUentry (Genarg.get_arg_tag wit_string),
                  Vernacextend.TyNonTerminal
                    ( Extend.TUentry (Genarg.get_arg_tag wit_link_type_params),
                      Vernacextend.TyTerminal
                        ( ":=",
                          Vernacextend.TyNonTerminal
                            ( Extend.TUlist1
                                (Extend.TUentry (Genarg.get_arg_tag wit_link_variant)),
                              Vernacextend.TyNil ) ) ) ) ),
          (fun path type_params variants ?loc:_ ~atts () ->
            Attributes.unsupported_attributes atts;
            command_typed_vernac (Link_model.EnumDecl { path; type_params; variants })),
          None );
    ]

(* Rocq >= 9.3: the known-module registry is gone; Declare ML Module
   resolves plugins through findlib alone. *)
let register_known_module (_name : string) : unit = ()

let pr_constr_expr (env : Environ.env) (sigma : Evd.evar_map)
    (expr : Constrexpr.constr_expr) : Pp.t =
  Ppconstr.pr_constr_expr ~flags:(Ppconstr.current_flags ()) env sigma expr

let vernac_argument_extend ~(plugin : string) ~(name : string) arg =
  Vernacextend.vernac_argument_extend ~plugin:(Some plugin) ~ignore_kw:false ~name arg

let static_vernac_extend ~(plugin : string) ~(command : string)
    ~(classifier : string -> Vernacextend.vernac_classification) ty =
  Vernacextend.static_vernac_extend ~plugin:(Some plugin) ~command
    ~classifier:(fun ~atts:_ s -> classifier s) ~ignore_kw:false ty

let symbol_list1sep elt sep =
  Procq.Symbol.list1sep elt sep

(* [Procq.terminal] was replaced by [CLexer.terminal] after 9.2. *)
let terminal (s : string) : string Tok.p = CLexer.terminal s

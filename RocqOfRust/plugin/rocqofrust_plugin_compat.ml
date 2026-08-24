(* Rocq <= 9.2: hand-rolled plugins must register as a known module. *)
let register_known_module (name : string) : unit = Mltop.add_known_module name

let pr_constr_expr (env : Environ.env) (sigma : Evd.evar_map)
    (expr : Constrexpr.constr_expr) : Pp.t =
  Ppconstr.pr_constr_expr env sigma expr

let vernac_argument_extend ~(plugin : string) ~(name : string) arg =
  Vernacextend.vernac_argument_extend ~plugin ~name arg

let static_vernac_extend ~(plugin : string) ~(command : string)
    ~(classifier : string -> Vernacextend.vernac_classification) ty =
  Vernacextend.static_vernac_extend ~plugin:(Some plugin) ~command ~classifier ty

let symbol_list1sep elt sep =
  Procq.Symbol.list1sep elt sep true

(* [Procq.terminal] was replaced by [CLexer.terminal] after 9.2. *)
let terminal (s : string) : string Tok.p = Procq.terminal s

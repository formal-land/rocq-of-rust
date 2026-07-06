open Link_model

exception Parse_error of string

let error (message : string) : 'a = raise (Parse_error message)

let trim : string -> string = String.trim

let starts_with ~(prefix : string) (s : string) : bool =
  let n = String.length prefix in
  String.length s >= n && String.sub s 0 n = prefix

let split_once (ch : char) (s : string) : (string * string) option =
  match String.index_opt s ch with
  | None -> None
  | Some i ->
      Some
        ( String.sub s 0 i,
          String.sub s (i + 1) (String.length s - i - 1) )

let parse_field (text : string) : field =
  match split_once ':' text with
  | None -> error ("expected field `name : type`, got `" ^ text ^ "`")
  | Some (name, ty) ->
      { field_name = trim name; field_ty = trim ty }

let split_fields (text : string) : field list =
  text
  |> String.split_on_char ';'
  |> List.map trim
  |> List.filter (fun s -> s <> "")
  |> List.map parse_field

let strip_wrapped (open_ch : char) (close_ch : char) (text : string) : string option =
  let text = trim text in
  let len = String.length text in
  if len < 2 || text.[0] <> open_ch || text.[len - 1] <> close_ch then
    None
  else
    Some (String.sub text 1 (len - 2))

let parse_header (line : string) (kind : string) : string * string =
  let line = trim line in
  let prefix = "RocqOfRustLink" ^ kind ^ " " in
  if not (starts_with ~prefix line) then
    error ("expected `" ^ prefix ^ "...`, got `" ^ line ^ "`");
  let rest = String.sub line (String.length prefix) (String.length line - String.length prefix) in
  match split_once '"' rest with
  | None -> error "expected quoted Rust path"
  | Some ("", rest) -> (
      match split_once '"' rest with
      | None -> error "unterminated Rust path"
      | Some (path, after) ->
          let after = trim after in
          if not (starts_with ~prefix:":=" after) then
            error ("expected `:=` after Rust path, got `" ^ after ^ "`");
          let after =
            String.sub after 2 (String.length after - 2) |> trim
          in
          path, after)
  | _ -> error "expected quoted Rust path"

let parse_variant (line : string) : variant =
  let line = trim line in
  if not (starts_with ~prefix:"|" line) then
    error ("expected enum variant line, got `" ^ line ^ "`");
  let rest = trim (String.sub line 1 (String.length line - 1)) in
  let name, payload_text =
    match String.index_opt rest ' ' with
    | None -> rest, ""
    | Some i ->
        String.sub rest 0 i,
        trim (String.sub rest (i + 1) (String.length rest - i - 1))
  in
  let name, rust_name, payload_text =
    if starts_with ~prefix:"as " payload_text then
      let after_as = trim (String.sub payload_text 3 (String.length payload_text - 3)) in
      match split_once '"' after_as with
      | Some ("", rest) -> (
          match split_once '"' rest with
          | Some (rust_name, after) -> name, rust_name, trim after
          | None -> error "unterminated variant Rust-name override")
      | _ -> error "expected quoted variant Rust-name override"
    else
      name, name, payload_text
  in
  let payload =
    if payload_text = "" then
      TuplePayload []
    else
      match strip_wrapped '(' ')' payload_text with
      | Some fields -> TuplePayload (split_fields fields)
      | None -> (
          match strip_wrapped '{' '}' payload_text with
          | Some fields -> RecordPayload (split_fields fields)
          | None -> error ("invalid variant payload `" ^ payload_text ^ "`"))
  in
  { name; rust_name; payload }

let command_start (line : string) : bool =
  starts_with ~prefix:"RocqOfRustLinkEnum " line
  || starts_with ~prefix:"RocqOfRustLinkRecord " line

let parse_command (lines : string list) : command =
  match lines with
  | [] -> error "empty command"
  | first :: rest when starts_with ~prefix:"RocqOfRustLinkRecord " (trim first) ->
      let path, after_header = parse_header first "Record" in
      let body = String.concat "\n" (after_header :: rest) |> trim in
      let body =
        if String.length body > 0 && body.[String.length body - 1] = '.' then
          String.sub body 0 (String.length body - 1)
        else
          body
      in
      let fields =
        match strip_wrapped '{' '}' body with
        | Some fields -> split_fields fields
        | None -> error "record command body must be wrapped in braces"
      in
      RecordDecl { path; fields }
  | first :: rest when starts_with ~prefix:"RocqOfRustLinkEnum " (trim first) ->
      let path, after_header = parse_header first "Enum" in
      let variants =
        (if after_header = "" then rest else after_header :: rest)
        |> List.map trim
        |> List.filter (fun line -> line <> "" && line <> ".")
        |> List.map (fun line ->
             let line =
               if String.length line > 0 && line.[String.length line - 1] = '.' then
                 String.sub line 0 (String.length line - 1)
               else
                 line
             in
             parse_variant line)
      in
      EnumDecl { path; variants }
  | first :: _ -> error ("unknown command start `" ^ first ^ "`")

let is_plugin_require (line : string) : bool =
  let stripped = trim line in
  starts_with ~prefix:"Require Import links.Plugin." stripped
  || starts_with ~prefix:"Require Export links.Plugin." stripped
  || starts_with ~prefix:"Require Import RocqOfRust.links.Plugin." stripped
  || starts_with ~prefix:"Require Export RocqOfRust.links.Plugin." stripped
  || stripped = "Declare ML Module \"rocqofrust_link_plugin\"."

let expand_file (output_root : string) (file : string) : unit =
  let lines = In_channel.with_open_text file In_channel.input_lines in
  let rec loop acc pending = function
    | [] ->
        let acc =
          match pending with
          | [] -> acc
          | pending ->
              Link_render.render (parse_command (List.rev pending)) @ acc
        in
        List.rev acc
    | line :: rest ->
        let stripped = trim line in
        if pending <> [] then
          if stripped = "." || (String.length stripped > 0 && stripped.[String.length stripped - 1] = '.') then
            let command = parse_command (List.rev (line :: pending)) in
            loop (List.rev (Link_render.render command) @ acc) [] rest
          else
            loop acc (line :: pending) rest
        else if is_plugin_require stripped then
          loop acc [] rest
        else if command_start stripped then
          if String.length stripped > 0 && stripped.[String.length stripped - 1] = '.' then
            let command = parse_command [ line ] in
            loop (List.rev (Link_render.render command) @ acc) [] rest
          else
            loop acc [ line ] rest
        else
          loop (line :: acc) [] rest
  in
  let rendered = loop [] [] lines in
  let output = Filename.concat output_root file in
  let output_dir = Filename.dirname output in
  Sys.command ("mkdir -p " ^ Filename.quote output_dir) |> ignore;
  Out_channel.with_open_text output (fun ch ->
      List.iter (fun line -> output_string ch line; output_char ch '\n') rendered)

let () : unit =
  match Array.to_list Sys.argv with
  | _ :: output_root :: files ->
      List.iter
        (fun file ->
          try expand_file output_root file with
          | Parse_error message ->
              prerr_endline (file ^ ": " ^ message);
              exit 1
          | Link_model.Error message ->
              prerr_endline (file ^ ": " ^ message);
              exit 1)
        files
  | _ ->
      prerr_endline "Usage: link_expand <output-root> <file.v>...";
      exit 1

open Shim
open Smoosh
open Printf

(* dump_ast: Parse a shell script and output the initial AST as JSON.
   Usage: dump_ast <script-file>
          dump_ast -c <command-string>
*)

let () =
  Dash.initialize ();
  let parse_src = ref ParseSTDIN in
  begin match Array.to_list Sys.argv with
  | [_; "-c"; cmd] -> parse_src := ParseString (ParseEval, cmd)
  | [_; file] -> parse_src := ParseFile (file, NoPushFile)
  | _ -> eprintf "Usage: dump_ast <script-file> | dump_ast -c <command>\n"; Stdlib.exit 1
  end;
  let _sstr = Shim.parse_init !parse_src in
  (* Collect all parsed stmts *)
  let rec collect_stmts acc =
    let res = Shim.parse_next Noninteractive in
    match res with
    | ParseDone | ParseError _ -> List.rev acc
    | ParseNull -> collect_stmts acc
    | ParseStmt c -> collect_stmts (c :: acc)
  in
  let stmts = collect_stmts [] in
  let result = match stmts with
    | [] -> json_of_stmt (Command ([], [], [], default_cmd_opts))
    | [s] -> json_of_stmt s
    | s :: rest ->
       let combined = List.fold_left (fun acc stmt -> Semi(acc, stmt)) s rest in
       json_of_stmt combined
  in
  let buf = Buffer.create 4096 in
  write_json buf result;
  Buffer.output_buffer stdout buf;
  print_newline ()
  (* Note: we skip cleanup to avoid the free() crash. The OS will reclaim memory. *)

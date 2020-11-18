open Ast
open Astutil
open Annot
open Lib
open Ctbl
open Typing
open Translate

type pathname = string

let progname = Sys.argv.(0)

let program_files : pathname list ref = ref []

let only_parse_flag     = ref false
let only_typecheck_flag = ref false
let debug               = ref false
let only_print_version  = ref false
let no_encap_check      = ref false

let output : out_channel option ref = ref None

let locEq_method : string ref = ref ""

let margin : int ref = ref 136

let set_output fname = output := Some (open_out fname)

let close_output () =
  match !output with
  | None -> ()
  | Some out_chan -> close_out out_chan

let get_formatter () =
  match !output with
  | None -> Format.std_formatter
  | Some out_chan -> Format.formatter_of_out_channel out_chan

let open_file_or_exit filename =
  match open_in filename with
  | fd -> fd
  | exception Sys_error msg ->
    Printf.fprintf stderr "%s: %s\n" progname msg;
    exit 1

let read_file filename =
  let fd = open_file_or_exit filename in
  let lines : string list ref = ref [] in
  let rec loop () =
    match input_line fd with
    | line -> lines := line :: !lines; loop ()
    | exception End_of_file ->
      close_in fd;
      String.concat "\n" @@ List.rev !lines in
  loop ()

let print_position outx (lexbuf: Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s" (string_of_loc pos)

let parse_with_error lexbuf =
  try Parser.top Lexer.token lexbuf with
  | Lexer.Lexer_error msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit 1
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit 1

let parse_file filename =
  let contents = read_file filename in
  let lexbuf = Lexing.from_string ~with_positions:true contents in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_with_error lexbuf

let parse_and_type_check filename =
  let program = parse_file filename in
  match tc_program program with
  | Ok _ -> ()
  | Error msg -> Printf.fprintf stderr "%s\n" msg

module Dep_graph : sig
  val dependencies : Ast.program -> ident list
  val sort : Ast.program -> Ast.program
end = struct

  open Ast

  type gph = (ident * ident list) list

  let interface_imports intr =
    let f elt = match elt.elt with
      | Intr_import {elt=(Iregular, intr', _); _} -> [intr']
      | _ -> [] in
    concat_map f intr.intr_elts

  let module_imports mdl =
    let f elt = match elt.elt with
      | Mdl_import {elt=(Iregular, mdl', _); _} -> [mdl']
      | _ -> [] in
    mdl.mdl_interface :: concat_map f mdl.mdl_elts

  let bimodule_imports bm =
    let f elt = match elt.elt with
      | Bimdl_import {elt=(Iregular, bimdl', _); _} -> [bimdl']
      | _ -> [] in
    bm.bimdl_left_impl :: bm.bimdl_right_impl :: concat_map f bm.bimdl_elts

  let build_gph programs =
    let f = function
      | Unr_intr i -> (i.elt.intr_name, interface_imports i.elt)
      | Unr_mdl  m -> (m.elt.mdl_name, module_imports m.elt)
      | Rel_mdl bm -> (bm.elt.bimdl_name, bimodule_imports bm.elt) in
    List.map f (get_elts programs)

  let dfs gph visited start =
    let open List in
    let rec walk path visited node =
      if mem node path then failwith "Cyclic imports" else
      if mem node visited then visited else
        let path = node :: path in
        let succ = assoc node gph in
        node :: fold_left (walk path) visited succ in
    walk [] visited start

  let dependencies program =
    let gph = build_gph program in
    List.fold_left (fun visited (node,_) -> dfs gph visited node) [] gph

  let sort program =
    let deps = List.rev (dependencies program) in
    List.sort (fun i j ->
        let i = index (get_program_elt_name i.elt) deps in
        let j = index (get_program_elt_name j.elt) deps in
        compare i j
      ) program

end

let handle_local_equivalence meth_name =
  let meth_name = Id meth_name in
  let fmt = Format.std_formatter in
  let program = concat_map parse_file !program_files in
  let program =
    let f e = match e.elt with Rel_mdl _ -> false | _ -> true in
    List.filter f program in
  let deps = List.rev @@ Dep_graph.dependencies program in
  let program = Dep_graph.sort program in
  if !debug then begin
    Printf.fprintf stderr "Deps: ";
    List.iter (Printf.fprintf stderr "%s " % string_of_ident) deps;
    Printf.fprintf stderr "\n";
  end;
  (* Respect other flags that may be passed in *)
  if !only_parse_flag then ()
  else match tc_program program with
    | Ok (penv, ctbl) ->
      if !only_typecheck_flag then ()
      else begin
        Format.pp_set_margin fmt !margin;
        let penv = Pretrans.process ctbl penv in
        try
          LocEq.pp_derive_locEq penv ctbl deps meth_name fmt;
          Format.pp_force_newline fmt ();
          Format.pp_print_flush fmt ()
        with LocEq.Unknown_method m ->
          Printf.fprintf stderr "Unknown method %s\n" m;
          exit 1
      end
    | Error msg -> Printf.fprintf stderr "%s\n" msg

let run () =
  let fmt = get_formatter () in
  let program = concat_map parse_file !program_files in
  let deps = List.rev @@ Dep_graph.dependencies program in
  let program = Dep_graph.sort program in
  if !debug then begin
    Printf.fprintf stderr "Deps: ";
    List.iter (Printf.fprintf stderr "%s " % string_of_ident) deps;
    Printf.fprintf stderr "\n";
  end;
  if !only_parse_flag then ()
  else match tc_program program with
    | Ok (penv, ctbl) ->
      if !only_typecheck_flag then ()
      else begin
        Format.pp_set_margin fmt !margin;
        let penv = Pretrans.process ctbl penv in
        if !debug then begin
          Printf.fprintf stderr "Resolved dependencies: ";
          List.iter (Printf.fprintf stderr "%s, " % string_of_ident) deps;
          Printf.fprintf stderr "\n";
        end;
        let flds = Ctbl.known_fields ctbl in
        if !debug then begin
          Printf.fprintf stderr "Known fields:\n";
          List.iter (fun {field_name; field_ty; _} ->
              Printf.fprintf stderr "%s: %s\n"
                (string_of_ident field_name.node)
                (T.string_of_ity field_ty)
            ) flds
        end;
        (* FIXME: TODO: use ctbl from typing. *)
        let global_ctxt, state_module = Translate.Build_State.mk penv in
        Why3.Mlw_printer.pp_mlw_file fmt state_module;
        Format.pp_print_newline fmt ();
        Format.print_flush ();
        let mlw_files = compile_penv global_ctxt penv deps in
        List.iter (fun mlw ->
            Why3.Mlw_printer.pp_mlw_file fmt mlw;
            Format.pp_print_newline fmt ();
            Format.pp_print_newline fmt ();
            Format.print_flush ()
          ) mlw_files
      end;
      close_output ()
    | Error msg -> Printf.fprintf stderr "%s\n" msg

let print_version () = Printf.fprintf stdout "WhyRel, version 0.2\n"

let args =
  let open Arg in
  ["-parse", Set only_parse_flag,
   " Parse program and exit";

   "-type-check", Set only_typecheck_flag,
   " Type check program and exit";

   "-debug", Set debug,
   " Print debug information";

   "-o", String (fun f -> set_output f),
   "<file>  Set output file name to <file>";

   "-margin", Set_int margin,
   "<n>  Set printer max columns to <n>";

   "-locEq", Set_string locEq_method,
   "<meth>  Derive the local equivalence spec for method <meth>";

   "-no-encap", Set no_encap_check,
   " Do not perform the Encap check";

   "-version", Set only_print_version,
   " Print version";
  ]

let usage = "Usage: " ^ progname ^ " [options] [<file>...]"

let main () =
  let add_program_file s = program_files := s :: !program_files in
  Arg.parse (Arg.align args) add_program_file usage;
  program_files := List.rev !program_files;
  tc_debug := !debug; trans_debug := !debug;
  Pretrans.pretrans_debug := !debug;
  Pretrans.encap_check := not (!no_encap_check);
  if !only_print_version then print_version () else
  if List.length !program_files = 0 then () else
  if !locEq_method <> "" then handle_local_equivalence !locEq_method
  else run ()

;;

if not !Sys.interactive
then main ()
else ()

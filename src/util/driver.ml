open Printf
open Platform
open Ast_print

(* configuration flags ------------------------------------------------------ *)
let interpret_ll = ref false   (* run the ll interpreter? *)
let print_ll_flag = ref false       (* print the generated ll code? *)
let print_x86_flag = ref false      (* print the generated x86 code? *)
let print_ast_flag = ref false
let print_oat_flag = ref false
let clang = ref false          (* use the clang backend? *)
let assemble = ref true        (* assemble the .s to .o files? *)
let link = ref true            (* combine multiple .o files executable? *)
let execute_x86 = ref false    (* run the resulting x86 program? *)
let executable_filename = ref "a.out"


(* files processed during this run of the compiler *)
let files : string list ref = ref []

let link_files : string list ref = ref []
let add_link_file path =
  link_files := path :: (!link_files)


(* terminal output ---------------------------------------------------------- *)
  
let print_banner s =
  let rec dashes n = if n = 0 then "" else "-"^(dashes (n-1)) in
  printf "%s %s\n%!" (dashes (79 - (String.length s))) s

(*let print_ll file ll_ast =
    print_banner (file ^ ".ll");
    print_endline (Llutil.string_of_prog ll_ast)
*)

let print_x86 file asm_str =
    print_banner file;
    print_endline asm_str

(* file i/o ----------------------------------------------------------------- *)

let read_file (file:string) : string =
  let lines = ref [] in
  let channel = open_in file in
  try while true; do
      lines := input_line channel :: !lines
  done; ""
  with End_of_file ->
    close_in channel;
    String.concat "\n" (List.rev !lines)

let write_file (file:string) (out:string) =
  let channel = open_out file in
  fprintf channel "%s" out;
  close_out channel


(* running the generated code ----------------------------------------------- *)

(*let interpret program args : string =
  let result = Llinterp.interp_prog program args in
  Llinterp.string_of_sval result
*)

let run_executable arg pr =
  let cmd = sprintf "%s%s %s" dot_path pr arg in
  sh cmd (fun _ i -> i)
  
let run_executable_to_tmpfile arg pr tmp =
  let cmd = sprintf "%s%s %d > %s 2>&1" dot_path pr arg tmp in
  sh cmd ignore_error


let run_program (args:string) (executable:string) (tmp_out:string) : string =
  let cmd = sprintf "%s%s %s > %s 2>&1" dot_path executable args tmp_out in
  let _ = sh cmd ignore_error
  in
  read_file tmp_out

let run_program_error (args:string) (executable:string) (tmp_out:string) : string =
  let cmd = sprintf "%s%s %s > %s 2>&1" dot_path executable args tmp_out in
  let result = sh cmd (fun _ i -> i)
  in
  (read_file tmp_out) ^ (string_of_int result)

  
(* compiler pipeline -------------------------------------------------------- *)

(* These functions implement the compiler pipeline for a single ll file:
     - parse the file 
     - compile to a .s file using either clang or backend.ml
     - assemble the .s to a .o file using clang
*)
(*
let parse_ll_file filename =
  let program = read_file filename |> 
                Lexing.from_string |>
                Llparser.prog Lllexer.token
  in
  program


let string_of_ll_ast path ll_ast =
  let ll_str = Llutil.string_of_prog ll_ast in
  let prog = Printf.sprintf "; generated from: %s\ntarget triple = \"%s\"\n%s\n"
      path !Platform.target_triple ll_str in
  prog


let process_ll_ast path file ll_ast =
  let _ = if !print_ll_flag then print_ll file ll_ast in

  (* Optionally interpret it using the cs516 reference interperter. *)
  let _ = if !interpret_ll then
      let result = interpret ll_ast [] in
      Printf.printf "Interpreter Result: %s\n" result
  in

  (* generated file names *)
  let dot_s_file = Platform.gen_name !Platform.output_path file ".s" in
  let dot_o_file = Platform.gen_name !Platform.output_path file ".o" in

  let _ =
    if !clang then begin
      Platform.verb "* compiling with clang";
      Platform.clang_compile path dot_s_file;
      if !print_x86_flag then begin
        print_banner dot_s_file;
        Platform.sh (Printf.sprintf "cat %s" dot_s_file) Platform.raise_error
      end
    end else begin
      Platform.verb "* compiling with cs516 backend";
      let asm_ast = Backend.compile_prog ll_ast in
      let asm_str = X86.string_of_prog asm_ast in
      let _ = if !print_x86_flag then print_x86 dot_s_file asm_str in
      let _ = write_file dot_s_file asm_str in
      ()
    end
  in
  let _ = if !assemble then Platform.assemble dot_s_file dot_o_file in
  let _ = add_link_file dot_o_file in 
  ()

let process_ll_file path file =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let ll_ast = parse_ll_file path in
  process_ll_ast path file ll_ast
*)
(* oat pipeline ------------------------------------------------------------- *)

let parse_oat_file filename =
  let lexbuf = read_file filename |> 
               Lexing.from_string
  in
  Vcy_lexer.reset_lexbuf filename 0 lexbuf;  (* set the filename *)  
  try
    Vcy_parser.prog Vcy_lexer.token lexbuf
  with
  | Vcy_parser.Error -> failwith @@ Printf.sprintf "Parse error at: %s"
      (Range.string_of_range (Range.lex_range lexbuf))
    

let print_oat file ll_ast =
    print_banner (file ^ ".oat");
    AstPP.print_prog ll_ast

let print_ast p = Printf.printf "\n%s\n\n" (AstML.string_of_prog p)

(*
let process_oat_ast path file oat_ast =
  if !print_oat_flag then print_oat file oat_ast;
  if !print_ast_flag then print_ast oat_ast;
  let ll_ast = Frontend.cmp_prog oat_ast in
  let dot_ll_file = Platform.gen_name !Platform.output_path file ".ll" in
  Platform.verb @@ Printf.sprintf "writing file: %s\n" dot_ll_file;
  let prog = string_of_ll_ast path ll_ast in
  write_file dot_ll_file prog;
  process_ll_ast dot_ll_file file ll_ast 

let process_oat_file path basename =
  Platform.verb @@ Printf.sprintf "* processing file: %s\n" path;
  let oat_ast = parse_oat_file path in
  process_oat_ast path basename oat_ast
*)

(* process files based on extension ----------------------------------------- *)

(*
let process_file path =
  let basename, ext = Platform.path_to_basename_ext path in
  begin match ext with
    | "oat" -> process_oat_file path basename
    | "ll" -> process_ll_file path basename
    | "o" -> add_link_file path
    | "c" -> add_link_file path
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

(* process each file separately and then link all of them together *)
let process_files files =
  if (List.length files) > 0 then begin

    List.iter process_file files;

    ( if !assemble && !link then
        Platform.link (List.rev !link_files) !executable_filename );

    ( if !assemble && !link && !execute_x86 then
        let ret = run_executable "" !executable_filename in
        print_banner @@ Printf.sprintf "Executing: %s" !executable_filename;
        Printf.printf "* %s returned %d\n" !executable_filename ret )
  end
*)
open Vcy
open Util

exception BadCommandLine of string

module type Runner = sig
  val run : unit -> unit (* Uses all of argv *)
end

module RunParse : Runner = struct
  open Ast_print

  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " parse [<flags>] <vcy program>"
  
  let debug = ref false
  let include_nodes = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-o",      Arg.Set_string output_file, "<file> Output AST to file (defaults to stdout)"
    ; "-n",      Arg.Set include_nodes, " Include node information in parse output"
    ] |>
    Arg.align

  let parse prog =
    if !debug then begin
      Printexc.record_backtrace true;
      ignore @@ Parsing.set_trace true
    end;

    AstML.include_nodes := !include_nodes;

    let ast =
      Driver.parse_oat_file prog |>
      AstML.string_of_prog
    in

    if !output_file = ""
    then Printf.printf "%s\n" ast
    else
      let out_chan = open_out !output_file in
      output_string out_chan ast;
      close_out out_chan

  (* Assumes argc > 2 and argv[1] = "parse" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog] -> parse prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))

end

module RunYaml : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " yaml [<flags>] <vcy program>"
  
  let debug = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""
  let output_dir = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-t",      Arg.Set_string output_dir, "<dir> Set output directory. Default is CWD"
    ; "-o",      Arg.Set_string output_file, "<file> Output YAML to file. Default file is name of program with yml extension"
    ] |>
    Arg.align

  let gen_yaml prog_name =
    (* if !debug then begin
      Printexc.record_backtrace true
    end;

    let prog = Driver.parse_oat_file prog_name in

    let yaml_of_prog = Yaml_generator.compile_file_to_yaml prog_name prog in

    if !output_file = ""
      then output_file :=
        (* TODO this'll be correct except in weird edge cases *)
        Filename.remove_extension (Filename.basename prog_name) 
        ^ "." ^ Yaml_generator.file_ext;

    output_file := Filename.concat !output_dir !output_file;

    let out_chan = open_out !output_file in
    output_string out_chan yaml_of_prog;
    close_out out_chan *)
    failwith "revise later!"

  (* Assumes argc > 2 and argv[1] = "parse" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog] -> gen_yaml prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))

end

(* TODO it'll consider hyphenated things after vcy program to be flags instead of program args *)
module RunInterp : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " interp [<flags>] <vcy program> [<vcy args>]"
  
  let debug = ref false
  let force_sequential = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let get_execution_time = ref false

  let prover_name = ref ""
  let timeout = ref None

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--force-sequential", Arg.Set force_sequential, " Force all commutativity blocks to execute in sequence"
    ; "--time", Arg.Set get_execution_time, " Output execution time instead of main's return"
    ; "--verbose", Arg.Set Servois2.Util.verbosity, "Servois2 verbose output"
    ; "--very-verbose", Arg.Set Servois2.Util.very_verbose, " Very verbose output and print smt query files"
    ; "--prover", Arg.Set_string prover_name, "<name> Use a particular prover (default: CVC4)"
    ; "--timeout", Arg.Float (fun f -> timeout := Some f), "<name> Set timeout for servois2 queries"
    ] |>
    Arg.align

  let get_prover () : (module Servois2.Provers.Prover) =
      match !prover_name |> String.lowercase_ascii with
      | "cvc4" -> (module Servois2.Provers.ProverCVC4)
      | "cvc5" -> (module Servois2.Provers.ProverCVC5)
      | "z3"   -> (module Servois2.Provers.ProverZ3)
      | ""     -> (module Servois2.Provers.ProverCVC4)
      | "mathsat" -> (module Servois2.Provers.ProverMathSAT)
      | s      -> raise @@ Invalid_argument (sp "Unknown/unsupported prover '%s'" s)

  let interp prog_name argv =
    try
      if !debug then begin
        Interp.debug_display := true;
        Interp.emit_inferred_phis := true;
        Printexc.record_backtrace true
      end;

      if !force_sequential then begin
        Interp.force_sequential := true;
      end;

      let prog = Driver.parse_oat_file prog_name in
      Random.self_init ();

      begin if !get_execution_time then
        let time = Interp.interp_prog_time prog argv in
        Printf.printf "%f\n" time
      else
        let ret = Interp.interp_prog prog argv in
        Printf.printf "Return: %Ld\n" ret
      end;

      flush stdout

    with e ->
      let msg = Printexc.to_string e in
      let stack = Printexc.get_backtrace () in
      Printf.eprintf "An error occurred: %s\n%s\n" msg stack

  let run () =

    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    let synth_options = {
      Servois2.Synth.default_synth_options with prover = get_prover (); timeout = !timeout
    } in
    Util.servois2_synth_option := synth_options;
    match anons with
    | prog :: argv -> interp prog (Array.of_list (prog :: argv))
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))

end


module RunTranslate : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " translate [<flags>] <vcy program>"
  
  let debug = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let get_execution_time = ref false

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--time", Arg.Set get_execution_time, " Output execution time instead of main's return"
    ] |>
    Arg.align

  let translate prog_name =
    try
      if !debug then begin
        Printexc.record_backtrace true
      end;

      let prog = Driver.parse_oat_file prog_name in
      
      Printf.printf "%s" @@ Ast_to_c.c_of_prog prog;

      flush stdout

    with e ->
      let msg = Printexc.to_string e in
      let stack = Printexc.get_backtrace () in
      Printf.eprintf "An error occurred: %s\n%s\n" msg stack

  let run () =

    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | prog :: _ -> translate prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))

end


module RunInterface : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " interface [<flags>] <vcy program>"
  
  let debug = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""
  let output_dir = ref ""
  let input_file = ref ""
  let input_yaml = ref ""

  let no_commutes = ref false

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-o",      Arg.Set_string output_file, "<file> Output generated interface to file. Default file is name of program with vcyi extension."
    ; "-i",      Arg.Set_string input_file, "<file> Input a partial or manually constructed interface. (doesn't work yet)"
    ; "-x",      Arg.Set no_commutes, " Don't generate commutativity conditions"
    ; "-y",      Arg.Set_string input_yaml, "<file> Use an existing YAML file. Uses vcy YAML generator by default"
    ; "-t",      Arg.Set_string output_dir, "<dir> Set output directory. Default is CWD"
    ] |>
    Arg.align

  let generate_interface prog_name =
    (* if !debug then begin
      Printexc.record_backtrace true;
      Interface.debug_display := true;
      Interp.emit_inferred_phis := true;
    end;

    if !output_file = ""
    then output_file :=
      (* TODO this'll be correct except in weird edge cases *)
      Filename.remove_extension (Filename.basename prog_name)
      ^ "." ^ Interface.file_ext;

    output_file := Filename.concat !output_dir !output_file;

    let prog = Driver.parse_oat_file prog_name in

    let yaml =
      if !input_yaml = ""
      then Yaml_generator.compile_file_to_yaml prog_name prog
      else
        let in_chan = open_in !input_yaml in
        String.concat "\n" @@ read_all_in in_chan
    in

    let intf =
      if !input_file = ""
      then Interface.generate_interface prog_name prog yaml !no_commutes
      else begin
        let in_chan = open_in !input_file in
        let s = String.concat "\n" @@ read_all_in in_chan in
        let init = Interface.interface_of_string s in
        Interface.augment_interface prog init !no_commutes
      end
    in

    let s = Interface.string_of_interface intf in

    let out_chan = open_out !output_file in
    output_string out_chan s;
    close_out out_chan *)
    failwith "revise later!"

  (* Assumes argc > 2 and argv[1] = "interface" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog] -> generate_interface prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

module RunPhi : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " phi [<flags>] <vcy program> <method 1> <method 2>"
  
  let debug = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""
  let input_yaml = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-o",      Arg.Set_string output_file, "<file> Output generated condition to file. Default file is stdout."
    ; "-y",      Arg.Set_string input_yaml, "<file> Use an existing YAML file. Uses vcy YAML generator by default"
    ] |>
    Arg.align

  let generate_phi prog_name method1 method2 =
    (* if !debug then begin
      Printexc.record_backtrace true
    end;

    let prog = Driver.parse_oat_file prog_name in
    let env = Interp.initialize_env prog false in

    let yaml =
      if !input_yaml = ""
      then Yaml_generator.compile_file_to_yaml prog_name prog
      else
        let in_chan = open_in !input_yaml in
        String.concat "\n" @@ read_all_in in_chan
    in

    let res =
      try
        Analyze.invoke_servois yaml method1 method2 |>
        Analyze.exp_of_servois_output env |>
        Ast.no_loc |>
        Astlib.AstPP.string_of_exp
      with e ->
        raise @@ Failure "Phi generation failed"
    in

    if !output_file = ""
    then Printf.printf "%s\n" res
    else
      let out_chan = open_out !output_file in
      output_string out_chan res;
      close_out out_chan *)
      failwith "revise later!"

  (* Assumes argc > 2 and argv[1] = "interface" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog;method1;method2] -> generate_phi prog method1 method2
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end


module RunInfer : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " infer [<flags>] <vcy program>"
  
  let debug = ref false

  let time_servois = ref false

  let quiet = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let prover_name = ref ""
  let output_file = ref ""
  let timeout = ref None
  let lattice = ref false
  let lattice_timeout = ref (Some 30.)
  let stronger_pred_first = ref false
  let no_cache = ref true

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--time",  Arg.Set time_servois, " Output time of Servois execution to stderr"
    ; "-q", Arg.Set quiet, " Quiet - just display conditions"
    (* ; "--poke", Arg.Unit (fun () -> Choose.choose := Choose.poke), " Use servois poke heuristic (default: simple)"
    ; "--poke2", Arg.Unit (fun () -> Choose.choose := Choose.poke2), " Use improved poke heuristic (default: simple)" *)
    ;"--poke", Arg.Unit (fun () -> Servois2.Choose.choose := Servois2.Choose.poke), " Use servois poke heuristic (default: simple)"
    ; "--poke2", Arg.Unit (fun () -> Servois2.Choose.choose := Servois2.Choose.poke2), " Use improved poke heuristic (default: simple)"
    ; "--mcpeak-bisect", Arg.Unit (fun () -> Servois2.Choose.choose := Servois2.Choose.mc_bisect), " Use model counting based synthesis with strategy: bisection"    
    ; "--mcpeak-max", Arg.Unit (fun () -> Servois2.Choose.choose := Servois2.Choose.mc_max), " Use model counting based synthesis with strategy: maximum-coverage"
    ; "--mcpeak-max-poke2", Arg.Unit (fun () -> Servois2.Choose.choose := Servois2.Choose.mc_max_poke), " Use model counting based synthesis with strategy: maximum-coverage, then poke2"
    ; "--lattice-timeout", Arg.Float (fun f -> lattice_timeout := Some f), " Set the time limit for lattice construction"
    ; "--stronger-pred-first", Arg.Unit (fun () -> stronger_pred_first := true), " Choose stronger predicates first"
    ; "--lattice", Arg.Unit (fun () -> lattice := true), " Create and use lattice of predicate implication"
    ; "--timeout", Arg.Float (fun f -> timeout := Some f), " Set time limit for execution"
    ; "--auto-terms", Arg.Unit (fun () -> Servois2.Predicate.autogen_terms := true), " Automatically generate terms from method specifications"
    ; "--cache", Arg.Unit (fun () -> no_cache := false), " Use cached implication lattice" 
    
    ; "--verbose", Arg.Set Servois2.Util.verbosity, " Servois2 verbose output"
    ; "--very-verbose", Arg.Set Servois2.Util.very_verbose, " Very verbose output and print smt query files"
    ; "--prover", Arg.Set_string prover_name, "<name> Use a particular prover (default: CVC4)"
    ; "--force", Arg.Set Interp.force_infer, " Force inference of all commutativity conditions (even when one is provided)"
    ; "--timeout", Arg.Float (fun f -> timeout := Some f), "<name> Set timeout for servois2 queries"
    ; "-o",      Arg.Set_string output_file, "<file> Output transformed program to file. Default is stdout."
    ] |>
    Arg.align

  let get_prover () : (module Servois2.Provers.Prover) =
      match !prover_name |> String.lowercase_ascii with
      | "cvc4" -> (module Servois2.Provers.ProverCVC4)
      | "cvc5" -> (module Servois2.Provers.ProverCVC5)
      | "z3"   -> (module Servois2.Provers.ProverZ3)
      | ""     -> (module Servois2.Provers.ProverCVC4)
      | "mathsat" -> (module Servois2.Provers.ProverMathSAT)
      | s      -> raise @@ Invalid_argument (sp "Unknown/unsupported prover '%s'" s)

  let infer_phis prog_name =
    if !debug then begin
      Printexc.record_backtrace true;
      Interp.debug_display := true;
    end;

    Interp.time_servois := !time_servois;
    Interp.emit_inferred_phis := true; (*not @@ !Interp.time_servois;*)
    Interp.emit_quiet := !quiet;

    let prog = Driver.parse_oat_file prog_name in
    let env = Interp.initialize_env prog true in
    let open Ast in
    if !output_file != "" then begin
      let gmdecls = List.map (fun (name, tmethod) -> Gmdecl(no_loc @@ mdecl_of_tmethod name tmethod)) env.g.methods in
      let prog' = gmdecls @ List.filter (function Gvdecl _ | Gsdecl _ -> true | Gmdecl _ -> false) prog in
      let translated_prog = Ast_print.AstPP.string_of_prog prog' in
      let out_chan = open_out !output_file in
      output_string out_chan translated_prog;
      close_out out_chan
    end

  (* Assumes argc > 2 and argv[1] = "interface" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    let synth_options = {
      Servois2.Synth.default_synth_options with prover = get_prover (); timeout = !timeout; 
                                        lattice = !lattice;
                                        lattice_timeout = !lattice_timeout;
                                         no_cache = !no_cache;
                                         stronger_predicates_first = !stronger_pred_first;
    } in
    Util.servois2_synth_option := synth_options;
    match anons with
    | [prog] -> infer_phis prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

module RunVerify : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " verify [<flags>] <vcy program>"
  
  let debug = ref false
  let time_servois = ref false
  let quiet = ref false
  let anons = ref []
  let cond = ref false 

  let anon_fun (v : string) =
    anons := v :: !anons

  let prover_name = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--time",  Arg.Set time_servois, " Display time of Servois execution instead of inference"
    ; "-q", Arg.Set quiet, " Quiet - just display conditions"
    ; "--verbose", Arg.Set Servois2.Util.verbosity, " Servois2 verbose output"
    ; "--very-verbose", Arg.Set Servois2.Util.very_verbose, " Very verbose output and print smt query files"
    ; "--prover", Arg.Set_string prover_name, "<name> Use a particular prover (default: CVC4)"
    ; "--cond", Arg.Set cond, " Display provided commute condition"
    ] |>
    Arg.align

  let get_prover () : (module Servois2.Provers.Prover) =
      match !prover_name |> String.lowercase_ascii with
      | "cvc4" -> (module Servois2.Provers.ProverCVC4)
      | "cvc5" -> (module Servois2.Provers.ProverCVC5)
      | "z3"   -> (module Servois2.Provers.ProverZ3)
      | ""     -> (module Servois2.Provers.ProverCVC4)
      | "mathsat" -> (module Servois2.Provers.ProverMathSAT)
      | s      -> raise @@ Invalid_argument (sp "Unknown/unsupported prover '%s'" s)

  let verify prog_name =
    if !debug then begin
      Printexc.record_backtrace true;
      Interp.debug_display := true;
    end;

    Interp.emit_inferred_phis := true;
    Interp.emit_quiet := !quiet;
    Interp.print_cond := !cond;

    let prog = Driver.parse_oat_file prog_name in
    let env = Interp.initialize_env prog false in
    let dt, _ =
        time_exec @@ fun () -> Interp.verify_phis_of_prog env.g
    in if !time_servois
    then Printf.eprintf "%f\n" dt

  (* Assumes argc > 2 and argv[1] = "interface" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    let synth_options = {
      Servois2.Synth.default_synth_options with prover = get_prover ();
    } in
    Util.servois2_synth_option := synth_options;
    match anons with
    | [prog] -> verify prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

type command =
  | CmdHelp (* Show help info *)
  | CmdParse (* Parse program *)
  | CmdInterp (* Interpret program *)
  | CmdInterface (* Generate interface *)
  | CmdYaml (* Generate YAML for Servois *)
  | CmdPhi (* Generate commutativity condition *)
  | CmdInfer (* Infer commute conditions *)
  | CmdVerify
  | CmdTranslate

let command_map =
  [ "help",      CmdHelp
  ; "parse",     CmdParse
  ; "interp",    CmdInterp
  (*; "interpret", CmdInterp*)
  ; "interface", CmdInterface
  (*; "yaml",      CmdYaml*)
  (*; "phi",       CmdPhi*)
  ; "infer",     CmdInfer
  ; "verify",    CmdVerify
  ; "translate", CmdTranslate
  ]

let runner_map : (command * (module Runner)) list =
  [ CmdInterp,    (module RunInterp)
  ; CmdParse,     (module RunParse)
  (*; CmdInterface, (module RunInterface)*)
  (*; CmdYaml,      (module RunYaml)*)
  (*; CmdPhi,       (module RunPhi)*)
  ; CmdInfer,     (module RunInfer)
  ; CmdVerify,    (module RunVerify)
  ; CmdTranslate, (module RunTranslate)
  ]

let display_help_message exe_name = 
  let details =
    "Commands:\n" ^
    "  help        Display this message\n" ^
    "  parse       Generate the AST of a Veracity program\n" ^
    "  interp      Interpret a Veracity program\n" ^
    (*"  interface   Generate an interface for a Veracity program\n" ^*)
    (*"  yaml        Generate YAML representation of Veracity program\n" ^*)
    (*"  phi         Generate commutativty condition between two methods\n" ^*)
    "  infer       Infer and emit all blank commutativity conditions\n" ^
    "  verify      Verify all provided commutativity conditions\n" ^
    "  translate   Translate program to C\n "
  in Printf.eprintf "Usage: %s <command> [<flags>] [<args>]\n%s" exe_name details

(* Check first argument for command *)
let run () =
  match Sys.argv with
  | [| |] -> raise @@ UnreachableFailure "Empty argv"
  | [| exe_name |] -> display_help_message exe_name
  | _ ->
    (*Sys.chdir @@ Filename.dirname Sys.argv.(0); (* Make working directory relative to executable *)*)
    let exe_name, cmd = Sys.argv.(0), Sys.argv.(1) in
    match List.assoc_opt Sys.argv.(1) command_map with
    | None -> (* Unknown command *)
      Printf.eprintf "Unknown command \"%s\".\n" cmd;
      display_help_message exe_name
    | Some CmdHelp ->
      display_help_message exe_name
    | Some cmd ->
      let module R =
        (val (List.assoc cmd runner_map))
      in R.run ()

let () = run ()

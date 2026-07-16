open Ast
open Util

type input =
  | File   of string
  | Source of string
  | Prog   of Ast.prog

type options = {
  prover  : [ `CVC4 | `CVC5 | `Z3 | `Yices ];
  timeouts : Servois2.Timeouts.t;
  use_ae  : bool;
  html    : bool;
  silent  : bool;
  cvc5_extra_args : string list;
  out_dir : string option;
}

let default_options = {
  prover  = `CVC5;
  timeouts = Servois2.Timeouts.default;
  use_ae  = false;
  html    = false;
  silent  = true;
  cvc5_extra_args = [];
  out_dir = None;
}

type error =
  | ParseError  of string
  | InterpError of string
  | InferError  of string
  | VerifyError of string

type 'a api_result = ('a, error) result

let resolve : input -> Ast.prog api_result = function
  | File path ->
    (try Ok (Driver.parse_oat_file path)
     with Failure msg  -> Error (ParseError msg)
        | Sys_error msg -> Error (ParseError msg))
  | Source src ->
    (try Ok (Driver.parse_oat_string src)
     with Failure msg -> Error (ParseError msg))
  | Prog p -> Ok p

let configure opts =
  let prover : (module Servois2.Provers.Prover) = match opts.prover with
    | `CVC4 -> (module Servois2.Provers.ProverCVC4)
    | `CVC5 -> (module Servois2.Provers.ProverCVC5)
    | `Z3   -> (module Servois2.Provers.ProverZ3)
    | `Yices -> (module Servois2.Provers.ProverYices)
  in
  (* Publish the caller's timeouts to the shared record before building the
     synth options, since default_synth_options reads its synth/lattice limits
     from there and the per-query limit is applied at solver-invocation time. *)
  Servois2.Timeouts.set opts.timeouts;
  Util.servois2_synth_option := {
    Servois2.Synth.default_synth_options with
      prover  = prover;
      timeout = opts.timeouts.Servois2.Timeouts.synth;
      lattice_timeout = opts.timeouts.Servois2.Timeouts.lattice;
      use_ae  = opts.use_ae;
  };
  Util.servois2_verify_option := {
    Servois2.Verify.default_verify_options with
      prover = prover;
      use_ae = opts.use_ae;
  };
  (* Extra CVC5 flags flow through to the solver invocation (Provers.run_prover);
     only applied for the CVC5 prover. *)
  Servois2.Provers.cvc5_extra_args := opts.cvc5_extra_args;
  Interp.silent := opts.silent;
  (* A caller-supplied dir makes this run nest inside the caller's tree; each
     call resets it, so a caller driving many runs gets one dir per run. *)
  Util.output_root := opts.out_dir;
  Util.commute_counter := 0

let parse input = resolve input

let interp ?(opts = default_options) input argv =
  match resolve input with
  | Error e -> Error e
  | Ok prog ->
    configure opts;
    (try Ok (Interp.interp_prog prog argv)
     with e -> Error (InterpError (Printexc.to_string e)))

let ae_msg = "Program contains havoc (nondeterminism); \
forall/exists reasoning is required. Set use_ae = true in options."

let infer ?(opts = default_options) input =
  match resolve input with
  | Error e -> Error e
  | Ok prog ->
    if Analyze.prog_has_havoc prog && not opts.use_ae then
      Error (InferError ae_msg)
    else begin
      configure opts;
      let saved_emit = !Interp.emit_inferred_phis in
      Interp.emit_inferred_phis := false;
      let html_session =
        if opts.html then begin
          Servois2.Util.diagram      := true;
          Servois2.Util.dump_queries := true;
          let sdir = Html_output.create_session_dir () in
          Util.session_dir     := Some sdir;
          Util.commute_counter := 0;
          Util.commute_records := [];
          Some (sdir, input)
        end else None
      in
      (try
        let env = Interp.initialize_env prog true in
        Interp.emit_inferred_phis := saved_emit;
        let html_path = match html_session with
          | None -> None
          | Some (sdir, inp) ->
            let source_file = match inp with
              | File path -> path
              | Source src ->
                let p = Filename.concat sdir "source.vcy" in
                let oc = open_out p in
                output_string oc src;
                close_out oc;
                p
              | Prog p ->
                let src = Ast_print.AstPP.string_of_prog p in
                let path = Filename.concat sdir "source.vcy" in
                let oc = open_out path in
                output_string oc src;
                close_out oc;
                path
            in
            Some (Html_output.generate
              ~source_file
              ~session_dir:sdir
              ~records:!Util.commute_records)
        in
        Ok (env.g, html_path)
       with e ->
         Interp.emit_inferred_phis := saved_emit;
         Error (InferError (Printexc.to_string e)))
    end

let verify ?(opts = default_options) input =
  match resolve input with
  | Error e -> Error e
  | Ok prog ->
    if Analyze.prog_has_havoc prog && not opts.use_ae then
      Error (VerifyError ae_msg)
    else begin
      configure opts;
      let saved_emit = !Interp.emit_inferred_phis in
      Interp.emit_inferred_phis := false;
      let html_session =
        if opts.html then begin
          Servois2.Util.diagram      := true;
          Servois2.Util.dump_queries := true;
          let sdir = Html_output.create_session_dir () in
          Util.session_dir     := Some sdir;
          Util.commute_counter := 0;
          Util.commute_records := [];
          Some (sdir, input)
        end else None
      in
      (try
        let env = Interp.initialize_env prog false in
        let _ = Interp.verify_phis_of_prog env.g in
        Interp.emit_inferred_phis := saved_emit;
        let html_path = match html_session with
          | None -> None
          | Some (sdir, inp) ->
            let source_file = match inp with
              | File path -> path
              | Source src ->
                let p = Filename.concat sdir "source.vcy" in
                let oc = open_out p in
                output_string oc src;
                close_out oc;
                p
              | Prog p ->
                let src = Ast_print.AstPP.string_of_prog p in
                let path = Filename.concat sdir "source.vcy" in
                let oc = open_out path in
                output_string oc src;
                close_out oc;
                path
            in
            Some (Html_output.generate
              ~source_file
              ~session_dir:sdir
              ~records:!Util.commute_records)
        in
        Ok ((), html_path)
       with e ->
         Interp.emit_inferred_phis := saved_emit;
         Error (VerifyError (Printexc.to_string e)))
    end

let check_assertions ?(opts = default_options) input =
  match resolve input with
  | Error e -> Error e
  | Ok prog ->
    configure opts;
    let prover : (module Servois2.Provers.Prover) = match opts.prover with
      | `CVC4 -> (module Servois2.Provers.ProverCVC4)
      | `CVC5 -> (module Servois2.Provers.ProverCVC5)
      | `Z3   -> (module Servois2.Provers.ProverZ3)
    | `Yices -> (module Servois2.Provers.ProverYices)
    in
    let html_session =
      if opts.html then begin
        let sdir = Html_output.create_session_dir () in
        Util.session_dir     := Some sdir;
        Util.commute_counter := 0;
        Util.commute_records := [];
        Some (sdir, input)
      end else None
    in
    (try
      let results = Analyze.collect_asserts_in_prog prog prover in
      let failures = List.filter_map (fun (loc_str, res) ->
        match res with
        | Servois2.Provers.Unsat -> None
        | Servois2.Provers.Sat _ ->
            Some (Printf.sprintf "Assert at %s: FAILED (counterexample exists)" loc_str)
        | Servois2.Provers.Unknown ->
            Some (Printf.sprintf "Assert at %s: unknown" loc_str)
      ) results in
      let html_path = match html_session with
        | None -> None
        | Some (sdir, inp) ->
          let source_file = match inp with
            | File path -> path
            | Source src ->
              let p = Filename.concat sdir "source.vcy" in
              let oc = open_out p in output_string oc src; close_out oc; p
            | Prog p ->
              let src = Ast_print.AstPP.string_of_prog p in
              let path = Filename.concat sdir "source.vcy" in
              let oc = open_out path in output_string oc src; close_out oc; path
          in
          Some (Html_output.generate
            ~source_file
            ~session_dir:sdir
            ~records:!Util.commute_records)
      in
      (match failures with
      | []   -> Ok ((), html_path)
      | msgs -> Error (VerifyError (String.concat "\n" msgs)))
    with e ->
      Error (VerifyError (Printexc.to_string e)))

let check_invariants ?(opts = default_options) input =
  match resolve input with
  | Error e -> Error e
  | Ok prog ->
    configure opts;
    let prover : (module Servois2.Provers.Prover) = match opts.prover with
      | `CVC4 -> (module Servois2.Provers.ProverCVC4)
      | `CVC5 -> (module Servois2.Provers.ProverCVC5)
      | `Z3   -> (module Servois2.Provers.ProverZ3)
    | `Yices -> (module Servois2.Provers.ProverYices)
    in
    (try
      let env = Interp.initialize_env prog false in
      let results = Invariants.check_prog env.g prover in
      let failures = List.filter_map (fun (loc, res) ->
        match res with
        | Servois2.Provers.Sat _   ->
            Some (Printf.sprintf "Loop invariant at %s: does not hold (counterexample exists)"
              (Range.string_of_range loc))
        | Servois2.Provers.Unsat   -> None
        | Servois2.Provers.Unknown ->
            Some (Printf.sprintf "Loop invariant at %s: could not be verified (unknown)"
              (Range.string_of_range loc))
      ) results in
      match failures with
      | []   -> Ok ()
      | msgs -> Error (VerifyError (String.concat "\n" msgs))
    with e ->
      Error (VerifyError (Printexc.to_string e)))

open Ast
open Util

type input =
  | File   of string
  | Source of string
  | Prog   of Ast.prog

type options = {
  prover  : [ `CVC4 | `CVC5 | `Z3 ];
  timeout : float option;
  use_ae  : bool;
}

let default_options = {
  prover  = `CVC5;
  timeout = None;
  use_ae  = false;
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
  in
  Util.servois2_synth_option := {
    Servois2.Synth.default_synth_options with
      prover  = prover;
      timeout = opts.timeout;
      use_ae  = opts.use_ae;
  };
  Util.servois2_verify_option := {
    Servois2.Verify.default_verify_options with
      prover = prover;
      use_ae = opts.use_ae;
  }

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
      (try
        let env = Interp.initialize_env prog true in
        Interp.emit_inferred_phis := saved_emit;
        Ok env.g
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
      (try
        let env = Interp.initialize_env prog false in
        let _ = Interp.verify_phis_of_prog env.g in
        Interp.emit_inferred_phis := saved_emit;
        Ok ()
       with e ->
         Interp.emit_inferred_phis := saved_emit;
         Error (VerifyError (Printexc.to_string e)))
    end

(** Veracity API — programmatic access to parse, interpret, infer, and verify. *)

(** Input to any API function. *)
type input =
  | File   of string    (** Path to a .vcy source file *)
  | Source of string    (** Raw source text *)
  | Prog   of Ast.prog  (** Pre-parsed AST *)

(** Options for inference and verification calls. *)
type options = {
  prover  : [ `CVC4 | `CVC5 | `Z3 ];
  timeout : float option;
  use_ae  : bool;
  html    : bool;  (** Generate a self-contained HTML report; [infer] returns its path. *)
}

val default_options : options

type error =
  | ParseError  of string
  | InterpError of string
  | InferError  of string
  | VerifyError of string

type 'a api_result = ('a, error) result

(** Parse input and return the AST. *)
val parse : input -> Ast.prog api_result

(** Interpret the program with the given argv (argv.(0) should be the program name). *)
val interp : ?opts:options -> input -> string array -> int64 api_result

(** Infer commutativity conditions; returns the global environment with PhiInf
    replaced by PhiExp entries, and the path to the generated HTML report when
    [opts.html = true] (None otherwise). *)
val infer : ?opts:options -> input -> (Ast.global_env * string option) api_result

(** Verify explicit commutativity conditions.  Returns [Ok ()] when all conditions
    are processed (individual condition results are printed to stdout as normal).
    Returns [Error (VerifyError _)] only on a runtime/solver exception. *)
val verify : ?opts:options -> input -> unit api_result

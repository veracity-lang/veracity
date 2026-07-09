(** Veracity API — programmatic access to parse, interpret, infer, and verify. *)

(** Input to any API function. *)
type input =
  | File   of string    (** Path to a .vcy source file *)
  | Source of string    (** Raw source text *)
  | Prog   of Ast.prog  (** Pre-parsed AST *)

(** Options for inference and verification calls. *)
type options = {
  prover  : [ `CVC4 | `CVC5 | `Z3 | `Yices ];
  timeout : float option;
  use_ae  : bool;
  html    : bool;    (** Generate a self-contained HTML report; [infer] returns its path. *)
  silent  : bool;    (** Suppress all stdout output from the interpreter (default [true] via API). *)
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

(** Verify explicit commutativity conditions.  Returns [Ok ((), html_path)] when
    all conditions are processed; [html_path] is the path to the generated report
    when [opts.html = true], [None] otherwise. Individual condition results are
    printed to stdout as normal. Returns [Error (VerifyError _)] only on a
    runtime/solver exception. *)
val verify : ?opts:options -> input -> (unit * string option) api_result

(** Check every annotated while-loop invariant in the program.
    Each invariant [I] on [while (G) invariant I { B }] is verified by
    checking [{I ∧ G} B {I}] using the configured SMT prover.
    Returns [Ok ()] if all invariants hold, [Error (VerifyError _)] if any
    fail (the message names the location and the failing invariant). *)
val check_invariants : ?opts:options -> input -> unit api_result

(** Check every assert() statement in every method of the program using
    VCGen-based strongest-postcondition reasoning.
    Returns [Ok ((), html_path)] if all assertions are verified; [html_path]
    is the HTML report path when [opts.html = true], [None] otherwise.
    Returns [Error (VerifyError msg)] listing each failed or unknown assertion. *)
val check_assertions : ?opts:options -> input -> (unit * string option) api_result

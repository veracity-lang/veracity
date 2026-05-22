# Veracity OCaml API

The `Vcy.Veracity` module exposes Veracity's parse/interpret/infer/verify pipeline as a typed OCaml API. Programs can be supplied as file paths, raw source strings, or pre-built ASTs; all functions return a `result` type rather than raising exceptions.

## Linking

The library is called `vcy`. Add it to your dune stanza:

```scheme
(executable
 (name my_tool)
 (libraries vcy))
```

Then open the module:

```ocaml
open Vcy
```

All API types and functions live in `Vcy.Veracity` (or just `Veracity` after the open).

## Types

### `input`

```ocaml
type input =
  | File   of string    (* path to a .vcy source file *)
  | Source of string    (* raw source text *)
  | Prog   of Ast.prog  (* pre-parsed AST *)
```

Every API function accepts any of the three forms. `File` reads and parses the file; `Source` parses the string in-memory; `Prog` skips parsing entirely.

### `options`

```ocaml
type options = {
  prover  : [ `CVC4 | `CVC5 | `Z3 ];
  timeout : float option;
  use_ae  : bool;
  html    : bool;
}

val default_options : options
(* { prover = `CVC5; timeout = None; use_ae = false; html = false } *)
```

`use_ae` enables forall/exists (AE) mode in Servois2, which is required when the program contains `havoc` statements.

`html` generates a self-contained HTML report in a fresh `/tmp/veracity_*` directory. Only meaningful with `infer`; the path to `index.html` is returned as the second element of the `Ok` tuple.

### `error`

```ocaml
type error =
  | ParseError  of string   (* lexer/parser failure *)
  | InterpError of string   (* runtime error during interpretation *)
  | InferError  of string   (* failure during condition inference *)
  | VerifyError of string   (* failure during condition verification *)
```

### `api_result`

```ocaml
type 'a api_result = ('a, error) result
```

Standard OCaml `result`; all API functions return this type.

## Functions

### `parse`

```ocaml
val parse : input -> Ast.prog api_result
```

Parses the input and returns the AST. Does not invoke any solver.

```ocaml
match Veracity.parse (Veracity.Source "int main(int argc, string[] argv) { return 0; }") with
| Ok prog  -> (* use prog *)
| Error (Veracity.ParseError msg) -> Printf.eprintf "Parse error: %s\n" msg
| Error _ -> assert false
```

### `interp`

```ocaml
val interp : ?opts:options -> input -> string array -> int64 api_result
```

Interprets the program. `argv.(0)` should be the program name (as with a normal C-style argv). Returns the integer value returned by `main`.

```ocaml
match Veracity.interp (Veracity.File "benchmarks/movers/counter.vcy") [| "counter"; "5" |] with
| Ok ret  -> Printf.printf "Return: %Ld\n" ret
| Error (Veracity.InterpError msg) -> Printf.eprintf "Runtime error: %s\n" msg
| Error _ -> assert false
```

### `infer`

```ocaml
val infer : ?opts:options -> input -> (Ast.global_env * string option) api_result
```

Infers commutativity conditions for every `commute _` block (i.e., blocks whose condition is `PhiInf`). Returns the global environment with each `PhiInf` entry replaced by a `PhiExp` holding the synthesised condition expression, paired with the HTML report path when `opts.html = true` (None otherwise).

If the program contains `havoc` statements and `opts.use_ae` is `false`, returns `Error (InferError _)` immediately with a message explaining that AE mode is required.

```ocaml
let opts = { Veracity.default_options with prover = `CVC5 } in
match Veracity.infer ~opts (Veracity.File "benchmarks/prepost/pre.vcy") with
| Ok (g, _) ->
    List.iter (fun (name, _m) ->
      Printf.printf "Method: %s\n" name) g.Ast.methods
| Error (Veracity.InferError msg) -> Printf.eprintf "Inference failed: %s\n" msg
| Error _ -> assert false
```

**Nondeterministic programs.** When the program uses `havoc`, set `use_ae = true`:

```ocaml
let opts = { Veracity.default_options with prover = `CVC5; use_ae = true } in
Veracity.infer ~opts (Veracity.File "my_havoc_program.vcy")
```

**HTML report.** Generate a self-contained HTML report alongside inference:

```ocaml
let opts = { Veracity.default_options with prover = `CVC5; html = true } in
match Veracity.infer ~opts (Veracity.File "benchmarks/prepost/pre.vcy") with
| Ok (_, Some path) -> Printf.printf "Report: %s\n" path
| Ok (_, None)      -> assert false
| Error _           -> ()
```

### `verify`

```ocaml
val verify : ?opts:options -> input -> (unit * string option) api_result
```

Verifies explicit commutativity conditions (blocks whose condition is `PhiExp e`). Individual results are printed to stdout in the same format as the CLI. Returns `Ok ((), html_path)` once all conditions have been processed; `html_path` is the path to the generated report when `opts.html = true`, `None` otherwise. Returns `Error (VerifyError _)` only on a solver or runtime exception.

As with `infer`, programs containing `havoc` without `use_ae = true` return an error immediately.

```ocaml
let opts = { Veracity.default_options with prover = `CVC5 } in
match Veracity.verify ~opts (Veracity.File "benchmarks/verify/even-odd.vcy") with
| Ok ((), _) -> ()
| Error (Veracity.VerifyError msg) -> Printf.eprintf "Verify error: %s\n" msg
| Error _ -> assert false
```

**HTML report.** Generate a self-contained HTML report alongside verification:

```ocaml
let opts = { Veracity.default_options with prover = `CVC5; html = true } in
match Veracity.verify ~opts (Veracity.File "benchmarks/verify/even-odd.vcy") with
| Ok ((), Some path) -> Printf.printf "Report: %s\n" path
| Ok ((), None)      -> assert false
| Error _            -> ()
```

## Error handling summary

| Situation | Error variant |
|-----------|--------------|
| Syntax error in source | `ParseError` |
| File not found | `ParseError` |
| Runtime exception during interpretation | `InterpError` |
| `havoc` present but `use_ae = false` | `InferError` / `VerifyError` |
| Solver or analysis failure during inference | `InferError` |
| Solver or analysis failure during verification | `VerifyError` |

## Complete example

```ocaml
open Vcy

let () =
  let opts = { Veracity.default_options with prover = `CVC5 } in

  (* Infer conditions from a source string *)
  let src = {|
    int main(int argc, string[] argv) {
      int x = int_of_string(argv[1]);
      int y = int_of_string(argv[2]);
      commute _ {
        { x = x + 1; }
        { y = y + 1; }
      }
      return 0;
    }
  |} in

  match Veracity.infer ~opts (Veracity.Source src) with
  | Ok (_g, _html) -> print_endline "Inference complete."
  | Error (Veracity.InferError msg) ->
      Printf.eprintf "Inference error: %s\n" msg;
      exit 1
  | Error (Veracity.ParseError msg) ->
      Printf.eprintf "Parse error: %s\n" msg;
      exit 1
  | Error _ -> assert false
```

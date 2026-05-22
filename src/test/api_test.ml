open OUnit2
open Vcy

(* Path helpers — tests run from the dune build directory, so we need to
   reach the repo root. *)
let bench path = "../" ^ path

(* ------------------------------------------------------------------ helpers *)

let assert_ok msg = function
  | Ok _    -> ()
  | Error _ -> assert_failure (msg ^ ": expected Ok, got Error")

let assert_error msg = function
  | Error _ -> ()
  | Ok _    -> assert_failure (msg ^ ": expected Error, got Ok")

let assert_parse_error msg = function
  | Error (Veracity.ParseError _) -> ()
  | Error _ -> assert_failure (msg ^ ": expected ParseError")
  | Ok _    -> assert_failure (msg ^ ": expected Error, got Ok")

(* ------------------------------------------------------------------ parse *)

let simple_src = {|
int main(int argc, string[] argv) {
  int x = 3;
  return x;
}
|}

let test_parse_string _ =
  assert_ok "parse from string" (Veracity.parse (Veracity.Source simple_src))

let test_parse_file _ =
  assert_ok "parse pre.vcy from file"
    (Veracity.parse (Veracity.File (bench "benchmarks/prepost/pre.vcy")))

let test_parse_ast _ =
  match Veracity.parse (Veracity.Source simple_src) with
  | Error _ -> assert_failure "could not parse simple source"
  | Ok prog ->
    assert_ok "parse from Ast variant" (Veracity.parse (Veracity.Prog prog))

let test_parse_error _ =
  assert_parse_error "bad syntax"
    (Veracity.parse (Veracity.Source "this is not valid vcy @@@"))

let test_parse_missing_file _ =
  assert_parse_error "missing file"
    (Veracity.parse (Veracity.File "/no/such/file.vcy"))

(* ------------------------------------------------------------------ interp *)

let interp_src = {|
int main(int argc, string[] argv) {
  int x = int_of_string(argv[1]);
  return x + 1;
}
|}

let test_interp_basic _ =
  let result =
    Veracity.interp (Veracity.Source interp_src)
      [| "prog"; "41" |]
  in
  match result with
  | Error _ -> assert_failure "interp returned Error"
  | Ok n    -> assert_equal ~printer:Int64.to_string 42L n

(* ------------------------------------------------------------------ infer *)

let test_infer_pre _ =
  assert_ok "infer pre.vcy"
    (Veracity.infer (Veracity.File (bench "benchmarks/prepost/pre.vcy")))

let test_infer_hoare _ =
  assert_ok "infer hoare.vcy"
    (Veracity.infer (Veracity.File (bench "benchmarks/prepost/hoare.vcy")))

(* After inference the returned global_env should have non-empty methods list
   (the main method is always present). *)
let test_infer_has_methods _ =
  match Veracity.infer (Veracity.File (bench "benchmarks/prepost/pre.vcy")) with
  | Error _ -> assert_failure "infer returned Error"
  | Ok (g, _) -> assert_bool "methods non-empty" (g.Ast.methods <> [])

(* ------------------------------------------------------------------ verify *)

let test_verify_even_odd _ =
  assert_ok "verify even-odd.vcy"
    (Veracity.verify (Veracity.File (bench "benchmarks/verify/even-odd.vcy")))

(* ------------------------------------------------------------------ havoc guard *)

let havoc_src = {|
int main(int argc, string[] argv) {
  int x = 0;
  commute _ {
    { havoc x; }
    { x = x + 1; }
  }
  return x;
}
|}

let test_infer_havoc_without_ae _ =
  match Veracity.infer (Veracity.Source havoc_src) with
  | Error (Veracity.InferError msg) ->
    assert_bool "error mentions -ae" (String.length msg > 0)
  | Error _ -> assert_failure "wrong error variant"
  | Ok _    -> assert_failure "expected Error for havoc without -ae"

let test_infer_havoc_with_ae _ =
  assert_ok "infer havoc with use_ae"
    (Veracity.infer ~opts:{ Veracity.default_options with use_ae = true }
       (Veracity.Source havoc_src))

(* ------------------------------------------------------------------ suite *)

let suite =
  "Veracity API" >::: [
    "parse/string"       >:: test_parse_string
  ; "parse/file"         >:: test_parse_file
  ; "parse/ast"          >:: test_parse_ast
  ; "parse/syntax-error" >:: test_parse_error
  ; "parse/missing-file" >:: test_parse_missing_file
  ; "interp/basic"       >:: test_interp_basic
  ; "infer/pre"          >:: test_infer_pre
  ; "infer/hoare"        >:: test_infer_hoare
  ; "infer/has-methods"  >:: test_infer_has_methods
  ; "verify/even-odd"    >:: test_verify_even_odd
  ; "infer/havoc-no-ae"  >:: test_infer_havoc_without_ae
  ; "infer/havoc-ae"     >:: test_infer_havoc_with_ae
  ]

let () = run_test_tt_main suite

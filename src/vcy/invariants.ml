open Ast
open Util

(* Check the inductive step of one loop invariant:
     {I ∧ G} B {I}
   Constructs the block [assume(I && G); body...; assert(I)] and dispatches
   it through the existing assert-VCG infrastructure.
   Returns one result per assert in the block (there is exactly one). *)
let check_while_invariant
    (g : global_env)
    (defs : ty bindlist)
    (guard : exp node)
    (inv   : exp node)
    (body  : block node)
    (prover : (module Servois2.Provers.Prover))
  : (Range.t * Servois2.Provers.solve_result) list =
  let assume_stmt = no_loc @@ Assume (no_loc @@ Bop (And, inv, guard)) in
  let assert_stmt = no_loc @@ Assert inv in
  let augmented : block = [assume_stmt] @ body.elt @ [assert_stmt] in
  let global_binds = List.map (fun (id,(ty,_)) -> (id, ty)) g.globals in
  let vars = defs @ global_binds in
  Analyze.check_asserts_of_block augmented vars prover

(* Recurse through a block, threading accumulated local type bindings so that
   variables declared before a While are visible to its invariant check. *)
let rec check_block
    (g      : global_env)
    (defs   : ty bindlist)
    (body   : block node)
    (prover : (module Servois2.Provers.Prover))
  : (Range.t * Servois2.Provers.solve_result) list =
  let rec go defs = function
    | [] -> []
    | stmt :: rest ->
        let results = check_stmt g defs stmt prover in
        let defs' = match stmt.elt with
          | Decl (id, (ty, _)) -> (id, ty) :: defs
          | _ -> defs
        in
        results @ go defs' rest
  in
  go defs body.elt

and check_stmt
    (g      : global_env)
    (defs   : ty bindlist)
    (stmt   : stmt node)
    (prover : (module Servois2.Provers.Prover))
  : (Range.t * Servois2.Provers.solve_result) list =
  match stmt.elt with
  | While (guard, Some inv, body) ->
      check_while_invariant g defs guard inv body prover
      @ check_block g defs body prover
  | While (_, None, body) ->
      check_block g defs body prover
  | If (_, b1, b2) ->
      check_block g defs b1 prover
      @ check_block g defs b2 prover
  | For (vds, _, _, body) ->
      let defs' = List.fold_left (fun d (id,(ty,_)) -> (id,ty) :: d) defs vds in
      check_block g defs' body prover
  | Commute (_, _, blocks, _, _) ->
      List.concat_map (fun b -> check_block g defs b prover) blocks
  | _ -> []

(* Walk all methods in the program and check every annotated while-loop
   invariant.  Returns a list of (location, solve_result) pairs — one per
   loop invariant found. *)
let check_prog
    (g      : global_env)
    (prover : (module Servois2.Provers.Prover))
  : (Range.t * Servois2.Provers.solve_result) list =
  let global_binds = List.map (fun (id,(ty,_)) -> (id, ty)) g.globals in
  List.concat_map (fun (name, m) ->
    (* Use mdecl_of_tmethod to get args in (ty * id) order, then flip to
       (id * ty) = ty bindlist as expected by check_asserts_of_block. *)
    let mdecl = mdecl_of_tmethod name m in
    let arg_binds = List.map (fun (ty, id) -> (id, ty)) mdecl.args in
    let defs = arg_binds @ global_binds in
    check_block g defs m.body prover
  ) g.methods

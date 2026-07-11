open Ast
open Util

let rec assoc_servois_ty (id : id) : embedding_map -> ty binding =
  function
  | [] -> raise @@ UnreachableFailure "ID not found"
  | (v,h)::t ->
    begin match h with
    | ETInt i when id = i -> v
    | ETBool i when id = i -> v
    | ETArr (i, _) when id = i -> v
    | ETHashTable (_,_,{ht;keys;size}) 
      when id = ht || id = keys || id = size -> v
    | _ -> assoc_servois_ty id t
    end

let generate_embedding_map (vars : ty bindlist) : embedding_map =
  let f (id, t) : ety =
    match t with
    | TInt -> ETInt id
    | TLoc -> ETInt id
    | TBool -> ETBool id
    | TStr -> ETStr id
    | TArr t -> ETArr (id, sty_of_ty t)
    | THashTable (tyk, tyv) ->
      ETHashTable
        ( sty_of_ty tyk, sty_of_ty tyv, 
          { ht = id ; keys = id ^ "_keys"; size = id ^ "_size" })
    | _ -> raise @@ NotImplemented "Unsupported type embedding"
  in
  List.map (fun v -> v, f v) vars


let rec smt_translation (input: Smt.exp) (embedding: embedding_map) : exp =
  let exp_node e = no_loc @@ smt_translation e embedding in
  match input with
  | EVar (Var s) | EVar (VarPost s) | EVar (VarM(_, s)) -> 
    let len = String.length s in
    if len < 5 then Id s
    else if String.sub s (len - 5) 5 = "_size"
    then Call(MethodL("ht_size", List.assoc "ht_size" Vcylib.lib_hashtable), [no_loc @@ Id(String.sub s 0 (len - 5))])
    else if String.sub s (len - 5) 5 = "_keys"
    then Id(String.sub s 0 (len - 5))
    else Id s
  | EArg i -> failwith "Not Implemented"
  | EConst c -> 
    begin match c with
    | CInt i -> CInt (Int64.of_int i)
    | CBool b -> CBool b 
    | CString s -> CStr s 
    end
  | EBop (bop, exp1, exp2) ->
    Bop (smt_bop_to_binop bop, exp_node exp1, exp_node exp2)
  | EUop (uop, exp) -> 
    Uop (smt_uop_to_unop uop, exp_node exp)
  | ELop (lop, expl) ->
    let rec elop_trans l =
      match l with
      | e1 :: e2 :: [] -> Bop (smt_lop_to_binop lop, exp_node e1, exp_node e2)
      | e :: el -> Bop (smt_lop_to_binop lop, exp_node e, no_loc (elop_trans el))
      | _ -> failwith "Wrong number of parameters."
    in
    elop_trans expl
  | ELet (exp_bindl, exp) -> failwith "ELET"
  | EITE (cexp, texp, fexp) -> failwith "EITE"
  | EFunc (s, expl) ->
    begin match s , expl with
    | "=", [e1; e2] -> smt_translation (EBop (Eq, e1, e2)) embedding
    | ">", [e1; e2] -> smt_translation (EBop (Gt, e1, e2)) embedding
    | "member", [e1; e2] | "set.member", [e1; e2] -> 
      let elem = exp_node e1 in 
      begin match e2 with
      | EVar (Var id) ->
        let id, t = assoc_servois_ty id embedding in
        begin match t with
        | THashTable _ ->
          CallRaw ("ht_mem", [no_loc @@ Id id; elem])
        | _ -> raise @@ Failure "Bad variable type for 'member'"
        end
      | _ -> raise @@ NotImplemented "Can't currently handle complicated things; requires recursive expression typechecking"
      end
    | "select", [e1; e2] ->
      let key = exp_node e2 in
      begin match e1 with
      | EVar (Var id) ->
        let id, t = assoc_servois_ty id embedding in
        begin match t with
        | TArr _ ->
          Index (no_loc @@ Id id, key)
        | THashTable _ ->
          Index (no_loc @@ Id id, key)
        | _ -> raise @@ Failure "Bad variable type for 'select'"
        end
      | _ -> raise @@ NotImplemented "Can't currently handle complicated things; requires recursive expression typechecking"
      end
    | "insert", [e1; e2] | "set.insert", [e1; e2] -> 
      let elem = exp_node e1 in 
        begin match e2 with
        | EVar (Var id) ->
          let id, t = assoc_servois_ty id embedding in
          begin match t with
          | THashTable _ ->
            CallRaw ("ht_put", [no_loc @@ Id id; elem])
          | _ -> raise @@ Failure "Bad variable type for 'insert'"
          end
        | _ -> raise @@ NotImplemented "Can't currently handle complicated things; requires recursive expression typechecking"
        end
    | _ -> failwith @@ "Function "^s^" not recognized or supported or improper arguments applied"
    end
  | EExists(binding, exp) -> raise @@ Failure "Cannot translate existential quantifier back from smt"

let exp_of_phi (phi : Servois2.Phi.disjunction) (embedding: embedding_map) : exp =
  smt_translation (Servois2.Phi.smt_of_disj phi) embedding
  
let phi_of_blocks (genv: global_env) (cv: commute_variant) (blks: block node list) (vars : ty bindlist) pre post =
  let embedding = generate_embedding_map vars in
  (* Point Servois2 at this commute's subdir *before* compiling the spec:
     compile_blocks_to_spec itself writes veracity_spec.smt through
     Servois2.Util.outfile, which would otherwise land in a stray
     servois2_output/ tree of its own. *)
  let commute_subdir = match !Util.session_dir with
    | None -> None
    | Some sdir ->
      let n = !Util.commute_counter in
      Util.commute_counter := n + 1;
      let d = Servois2.Rundir.child ~parent:sdir
                ~name:(Printf.sprintf "commute_%04d" n) in
      Servois2.Util.output_dir := Some d;
      Servois2.Util.query_counter := 0;
      Servois2.Diagram.diagram_counter := 0;
      Some d
  in
  let [@warning "-8"] spec , [m1;m2] = Spec_generator.compile_blocks_to_spec genv blks embedding pre post
  in
  Servois2.Choose.choose := Servois2.Choose.poke2;
  begin match cv with
  | CommuteVarLM ->
    Servois2.Solve.mode := Servois2.Solve.LeftMover
  | CommuteVarRM ->
    Servois2.Solve.mode := Servois2.Solve.RightMover
  | _ -> () end;
  let phi, _ = Servois2.Synth.synth ~options:!Util.servois2_synth_option spec m1 m2 in
  Printf.eprintf "%f, %f, %f, %d, %b\n" (!Servois2.Synth.last_benchmarks.time) (!Servois2.Synth.last_benchmarks.synth_time) (!Servois2.Synth.last_benchmarks.lattice_construct_time) (!Servois2.Synth.last_benchmarks.n_atoms) (!Servois2.Synth.last_benchmarks.answer_incomplete);
  Servois2.Solve.mode := Servois2.Solve.Bowtie;
  Servois2.Util.output_dir := None;
  Util.pending_subdir := commute_subdir;
  exp_of_phi phi embedding

let rec block_has_havoc (b : block) =
  List.exists stmt_has_havoc b
and stmt_has_havoc (s : stmt node) =
  match s.elt with
  | Havoc _ -> true
  | If (_, b1, b2) -> block_has_havoc b1.elt || block_has_havoc b2.elt
  | While (_, _, b)   -> block_has_havoc b.elt
  | For (_, _, _, b) -> block_has_havoc b.elt
  | Commute (_, _, bls, _, _) -> List.exists (fun b -> block_has_havoc b.elt) bls
  | _ -> false

let prog_has_havoc (prog : prog) =
  List.exists (function
    | Gmdecl m -> block_has_havoc m.elt.body.elt
    | _ -> false) prog

(* ── Assert checking ─────────────────────────────────────────────────────── *)

(* Build a self-contained SMT-LIB2 query whose satisfiability determines
   whether vc (a boolean sexp) can be falsified.  UNSAT → assertion proved. *)
(* The heap model variables that Spec_generator.generate_spec_state adds to the
   commute-spec state.  The VCGen assert queries also reference them — a TLoc
   'x != null' compiles to '0 <= x < heap_alloc' — so they must be declared here
   too, otherwise CVC5/Z3 reject the query with "Symbol heap_alloc is not
   declared" and the assert is skipped.  They are unconstrained (harmless) when
   the program does not use the heap. *)
let heap_model_decls : string list =
  let arr = Servois2.Smt.string_of_ty (Servois2.Smt.TArray (Servois2.Smt.TInt, Servois2.Smt.TInt)) in
  let int = Servois2.Smt.string_of_ty Servois2.Smt.TInt in
  [ sp "(declare-fun heap_value () %s)" arr
  ; sp "(declare-fun heap_next () %s)"  arr
  ; sp "(declare-fun heap_alloc () %s)" int ]

let assert_smt_query (embedding_vars: embedding_map) (vc: Smt.exp) : string =
  let stypes = Spec_generator.get_stypes embedding_vars in
  let decls = List.map (fun (id, sty) ->
    sp "(declare-fun %s () %s)" id (Servois2.Smt.string_of_ty sty)
  ) stypes in
  (* Avoid double-declaring a heap-model var if the embedding already has one. *)
  let declared_ids = List.map (fun (id, _) -> id) stypes in
  let heap_decls =
    List.filteri
      (fun i _ ->
         let name = List.nth ["heap_value"; "heap_next"; "heap_alloc"] i in
         not (List.mem name declared_ids))
      heap_model_decls
  in
  String.concat "\n" @@
    ["(set-logic ALL)"]
    @ decls
    @ heap_decls
    @ [ sp "(assert (not %s))" (Servois2.Smt.string_of_smt vc)
      ; "(check-sat)" ]

(* Verify every assert() in block.  vars are the method parameters (or any
   variables in scope before the block); they become SMT declare-funs.
   Returns (location, result) for each assert found. *)
let check_asserts_of_block (block: Ast.block)
    (vars: ty bindlist)
    (prover: (module Servois2.Provers.Prover))
    : (Range.t * Servois2.Provers.solve_result) list =
  let embedding = generate_embedding_map vars in
  Spec_generator.gstates := embedding;
  Hashtbl.clear Spec_generator.variable_ctr_list;
  List.iter (fun ((id,_),_) ->
    Hashtbl.replace Spec_generator.variable_ctr_list id (ref 0)
  ) embedding;
  let extra_vars = ref [] in
  let vcs = Spec_generator.generate_assert_vcs block extra_vars in
  List.filter_map (fun (loc, vc) ->
    match
      let query = assert_smt_query (embedding @ !extra_vars) vc in
      Servois2.Provers.parse_prover_output prover
        (Servois2.Provers.run_prover prover query)
    with
    | result -> Some (loc, result)
    | exception e ->
      let query_for_diag = assert_smt_query (embedding @ !extra_vars) vc in
      let tmp = Filename.temp_file "conquoer_vc_fail_" ".smt2" in
      (try let oc = open_out tmp in output_string oc query_for_diag; close_out oc
       with _ -> ());
      Printf.eprintf "Warning: skipping assert at %s: %s [query dumped to %s]\n"
        (Range.string_of_range loc) (Printexc.to_string e) tmp;
      None
  ) vcs

(* Scan every method in prog and check its assert() statements. *)
(* Returns true iff every assertion in every method was verified. *)
let check_asserts_in_prog (prog: Ast.prog)
    (prover: (module Servois2.Provers.Prover)) : bool =
  let all_ok = ref true in
  let gvars = List.filter_map (function
    | Ast.Gvdecl gv -> Some (gv.elt.Ast.name, gv.elt.Ast.ty)
    | _ -> None) prog
  in
  List.iter (function
    | Ast.Gmdecl m ->
      let meth = m.elt in
      let params = List.map (fun (ty, id) -> (id, ty)) meth.args in
      let results = check_asserts_of_block meth.body.elt (gvars @ params) prover in
      List.iter (fun (loc, result) ->
        let status = match result with
          | Servois2.Provers.Unsat   -> "verified"
          | Servois2.Provers.Sat _   -> (all_ok := false; "FAILED (counterexample exists)")
          | Servois2.Provers.Unknown -> (all_ok := false; "unknown")
        in
        Printf.printf "Assert at %s: %s\n" (Range.string_of_range loc) status
      ) results
    | _ -> ()
  ) prog;
  !all_ok

(* Silent variant used by the API: collects (location_string, result) pairs
   without printing to stdout.  Global variable declarations are included in
   the embedding so that infer_gstates_type returns correct array types (e.g.
   Location : tloc[][] = TArr(TArr TLoc)) rather than defaulting to TInt.
   This is necessary for null-coercion in indexed assignments to work correctly
   when the RHS is CNull TLoc but the slot element type is TArr TLoc. *)
let collect_asserts_in_prog (prog: Ast.prog)
    (prover: (module Servois2.Provers.Prover))
    : (string * Servois2.Provers.solve_result) list =
  let gvars = List.filter_map (function
    | Ast.Gvdecl gv -> Some (gv.elt.Ast.name, gv.elt.Ast.ty)
    | _ -> None) prog
  in
  List.concat_map (function
    | Ast.Gmdecl m ->
      let meth = m.elt in
      let params = List.map (fun (ty, id) -> (id, ty)) meth.args in
      let results = check_asserts_of_block meth.body.elt (gvars @ params) prover in
      List.map (fun (loc, result) -> (Range.string_of_range loc, result)) results
    | _ -> []
  ) prog

let rec subst_sfx sfx names (smt : Servois2.Smt.exp) : Servois2.Smt.exp =
  let go e = subst_sfx sfx names e in
  match smt with
  | Servois2.Smt.EVar (Servois2.Smt.Var n) when List.mem n names ->
      Servois2.Smt.EVar (Servois2.Smt.Var (n ^ sfx))
  | Servois2.Smt.EVar _ -> smt
  | Servois2.Smt.EBop (op, e1, e2) -> Servois2.Smt.EBop (op, go e1, go e2)
  | Servois2.Smt.ELop (op, es) -> Servois2.Smt.ELop (op, List.map go es)
  | Servois2.Smt.EUop (op, e) -> Servois2.Smt.EUop (op, go e)
  | Servois2.Smt.EConst _ -> smt
  | Servois2.Smt.EFunc (f, es) -> Servois2.Smt.EFunc (f, List.map go es)
  | Servois2.Smt.EITE (c, t, f) -> Servois2.Smt.EITE (go c, go t, go f)
  | Servois2.Smt.ELet (bs, e) ->
      Servois2.Smt.ELet (List.map (fun (v, e) -> (v, go e)) bs, go e)
  | Servois2.Smt.EForall (binds, e) -> Servois2.Smt.EForall (binds, go e)
  | Servois2.Smt.EExists (binds, e) -> Servois2.Smt.EExists (binds, go e)
  | Servois2.Smt.EArg _ -> smt

let verify_of_block e genv cv blks vars pre post : bool option * bool option =
  let embedding = generate_embedding_map vars in
  let [@warning "-8"] spec , [m1;m2] = Spec_generator.compile_blocks_to_spec genv blks embedding pre post in
  let cond = (fst @@ Spec_generator.exp_to_smt_exp e 1 Spec_generator.variable_ctr_list) in
  begin match cv with
  | CommuteVarLM | CommuteVarLMCtx _ -> Servois2.Solve.mode := Servois2.Solve.LeftMover
  | CommuteVarRM | CommuteVarRMCtx _ -> Servois2.Solve.mode := Servois2.Solve.RightMover
  | _ -> () end;
  let ctx_12_opt = match cv with
    | CommuteVarRMCtx ctx_exp | CommuteVarLMCtx ctx_exp ->
        let ctx_init = fst @@ Spec_generator.exp_to_smt_exp ctx_exp Spec_generator.right Spec_generator.variable_ctr_list in
        let state_names = List.map (fun (v, _) -> Servois2.Smt.string_of_var v) spec.state in
        Some (subst_sfx "12" state_names ctx_init)
    | _ -> None
  in
  let result =
    let main = Servois2.Verify.verify ~options:!Util.servois2_verify_option ~ctx_post_12:ctx_12_opt spec m1 m2 cond in
    let compl = match cv with
      | CommuteVarLM | CommuteVarRM | CommuteVarLMCtx _ | CommuteVarRMCtx _ -> None
      | _ -> Servois2.Verify.verify ~options:{(!Util.servois2_verify_option) with ncom = true} spec m1 m2 (EUop(Not, cond))
    in
    (main, compl)
  in
  Servois2.Solve.mode := Servois2.Solve.Bowtie;
  Servois2.Util.finalize_examine m1 m2 "verify";
  result

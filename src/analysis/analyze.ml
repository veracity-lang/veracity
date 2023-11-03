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
  
let phi_of_blocks (genv: global_env) (_: commute_variant) (blks: block node list) (vars : ty bindlist) =
  let embedding = generate_embedding_map vars in
  let [@warning "-8"] spec , [m1;m2] = Spec_generator.compile_blocks_to_spec genv blks embedding
  in
  Servois2.Choose.choose := Servois2.Choose.poke2;
  let phi, _ = Servois2.Synth.synth ~options:!Util.servois2_synth_option spec m1 m2 in
    Printf.eprintf "%f, %f, %f, %d, %b\n" (!Servois2.Synth.last_benchmarks.time) (!Servois2.Synth.last_benchmarks.synth_time) (!Servois2.Synth.last_benchmarks.lattice_construct_time) (!Servois2.Synth.last_benchmarks.n_atoms) (!Servois2.Synth.last_benchmarks.answer_incomplete);
    exp_of_phi phi embedding
  (* Servois2.Choose.choose := Servois2.Choose.poke2; *)

let verify_of_block e genv _ blks vars : bool option * bool option =
  let embedding = generate_embedding_map vars in
  let [@warning "-8"] spec , [m1;m2] = Spec_generator.compile_blocks_to_spec genv blks embedding in
  let cond = (fst @@ Spec_generator.exp_to_smt_exp e 1 Spec_generator.variable_ctr_list) in
  Servois2.Verify.verify spec m1 m2 cond,
  Servois2.Verify.verify ~options:{Servois2.Verify.default_verify_options with ncom = true} spec m1 m2 (EUop(Not, cond))

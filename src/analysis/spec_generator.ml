open Servois2.Spec
open Servois2.Smt
open Util
open Ast_print
open Ast


let left = 0 (* indicates the left of assignment *)
let right = 1 (* indicates the right of assignment *)

let mIndex = ref 0
let predicates_list = ref []
let gstates = ref [] 

let terms_list = ref []
let variable_ctr_list = (Hashtbl.create 50)
(* Allocation-validity conditions accumulated during exp_to_smt_exp for heap
   dereferences; consumed statement-by-statement in compile_block_to_smt. *)
let deref_conds : sexp list ref = ref []

(*
  heap_alloc : Int (next fresh ID)
  heap_value : Int -> Int (loc to value)
  heap_next  : Int -> Int (loc to next loc)
*)
let heap_model_vars = [ "heap_alloc"; "heap_value"; "heap_next" ]

let pre = ref (EConst (CBool true))

(* Set to false when none of the commute-block methods use heap operations.
 * When false, heap variables are kept in spec.state but their postcondition
 * equalities are emitted as flat top-level conjuncts (outside any ITE),
 * which lets the SMT solver find the array witnesses trivially. *)
let use_heap = ref true

let rec exp_uses_heap (e : exp node) = match e.elt with
  | HeapAlloc _ | HeapValue _ | HDerefValue _ | HDerefNext _ -> true
  | Bop (_, e1, e2)       -> exp_uses_heap e1 || exp_uses_heap e2
  | Uop (_, e1)           -> exp_uses_heap e1
  | Ternary (g, t, f)     -> exp_uses_heap g  || exp_uses_heap t || exp_uses_heap f
  | Index (e1, e2)        -> exp_uses_heap e1 || exp_uses_heap e2
  | Call (_, es) | CallRaw (_, es) -> List.exists exp_uses_heap es
  | CArr (_, es)          -> List.exists exp_uses_heap es
  | Proj (e1, _) | NewArr (_, e1) -> exp_uses_heap e1
  | Exists (_, _, body)   -> exp_uses_heap body
  | _                     -> false

and stmt_uses_heap (s : stmt node) = match s.elt with
  | Assn (e1, e2)         -> exp_uses_heap e1 || exp_uses_heap e2
  | Decl (_, (_, e))      -> exp_uses_heap e
  | Ret (Some e)          -> exp_uses_heap e
  | Ret None              -> false
  | SCallRaw (_, es)      -> List.exists exp_uses_heap es
  | SCall (_, es)         -> List.exists exp_uses_heap es
  | If (e, b1, b2)        -> exp_uses_heap e || block_uses_heap b1.elt || block_uses_heap b2.elt
  | While (e, inv, b)     -> exp_uses_heap e
                             || (match inv with Some i -> exp_uses_heap i | None -> false)
                             || block_uses_heap b.elt
  | For (vds, eo, sno, b) ->
      List.exists (fun (_, (_, e)) -> exp_uses_heap e) vds
      || (match eo  with None -> false | Some e -> exp_uses_heap e)
      || (match sno with None -> false | Some s -> stmt_uses_heap s)
      || block_uses_heap b.elt
  | Raise e | Assert e | Assume e | Require e -> exp_uses_heap e
  | Commute (_, _, bls, cpre, cpost) ->
      List.exists (fun b -> block_uses_heap b.elt) bls
      || (match cpre  with None -> false | Some e -> exp_uses_heap e)
      || (match cpost with None -> false | Some e -> exp_uses_heap e)
  | Havoc _ -> false

and block_uses_heap b = List.exists stmt_uses_heap b

let blocks_use_heap blks = List.exists (fun b -> block_uses_heap b.elt) blks

let sexp_of_sexp_list = function
  | [e] -> e
  | es -> ELop(And, es)

let get_stypes (embedding_vars : (ty binding * ety) list) : sty bindlist = 
  List.concat_map ( fun ((id,ty),ety) -> compile_ety_to_sty id ety ) embedding_vars

let smt_negone () = (EUop (Smt.Neg, Smt.EConst (CInt (1))))

let generate_spec_predicates (embedding_vars : (ty binding * ety) list) : Servois2.Smt.pred_sig list =
  List.iter (
    fun (_,sty) -> predicates_list := Smt.PredSig ("=", [sty; sty]) :: !predicates_list;
                  match sty with | Smt.TInt -> predicates_list := Smt.PredSig (">", [sty; sty]) :: !predicates_list; | _ -> ()
  ) (get_stypes embedding_vars);
  Util.remove_duplicate !predicates_list


let generate_spec_statesEqual (em_vars : (ty binding * ety) list) : sexp =
  let loc_vars, other_vars = List.partition (fun ((_, ty), _) -> ty = TLoc) em_vars in
  let loc_varnames   = List.map (fun ((id, _), _) -> id) loc_vars in
  (* tloc[] arrays get element-wise bijection; all other non-scalar-TLoc vars get plain equality *)
  let loc_arr_vars, plain_vars =
    List.partition (fun ((_, ty), _) -> ty = TArr TLoc) other_vars in
  let loc_arr_names =
    List.concat_map (fun ((id,_),ety) -> List.map fst (compile_ety_to_sty id ety)) loc_arr_vars in
  let other_varnames =
    List.concat_map (fun ((id,_),ety) -> List.map fst (compile_ety_to_sty id ety)) plain_vars in

  (* The bijection is determined by the tloc program variables:
       null  -> null
       v     -> v_new   for each tloc var v
       other -> other   (identity for untracked locations)
     Encoded as a quantifier-free ITE chain. *)
  let apply_bij x =
    let with_locs = List.fold_right (fun v acc ->
      EITE (EBop (Eq, x, EVar (Var v)), EVar (VarPost v), acc)
    ) loc_varnames x in
    EITE (EBop (Eq, x, smt_negone ()), smt_negone (), with_locs)
  in

  (* heap_alloc: same number of allocations in both orders *)
  let alloc_eq = EBop (Eq, EVar (Var "heap_alloc"), EVar (VarPost "heap_alloc")) in

  (* For each tloc variable v: heap_value[v] = heap_value_new[v_new] *)
  let value_eqs = List.map (fun n ->
    EBop (Eq,
      EFunc ("select", [EVar (Var "heap_value"); EVar (Var n)]),
      EFunc ("select", [EVar (VarPost "heap_value"); EVar (VarPost n)]))
  ) loc_varnames in

  (* For each tloc variable v: apply_bij(heap_next[v]) = heap_next_new[v_new] *)
  let next_eqs = List.map (fun n ->
    EBop (Eq,
      apply_bij (EFunc ("select", [EVar (Var "heap_next"); EVar (Var n)])),
      EFunc ("select", [EVar (VarPost "heap_next"); EVar (VarPost n)]))
  ) loc_varnames in

  (* For each tloc[] array: ∀ i. bij(arr[i]) = arr_new[i]
     Smt.TInt is qualified because open Ast (last) shadows the unqualified TInt. *)
  let loc_arr_eqs = List.map (fun n ->
    EForall ([(Var "i__ext", Smt.TInt)],
      EBop (Eq,
        apply_bij (EFunc ("select", [EVar (Var n);     EVar (Var "i__ext")])),
                   EFunc ("select", [EVar (VarPost n); EVar (Var "i__ext")])))
  ) loc_arr_names in

  (* other program variables: plain equality *)
  let other_eqs = List.map (fun n ->
    EBop (Eq, EVar (Var n), EVar (VarPost n))
  ) other_varnames in

  sexp_of_sexp_list ([alloc_eq] @ value_eqs @ next_eqs @ loc_arr_eqs @ other_eqs)

let generate_spec_state (embedding_vars: (ty binding * ety) list) : sty Smt.bindlist = 
    List.concat_map (fun ((id,ty),ety) -> let list_of_sty = compile_ety_to_sty id ety in
                        List.map (fun (id, sty) -> (Smt.Var id, sty)) list_of_sty
    ) embedding_vars
    @ 
    [ (Var "heap_value", Smt.TArray (Smt.TInt, Smt.TInt))
    ; (Var "heap_next",  Smt.TArray (Smt.TInt, Smt.TInt))
    ; (Var "heap_alloc", Smt.TInt)  ]
    (* [ (Var "realWorld_data", Smt.TArray (Smt.TString, Smt.TArray(Smt.TInt, Smt.TString)))
    ; (Var "realWorld_linenum", Smt.TArray (Smt.TString, Smt.TInt))
    ; (Var "realWorld_opened", Smt.TSet Smt.TString)] *)

let create_dummy_method (b: block node) : mdecl =
  mIndex := !mIndex + 1;
  { pure = false; mrtyp = TBool; mname = "dummyMethod_"^(Int.to_string !mIndex); args = []; body = b }

let get_exp_terms (e: exp node) : (sexp * ty) list = 
  let terms = ref [] in
  let rec get_exp_term (e: exp node) : sexp * ty = 
      match e.elt with
      | CNull _ -> terms := !terms @ [(smt_negone(), TInt)]; (smt_negone(), TInt)
      | CBool b -> terms := !terms @ [(Smt.EConst (CBool b), TBool)]; (Smt.EConst (CBool b), TBool)
      | CInt i -> terms := !terms @ [(Smt.EConst (CInt (Int64.to_int i)), TInt)]; (Smt.EConst (CInt (Int64.to_int i)), TInt)
      | CStr str -> terms := !terms @ [(Smt.EConst (CString str), TStr)]; (Smt.EConst (CString str), TStr)
      | Id id ->  
        begin match List.find_opt (fun ((v,_),_) -> (compare v id) == 0 ) !gstates with
          | Some ((id, typ),ety) ->
          terms := !terms @ [(EVar (Var id), typ)]; (EVar (Var id), typ)
          | None -> (EVar (Var id), TInt)
          (* terms := !terms @ [(id, TInt)]; (id, TInt) *)
        end
      (* | CArr (ty,exps) -> ("CARR",ty) *)
      | Index (e1,e2) -> 
        let t1, typ = get_exp_term e1 in
        let ty = match typ with
                | (TArr t) -> t
                | THashTable (t1,t2) -> t2
                | _ -> failwith "Index of a non-Arr, non-HT is not implemented"
        in

        let t2, _ = get_exp_term e2 in
        terms := !terms @ [(EFunc ("select", [t1; t2]), ty)];
        (EFunc ("select", [t1; t2]), ty)
      | HeapAlloc (e1, e2) ->
          let t1, ty1 = get_exp_term e1 in
          let t2, ty2 = get_exp_term e2 in
          (t2, ty2)
      | HDerefValue ( l ) -> get_exp_term l
      | HDerefNext  ( l ) -> get_exp_term l

      | Bop (op, e1, e2) ->
          let t1, ty1 = get_exp_term e1 in
          let t2, ty2 = get_exp_term e2 in

          let ret_typ_of_op = match op with
          | Add | Sub | Mul | Mod | Div | Exp -> ty1
          | Eq | Neq | Lt | Lte | Gt | Gte | And | Or | Implies -> TBool
          | _ -> failwith "unknown op type"
          in

          begin match op with
          | Sub | Mul | Mod | Div | Eq | Lt | Gt | Lte | Gte ->
            if (List.mem (t1, ty1) !terms && List.mem (t2, ty2) !terms) then
                terms := !terms @ [(EBop (bop_to_servoisBop op, t1, t2), ret_typ_of_op)];
            (EBop (bop_to_servoisBop op, t1, t2), ret_typ_of_op)
          | And | Add | Or ->
            if (List.mem (t1, ty1) !terms && List.mem (t2, ty2) !terms) then
                terms := !terms @ [(ELop (bop_to_servoisLop op, [t1; t2]), ret_typ_of_op)];
            (ELop (bop_to_servoisLop op, [t1; t2]), ret_typ_of_op)
          | Neq ->
            if (List.mem (t1, ty1) !terms && List.mem (t2, ty2) !terms) then
                terms := !terms @ [(EUop (Not, EBop (bop_to_servoisBop Eq, t1, t2)), ret_typ_of_op)];
            (EUop (Not, EBop (bop_to_servoisBop Eq, t1, t2)), ret_typ_of_op)
          | Implies ->
            (EBop (Imp, t1, t2), TBool)
          | _ -> failwith "unknown op type"
          end
      | Uop (op, e) -> 
        let t, typ = get_exp_term e in

        let ret_typ_of_op = match op with
          | Neg -> typ
          | Lognot -> typ
          | _ -> failwith "unknown op type"
        in
        
        if (List.mem (t, typ) !terms) then
          terms := !terms @ [(EUop (uop_to_servoisUop op, t), ret_typ_of_op)];

        (EUop (uop_to_servoisUop op, t), ret_typ_of_op)

      | Ternary(i, t, e) ->
        let t1, typ1 = get_exp_term i in
        let t2, typ2 = get_exp_term t in 
        let t3, typ3 = get_exp_term e in

        terms := !terms @ [(t1, typ1); (t2, typ2); (t3, typ3)];

        (t2, typ2) (* TODO: make sure if it's enough to return *)

      | Call (MethodL (id, {pc=Some pc;_}), el) -> (EConst(CInt 0), TInt) (* TODO: make it work when it doesn't have any involved terms *)
      | Exists (_, _, body) -> get_exp_term body
      | _ -> failwith @@ sp "get_exp_terms: undefined exp: %s" @@ AstML.string_of_exp e
  in
  let _ = get_exp_term e in
  !terms


let compile_block_to_term_list (b: block) : term_list list =
    let rec get_block_terms (b: block) : (sexp * ty) list =
    match b with
    | [] -> []
    | stmt :: tl ->
      let t = begin match stmt.elt with
        | Assn (path, e) -> (get_exp_terms path) @ (get_exp_terms e)
        | If (e,blk1,blk2) -> (get_exp_terms e) @ (get_block_terms blk1.elt) @ (get_block_terms blk2.elt)
        | _ -> []
      end
      in t @ (get_block_terms tl);
    in
   (* add 0 and 1 to terms anyway*)
    let blt = List.map (fun (exp,ty) -> (exp, sty_of_ty ty)) (get_block_terms b) in
    let block_terms = (Smt.EConst(CInt 0), Smt.TInt) :: (Smt.EConst(CInt 1), Smt.TInt) :: blt @ !terms_list in
    let unique_terms = Util.remove_duplicate block_terms in
    let terms = ref [] in
    List.iter (fun (e, sty) -> 
            let mem = List.find_opt (fun (styp,_) -> String.equal (string_of_sty sty) (string_of_sty styp) ) !terms in
            begin match mem with
            | None -> terms := !terms @ [(sty, ref [e])] 
            | Some (t, mlist) -> mlist := !mlist @ [e]
            end
    ) unique_terms; 

    List.map (fun (t, mlist) -> (t, !mlist)) !terms

let incr_uid (ctr: int ref) =
  ctr := !ctr + 1;
  !ctr

let set_counter (s: string) (vctrs : (string, int ref) Hashtbl.t) =
  if not (Hashtbl.mem vctrs s) then
    (* check if the veriable is global *)
    (* if (is_global s) then *)
      Hashtbl.add vctrs s (ref 0)

let set_variable_id (var: string) (side: int) (vctrs : (string, int ref) Hashtbl.t) (indexed : bool) : string =
  if indexed = false then var else begin
    if not (Hashtbl.mem vctrs var) && (side == 0) then
      set_counter var vctrs;

    if (Hashtbl.mem vctrs var) then begin
      let current_id = Hashtbl.find vctrs var in
      let update_id = if side == 0 
                      then begin
                        incr_uid (current_id) 
                      end
                      else begin
                          !current_id 
                      end in
      let new_id = if update_id == 0 then var else var ^ "_" ^ (Int.to_string update_id) in
      new_id
    end
    else
      var
  end

let get_postconditions () : sexp =
  let exp_list = ref [] in
  Hashtbl.iter (fun key -> fun value -> 
                if List.mem key heap_model_vars then exp_list := !exp_list @ [final_mangle_id !value key]
                else
                match List.find_opt (fun ((id,ty),_) -> String.equal key id) !gstates with
                | None -> () (* loop-internal variable not in state; skip *)
                | Some ((id,ty),ety) ->
                  let final = match ty with 
                  | THashTable (_,_) ->
                    final_mangle !value ety 
                  | _ -> let var = if !value == 0 then key else (key ^ "_" ^ Int.to_string (!value)) in
                          Smt.EBop (Eq, EVar (VarPost key), EVar (Var var));
                  in
                  exp_list := !exp_list @ [final]
                ) variable_ctr_list;
    sexp_of_sexp_list !exp_list

let reset_to_local_variable_ctrs (old_vctrs : (string * int) list) (new_vctrs : (string, int ref) Hashtbl.t) =
  Hashtbl.iter (
    fun id -> fun index ->
      if (List.mem_assoc id old_vctrs) 
      then begin
      let new_index = (List.assoc id old_vctrs) in
      Hashtbl.replace new_vctrs id (ref new_index) 
      end
      else 
      Hashtbl.replace new_vctrs id (ref 0) 
  ) new_vctrs;
  new_vctrs

let make_temp_value_of_htbl (htbl : (string, int ref) Hashtbl.t) : (string * int) list =
  let temp = ref [] in
  Hashtbl.iter (fun id -> fun index -> temp := !temp @ [(id, !index)] ) htbl;
  ! temp

(* Tracks variables bound by 'exists' so they bypass version-mangling in Id. *)
let bound_vars : (string, unit) Hashtbl.t = Hashtbl.create 4

let rec exp_to_smt_exp (e: exp node) (side: int) ?(indexed = true) (vctrs : (string, int ref) Hashtbl.t) : sexp * sexp Smt.bindlist =
    match e.elt with
    | CBool b -> Smt.EConst (CBool b), []
    | CInt i -> Smt.EConst (CInt (Int64.to_int i)), []
    | CNull _ -> smt_negone(), []
    | CStr str -> Smt.EConst (CString str), []
    | Id id ->
        if Hashtbl.mem bound_vars id
        then EVar (Var id), []
        else EVar (Var (set_variable_id id side vctrs indexed)), []
    | Index (e1,e2) when side == 1 -> 
        let rtn1, binds1 = exp_to_smt_exp e1 side ~indexed vctrs in
        let rtn2, binds2 = exp_to_smt_exp e2 side ~indexed vctrs in
        EFunc ("select", [rtn1; rtn2]), binds1 @ binds2
    | Bop (op, e1, e2) ->
        let rtn1, binds1 = exp_to_smt_exp e1 side ~indexed vctrs in
        let rtn2, binds2 = exp_to_smt_exp e2 side ~indexed vctrs in

        begin match op with
        | Sub | Mul | Mod | Div | Eq | Lt | Gt | Lte | Gte ->
            EBop (bop_to_servoisBop op, rtn1, rtn2),  binds1 @ binds2
        | And | Add | Or ->
            ELop (bop_to_servoisLop op, [rtn1; rtn2]),  binds1 @ binds2
        | Neq ->
            EUop (Not, EBop (bop_to_servoisBop Eq, rtn1, rtn2)), binds1 @ binds2
        | Implies ->
            EBop (Imp, rtn1, rtn2), binds1 @ binds2
        | _ -> failwith @@ sp "undefined op: %s" @@ AstML.string_of_binop op
        end
    | Uop (op, e) -> 
        let rtn, binds = exp_to_smt_exp e side ~indexed vctrs in

        EUop (uop_to_servoisUop op, rtn), binds

    | Call (MethodL (id, {pc=Some pc;_}), el) -> 
      let args_rtn, args_binds = List.split @@ List.map (fun exp -> exp_to_smt_exp exp right ~indexed vctrs) el in

      let id_value = match (List.hd args_rtn) with | Smt.EVar (Var v) -> v | _ -> failwith "non string var" in     
      let dst_id = remove_index (id_value) in
      let ((_,_),ety) = List.find (fun ((gid,_),_) -> String.equal gid dst_id) !gstates in 
      let embedding_type_index = match (Hashtbl.find_opt vctrs dst_id) with | None -> 0 | Some i -> !i in
      (* let fun_args = (embedding_type_index, ety, List.fold_left (fun acc x -> acc @ [Smt.Smt_ToMLString.exp x]) [] (List.tl args_rtn)) in *)
      let heap_version = !(Hashtbl.find vctrs (List.hd heap_model_vars)) in
      let fun_args = (embedding_type_index, ety, (List.tl args_rtn)) in
      (* Methods that update the heap - MAybe needed later. *)
      (*
      let {bindings=binds; ret_exp=rtn; asserts= asts; terms= t; preds = p; updates_heap} = pc fun_args in
      begin if updates_heap then List.iter (fun id -> Hashtbl.replace vctrs id (ref(!(Hashtbl.find vctrs id) + 1))) heap_model_vars
      else () end;
      *)
      let {bindings=binds; ret_exp=rtn; asserts= asts; terms= t; preds = p} = pc fun_args in

      Hashtbl.replace vctrs dst_id (ref(embedding_type_index + 1)) ; 
      predicates_list := !predicates_list @ (List.map (fun (x,y) -> Smt.PredSig (x,y)) p);
      terms_list := !terms_list @ t;

       rtn, List.concat args_binds @ binds
    | Ternary(i, t, e) ->
        let f x = exp_to_smt_exp x side ~indexed vctrs in
        let i', i_binds = f i in
        let t', t_binds = f t in
        let e', e_binds = f e in
        EITE(i', t', e'), i_binds @ t_binds @ e_binds
        (* We deal with this in statement Assign(lhs,HeapAlloc) instead *)
    | HDerefValue ( l ) ->
        let f x = exp_to_smt_exp x side ~indexed vctrs in
        let l', v_binds = f l in
        let ha = EVar (Var (set_variable_id "heap_alloc" right vctrs indexed)) in
        deref_conds := !deref_conds @
          [ EBop (Gte, l', EConst (CInt 0)); EBop (Lt, l', ha) ];
        let hv_var = EVar (Var (set_variable_id "heap_value" side vctrs indexed)) in
        EFunc ("select", [hv_var; l']), v_binds
    | HDerefNext ( l ) ->
        let f x = exp_to_smt_exp x side ~indexed vctrs in
        let l', v_binds = f l in
        let ha = EVar (Var (set_variable_id "heap_alloc" right vctrs indexed)) in
        deref_conds := !deref_conds @
          [ EBop (Gte, l', EConst (CInt 0)); EBop (Lt, l', ha) ];
        let hv_var = EVar (Var (set_variable_id "heap_next" side vctrs indexed)) in
        EFunc ("select", [hv_var; l']), v_binds

    | HeapAlloc( v, l ) ->
        failwith "HeapAlloc - should not have to do this"

    | Exists (id, ty, body) ->
        Hashtbl.add bound_vars id ();
        let r, binds = exp_to_smt_exp body side ~indexed vctrs in
        Hashtbl.remove bound_vars id;
        EExists ([(Var id, sty_of_ty ty)], r), binds

    | _ -> failwith @@ sp "exp_to_smt_exp: undefined exp: %s" @@ AstML.string_of_exp e

let mk_var_pair var_id leftright vctrs = 
  let cur_ctr = !(Hashtbl.find vctrs var_id) in
  Hashtbl.replace vctrs var_id (ref(cur_ctr + 1));
  (EVar (Smt.Var(var_id^"_"^(string_of_int  cur_ctr))), 
   EVar (Smt.Var(var_id^"_"^(string_of_int (cur_ctr+1)))))

(* Collect base variable names that are written by a block of statements.
   Results may contain duplicates; caller should dedup.
   Includes heap model variable names when heap writes or allocations occur. *)
let rec loop_modified_vars (stmts : block) : string list =
  List.concat_map loop_modified_in_stmt stmts

and loop_modified_in_stmt (stmt : stmt node) : string list =
  let rec base_id_exp e = match e.elt with
    | Id n -> Some n
    | Index (b, _) -> base_id_exp b
    | HDerefValue b | HDerefNext b -> base_id_exp b
    | _ -> None
  in
  match stmt.elt with
  (* Heap allocation writes the lhs variable and all three heap model vars *)
  | Assn (lhs, {elt = HeapAlloc _; _}) ->
      heap_model_vars @ Option.to_list (base_id_exp lhs)
  (* Heap-field writes touch the relevant model array *)
  | Assn ({elt = HDerefValue _; _}, _) -> ["heap_value"]
  | Assn ({elt = HDerefNext  _; _}, _) -> ["heap_next"]
  | Assn (lhs, _)  -> Option.to_list (base_id_exp lhs)
  | Decl (id, _)   -> [id]
  | Havoc e ->
      let rec base_id = function
        | {elt=Id n;_} -> n
        | {elt=Index(b,_);_} -> base_id b
        | _ -> failwith "loop_modified_vars: unsupported havoc lvalue"
      in
      (match e.elt with
       | HDerefValue _ -> ["heap_value"]
       | HDerefNext _  -> ["heap_next"]
       | _             -> [base_id e])
  | If (_, b1, b2) ->
      loop_modified_vars b1.elt @ loop_modified_vars b2.elt
  | While (_, _, body) ->
      loop_modified_vars body.elt
  | For (vds, _, _, body) ->
      List.map (fun (id, _) -> id) vds @ loop_modified_vars body.elt
  | Commute (_, _, blocks, _, _) ->
      List.concat_map (fun b -> loop_modified_vars b.elt) blocks
  | _ -> []

let compile_block_to_smt_exp (genv: global_env) (b : block) =
  let local_variable_ctr_list = variable_ctr_list in
  let bind = function
    | [] -> Fun.id
    | exp -> fun (e) -> ELet(exp, e)
  in
  (* Drain deref_conds and wrap [rest] with each condition as a conjunct. *)
  let consume_deref_conds () =
    let cs = !deref_conds in deref_conds := []; cs
  in
  let with_conds conds rest =
    List.fold_right (fun c acc -> ELop (And, [c; acc])) conds rest
  in
  (* Validity conditions for a pointer: 0 <= loc < heap_alloc. *)
  let alloc_cond loc_smt ha_var =
    [ EBop (Gte, loc_smt, EConst (CInt 0)); EBop (Lt, loc_smt, ha_var) ]
  in
  let rec compile_block_to_smt (b: block) (vctrs : (string, int ref) Hashtbl.t) : sexp =
    match b with
      | [] -> get_postconditions ()
      | stmt :: tl ->   
        begin match stmt.elt with
        | Assn ({elt = Index (name_exp,index_exp); loc = _},exp) ->
          let name_exp_smt, _ = exp_to_smt_exp name_exp right vctrs  in
          let index_exp_smt, _ = exp_to_smt_exp index_exp right vctrs  in
          let exp_smt, _ = exp_to_smt_exp exp right vctrs  in
          let conds = consume_deref_conds () in
          let path_name_exp_smt, _ = match exp_to_smt_exp name_exp left vctrs with
                                  | Smt.EVar v, b -> v ,b
                                  | _, _ -> failwith "left of assignment should be variable"  in

          let store_smt = Smt.EFunc ("store", [name_exp_smt; index_exp_smt; exp_smt]) in
          with_conds conds @@ ELet([(path_name_exp_smt, store_smt)], compile_block_to_smt tl vctrs)
        
        (* Heap Allocation *)
        | Assn (exp, {elt = HeapAlloc ({ elt = val_exp; loc=l1 }, { elt = loc_exp; loc=l2}) as alloce; loc = ll }) ->
            let path_smt, _ = begin match exp_to_smt_exp exp left vctrs with
                            | EVar e, b -> e, b
                            | _, _ -> failwith "left of HeapAlloc should be variable"
                            end
            in
            (* Compile the value/next fields *)
            let v_rtn, v_binds = exp_to_smt_exp {elt= val_exp;loc=l1} right vctrs in
            let l_rtn, l_binds = exp_to_smt_exp {elt= loc_exp;loc=l2} right vctrs in

            (* heap_alloc42 = heap_alloc41 + 1
              heap_next42  = store heap_next41  heap_alloc41 l'
              heap_value42 = store heap_value41 heap_alloc41 v'
              ret = heap_alloc41
            *)
            let heapallocv, heapallocv' = mk_var_pair "heap_alloc" right vctrs in
            let heapnextv,  heapnextv'  = mk_var_pair "heap_next" right vctrs in
            let heapvaluev, heapvaluev' = mk_var_pair "heap_value" right vctrs in
            let to_var = function EVar v -> v | _ -> failwith "expected EVar" in
            bind (v_binds @ l_binds) @@ ELet ([(path_smt, heapallocv)],
              (ELet ([to_var heapallocv', ELop (Add, [heapallocv; EConst(CInt(1))])],
              (ELet ([to_var heapnextv' , EFunc ("store", [heapnextv;  heapallocv; l_rtn])],
              (ELet ([to_var heapvaluev', EFunc ("store", [heapvaluev; heapallocv; v_rtn])],
              compile_block_to_smt tl vctrs
              ))))))
            )

        | Assn (exp, {elt = Call (MethodL (id, {pc=Some pc;_}), el) as calle; loc = l}) ->
          let e_rtn, e_binds = exp_to_smt_exp {elt= calle;loc=l} right vctrs  in
          let path_smt, _ = begin match exp_to_smt_exp exp left vctrs with
                          | EVar e, b -> e, b
                          | _, _ -> failwith "left of assignment should be variable"
                          end
          in

          bind e_binds @@ ELet ([(path_smt, e_rtn)], compile_block_to_smt tl vctrs)

        (* Heap value field write: loc->value = val *)
        | Assn ({elt = HDerefValue loc_exp; _}, val_exp) ->
          let loc_smt, loc_binds = exp_to_smt_exp loc_exp right vctrs in
          let val_smt, val_binds = exp_to_smt_exp val_exp right vctrs in
          let nested = consume_deref_conds () in
          let ha = EVar (Var (set_variable_id "heap_alloc" right vctrs true)) in
          let conds = nested @ alloc_cond loc_smt ha in
          let heapvaluev, heapvaluev' = mk_var_pair "heap_value" right vctrs in
          let to_var = function EVar v -> v | _ -> failwith "expected EVar" in
          with_conds conds @@
            bind (loc_binds @ val_binds) @@
            ELet ([to_var heapvaluev', EFunc ("store", [heapvaluev; loc_smt; val_smt])],
              compile_block_to_smt tl vctrs)

        (* Heap next field write: loc->next = next_loc *)
        | Assn ({elt = HDerefNext loc_exp; _}, next_exp) ->
          let loc_smt, loc_binds = exp_to_smt_exp loc_exp right vctrs in
          let next_smt, next_binds = exp_to_smt_exp next_exp right vctrs in
          let nested = consume_deref_conds () in
          let ha = EVar (Var (set_variable_id "heap_alloc" right vctrs true)) in
          let conds = nested @ alloc_cond loc_smt ha in
          let heapnextv, heapnextv' = mk_var_pair "heap_next" right vctrs in
          let to_var = function EVar v -> v | _ -> failwith "expected EVar" in
          with_conds conds @@
            bind (loc_binds @ next_binds) @@
            ELet ([to_var heapnextv', EFunc ("store", [heapnextv; loc_smt; next_smt])],
              compile_block_to_smt tl vctrs)

        | Assn (path, e) ->
          let e_rtn, e_binds = exp_to_smt_exp e right vctrs in
          let conds = consume_deref_conds () in

          let path_smt, _ = begin match exp_to_smt_exp path left vctrs with
                          | EVar e, b -> e, b
                          | _, _ -> failwith "left of assignment should be variable"
                          end
          in

          with_conds conds @@
            bind e_binds @@ ELet ([(path_smt, e_rtn)], compile_block_to_smt tl vctrs)

        | Decl (id, (ty, expn)) ->
          let e_rtn, e_binds = exp_to_smt_exp expn right vctrs in
          let conds = consume_deref_conds () in

          with_conds conds @@
            bind e_binds @@ ELet ([(Var id, e_rtn)], compile_block_to_smt tl vctrs)

        | If (exn, bln1, bln2) ->  
          (* requires := !requires ^ ("(" ^ (exp_to_smt_exp exn 0)^ ")"); *)
          let str_exp, str_exp_binds = (exp_to_smt_exp exn right vctrs) in
          
          let temp_vctrs = make_temp_value_of_htbl vctrs in
          let t = compile_block_to_smt (bln1.elt @ tl) vctrs in
          let vctrs = reset_to_local_variable_ctrs temp_vctrs vctrs in
          let e = compile_block_to_smt (bln2.elt @ tl) vctrs in
          bind str_exp_binds @@ EITE(str_exp, t, e)

          (* | Ret _ ->
          get_postconditions ()  *)
          
        | SCall (MethodL (id, {pc=Some pc;_}), el) ->
          let args = List.map (fun exp -> exp_to_smt_exp exp right vctrs) el in
          let args_rtn, args_binds = List.split args in
      
          let id_value = match (List.hd args_rtn) with | Smt.EVar (Var v) -> v | _ -> failwith "non string var" in
          let dst_id = remove_index (id_value) in
          let ((_,_),ety) = List.find (fun ((gid,_),_) -> String.equal gid dst_id) !gstates in 

          let embedding_type_index = match (Hashtbl.find_opt vctrs dst_id) with | None -> 0 | Some i -> !i in
          let heap_version = !(Hashtbl.find vctrs (List.hd heap_model_vars)) in
          let fun_args = (embedding_type_index, ety, (List.tl args_rtn)) in
          (* Methods that update the heap - maybe needed later *)
          (*
          let {bindings=binds; ret_exp=rtn; asserts= asts; terms= t; preds = p; updates_heap} = pc fun_args in
          *)
          let {bindings=binds; ret_exp=rtn; asserts= asts; terms= t; preds = p} = pc fun_args in
          predicates_list := !predicates_list @ (List.map (fun (x,y) -> Smt.PredSig (x,y)) p);
          terms_list := !terms_list @ t;
          (*begin if updates_heap then List.iter (fun id -> Hashtbl.replace vctrs id (ref(!(Hashtbl.find vctrs id) + 1))) heap_model_vars
          else () end;*)
          Hashtbl.replace vctrs dst_id (ref(embedding_type_index + 1)) ;

          bind binds @@ compile_block_to_smt tl vctrs

        | Commute (_, _, blks, _, _) -> 
          (* List.map (fun {elt=bl; _} -> compile_block_to_smt bl ) blks *)
          let comm_blk = List.map (fun {elt=bl; _} -> bl ) blks in
          compile_block_to_smt (List.concat comm_blk) vctrs; 
          
        | Assume(e) ->
          let exp_smt,_ = exp_to_smt_exp e right vctrs  in
          let conds = consume_deref_conds () in
          with_conds conds @@ ELop(And, [exp_smt; compile_block_to_smt tl vctrs])

        | Havoc(e) ->
          let to_var = function EVar v -> v | _ -> failwith "expected EVar" in
          (match e.elt with
          | HDerefValue loc_exp ->
            let loc_smt, loc_binds = exp_to_smt_exp loc_exp right vctrs in
            let nested = consume_deref_conds () in
            let ha = EVar (Var (set_variable_id "heap_alloc" right vctrs true)) in
            let conds = nested @ alloc_cond loc_smt ha in
            let heapvaluev, heapvaluev' = mk_var_pair "heap_value" right vctrs in
            let havoc_id = "heap_value_havoc_val" in
            with_conds conds @@
              bind loc_binds @@
              EExists ([(Var havoc_id, Smt.TInt)],
                ELet ([to_var heapvaluev', EFunc ("store", [heapvaluev; loc_smt; EVar (Var havoc_id)])],
                  compile_block_to_smt tl vctrs))
          | HDerefNext loc_exp ->
            let loc_smt, loc_binds = exp_to_smt_exp loc_exp right vctrs in
            let nested = consume_deref_conds () in
            let ha = EVar (Var (set_variable_id "heap_alloc" right vctrs true)) in
            let conds = nested @ alloc_cond loc_smt ha in
            let heapnextv, heapnextv' = mk_var_pair "heap_next" right vctrs in
            let havoc_id = "heap_next_havoc_val" in
            with_conds conds @@
              bind loc_binds @@
              EExists ([(Var havoc_id, Smt.TInt)],
                ELet ([to_var heapnextv', EFunc ("store", [heapnextv; loc_smt; EVar (Var havoc_id)])],
                  compile_block_to_smt tl vctrs))
          | _ ->
            let rec base_id = function
              | {elt=Id n;_} -> n
              | {elt=Index(b,_);_} -> base_id b
              | _ -> failwith "havoc: unsupported lvalue expression"
            in
            let id = base_id e in
            let new_id = match fst @@ exp_to_smt_exp (no_loc (Id id)) left vctrs with EVar id -> id | _ -> failwith "havoc" in
            let is_tloc =
              match List.find_opt (fun ((vid,_),_) -> String.equal vid id) !gstates with
              | Some ((_, TLoc), _) -> true
              | _ -> false
            in
            if is_tloc then begin
              (* tloc havoc: allocate a fresh heap location rather than picking any integer *)
              let heapallocv, heapallocv' = mk_var_pair "heap_alloc" right vctrs in
              ELet ([(new_id, heapallocv)],
                ELet ([to_var heapallocv', ELop (Add, [heapallocv; EConst(CInt 1)])],
                  compile_block_to_smt tl vctrs))
            end else begin
              let havoc_id = id^"_havoc" in
              let exp_smt, _ = exp_to_smt_exp (no_loc @@ Id havoc_id) right vctrs in
              let havoc_sty =
                match List.find_opt (fun ((vid,_),_) -> String.equal vid id) !gstates with
                | Some ((_, ty), _) -> sty_of_ty ty
                | None ->
                    if List.mem id heap_model_vars
                    then Smt.TArray (Smt.TInt, Smt.TInt)
                    else Smt.TInt
              in
              EExists([(Var havoc_id, havoc_sty)], ELet([new_id, exp_smt], compile_block_to_smt tl vctrs))
            end)

        | Require(e) ->
          let exp_smt,_ = exp_to_smt_exp e right ~indexed:false vctrs in
          pre := exp_smt;
          compile_block_to_smt tl vctrs;

        (* Loop with a verified invariant: replace the loop with its invariant.
           Existentially quantify over post-loop values of all variables
           written by the body, assert (I ∧ ¬G) at the post-loop state, then
           continue with the block tail. *)
        | While (guard, Some inv, body) ->
          let modified =
            loop_modified_vars body.elt
            |> List.sort_uniq String.compare
            |> List.filter (fun id ->
                (* Include variables already tracked, global state variables,
                   and heap model vars — so the invariant is evaluated at
                   the post-loop state of all variables the body can modify. *)
                Hashtbl.mem vctrs id
                || List.exists (fun ((vid,_),_) -> String.equal vid id) !gstates
                || List.mem id heap_model_vars)
          in
          (* Bump version counter for each modified variable (side-effects vctrs). *)
          let havoc_triples = List.map (fun id ->
            let hv = id ^ "_loop_havoc" in
            let new_id =
              match fst @@ exp_to_smt_exp (no_loc (Id id)) left vctrs with
              | EVar v -> v
              | _ -> failwith ("loop_modified_vars: expected EVar for " ^ id)
            in
            let sty =
              match List.find_opt (fun ((vid,_),_) -> String.equal vid id) !gstates with
              | Some ((_, ty), _) -> sty_of_ty ty
              | None ->
                  if List.mem id heap_model_vars
                  then Smt.TArray (Smt.TInt, Smt.TInt)
                  else Smt.TInt
            in
            (new_id, Smt.EVar (Smt.Var hv), hv, sty)
          ) modified in
          (* Evaluate invariant and guard under the post-loop variable versions. *)
          let inv_smt,   _ = exp_to_smt_exp inv   right vctrs in
          let guard_smt, _ = exp_to_smt_exp guard right vctrs in
          let exit_cond = ELop (And, [inv_smt; EUop (Not, guard_smt)]) in
          let existentials = List.map (fun (_, _, hv, sty) -> (Smt.Var hv, sty)) havoc_triples in
          let lets         = List.map (fun (nid, e, _, _) -> (nid, e)) havoc_triples in
          EExists (existentials,
            ELet (lets,
              ELop (And, [exit_cond; compile_block_to_smt tl vctrs])))

        | While (_, None, _) ->
          compile_block_to_smt tl vctrs

        | _ -> compile_block_to_smt tl vctrs
        end
  in
  let ety_init_list = ref [] in 
  List.iter (
    fun [@warning "-8"] ((id,ty),ety) -> 
          match ty with 
          | THashTable (_,_) -> begin 
          let ety_inits = init_mangle ety in
          List.iter (fun s -> ety_init_list := !ety_init_list @ [s]) ety_inits;

          if not (Hashtbl.mem variable_ctr_list id) then
          Hashtbl.add variable_ctr_list id (ref 1)
        end
        | _ -> ()
    
  ) !gstates;
  if !use_heap then
  List.iter (
    fun [@warning "-8"] id ->
          ety_init_list := !ety_init_list @ [init_mangle_id id];
          if not (Hashtbl.mem variable_ctr_list id) then
          Hashtbl.add variable_ctr_list id (ref 1) else
          Hashtbl.replace variable_ctr_list id (ref 1) (* TODO: Don't need to set existing member to 1 in else case? *)
  ) heap_model_vars;
  let res = compile_block_to_smt b local_variable_ctr_list in
  if (List.length !ety_init_list == 0) then
    res, local_variable_ctr_list
  else
  ELet (!ety_init_list, res), local_variable_ctr_list

let generate_method_spec_postcondition (genv: global_env) (b : block) : sexp =
    let block_to_exp, local_variable_ctr_list = (compile_block_to_smt_exp genv b) in

    let remain_variables = ref [] in
    List.iter (fun ((id,_),_) ->
            if not (Hashtbl.mem variable_ctr_list id)
            then
            remain_variables := !remain_variables @ [Smt.EBop (Eq, EVar (VarPost id), EVar (Var id))]
    ) !gstates;
    let heap_passthrough =
      if !use_heap then []
      else List.map (fun id ->
        Smt.EBop (Eq, EVar (VarPost id), EVar (Var id))
      ) heap_model_vars
    in
    ELop (And, block_to_exp :: !remain_variables @ heap_passthrough @ [Smt.EBop (Eq, EVar (Var "result"), EConst (CBool true))])

let generate_spec_pre_post_condition pre post =
  let vctrs = variable_ctr_list in
  match pre, post with 
  | Some pre, Some post -> (fst @@ exp_to_smt_exp pre right vctrs),(fst @@ exp_to_smt_exp post right vctrs)
  | None, None -> (Smt.EConst (CBool true)),(Smt.EConst (CBool true))
  | None, Some post -> (Smt.EConst (CBool true)),(fst @@ exp_to_smt_exp post right vctrs)
  | Some pre, None -> (fst @@ exp_to_smt_exp pre right vctrs),(Smt.EConst (CBool true))

let compile_method_to_methodSpec (genv: global_env) (m:mdecl) : method_spec =
    let args = List.map (fun (ty,id) -> (Smt.Var id, sty_of_ty ty)) m.args in
    let updated_return_type = 
    match m.mrtyp with
    | TVoid -> Smt.TBool
    | t -> sty_of_ty t
    in
    let ret = [(Smt.Var "result", updated_return_type)] in 
    let post = generate_method_spec_postcondition genv m.body.elt in
    let terms = compile_block_to_term_list m.body.elt in 
    let heap_inv = EBop (Gte, EVar (Var "heap_alloc"), EConst (CInt 0)) in
    let loc_varnames = List.filter_map (fun ((id, ty), _) -> if ty = TLoc then Some id else None) !gstates in
    (* Each loc var address is a valid allocated cell: 0 <= v < heap_alloc *)
    let loc_valid = List.concat_map (fun v -> [
      EBop (Gte, EVar (Var v), EConst (CInt 0));
      EBop (Lt, EVar (Var v), EVar (Var "heap_alloc"))
    ]) loc_varnames in
    (* Each loc var's next pointer is either null (-1) or a valid heap address.
       This is weaker than the original closed-world constraint (which required
       heap_next to point only to tracked TLoc variables), allowing next pointers
       to address heap cells that are not currently tracked as named TLoc vars.
       Safe as long as blocks in the commute check do not write fresh allocation
       addresses into heap_next: in that case the states_equal bijection handles
       untracked next values via its else branch (raw equality), which holds when
       both orderings leave those heap_next entries unmodified. *)
    let heap_next_valid = List.map (fun v ->
      let sel = EFunc ("select", [EVar (Var "heap_next"); EVar (Var v)]) in
      ELop (Or, [
        EBop (Eq, sel, smt_negone ());
        ELop (And, [
          EBop (Gte, sel, EConst (CInt 0));
          EBop (Lt,  sel, EVar (Var "heap_alloc"))
        ])
      ])
    ) loc_varnames in
    let method_spec = { name = m.mname; args = args; ret = ret;
                        pre = ELop (And, ([!pre; heap_inv] @ loc_valid @ heap_next_valid));
                        post = post; terms = terms} in

    terms_list := [];
    Hashtbl.iter (fun id -> fun _ -> (* keep the local variables that defined in last block *)
                    if (List.exists (fun ((name,_),_) -> String.equal id name) !gstates) then
                    Hashtbl.remove variable_ctr_list id
                    else 
                    Hashtbl.replace variable_ctr_list id (ref 0)
    ) variable_ctr_list;

    method_spec

let compile_blocks_to_spec (genv: global_env) (blks: block node list) (embedding_vars : (ty binding * ety) list) pre post =
  let embedding_vars = List.filter (fun ((id, _),_) -> not (String.equal id "argv") ) embedding_vars in
  gstates := embedding_vars;

  let has_loc_vars = List.exists (fun ((_, ty), _) -> ty = TLoc) embedding_vars in
  use_heap := has_loc_vars || blocks_use_heap blks;

  let predicates = generate_spec_predicates embedding_vars in
  let state_equal = generate_spec_statesEqual embedding_vars in
  let state = generate_spec_state embedding_vars in

  (* Seed terms from pre/post annotations so empty-block commute queries
     (e.g. subsumption checks) still provide meaningful candidates. *)
  let pre_post_terms =
    let extract = function
      | None -> []
      | Some e -> List.map (fun (smt, ty) -> (smt, sty_of_ty ty)) (get_exp_terms e)
    in
    extract pre @ extract post
  in

  let mdecls = List.map create_dummy_method blks in
  let methods = List.map (fun m ->
      terms_list := pre_post_terms;
      compile_method_to_methodSpec genv m
  ) mdecls in

  let pre, post = generate_spec_pre_post_condition pre post in

  let preamble = None in

  let spec = { name = "test"; preamble = preamble; preds = predicates; state_eq = state_equal;
              precond = pre; postcond = post; state = state; methods= methods; smt_fns = []} in
  let mnames = List.map (fun ({mname = name; _}) -> name) mdecls 
  in

  (* When query dumping is active (e.g. --html), write the compiled Servois2
     spec to a file alongside the SMT query files.  The post-condition of each
     method is the SMT formula produced by compile_block_to_smt, so the While
     → ∃(loop_havoc). let … in (inv ∧ ¬guard) ∧ tail transformation is visible
     in the "post:" section of whichever method contains the While loop. *)
  if !Servois2.Util.dump_queries then begin
    (try
      let path = Servois2.Util.outfile "veracity_spec.smt" in
      let oc = open_out path in
      let pr fmt = Printf.fprintf oc fmt in
      pr "; state variables\n";
      List.iter (fun (v, ty) ->
        pr ";   %s : %s\n" (string_of_var v) (string_of_ty ty)
      ) spec.state;
      List.iter (fun (m : method_spec) ->
        pr "\n; --- method: %s ---\n" m.name;
        pr "; pre:\n%s\n" (string_of_smt m.pre);
        pr "\n; post:\n%s\n" (string_of_smt m.post)
      ) spec.methods;
      close_out oc
    with _ -> ())
  end;
  spec, mnames

(* ── Assert verification condition generator ─────────────────────────────── *)

(* Walk a block using a continuation-passing wrapper so that every let-binding
   from preceding assignments is in scope when we reach an assert.  For each
   assert(e) we record (location, vc) where vc is the boolean SMT expression
   that is satisfiable iff the assertion could fail.  Succeeding asserts are
   treated as assumes for subsequent VCs. *)
let generate_assert_vcs (b: block) (extra_vars: embedding_map ref) : (Range.t * sexp) list =
  let bind = function [] -> Fun.id | exp -> fun e -> ELet(exp, e) in
  let vcs = ref [] in
  let rec go (stmts: block) (vctrs: (string, int ref) Hashtbl.t) (wrap: sexp -> sexp) =
    match stmts with
    | [] -> ()
    | stmt :: tl ->
      begin match stmt.elt with
      | Assert e ->
          let e_smt, e_binds = exp_to_smt_exp e right vctrs in
          let inner = bind e_binds e_smt in
          vcs := !vcs @ [(stmt.loc, wrap inner)];
          (* Use implication so subsequent VCs are checked *assuming* this
             assertion holds, not in conjunction with it.  This avoids the
             inconsistent-context problem when an assertion is false. *)
          go tl vctrs (fun k -> wrap (EBop (Imp, inner, k)))
      | Assn (path, e) ->
          begin try
            let e_rtn, e_binds = exp_to_smt_exp e right vctrs in
            let path_smt = match exp_to_smt_exp path left vctrs with
              | EVar v, _ -> v
              | _ -> failwith "assert VCG: lhs of assignment must be a variable" in
            go tl vctrs (fun k -> wrap (bind e_binds @@ ELet ([(path_smt, e_rtn)], k)))
          with _ -> go tl vctrs wrap end
      | Decl (id, (ty, expn)) ->
          begin try
            let e_rtn, e_binds = exp_to_smt_exp expn right vctrs in
            go tl vctrs (fun k -> wrap (bind e_binds @@ ELet ([(Var id, e_rtn)], k)))
          with _ ->
            (* Treat as "int id = 1; havoc(id)": id is unconstrained.
               Record it in extra_vars so it gets a declare-fun in the SMT query. *)
            let ety = match ty with
              | TInt | TLoc -> ETInt id
              | TBool -> ETBool id
              | _ -> ETInt id
            in
            if not (List.exists (fun ((eid, _), _) -> String.equal eid id) !extra_vars) then
              extra_vars := !extra_vars @ [((id, ty), ety)];
            Hashtbl.replace vctrs id (ref 0);
            go tl vctrs wrap
          end
      | Assume e ->
          let e_smt, _ = exp_to_smt_exp e right vctrs in
          (* assume P; assert Q  →  check P ⇒ Q, i.e. P ∧ ¬Q for SAT *)
          go tl vctrs (fun k -> wrap (EBop (Imp, e_smt, k)))
      | _ -> go tl vctrs wrap
      end
  in
  go b variable_ctr_list Fun.id;
  !vcs

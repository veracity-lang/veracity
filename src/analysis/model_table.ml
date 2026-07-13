(* Counterexample model, tabulated by Veracity expression.
 *
 * Servois2 already emits heap_table.html, but its rows are the SMT *state
 * variables* -- so reading a counterexample means mentally undoing Veracity's
 * translation. This table is keyed by the expressions actually written in the
 * commute block, showing for each one its SMT translation and its value in
 * each version of the state:
 *
 *   ""    the initial state
 *   "1"   after the first block
 *   "12"  after the first block, then the second
 *
 * (Those are the three state versions that carry model values under the AE
 * encoding; "2" and "21" are exists-bound and so are not in the model.)
 *
 * We get the values by handing Servois2 the suffixed SMT form of each
 * expression as an extra (get-value ...) probe -- see Solve.extra_model_exprs.
 *)

open Ast

module Smt = Servois2.Smt

(* Rewrite each state variable [v] in an SMT expression to [v ^ sfx], which is
   how Servois2 names that variable in the given version of the state. *)
let rec subst_sfx sfx names (smt : Smt.exp) : Smt.exp =
  let go e = subst_sfx sfx names e in
  match smt with
  | Smt.EVar (Smt.Var n) when List.mem n names -> Smt.EVar (Smt.Var (n ^ sfx))
  | Smt.EVar _ -> smt
  | Smt.EBop (op, e1, e2) -> Smt.EBop (op, go e1, go e2)
  | Smt.ELop (op, es) -> Smt.ELop (op, List.map go es)
  | Smt.EUop (op, e) -> Smt.EUop (op, go e)
  | Smt.EConst _ -> smt
  | Smt.EFunc (f, es) -> Smt.EFunc (f, List.map go es)
  | Smt.EITE (c, t, f) -> Smt.EITE (go c, go t, go f)
  | Smt.ELet (bs, e) -> Smt.ELet (List.map (fun (v, e) -> (v, go e)) bs, go e)
  | Smt.EForall (binds, e) -> Smt.EForall (binds, go e)
  | Smt.EExists (binds, e) -> Smt.EExists (binds, go e)
  | Smt.EArg _ -> smt

(* The state versions we tabulate, as (suffix, column heading).

   Under the default bowtie encoding all five versions are ordinary declared
   constants, so we can show both interleavings side by side. That matters:
   a commutativity counterexample *is* the disagreement between them, and with
   only the forward run on screen the reader cannot see it.

   Under AE the reversed run is existentially bound to fresh names (cw2, cw21,
   ...), which leaves the declared c2/c21 unconstrained -- probing them would
   report junk -- so there we show the forward run only. *)
let columns ~(use_ae : bool) : (string * string) list =
  let forward =
    [ "",   "initial"
    ; "1",  "after block 1"
    ; "12", "after block 1; block 2" ]
  in
  if use_ae then forward
  else forward @ [ "2",  "after block 2"
                 ; "21", "after block 2; block 1" ]

(* The two final states, whose disagreement is the counterexample. *)
let final_fwd = "12"
let final_rev = "21"

(* Every expression and subexpression appearing in a block, in source order.
   Calls are skipped: they have no direct SMT translation as a term. *)
let rec exps_of_exp (e : exp node) : exp node list =
  let sub =
    match e.elt with
    | Index (a, b) | Bop (_, a, b) | HeapAlloc (a, b) | HeapValue (a, b) ->
      exps_of_exp a @ exps_of_exp b
    | Uop (_, a) | Proj (a, _) | HDerefValue a | HDerefNext a -> exps_of_exp a
    | Ternary (a, b, c) -> exps_of_exp a @ exps_of_exp b @ exps_of_exp c
    | CArr (_, es) -> List.concat_map exps_of_exp es
    | _ -> []
  in
  sub @ [ e ]

let rec exps_of_stmt (s : stmt node) : exp node list =
  match s.elt with
  | Assn (lhs, rhs) -> exps_of_exp lhs @ exps_of_exp rhs
  | Decl (_, (_, e)) -> exps_of_exp e
  | Ret (Some e) -> exps_of_exp e
  | Ret None -> []
  | If (c, t, f) ->
    exps_of_exp c @ exps_of_block t.elt @ exps_of_block f.elt
  | While (c, _, b) -> exps_of_exp c @ exps_of_block b.elt
  | For (_, c, _, b) ->
    (match c with Some e -> exps_of_exp e | None -> []) @ exps_of_block b.elt
  | Assert e | Assume e | Havoc e | Require e | Raise e -> exps_of_exp e
  | _ -> []

and exps_of_block (b : block) : exp node list = List.concat_map exps_of_stmt b

(* Only scalar-valued expressions can be probed.  Asking the solver for the
   value of an array-valued term gets back a (store ...) / (as const ...) term,
   which Veracity's model parser cannot read -- it would abort the whole run.
   So [r] is excluded while [r[0]] is kept, which is the useful row anyway.

   The judgement is made on the SMT side, against the sorts Servois2 declared
   for the state: a Veracity-level type inference misses locals like [r] that
   are not in gstates and silently defaults them to int. *)
let is_scalar (state_types : (string * Smt.ty) list) (smt : Smt.exp) : bool =
  match smt with
  | Smt.EVar (Smt.Var n) ->
    (match List.assoc_opt n state_types with
     | Some Smt.TInt | Some Smt.TBool -> true
     | Some _ -> false
     | None -> true (* method-local scalar, not part of the state *))
  | Smt.EFunc ("select", _) -> true
  | Smt.EFunc _ -> false (* e.g. (as const (Array Int Int)) *)
  | Smt.EConst _ | Smt.EBop _ | Smt.ELop _ | Smt.EUop _ | Smt.EITE _ -> true
  | _ -> false

(* Translate each expression of the commute blocks to its SMT form over the
   base (unsuffixed) state names, keeping the source text as the label.

   [~indexed:false] is what gives us the base names: it bypasses the SSA
   version-mangling that would otherwise rename a variable to x_1, x_2, ... at
   each assignment. We want the expression as written, evaluated in whichever
   state version the column names -- not at some point inside a method body. *)
let expr_table (blks : block node list) (state_types : (string * Smt.ty) list)
  : (string * Smt.exp) list =
  let state_names = List.map fst state_types in
  let exps = List.concat_map (fun b -> exps_of_block b.elt) blks in
  let seen = Hashtbl.create 32 in
  List.filter_map
    (fun e ->
      let label = Ast_print.AstPP.string_of_exp e in
      if Hashtbl.mem seen label then None
      else begin
        Hashtbl.add seen label ();
        (* Translating a heap deref appends allocation-validity conditions to
           Spec_generator.deref_conds. We are only probing, not building a
           query, so drop them -- left behind they would be picked up as
           conjuncts by whoever next drains that global. *)
        let translate e =
          let r =
            try Some (fst (Spec_generator.exp_to_smt_exp e 1 ~indexed:false
                             (Hashtbl.create 1)))
            with _ -> None
          in
          Spec_generator.deref_conds := [];
          r
        in
        match translate e with
        | None -> None
        | Some smt when is_scalar state_types smt ->
          (* Keep only expressions that actually read the state: anything else
             has the same value in all three columns and is just noise. *)
          let rec mentions_state = function
            | Smt.EVar (Smt.Var n) -> List.mem n state_names
            | Smt.EBop (_, a, b) -> mentions_state a || mentions_state b
            | Smt.EUop (_, a) -> mentions_state a
            | Smt.ELop (_, es) | Smt.EFunc (_, es) -> List.exists mentions_state es
            | Smt.EITE (a, b, c) ->
              mentions_state a || mentions_state b || mentions_state c
            | Smt.ELet (bs, e) ->
              List.exists (fun (_, e) -> mentions_state e) bs || mentions_state e
            | Smt.EForall (_, e) | Smt.EExists (_, e) -> mentions_state e
            | _ -> false
          in
          if mentions_state smt then Some (label, smt) else None
        | Some _ -> None
      end)
    exps

(* The probes handed to Servois2: each expression at each state version, in a
   fixed order so the values can be matched back positionally. *)
let probes ~(columns : (string * string) list) (table : (string * Smt.exp) list)
    (state_names : string list) : Smt.exp list =
  List.concat_map
    (fun (_, smt) ->
      List.map (fun (sfx, _) -> subst_sfx sfx state_names smt) columns)
    table

(* ---------------------------------------------------------------- html -- *)

(* SMT prints negative integers as "(- 1)"; show them as "-1". *)
let pretty_val (v : Smt.exp) : string =
  match v with
  | Smt.EUop (Smt.Neg, Smt.EConst (Smt.CInt n)) -> string_of_int (-n)
  | Smt.EFunc ("-", [ Smt.EConst (Smt.CInt n) ]) -> string_of_int (-n)
  | _ ->
    let s = Smt.string_of_smt v in
    let n = String.length s in
    (* Fallback for however the printer spells it. *)
    if n > 4 && String.sub s 0 3 = "(- " && s.[n - 1] = ')' then
      "-" ^ String.trim (String.sub s 3 (n - 4))
    else s

let esc s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '&' -> Buffer.add_string b "&amp;"
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

(* Styling matches the heap_table.html this sits beside in the report. *)
let th = "padding:5px 10px;text-align:left;color:#7ec8e3;border:1px solid #2a4a60"
let td = "padding:4px 10px;color:#b5d0e8;border:1px solid #2a4a60"
let td_val =
  "padding:4px 10px;text-align:right;color:#e0b0ff;border:1px solid #2a4a60;white-space:nowrap"

let render ~(columns : (string * string) list) ~(table : (string * Smt.exp) list)
    ~(state_names : string list)
    ~(models : (int * string * (Smt.exp * Smt.exp) list) list) : string =
  let buf = Buffer.create 4096 in
  let put = Buffer.add_string buf in
  let sp = Printf.sprintf in
  (* The model value of [smt] in state version [sfx], if the solver gave one. *)
  let value model smt sfx =
    List.assoc_opt (subst_sfx sfx state_names smt) model |> Option.map pretty_val
  in
  List.iter
    (fun (idx, result, model) ->
      (* A row diverges when the two interleavings end with different values for
         it. Only meaningful when both final states are on screen (bowtie). *)
      let diverges smt =
        match value model smt final_fwd, value model smt final_rev with
        | Some a, Some b -> a <> b
        | _ -> false
      in
      let any_divergence = List.exists (fun (_, smt) -> diverges smt) table in
      put (sp "<div style=\"margin:1.2em 0\">");
      put
        (sp
           "<div style=\"color:#7ec8e3;font-family:monospace;margin-bottom:6px\">\
            Commute-block expressions &mdash; model of \
            <b>servois2_query_%04d.smt</b> (%s)</div>"
           idx (esc result));
      if any_divergence then
        put
          (sp
             "<div style=\"color:#e08080;font-family:monospace;font-size:12px;\
              margin-bottom:6px\">Highlighted rows end with different values \
              under the two interleavings &mdash; this is the counterexample to \
              commutativity.</div>");
      put
        {|<table style="border-collapse:collapse;font-family:'Courier New',Courier,monospace;font-size:12px">|};
      put {|<tr style="background:#1e3a50">|};
      put (sp {|<th style="%s">Veracity expression</th>|} th);
      put (sp {|<th style="%s">SMT expression</th>|} th);
      List.iter
        (fun (_, heading) -> put (sp {|<th style="%s">%s</th>|} th (esc heading)))
        columns;
      put "</tr>";
      List.iteri
        (fun i (label, smt) ->
          let bad = diverges smt in
          let bg =
            if bad then "#3a1e24"
            else if i mod 2 = 0 then "#14212c"
            else "#182634"
          in
          put (sp {|<tr style="background:%s">|} bg);
          put (sp {|<td style="%s">%s</td>|} td (esc label));
          put (sp {|<td style="%s">%s</td>|} td (esc (Smt.string_of_smt smt)));
          List.iter
            (fun (sfx, _) ->
              let v = match value model smt sfx with Some v -> v | None -> "&mdash;" in
              (* Values are already SMT-printed; only the em-dash is markup. *)
              let style =
                if bad && (sfx = final_fwd || sfx = final_rev) then
                  td_val ^ ";color:#ff9d9d;font-weight:bold"
                else td_val
              in
              put (sp {|<td style="%s">%s</td>|} style
                     (if v = "&mdash;" then v else esc v)))
            columns;
          put "</tr>")
        table;
      put "</table></div>")
    models;
  Buffer.contents buf

(* Write expr_table.html into the current Servois2 output dir (the commute
   subdir), where Veracity's and ConQuoer's report generators pick up .html
   fragments and inline them. Nothing is written when there is no SAT model. *)
let write ~(columns : (string * string) list) ~(table : (string * Smt.exp) list)
    ~(state_names : string list) : unit =
  let models =
    List.filter (fun (_, _, m) -> m <> []) !Servois2.Solve.extra_models
  in
  if table <> [] && models <> [] then begin
    let html = render ~columns ~table ~state_names ~models in
    if html <> "" then begin
      let path = Servois2.Util.outfile "expr_table.html" in
      let oc = open_out path in
      output_string oc html;
      close_out oc
    end
  end

(* Helper functions of abstract syntax of trees. *)
(******************************************************************************)

open Format
open Ast
open Range
open Util

let greenize = ColorPrint.color_string Default Light_green 
let reddize = ColorPrint.color_string Default Light_red 
let greyize = ColorPrint.color_string Dark_gray Default 
  
(*** Pretty print AST back into concrete syntax ***)
module AstPP = struct
  (* Precedence for expressions and operators *)
  (* Higher precedences bind more tightly     *)

  let prec_of_binop = function
  | Exp -> 110
  | Mul | Mod | Div -> 100
  | Add | Sub -> 90
  | Shl | Shr | Sar -> 80
  | Lt  | Lte | Gt | Gte -> 70
  | Eq  | Neq -> 60
  | And  -> 50
  | Or   -> 40
  | IAnd -> 30
  | IOr  -> 20
  | Concat -> 10

  let prec_of_unop = function _ -> 110

  let prec_of_exp = function
  | Bop (o,_,_) -> prec_of_binop o
  | Uop (o,_) -> prec_of_unop o
  | _ -> 130


  (* Pretty Printer for AST *)
  let string_of_unop = function
  | Neg -> "-"
  | Lognot -> "!"
  | Bitnot -> "~"

  let string_of_binop = function
  | Mul    -> "*"
  | Div    -> "/"
  | Exp    -> "**"
  | Add    -> "+"
  | Sub    -> "-"
  | Shl    -> "<<"
  | Shr    -> ">>"
  | Sar    -> ">>>"
  | Lt     -> "<"
  | Lte    -> "<="
  | Gt     -> ">"
  | Gte    -> ">="
  | Eq     -> "=="
  | Neq    -> "!="
  | And    -> "&&"
  | Or     -> "||"
  | IAnd   -> "&"
  | IOr    -> "|"
  | Concat -> "^"
  | Mod    -> "%"

  let print_id_aux fmt (x:id) = pp_print_string fmt x

  let rec print_list_aux fmt sep pp l =
    begin match l with
      | []    -> ()
      | [h]   -> pp fmt h
      | h::tl -> pp fmt h; sep ();
              print_list_aux fmt sep pp tl
    end

  let rec print_ty_aux fmt t =
    let pps = pp_print_string fmt in
    match t with
    | TBool  -> pps "bool"
    | TInt   -> pps "int"
    | TVoid  -> pps "void"
    | TStr   -> pps "string"
    | TChanR -> raise @@ NotImplemented "TChanR pretty print"
    | TChanW -> raise @@ NotImplemented "TChanW pretty print"
    | THashTable (tyk, tyv) -> pps "hashtable["; print_ty_aux fmt tyk; pps ", "; print_ty_aux fmt tyv; pps "]"
    | TStruct sid -> pps sid
    | TArr ty -> print_ty_aux fmt ty; pps "[]"

  and print_exp_aux level fmt e =
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in
    let this_level = prec_of_exp e.elt in

    if this_level < level then pps "(";
    begin match e.elt with
      | CNull t -> print_ty_aux fmt t; pps "null"
      | CBool v -> pps (if v then "true" else "false")
      | CInt  v -> pps (Int64.to_string v)
      | CStr  v -> pps (Printf.sprintf "%S" v)
      | CArr (ty,vs) -> begin
          pps "new "; print_ty_aux fmt ty; pps "[]";
          pps "{";
          pp_open_hbox fmt ();
          print_list_aux fmt (fun () -> pps ","; pp_print_space fmt()) (print_exp_aux 0) vs;
          pp_close_box fmt ();
          pps "}";
        end
      | Id id -> print_id_aux fmt id
      | Index (e,i) -> print_exp_aux this_level fmt e; pps "["; print_exp_aux 0 fmt i; pps "]"
      | Call (e, es) -> 
        let name = match e with
          | MethodM(s, _) | MethodL(s, _) -> s in
        print_id_aux fmt name; print_exps_aux "(" ")" fmt es
      | CallRaw (name, es) ->
        print_id_aux fmt name; print_exps_aux "(" ")" fmt es
      | NewArr (ty, e1) ->
          pps "new "; print_ty_aux fmt ty;
          pps "["; print_exp_aux 0 fmt e1; pps "]"
      | NewHashTable (variant, tyk, tyv) ->
          pps "new "; pps (match variant with HTVarSequential -> "hashtable_seq" | _ -> "hashtable");
          pps "["; print_ty_aux fmt tyk; pps ", "; print_ty_aux fmt tyv; pps "]"
      | Proj (e, id) ->
          pp_open_box fmt 0;
          print_exp_aux this_level fmt e;
          ppsp (); pps "."; ppsp (); pps id;
          pp_close_box fmt ()
      | CStruct (t, l) ->
          pps "new "; pps t;
          pp_open_box fmt 0;
          pps "{";
          List.iter (fun s -> print_cfield_aux this_level fmt s; pps "; ") l;
          pps "}";
          pp_close_box fmt () 
      | Bop (o,l,r) ->
          pp_open_box fmt 0;
          print_exp_aux this_level fmt l;
          ppsp (); pps (string_of_binop o); ppsp ();
          print_exp_aux this_level fmt r;
          pp_close_box fmt ()
      | Uop (o,v) ->
          pp_open_box fmt 0;
          pps (string_of_unop o);
          print_exp_aux this_level fmt v;
          pp_close_box fmt ()
      | Ternary(i, t, e) -> 
          pp_open_box fmt 0;
          print_exp_aux this_level fmt i;
          pps " ? ";
          print_exp_aux this_level fmt t;
          pps " : ";
          print_exp_aux this_level fmt e;
          pp_close_box fmt ()
    end; if this_level < level then pps ")"

  and print_cfield_aux l fmt (name, exp) =
    pp_open_box fmt 0; 
    pp_print_string fmt name; 
    pp_print_string fmt "="; print_exp_aux l fmt exp;
    pp_close_box fmt ();

  and print_exps_aux l r fmt es =
    let pps = pp_print_string fmt in
    pps l;
    pp_open_hvbox fmt 0;
    print_list_aux fmt
      (fun () -> pps ","; pp_print_space fmt())
      (fun fmt -> fun e -> print_exp_aux 0 fmt e) es;
    pp_close_box fmt ();
    pps r

  let print_vdecl_aux semi fmt (id, (ty, init)) =
    (* TODO: raise @@ NotImplemented "print_vdecl_aux" *)
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in
    pp_open_hbox fmt ();
    print_ty_aux fmt ty; pps " "; print_id_aux fmt id;
    ppsp (); pps "="; ppsp ();
    print_exp_aux 0 fmt init; pps semi;
    pp_close_box fmt ()

  let rec print_block_aux fmt (b : block node) =
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in
    let ppnl = pp_force_newline fmt in

    if (List.length b.elt) > 0 then
      begin pps "{"; ppnl (); pps "  ";
            pp_open_vbox fmt 0;
            print_list_aux fmt (fun () -> ppsp ()) print_stmt_aux b.elt;
            pp_close_box fmt ();
            ppnl (); pps "}"
      end
    else pps "{ }"

  and print_cond_aux fmt (b_then : block node) (opt_b_else : block node) =
    let pps = pp_print_string fmt in
    print_block_aux fmt b_then;
    begin match opt_b_else with
      | {elt=[];_} -> ()
      | b_else -> pps " else "; print_block_aux fmt b_else
    end

  and print_stmt_aux fmt s =
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in

    begin match s.elt with
      | Decl d -> print_vdecl_aux ";" fmt d

      | Assn (p,e) ->
          pp_open_box fmt 0;
        print_exp_aux 0 fmt p;
        pps " ="; ppsp ();
        print_exp_aux 0 fmt e;
        pps ";"; pp_close_box fmt ()

      | SCallRaw (e, es) -> 
        print_id_aux fmt e; print_exps_aux "(" ")" fmt es; pps ";"

      | SCall (variant, es) -> let e = match variant with MethodM(s, _) | MethodL(s, _) -> s in
          print_id_aux fmt e; print_exps_aux "(" ")" fmt es; pps ";"

      | Ret (eo) ->
          pps "return";
          begin match eo with
            | None -> ()
            | Some e -> pps " "; print_exp_aux 0 fmt e
          end; pps ";"

      | If (e, b_then, opt_b_else) ->
          pps "if ("; print_exp_aux 0 fmt e; pps ") ";
          print_cond_aux fmt b_then opt_b_else

      | While(e, b) ->
        pps "while ("; print_exp_aux 0 fmt e; pps ") ";
        print_block_aux fmt b

      | For(decls, eo, so, body) ->
        pps "for ("; pp_open_hvbox fmt 0;
          print_list_aux fmt (fun () -> pps ","; ppsp ()) (print_vdecl_aux "") decls;
          pps ";"; ppsp ();
        begin match eo with
          | None -> ();
          | Some e -> print_exp_aux 0 fmt e;
        end;
        pps ";"; ppsp ();
        begin match so with
          | None -> ()
          | Some s -> print_stmt_aux fmt s
        end; pp_close_box fmt ();
        pps ") "; print_block_aux fmt body

      | Commute(variant, phi, bodies) ->
          pps "commute_";
          begin match variant with
            | CommuteVarSeq -> pps "seq"
            | CommuteVarPar -> pps "par"
          end;
          begin match phi with
            | PhiExp(e) -> pps " ("; print_exp_aux 0 fmt e; pps ") "
            | PhiInf -> pps " _ "
          end;
          let ppnl = pp_force_newline fmt in
          (* Basically copy pasted from print_block_aux *)
          if (List.length bodies) > 0 then
            begin pps "{"; ppnl (); pps "  ";
                  pp_open_vbox fmt 0;
                  List.iter (Util.compose ppnl (print_block_aux fmt)) bodies;
                  pp_close_box fmt ();
                  ppnl (); pps "}"
            end
          else pps "{ }"
      | Raise _ -> raise @@ NotImplemented "print_stmt_aux Raise"
      | Assert _ -> raise @@ NotImplemented "print_stmt_aux Assert"
      | Assume(e) ->
        pps "assume("; print_exp_aux 0 fmt e; pps ");"
      | Havoc(id) ->
        pps "havoc "; pps id; pps ";"
    end

  let print_mdecl_aux fmt {elt={pure; mrtyp; mname; args; body};_} = (* TODO: doesn't use pure *)
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in
    let ppnl = pp_force_newline fmt in

    print_ty_aux fmt mrtyp;
    pps @@ Printf.sprintf " %s(" mname;
    pp_open_hbox fmt ();
    print_list_aux fmt (fun () -> pps ","; ppsp ())
      (fun fmt -> fun (t, id) ->
        print_ty_aux fmt t;
        pps " ";
        print_id_aux fmt id;
      ) args;
    pp_close_box fmt ();
    pps ") "; print_block_aux fmt body; ppnl ()

  let print_gdecl_aux fmt (gd:gdecl) =
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in
    pp_open_hbox fmt ();
    pps @@ Printf.sprintf "global %s =" gd.name; ppsp ();
    print_exp_aux 0 fmt gd.init; pps ";";
    pp_close_box fmt ()

  let print_field fmt f =
    let pps = pp_print_string fmt in
    pp_open_hbox fmt ();
    print_ty_aux fmt f.ftyp; pps " "; pps f.field_name;
    pp_close_box fmt ()

  let print_sdecl_aux fmt ({sname;fields}:Ast.sdecl) =
    let pps = pp_print_string fmt in
    let ppsp = pp_print_space fmt in
    pp_open_hbox fmt ();
    pps @@ Printf.sprintf "struct %s " sname; ppsp ();
    pps "{";
    List.iter (fun s -> print_field fmt s; pps "; ") fields;
    pps "}";
    pp_close_box fmt ()

  let print_decl_aux fmt g =
    begin match g with
      | Gvdecl d -> print_gdecl_aux fmt d.elt
      | Gmdecl m -> print_mdecl_aux fmt m
      | Gsdecl s -> print_sdecl_aux fmt s.elt
    end

  let print_prog_aux fmt p =
    let ppnl = pp_force_newline fmt in
    pp_open_vbox fmt 0;
    List.iter (fun g -> print_decl_aux fmt g; ppnl (); ppnl ()) p;
    pp_close_box fmt ()

  let print ppx x : unit =
    pp_open_hvbox std_formatter 0;
    ppx std_formatter x;
    pp_close_box std_formatter ();
    pp_print_newline std_formatter ()

  let string_of ppx x : string =
    pp_open_hvbox str_formatter 0;
    ppx str_formatter x;
    pp_close_box str_formatter ();
    flush_str_formatter ()

  let print_prog (p:prog) : unit = print print_prog_aux p
  let string_of_prog (p:prog) : string = string_of print_prog_aux p

  let print_stmt (s:stmt node) : unit = print print_stmt_aux s
  let string_of_stmt (s:stmt node) : string = string_of print_stmt_aux s

  let print_block (b:block node) : unit = print print_block_aux b
  let string_of_block (b:block node) : string = string_of print_block_aux b

  let print_exp (e:exp node) : unit = print (print_exp_aux 0) e
  let string_of_exp (e:exp node) : string = (string_of (print_exp_aux 0) e) |> Util.replace "\r" " " |> Util.replace "\n" " "

  let print_ty (t:ty) : unit = print print_ty_aux t
  let string_of_ty (t:ty) : string = string_of print_ty_aux t

end

(*** Print ML encoding of AST as a string ***)
module AstML = struct
  (* AST to ML *)

  let include_nodes = ref true

  let sp = Printf.sprintf

  let string_of_list (f: 'a -> string) (l: 'a list) : string =
    sp "[ %s ]" (String.concat " ; \n" (List.map f l))

  let string_of_option (f: 'a -> string) (o: 'a option) : string =
    begin match o with
    | None -> sp "None"
    | Some x -> sp "Some (%s)" (f x)
    end

  let string_of_node (f: 'a -> string) ({elt;loc}: 'a node) =
    if !include_nodes 
    then sp "{ elt = %s; loc = %s }" (f elt) (Range.string_of_range loc)
    else f elt

  let string_of_id : id -> string = (sp "\"%s\"")

  let string_of_htvariant = function
    | HTVarNaiveConcurrent -> "HTVarNaiveConcurrent"
    | HTVarSequential -> "HTVarSequential"

  let rec string_of_ty (t:ty) : string =
    match t with
    | TBool -> "TBool"
    | TInt -> "TInt"
    | TVoid -> "TVoid"
    | TStr -> "TStr"
    | TChanR -> "TChanR"
    | TChanW -> "TChanW"
    | THashTable (tyk, tyv) ->
      sp "THashTable (%s, %s)" (string_of_ty tyk) (string_of_ty tyv)
    | TArr ty -> sp "TArr (%s)" @@ string_of_ty ty
    | TStruct id -> sp "TStruct (%s)" @@ string_of_id id

  let string_of_binop : binop -> string = function
    | Add    -> "Add"
    | Div    -> "Div"
    | Exp    -> "Exp"
    | Sub    -> "Sub" 
    | Mul    -> "Mul" 
    | Eq     -> "Eq" 
    | Neq    -> "Neq" 
    | Lt     -> "Lt" 
    | Lte    -> "Lte" 
    | Gt     -> "Gt" 
    | Gte    -> "Gte" 
    | And    -> "And" 
    | Or     -> "Or" 
    | IAnd   -> "IAnd" 
    | IOr    -> "IOr" 
    | Shl    -> "Shl" 
    | Shr    -> "Shr" 
    | Sar    -> "Sar" 
    | Concat -> "Concat"
    | Mod    -> "Mod"

  let string_of_unop : unop -> string = function
    | Neg    -> "Neg"
    | Lognot -> "Lognot"
    | Bitnot -> "Bitnot"

  let string_of_tmethod (m : tmethod) : string =
    raise @@ NotImplemented "string_of_tmethod"

  let string_of_method_variant (mv : method_variant) : string =
    raise @@ NotImplemented "string_of_method_variant"

  let rec string_of_exp_aux (e: exp) : string =
    begin match e with 
      | CNull t -> sp "CNull %s" (string_of_ty t)
      | CBool b -> sp "CBool %b" b
      | CInt i -> sp "CInt %LiL" i
      | CStr s -> sp "CStr %S" s
      | CArr (t,cs) -> sp "CArr (%s, %s)" 
                          (string_of_ty t) 
                          (string_of_list string_of_exp cs)
      | Id id -> sp "Id %s" (string_of_id id)
      | Index (e, i) -> sp "Index (%s, %s)" 
                          (string_of_exp e) (string_of_exp i)
      | Call (mv, exps) ->
        sp "Call (%s, %s)"
          (string_of_method_variant mv)
          (string_of_list string_of_exp exps)
      | CallRaw (id, exps) ->
        sp "CallRaw (%s, %s)"
          (string_of_id id)
          (string_of_list string_of_exp exps)
      | NewArr (t,e1) -> sp "NewArr (%s, %s)"
          (string_of_ty t) (string_of_exp e1)
      | NewHashTable (variant, tyk, tyv) -> sp "NewHashTable (%s, %s, %s)"
        (string_of_htvariant variant) (string_of_ty tyk) (string_of_ty tyv)
      | Bop (b, e1, e2) -> sp "Bop (%s, %s, %s)"
          (string_of_binop b) (string_of_exp e1) (string_of_exp e2)
      | Uop (u, e) -> sp "Uop (%s, %s)"
          (string_of_unop u) (string_of_exp e)
      | Ternary (c, t, e) -> sp "Ternary (%s, %s, %s)"
          (string_of_exp c) (string_of_exp t) (string_of_exp e)
      | CStruct (id, l) -> 
        sp "CStruct (%s, %s)"
          id
          (string_of_list string_of_field l)
      | Proj(exp, id) -> sp "Proj (%s, %s)" (string_of_exp exp) (string_of_id id)
    end

  and string_of_exp (e:exp node) : string = 
    string_of_node string_of_exp_aux e

  and string_of_field ((id, exp) : cfield) : string =
    sp "%s = %s;" (string_of_id id) (string_of_exp exp)

  let string_of_vdecl_aux (id,(ty,init):vdecl) : string =
    sp "(%s, (%s, %s))"
    (string_of_id id) (string_of_ty ty) (string_of_exp init)

  let string_of_vdecl (d:vdecl node) : string =
    string_of_node string_of_vdecl_aux d

  let rec string_of_stmt_aux (s:stmt) : string =
    match s with
    | Assn (p, e) -> sp "Assn (%s, %s)" (string_of_exp p) (string_of_exp e)
    | Decl d -> sp "Decl (%s)" (string_of_vdecl_aux d)
    | Ret e -> sp "Ret (%s)" (string_of_option string_of_exp e)
    | SCallRaw (exp, exps) -> 
      sp "SCallRaw (%s, %s)" (string_of_id exp) (string_of_list string_of_exp exps)
    | SCall (mv, exps) ->
      sp "SCall (%s, %s)" (string_of_method_variant mv) (string_of_list string_of_exp exps)
    | If (e,b1,b2) -> sp "If (%s, %s, %s)"
                        (string_of_exp e) (string_of_block b1) (string_of_block b2)
    | For (d,e,s,b) -> sp "For (%s, %s, %s, %s)"
                          (string_of_list string_of_vdecl_aux d) 
                          (string_of_option string_of_exp e)
                          (string_of_option string_of_stmt s) (string_of_block b)
    | While (e,b) -> sp "While (%s, %s)" (string_of_exp e) (string_of_block b)
    | Commute (var,phi,bl) -> 
      sp "Commute (%s, %s, %s)"
        begin match var with
        | CommuteVarSeq -> "CommuteVarSeq"
        | CommuteVarPar -> "CommuteVarPar"
        end
        begin match phi with 
        | PhiInf   -> "PhiInf" 
        | PhiExp e -> sp "PhiExp (%s)" (string_of_exp e)
        end
        (string_of_list string_of_block bl)
    | Raise e ->
      sp "Raise (%s)" (string_of_exp e)
    | Assert e ->
      sp "Assert (%s)" (string_of_exp e)
    | Assume e ->
      sp "Assume (%s)" (string_of_exp e)
    | Havoc id ->
      sp "Havoc %s" (string_of_id id)

  and string_of_stmt (s:stmt node) : string =
    string_of_node string_of_stmt_aux s

  and string_of_block (b:block node) : string =
    string_of_list string_of_stmt b.elt

  let string_of_args : (ty * id) list -> string =
    string_of_list (fun (t,i) ->
      sp "(%s,%s)" (string_of_ty t) (string_of_id i))

  let rec string_of_mdecl_aux (m:mdecl) : string =
    sp "{ mrtyp = %s; mname = %s; args = %s; body = %s }"
    (string_of_ty m.mrtyp) (string_of_id m.mname)
    (string_of_args m.args) (string_of_block m.body)

  and string_of_mdecl (m:mdecl node) : string =
    string_of_node string_of_mdecl_aux m

  let string_of_gdecl_aux (gd:gdecl) : string =
    sp "{ name = %s; init = %s }"
      (string_of_id gd.name) (string_of_exp gd.init)

  let string_of_gdecl (d:gdecl node) : string =
    string_of_node string_of_gdecl_aux d

  let string_of_field {field_name; ftyp} : string =
    sp "{ field_name = %s; ftyp = %s }"
      (string_of_id field_name) (string_of_ty ftyp)

  let string_of_sdecl_aux ({sname;fields} : sdecl) : string =
    sp "{ sname = %s, fields = (%s))" (string_of_id sname) (string_of_list string_of_field fields)

  let string_of_sdecl (s:sdecl node) : string =
    string_of_node string_of_sdecl_aux s

  let string_of_decl : decl -> string = function
    | Gvdecl d -> sp "Gvdecl (%s)" (string_of_gdecl d)
    | Gmdecl m -> sp "Gmdecl (%s)" (string_of_mdecl m)
    | Gsdecl s -> sp "Gsdecl (%s)" (string_of_sdecl s)

  let string_of_prog : prog -> string =
    string_of_list string_of_decl

  let rec string_of_value : value -> string =
    function
    | VVoid   -> "void"
    | VNull t -> string_of_ty t ^ " null"
    | VBool v -> if v then "true" else "false"
    | VInt v  -> Int64.to_string v
    | VStr v  -> "\"" ^ v ^ "\""
    
    | VArr (_, v) -> 
      let ss = Array.to_list @@ Array.map string_of_value v in
      "[" ^ (String.concat "; " ss) ^ "]"

    | VChanR (s, _, _) -> "read_channel(" ^ s ^ ")"
    | VChanW (s, _)    -> "write_channel(" ^ s ^ ")"

    | VHashTable _ -> raise @@ NotImplemented "string_of_value VHashTable"

    | VStruct (id,vs) ->
      List.map (fun (i,v) -> sp " %s = %s" i (string_of_value !v)) vs |>
      String.concat ";" |>
      sp "%s {%s }" id
        
  let string_of_binding_list (l : tyval bindlist) : string =
    let s =
      l |>
      List.map (fun (i,(t,v)) ->
        string_of_ty t ^ " " ^ i ^ " = " ^ string_of_value !v) 
      |>
      String.concat (greyize " , ")
    in greyize "( " ^ s ^ greyize " )"

  let string_of_blockstk (l : blockstk) : string =
    let s =
      l |>
      List.map string_of_binding_list |>
      String.concat (reddize " ; ")
    in greenize "[ " ^ s ^ greenize " ]"

  let string_of_callstk (callstk : callstk) : string =
    let s =
      callstk |>
      List.map string_of_blockstk |>
      String.concat (reddize " | ")
    in "{ " ^ s ^ " }"

end
  
(* Create printing scheme for custom exceptions *)
let () =
  Printexc.register_printer @@
  function
  | TypeFailure (s,r) ->
    Some (Printf.sprintf "TypeFailure(%s, %s)" s @@ Range.string_of_range r)
  | TypeMismatchFailure (s,expected,received,r) ->
    Some (Printf.sprintf "Type mismatch at %s: %s. Expected %s, received %s." 
      (Range.string_of_range r)
      s
      (AstML.string_of_ty expected)
      (AstML.string_of_ty received))
  | ValueFailure (s,r) -> 
    Some (Printf.sprintf "ValueFailure(%s, %s)" s @@ Range.string_of_range r)
  | UnreachableFailure s -> 
    Some (Printf.sprintf "UnreachableFailure(%s)" s)
  | IdNotFound (s,r) ->
    Some (Printf.sprintf "IdNotFound(%s, %s)" s @@ Range.string_of_range r)
  | NotImplemented s ->
    Some (Printf.sprintf "NotImplemented(%s)" s)
  | CommuteFailure (s,r) ->
    Some (Printf.sprintf "CommuteFailure(%s, %s)" s @@ Range.string_of_range r)
  | AssertFailure r ->
    Some (sp "Assertion at %s failed" @@ Range.string_of_range r)
  | _ -> None

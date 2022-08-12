open Ast
open Ast_print
open Util

(* TODO: Make all of these local to c_of_prog *)
let indent = ref 0
let mk_newline () = "\n" ^ String.make !indent ' '

(* TODO: Return type -- not pure string, but a string with state? state monad and do St string?
   To capture env vars such as string/array constants. *)

let rec c_of_ty = function
    | TVoid -> "void"
    | TInt -> "int"
    | TBool -> "bool" (* TODO: Not ansi C. can use int, or stdbool.h? *)
    | TStr -> "const char*"
    | TArr(ty) -> sp "%s*" (c_of_ty ty)
    | THashTable(kty, vty) -> raise @@ NotImplemented "c_of_ty THashTable"
    | TChanR -> raise @@ NotImplemented "c_of_ty TChanR"
    | TChanW -> raise @@ NotImplemented "c_of_ty TChanW"
    | TStruct(id) -> raise @@ NotImplemented "c_of_ty TStruct"

let rec c_of_expnode x = c_of_exp x.elt
and c_of_exp = function
    | CNull(ty) -> "0"
    | CBool(b) -> string_of_bool b
    | CInt(i) -> Int64.to_string i (* ^ "L" *)
    | CStr(s) -> sp "\"%s\"" s
    | CArr(ty, e) -> raise @@ NotImplemented "c_of_exp CArr"
    | NewArr(ty, e) -> raise @@ NotImplemented "c_of_exp NewArr"
    | NewHashTable(var, kty, vty) -> raise @@ NotImplemented "c_of_exp NewHashTable"
    | Id(id) -> (!mangle id)
    | Index(arr, idx) -> sp "(%s[%s])" (c_of_expnode arr) (c_of_expnode idx)
    | CallRaw(id, es) -> sp "(%s(%s))" id (String.concat ", " @@ List.map c_of_expnode es)
    | Call(var, es) -> begin match var with
        | MethodM(id, tmethod) -> raise @@ NotImplemented "c_of_exp Call.MethodM"
        | MethodL(id, lmethod) -> raise @@ NotImplemented "c_of_exp Call.MethodL"
        end
    | Bop(bop, l, r) -> sp "(%s%s%s)" (c_of_expnode l) (AstPP.string_of_binop bop) (c_of_expnode r)
    | Uop(uop, e) -> sp "(%s%s)" (AstPP.string_of_unop uop) (c_of_expnode e)
    | Ternary(g,t,e) -> sp "(%s?%s:%s)" (c_of_expnode g) (c_of_expnode t) (c_of_expnode e)
    | CStruct(id, e) -> raise @@ NotImplemented "c_of_exp CStruct"
    | Proj(e, id) -> raise @@ NotImplemented "c_of_exp Call.Proj"

and c_of_stmt = function
    | Assn(lhs, rhs) -> sp "%s = %s" (c_of_expnode lhs) (c_of_expnode rhs)
    | Decl(id, (ty, rhs)) -> env := (ty, id) :: !env; sp "%s %s = %s" (c_of_ty ty) (!mangle id) (c_of_expnode rhs)
    | Ret(eo) -> begin match eo with
        | Some e -> sp "return %s" @@ c_of_expnode e
        | None -> "return"
        end
    | SCallRaw(id, args) -> sp "%s(%s)" id (String.concat ", " @@ List.map c_of_expnode args)
    | SCall(var, args) -> begin match var with
        | MethodM(id, tmethod) -> raise @@ NotImplemented "c_of_stmt SCall.MethodM"
        | MethodL(id, lmethod) -> raise @@ NotImplemented "c_of_stmt SCall.MethodL"
        end
    | If(guard, t, e) -> sp "if(%s) %s%selse %s" (c_of_expnode guard) (c_of_blocknode t) (mk_newline ()) (c_of_blocknode e)
    | For(inits, guard, update, body) -> sp "for(%s; %s; %s) %s" (String.concat ", " @@ List.map (fun (id, (ty, rhs)) -> sp "%s %s = %s" (c_of_ty ty) (!mangle id) (c_of_expnode rhs)) inits) (guard |> Option.map c_of_expnode |> Option.value ~default:"") (update |> Option.map c_of_stmtnode |> Option.value ~default:"") (c_of_blocknode body)
    | While(guard, body) -> sp "while(%s) %s" (c_of_expnode guard) (c_of_blocknode body)
    | Raise(e) -> raise @@ NotImplemented "c_of_stmt Raise"
    | Commute(var, phi, bodies) -> !handle_comm phi bodies
    | Havoc(id) -> sp "/* %s = __VERIFIER_nondet_int() */" (!mangle id)
    | Assume(e) -> sp "/* assume%s */" (c_of_expnode e)
and c_of_stmtnode x = c_of_stmt x.elt
and c_of_block b = let indent_pre = !indent in 
    indent := indent_pre + 4;
    let res = "{" ^ mk_newline () ^ String.concat (mk_newline ()) @@ List.map (fun x -> x ^ ";") @@ List.map c_of_stmtnode b in
    indent := indent_pre;
    res ^ mk_newline () ^ "}"
and c_of_blocknode b = c_of_block b.elt

and sequential_comm phi bodies =
    c_of_block (List.concat @@ List.map (fun x -> x.elt) bodies)

and handle_comm = ref ultimate_comm (* TODO: Default this to sequential; is like this just for testing *)

and mangle = ref Fun.id

and ultimate_comm phi (left :: right :: []) =
    let mangle_temp = !mangle in
    let acc = ref "" in
    let (^=) l r = l := !l ^ r in
    mangle := compose Fun.id mangle_temp;
    acc ^= c_of_blocknode left;
    acc ^= mk_newline ();
    acc ^= c_of_blocknode right;
    acc ^= mk_newline ();
    let mangle_right = compose (fun x -> x ^ "_2") mangle_temp in
    mangle := mangle_right;
    acc := (List.fold_left (fun acc decl -> acc ^ decl ^ ";" ^ mk_newline ()) "" @@ List.map (fun (ty, id) -> sp "%s %s = %s" (c_of_ty ty) (!mangle id) id) !env) ^ !acc; (* Copy pre first run *)
    let env' = !env in
    acc ^= c_of_blocknode right;
    acc ^= mk_newline ();
    acc ^= c_of_blocknode left;
    mangle := mangle_temp;
    !acc ^ mk_newline () ^ let st_eq = String.concat " && " @@ List.map (fun (_, id) -> sp "%s == %s" id (mangle_right id)) env' in
        match phi with
        | PhiExp(e) -> sp "if(%s && !(%s)) { reach_error(); }" (c_of_expnode e) st_eq
        | PhiInf -> sp "if(!(%s)) { reach_error(); }" st_eq (* TODO: Maybe do this after inference? Or the point is to use Ultimate to help infer. *)

and env = ref [] (* TODO: When to refresh? etc? Better as state monad *)
    
let c_of_decl = function
    | Gvdecl(dnode) -> let d = dnode.elt in sp "%s %s %s;" (c_of_ty d.ty) d.name (c_of_expnode d.init)
    | Gmdecl(dnode) -> let d = dnode.elt in sp "%s %s(%s) %s" (c_of_ty d.mrtyp) d.mname (String.concat ", " @@ List.map (fun (ty, id) -> sp "%s %s" (c_of_ty ty) id) d.args) (c_of_blocknode d.body)
    | Gsdecl(d) -> raise @@ NotImplemented "c_of_decl Gsdecl"

let c_of_prog prog =
    String.concat "\n\n" @@ List.map c_of_decl prog

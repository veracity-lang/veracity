open Util

module Smt = struct 
    include Servois2.Smt
end

let main_method_name = "main"

type 'a node = { elt : 'a; loc : Range.t }

let no_loc x =
  { elt = x; loc = Range.norange }

let node_app f n =
  { n with elt = f n.elt }

let node_up n v =
  { n with elt = v }


let map_elt (l : ('a node) list) : 'a list =
  List.map (fun n -> n.elt) l

(** types related to servois2 *)
type sty = Smt.ty
type sexp = Smt.exp

type id = string

type 'a binding = id * 'a
type 'a bindlist = 'a binding list

type unop =
| Neg
| Lognot
| Bitnot

type binop =
| Add  | Sub | Mul | Mod
| Div | Exp
| Eq   | Neq

| Lt   | Lte | Gt | Gte
| And  | Or
| IAnd | IOr (* Bitwise ops *)
| Shl  | Shr | Sar
| Concat

type hashtable_variant =
| HTVarSequential
| HTVarNaiveConcurrent

type ty =
| TVoid
| TInt | TBool | TStr
| TArr of ty
| THashTable of ty * ty
| TChanR | TChanW
| TStruct of id


let rec sty_of_ty = function
  | TInt -> Smt.TInt
  | TBool -> Smt.TBool
  | TStr -> Smt.TString
  | TArr t -> Smt.TArray (Smt.TInt, sty_of_ty t)
  | _ -> raise @@ NotImplemented "Conversion to Servois type not supported"


type sht_ids = { ht : id; keys : id; size : id }

(* Embedded types from VCY to servois *)
type ety =
  | ETInt of id
  | ETBool of id
  | ETStr of id
  | ETArr of id * sty
  | ETHashTable of sty * sty * sht_ids

type arglist = ty bindlist

type tstruct = ty bindlist

type exp =
| CNull of ty
| CBool of bool
| CInt of int64
| CStr of string
| CArr of ty * exp node list
| NewArr of ty * exp node
| NewHashTable of hashtable_variant * ty * ty
| Id of id
| Index of exp node * exp node
| CallRaw of id * exp node list
| Call of method_variant * exp node list
| Bop of binop * exp node * exp node
| Uop of unop * exp node
| Ternary of exp node * exp node * exp node
| CStruct of id * exp node bindlist
| Proj of exp node * id

and tmethod =
  { pure : bool
  ; rty  : ty
  ; args : arglist
  ; body : block node
  }

and method_variant =
| MethodM of tmethod binding
| MethodL of lib_method binding

and cfield = exp node binding

and vdecl = (ty * exp node) binding

and commute_condition =
| PhiExp of exp node (* Explicit commute condition *)
| PhiInf             (* Infer condition with analysis *)

and commute_variant =
| CommuteVarSeq
| CommuteVarPar

and block = stmt node list

and stmt =
| Assn of exp node * exp node
| Decl of vdecl
| Ret of exp node option
| SCallRaw of id * exp node list
| SCall of method_variant * exp node list
| If of exp node * block node * block node
| For of vdecl list * exp node option * stmt node option * block node
| While of exp node * block node
| Raise of exp node
| Commute of commute_variant * commute_condition * block node list
| Assert of exp node
| Assume of exp node
| Havoc of id
| Require of exp node

and tyval = ty * (value ref)

and blockstk = tyval bindlist list
and callstk = blockstk list


and global_env =
  { methods : tmethod bindlist
  ; globals : tyval bindlist
  ; structs : tstruct bindlist
  ; lib_methods : lib_method bindlist
  }
and env =
  { g : global_env  (* Global environment *)
  ; l : callstk     (* Local environment *)
  }
and lib_method =
  { pure : bool
  (*; spec : method_spec *) (* TODO reintroduce *)
  ; func : env * value list -> env * value
  ; pc : (int * ety * sexp list -> post_condition) option
  }

and post_condition =
  { bindings : sexp Smt.bindlist                (* All new let bindings *)
  ; ret_exp  : sexp                     (* Value of method return *)
  ; asserts  : sexp list                (* Any additional assertions made *)
  ; terms    : (sexp * sty) list        (* Terms *)
  ; preds    : (string * (sty list)) list (* Any particular predicates *)
  }

(*and method_spec = (* TODO For inlining procedure *)
  { args : aid list
  ; ret  : aid
  ; pc   : aexp
  }*)

and value =
  | VVoid
  | VNull  of ty
  | VBool  of bool
  | VInt   of int64
  | VStr   of string
  | VArr   of ty * value array
  | VHashTable of hashtable
  | VChanR  of string * in_channel * int
  | VChanW  of string * out_channel
  | VStruct of id * value ref bindlist

and hashtable = ty * ty * ht_variant

and ht_variant =
  | VHTSequential of value Hashtables.Hashtable_seq.t
  | VHTNaive of value Hashtables.Hashtable_naive.t

(* VCY type <=> mangle index, servois type *)
type embedding_map = (ty binding * ety) list


let mangle_servois_id id index =
  Smt.EVar (Var (id ^ "_" ^ string_of_int index))

let mangle_servois_id_pair id index =
  mangle_servois_id id index, mangle_servois_id id (index + 1)

let mangle_servois_id_final id =
  Smt.EVar (VarPost id)

let rec string_of_sty = function
  | Smt.TInt -> "Int"
  | Smt.TBool -> "Bool"
  | Smt.TString -> "String"
  | Smt.TArray (k,v) -> sp "(Array %s %s)" (string_of_sty k) (string_of_sty v)
  | Smt.TSet t -> sp "(Set %s)" (string_of_sty t)
  | _ -> failwith "string_of_sty"
  (* | STGen g -> g *) (* TODO: we need this? *)

(*
(*** Inlining analysis types ***)

(* Variants of analysis ID 
 * Globals need to track the ID to which they correspond,
 *   so that Servois' result can be turned back into
 *   and expression in terms of the globals
 *)
and aid_variant =
| ATrueGlobal of id
| ARelGlobal of id   (* Relative global *)
| ALocal

(* Analysis ID *)
and aid = aid_variant ref

(* TODO introduce more possible things *)
and aconst =
| ABool of bool
| AInt of int64

(* TODO add more
 * Predicates more complex than arithmetic (in)equality *)
and apredicate =
| AMember of aid * aexp

(* TODO introduce more possible things *)
and aexp =
| AConst of aconst
| AId of aid
| ABop of binop * aexp * aexp
| AUop of unop * aexp
| APred of apredicate

(* TODO introduce more possible things, namely loops *)
type astmt =
| AAssn of aid * aexp (* Could be a new local, or an extant global/local *)
| ABranch of aexp * aseq * aseq
| AAssert of aexp
and aseq = astmt list

*)





type gdecl = { name : id; ty : ty; init : exp node }

type mdecl = { pure : bool; mrtyp : ty; mname : id; args : (ty * id) list; body : block node }
let mdecl_of_tmethod name (t : tmethod) = { pure = t.pure; mrtyp = t.rty; mname = name; args = List.map flip t.args; body = t.body }
(*type fdecl = { frtyp : ty; fname : id; args : (ty * id) list; body : exp node }*)

type field = { field_name : id; ftyp : ty }
type sdecl = { sname : id; fields : field list }

type decl =
| Gvdecl of gdecl node (* Global variable *)
| Gmdecl of mdecl node (* Method *)
| Gsdecl of sdecl node (* Struct *)

type prog = decl list


(* Stuff for interpretation *)

exception TypeFailure of string * Range.t

(* Description of situation, expected, received, location *)
exception TypeMismatchFailure of string * ty * ty * Range.t

exception ValueFailure of string * Range.t
exception IdNotFound of id * Range.t
exception CommuteFailure of string * Range.t
exception RuntimeFailure of string * Range.t

exception AssertFailure of Range.t

let initial_hashtable_size = 16

let type_of_value : value -> ty =
  function
  | VNull ty -> ty
  | VVoid    -> TVoid
  | VBool _  -> TBool
  | VInt _   -> TInt
  | VStr _   -> TStr
  | VChanR _ -> TChanR
  | VChanW _ -> TChanW
  | VArr (ty,_)    -> TArr ty
  | VStruct (id,_) -> TStruct id
  | VHashTable (tyk, tyv, _) -> THashTable (tyk, tyv)

(* Is a type passed by reference (sort of)? 
 * Technically everything is passed by value.
 *)
let type_is_reference : ty -> bool =
  function
  | TChanR | TChanW | TArr _ | THashTable _ | TStruct _ -> true
  | _ -> false

(* Presently this does the same as ( = ) *)
let rec ty_eq (env : env) ty1 ty2 =
  match ty1, ty2 with
  | TVoid, TVoid
  | TInt, TInt
  | TBool, TBool
  | TStr, TStr
  | TChanR, TChanR
  | TChanW, TChanW
    -> true
  | TArr t1, TArr t2 ->
    ty_eq env t1 t2
  | THashTable (k1,v1), THashTable (k2,v2) ->
    ty_eq env k1 k2 &&
    ty_eq env v1 v2
  | TStruct id1, TStruct id2 ->
    id1 = id2
  | _ -> false

let ty_match env v ty =
  ty_eq env (type_of_value v) ty

let ty_default_value (env : env) : ty -> value =
  function
  | TVoid  -> VVoid
  | TBool  -> VBool false
  | TInt   -> VInt 0L
  | TStr   -> VStr ""
  | TChanR -> VNull TChanR
  | TChanW -> VNull TChanW
  | TArr ty    -> VNull (TArr ty)
  | TStruct id -> VNull (TStruct id)
  | THashTable (tyk, tyv) -> VNull (THashTable (tyk, tyv))

let value_of_htdata : value Hashtables.htdata -> value =
  function
  | Hashtables.HTD v -> v
  | Hashtables.HTint i -> VInt (Int64.of_int i)

let htdata_of_value : value -> value Hashtables.htdata =
  function
  | VInt i -> Hashtables.HTint (Int64.to_int i)
  | v -> Hashtables.HTD v


let init_mangle : ety -> Smt.exp Smt.bindlist =
  let [@warning "-8"] bind i =
    let Smt.EVar mangled = (mangle_servois_id i 1) in
    (mangled, Smt.EVar (Var i))
  in function
  | ETInt i | ETBool i | ETStr i | ETArr (i, _) ->
    [bind i]
  | ETHashTable (_,_,{ht;keys;size}) ->
    List.map bind [ht;keys;size]

let final_mangle (mangle : int) : ety -> Smt.exp = 
  let bind i =
    Smt.EBop (Eq, (mangle_servois_id_final i), (mangle_servois_id i mangle))
  in function
  | ETInt i | ETBool i | ETStr i | ETArr (i, _) ->
    bind i
  | ETHashTable (_,_,{ht;keys;size}) ->
    Smt.ELop (And, (List.map bind [ht;keys;size]))

let remove_index (mangled_id: string) : string =
  let r = Str.regexp "_[0-9]+" in 
  Str.replace_first r "" mangled_id 


let compile_ety_to_sty (id: string) (ty : ety) : (string * sty) list = 
  match ty with
  | ETInt _ -> [(id, Smt.TInt)]
  | ETBool _ -> [(id, Smt.TBool)]
  | ETStr _ -> [(id, Smt.TString)]
  | ETArr (_, sty) -> [(id, Smt.TArray (Smt.TInt, sty))]
  | ETHashTable (styk, styv, {ht=ht_id; keys=ht_keys; size=ht_size}) -> 
    [(ht_id, Smt.TArray (styk, styv)); (ht_keys, Smt.TSet styk); (ht_size, Smt.TInt)]


(** AST to SMT types *)

let bop_to_servoisBop (op: binop) : Smt.bop =
  match op with
  | Sub -> Smt.Sub
  | Mul -> Smt.Mul
  | Mod -> Smt.Mod
  | Div -> Smt.Div
  | Eq -> Smt.Eq
  | Lt -> Smt.Lt
  | Gt -> Smt.Gt
  | Lte -> Smt.Lte
  | Gte -> Smt.Gte
  | _ -> failwith "undefined op"

let bop_to_servoisLop (op: binop) : Smt.lop =
    match op with
    | Add -> Smt.Add
    | And -> Smt.And
    | Or -> Smt.Or
    | _ -> failwith "undefined op"

let uop_to_servoisUop (op: unop) : Smt.uop =
    match op with
    | Lognot -> Smt.Not
    | Neg -> Smt.Neg
    | _ -> failwith "undefined op"


    (** SMT to AST types *)

let smt_bop_to_binop (op: Smt.bop) : binop =
  match op with
  | Smt.Sub -> Sub
  | Smt.Mul -> Mul
  | Smt.Mod -> Mod
  | Smt.Div -> Div
  | Smt.Eq -> Eq
  | Smt.Lt -> Lt
  | Smt.Gt -> Gt
  | Smt.Lte -> Lte
  | Smt.Gte -> Gte
  | _ -> failwith "undefined op"

let smt_lop_to_binop (op: Smt.lop) : binop =
  match op with 
  | Smt.Add -> Add 
  | Smt.And -> And
  | Smt.Or -> Or

let smt_uop_to_unop (op: Smt.uop) : unop =
  match op with
  | Smt.Not -> Lognot
  | Smt.Neg -> Neg

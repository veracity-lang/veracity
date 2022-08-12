open Ast
open Util
open Ast_print

let file_ext = "vcyi"

let debug_display = ref false

let debug_print (s : string lazy_t) =
  if !debug_display then print_string (Lazy.force s); flush stdout

type interface =
  { name      : string
  ; methods   : (ty * arglist) bindlist
  ; functions : (ty * arglist) bindlist
  ; structs   : (ty bindlist)  bindlist
  ; globals   :  ty            bindlist

  (* Commutativity conditions *)
  ; phis      : ((id * id) * exp option) list
  }


let generate_interface (prog_name : string) (prog : prog) (yaml_of_prog : string) (no_commute : bool) : interface =
  raise @@ NotImplemented "generate_interface"
  (*let env = Interp.initialize_env prog in

  let gen_phi m n =
    try
      debug_print @@ lazy (Printf.sprintf "Generating %s |><| %s\n" m n);
      let res = Analyze.invoke_servois yaml_of_prog m n in
      Some (Analyze.exp_of_servois_output env res)
    with e ->
      None
  in

  { name = prog_name
  ; methods =
    List.map (fun (id,(rty,args,_)) -> (id,(rty,args)))
      env.g.methods
  ; functions =
    List.map (fun (id,(rty,args,_)) -> (id,(rty,args)))
      env.functions
  ; structs =
    env.structs
  ; globals = 
    List.map (fun (id,v) -> (id, type_of_value v)) !(env.globals)
  ; phis =
    if no_commute then []
    else
      List.map fst env.methods |> 
      list_remove_instance main_method_name |>
      square_list_unordered |>
      List.map (fun (m,n) -> ((m,n), gen_phi m n))
  }*)

let augment_interface (prog : prog) (init_intf : interface) (no_commute : bool) : interface =
  raise @@ NotImplemented "augment_interface"

  (* TODO *)
let string_of_interface : interface -> string =
  let string_of_idty (id,ty) =
    Printf.sprintf "%s %s" (AstPP.string_of_ty ty) id
  in

  let string_of_global g =
    Printf.sprintf "%s;\n" (string_of_idty g)
  in

  let string_of_method (id,(ty,args)) =
    List.map string_of_idty args |>
    String.concat ", " |>
    Printf.sprintf "%s %s(%s);\n" (AstPP.string_of_ty ty) id 
  in

  let string_of_struct (id,fields) =
    fields |>
    List.map (fun field -> "\t" ^ string_of_idty field ^ ";") |>
    String.concat "\n" |>
    Printf.sprintf "struct %s {\n%s\n}\n" id
  in

  let string_of_function f =
    "pure " ^ string_of_method f
  in

  let string_of_phi ((m,n),e) =
    let phi =
      match e with
      | Some e -> AstPP.string_of_exp @@ Ast.no_loc e
      | None -> "?"
    in
    Printf.sprintf "%s |><| %s <= %s;\n" m n phi
  in

  fun {name;methods;functions;structs;globals;phis} ->
    List.map string_of_struct structs ::
    List.map string_of_function functions ::
    List.map string_of_global globals ::
    List.map string_of_method methods ::
    List.map string_of_phi phis ::
    [] |>
    List.map (String.concat "") |>
    String.concat "\n" |>
    Util.normalize_newlines |>
    String.trim

(* TODO implement interface parsing *)
let interface_of_string (s : string) : interface =
  raise @@ NotImplemented "interface_of_string"

(*

structs:
  <struct id> { <type> <field id> ; [...] } ;
  [...]

functions:
  <type> <method id> ( <type> <arg id> , [...] ) ;
  [...]

globals:
  <type> <global id> ;
  [...]

methods:
  <type> <method id> ( <type> <arg id> , [...] ) ;
  [...]

conditions:
  <method id> ( m_<arg id> , [...] )  |><|  <method id> ( n_<arg id> , [...] )  <=  <exp> ;
  [...]

*)
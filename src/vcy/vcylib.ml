open Ast
open Ast_print
open Util

let sp = Printf.sprintf

let smt_bind = sp "(%s %s)"

let smt_e e = match e with | Smt.EVar (Var v) ->  v | _ -> failwith "bad input"
let var_of_string s = Smt.Var s

let pure_id = fun x -> Smt.EVar (Var (remove_index x))

(* Only applies to stdout printing, not debug printing *)
let suppress_print = ref false

let counters : (int64 * Concurrent_counter.t) list ref = ref []

let mutexes : (int64 * Mutex.t) list ref = ref []

type method_library = lib_method bindlist

let lib_string : method_library =
  [ "length_of_string",
    { pure = true
    ; func = begin function
      | env, [VStr v] -> env, VInt (Int64.of_int @@ String.length v)
      | _ -> raise @@ TypeFailure ("length_of_string arguments", Range.norange)
      end
    ; pc = None
    }
  ; "string_of_int",
    { pure = true
    ; func = begin function
      | env, [VInt v] -> env, VStr (Int64.to_string v)
      | _ -> raise @@ TypeFailure ("string_of_int arguments", Range.norange)
      end
    ; pc = None
    }
  ; "string_of_bool",
    { pure = true
    ; func = begin function
      | env, [VBool v] ->
        env, if v then VStr "true" else VStr "false"
      | _ -> raise @@ TypeFailure ("string_of_bool arguments", Range.norange)
      end
    ; pc = None
    }
  ; "int_of_string",
    { pure = true
    ; func = begin function
      | env, [VStr s] ->
        env, VInt (Int64.of_string s)
      | _ -> raise @@ TypeFailure ("int_of_string arguments", Range.norange)
      end
    ; pc = None
    }
  ]

let lib_counter : method_library =
  [ "counter_init",
    { pure = false
    ; func = begin function
      | env, [VInt v] ->
        if List.mem_assoc v !counters
        then raise @@ ValueFailure ("counter " ^ Int64.to_string v ^ " already exists", Range.norange)
        else
          counters := (v, Concurrent_counter.init ()) :: !counters;
          env, VVoid
      | _ -> raise @@ TypeFailure ("counter_init arguments", Range.norange)
      end
    ; pc = None
    }
  ; "counter_incr",
    { pure = false
    ; func = begin function
      | env, [VInt v] ->
        begin match List.assoc_opt v !counters with
        | None -> raise @@ ValueFailure ("unknown counter " ^ Int64.to_string v, Range.norange)
        | Some c ->
          Concurrent_counter.increment c;
          env, VVoid
        end
      | _ -> raise @@ TypeFailure ("counter_incr arguments", Range.norange)
      end
    ; pc = None
    }
  ; "counter_decr",
    { pure = false
    ; func = begin function
      | env, [VInt v] ->
        begin match List.assoc_opt v !counters with
        | None -> raise @@ ValueFailure ("unknown counter " ^ Int64.to_string v, Range.norange)
        | Some c ->
          Concurrent_counter.decrement c;
          env, VVoid
        end
      | _ -> raise @@ TypeFailure ("counter_decr arguments", Range.norange)
      end
    ; pc = None
    }
  ; "counter_read",
    { pure = false
    ; func = begin function
      | env, [VInt v] ->
        begin match List.assoc_opt v !counters with
        | None -> raise @@ ValueFailure ("unknown counter " ^ Int64.to_string v, Range.norange)
        | Some c ->
          env, VInt (Concurrent_counter.read c)
        end
      | _ -> raise @@ TypeFailure ("counter_read arguments", Range.norange)
      end
    ; pc = None
    }
  ]

let lib_array : method_library =
  [ "string_of_array",
    { pure = false
    ; func = begin function
      | env, [VArr (TInt, a)] ->
        let f = function
        | VInt v -> Int64.to_int v |> Char.chr
        | _ -> raise @@ TypeFailure ("string_of_array: value is not int", Range.norange)
        in let s =
          Array.map f a |>
          Array.to_seq |>
          String.of_seq
        in env, VStr s
      | _ -> raise @@ TypeFailure ("string_of_array arguments", Range.norange)
      end
    ; pc = None
    }
  ; "array_of_string",
    { pure = false
    ; func = begin function
      | env, [VStr s] ->
        let f c = VInt (String.get s c |> Char.code |> Int64.of_int) in
        env, VArr (TInt, Array.init (String.length s) f)
      | _ -> raise @@ TypeFailure ("array_of_string arguments", Range.norange)
      end
    ; pc = None
    }
  ; "length_of_array",
    { pure = false
    ; func = begin function
      | env, [VArr (_,a)] ->
        env, VInt (Array.length a |> Int64.of_int)
      | _ -> raise @@ TypeFailure ("length_of_array arguments", Range.norange)
      end
    ; pc = None
    }
  ]

let lib_debug : method_library =
  [ "debug_stack",
    { pure = false
    ; func = begin function
      | env, [] ->
        print_string @@ AstML.string_of_callstk env.l ^ "\n";
        env, VVoid
      | _ -> raise @@ TypeFailure ("debug_display arguments", Range.norange) 
      end
    ; pc = None
    }
  ; "debug_value",
    { pure = false
    ; func = begin function
      | env, [v] ->
        print_string @@ AstML.string_of_value v ^ "\n";
        env, VVoid
      | _ -> raise @@ TypeFailure ("debug_value arguments", Range.norange)
      end
    ; pc = None
    }
  ; "busy_wait",
    { pure = true
    ; func = begin function
      | env, [VInt t] ->
        let t = ref t in
        while !t > 0L do
          t := Int64.pred !t
        done;
        env, VVoid
      | _ -> raise @@ TypeFailure ("busy_wait arguments", Range.norange)
      end
    ; pc = None
    }
  ; "random",
    { pure = true
    ; func = begin function
      | env, [VInt low; VInt high] ->
        let range = Int64.sub high low in
        let r = Random.int64 range in
        let d = Int64.add r low in
        env, VInt d
      | _ -> raise @@ TypeFailure ("random arguments", Range.norange)
      end
    ; pc = None
    }
  ]
 
let lib_hashtable : method_library =
  let member_func () = let module P = (val check_prover ()) in
    match P.name with 
    | "CVC5" -> "set.member"
    | _ -> "member"
  in let insert_func () = let module P = (val check_prover ()) in
    match P.name with 
    | "CVC5" -> "set.insert"
    | _ -> "insert"
  in
  let open Hashtables in
  [ "ht_size", 
    { pure = false
    ; func = begin function
      | env, [VHashTable (_, _, ht)] ->
        let size = 
          match ht with
          | VHTNaive t      -> Hashtable_naive.size t
          | VHTSequential t -> Hashtable_seq.size t
        in
        env, VInt (Int64.of_int size)
      | _ -> raise @@ TypeFailure ("hashtable_size arguments", Range.norange)
      end
    ; pc = Some (fun [@warning "-8"]
      (mangle, ETHashTable (tyk, _, {ht;keys;size}), []) ->
      let ht0, ht1 = mangle_servois_id_pair ht mangle in
      let keys0, keys1 = mangle_servois_id_pair keys mangle in
      let size0, size1 = mangle_servois_id_pair size mangle in
      { bindings =
        [ var_of_string @@ smt_e ht1, ht0
        ; var_of_string @@ smt_e keys1, keys0
        ; var_of_string @@ smt_e size1, size0
        ]
      ; ret_exp = size0
      ; asserts = []
      ; terms = []
      ; preds = []
      }
    )
    }
  ; "ht_mem", 
    { pure = false
    ; func = begin function
      | env, [VHashTable (tyk, _, ht); k] ->
        if not @@ ty_match env k tyk
        then raise @@ TypeFailure ("hashtable key type", Range.norange)
        else 
        let k = htdata_of_value k in
        let mem = 
          match ht with
          | VHTNaive t      -> Hashtable_naive.mem t k
          | VHTSequential t -> Hashtable_seq.mem t k
        in
        env, VBool mem
      | _ -> raise @@ TypeFailure ("hashtable_size arguments", Range.norange)
      end
    ; pc = Some (fun [@warning "-8"]
      (mangle, ETHashTable (tyk, _, {ht;keys;size}), [k]) ->
      let ht0, ht1 = mangle_servois_id_pair ht mangle in
      let keys0, keys1 = mangle_servois_id_pair keys mangle in
      let size0, size1 = mangle_servois_id_pair size mangle in
      (*let k1, k0 =
        match k with
        | ETInt i | ETBool i | ETArr (i, _) ->
          mangle_servois_id_pair i ik
        | _ -> raise @@ NotImplemented "Complex hashtables"
      in*)
      { bindings =
        [ var_of_string @@ smt_e ht1, ht0
        ; var_of_string @@ smt_e keys1, keys0
        ; var_of_string @@ smt_e size1, size0
        (*; smt_bind k1 k0*)
        ]
      ; ret_exp = 
        Smt.EFunc (member_func (), [k; keys0])
      ; asserts = []
      ; terms = []
      ; preds =
        [ member_func (), [tyk; Smt.TSet tyk] ]
      }
    )
    }
  ; "ht_put",
    { pure = false
    ; func = begin function
      | env, [VHashTable (tyk, tyv, ht); k; v] ->
        if not @@ ty_match env k tyk
        then raise @@ TypeFailure ("hashtable key type", Range.norange)
        else if not @@ ty_match env v tyv
        then raise @@ TypeFailure ("hashtable value type", Range.norange)
        else
          let k = htdata_of_value k in
          let v = htdata_of_value v in
          let res =
            match ht with
            | VHTNaive t      -> Hashtable_naive.put t k v
            | VHTSequential t -> Hashtable_seq.put t k v
          in
          env, VBool res
      | _ -> raise @@ TypeFailure ("hashtable put arguments", Range.norange)
      end
    ; pc = Some (fun [@warning "-8"]
      (mangle, ETHashTable (tyk, tyv, {ht;keys;size}), [k;v]) ->
      let ht0, ht1   = mangle_servois_id_pair ht mangle in
      let keys0, keys1 = mangle_servois_id_pair keys mangle in
      let size0, size1 = mangle_servois_id_pair size mangle in
      (*let k0, k1 =
        match k with
        | ETInt i | ETBool i | ETArr (i, _) | ETStr i ->
          mangle_servois_id_pair i ik
        | _ -> raise @@ NotImplemented "Complex hashtables"
      in let v0, v1 =
        match v with
        | ETInt i | ETBool i | ETArr (i, _) | ETStr i ->
          mangle_servois_id_pair i iv
        | _ -> raise @@ NotImplemented "Complex hashtables"
      in*)
      { bindings =
        [ var_of_string @@ smt_e ht1,
          EITE (ELop (And, [EFunc (member_func (),[k; keys0]); EBop(Eq, v, EFunc ("select", [ht0; k]))]),
            ht0,
            EFunc ("store", [ht0; k; v]))
        ; var_of_string @@ smt_e keys1,
          EITE (EFunc (member_func (), [k; keys0]),
            keys0,
            EFunc (insert_func (), [k; keys0]))
        ; var_of_string @@ smt_e size1,
          EITE (EFunc (member_func (), [k; keys0]),
            size0,
            ELop (Add, [size0; EConst(CInt 1)]))
        (*; smt_bind k1 k0
        ; smt_bind v1 v0*)
        ]
      ; ret_exp = 
        EITE (EFunc (member_func (), [k; keys0]),
          EUop (Not, (EBop (Eq, v, EFunc ("select", [ht0; k])))),
          EConst (CBool true))
      ; asserts = []
      ; terms = [
        (Smt.EConst (CInt 1)), Smt.TInt;
        pure_id size, Smt.TInt;
        ELop (Add, [pure_id size; EConst(CInt 1)]), Smt.TInt;
        pure_id @@ smt_e v, tyv;
        pure_id @@ smt_e k, tyk;
        EFunc ("select", [pure_id ht; pure_id @@ smt_e k]), tyk;
        pure_id keys, Smt.TSet tyk;
        EFunc (insert_func (), [pure_id @@ smt_e k; pure_id keys]), Smt.TSet tyk;
        pure_id ht, Smt.TArray (tyk,tyv);
        EFunc ("store", [pure_id ht; pure_id @@ smt_e k; pure_id @@ smt_e v]), Smt.TArray (tyk,tyv)
        ]
      ; preds =
        [ member_func (), [tyk; Smt.TSet tyk] ]
      }
    )
    }
  ; "ht_get",
    { pure = false
    ; func = begin function
      | env, [VHashTable (tyk, tyv, ht); k] ->
        if not @@ ty_match env k tyk
        then raise @@ TypeFailure ("hashtable key type", Range.norange)
        else let k = htdata_of_value k in
        let res =
          match ht with
          | VHTNaive t      -> Hashtable_naive.get t k
          | VHTSequential t -> Hashtable_seq.get t k
        in begin match res with
        | None -> env, VNull tyv
        | Some d -> env, value_of_htdata d
        end
      | _ -> raise @@ TypeFailure ("hashtable put arguments", Range.norange)
      end
    ; pc = Some (fun [@warning "-8"]
      (mangle, ETHashTable (tyk, tyv, {ht;keys;size}), [k]) ->
      let ht0, ht1     = mangle_servois_id_pair ht mangle in
      let keys0, keys1 = mangle_servois_id_pair keys mangle in
      let size0, size1 = mangle_servois_id_pair size mangle in
      (*let k0, k1 =
        match k with
        | ETInt i | ETBool i | ETArr (i, _) ->
          mangle_servois_id_pair i ik
        | _ -> raise @@ NotImplemented "Complex hashtables"
      in*)
      { bindings =
        [ var_of_string @@ smt_e ht1, ht0
        ; var_of_string @@ smt_e keys1, keys0
        ; var_of_string @@ smt_e size1, size0
        (*; smt_bind k1 k0*)
        ]
      ; ret_exp =
        Smt.EFunc ("select", [ht0; k])
      ; asserts = []
      ; terms = [
        pure_id size, Smt.TInt;
        pure_id @@ smt_e k, tyk;
        EFunc ("select", [pure_id ht; pure_id @@ smt_e k]), tyv;
        pure_id keys, Smt.TSet tyk;
        pure_id ht, Smt.TArray (tyk,tyv)
      ]
      ; preds = []
      }
    )
    }
  ]

let lib_io : method_library =
  [ "print", 
    { pure = false
    ; func = begin function
      | env, [VStr v] ->
        if not @@ !suppress_print then begin
          Printf.printf "%s" v;
          flush stdout
        end;
        env, VVoid
      | _ -> raise @@ TypeFailure ("print arguments", Range.norange)
      end
    ; pc = None
    }
  ; "read_stdin",
    { pure = false
    ; func = begin function
      | env, [] ->
        env, VStr (read_line ())
      | _ -> raise @@ TypeFailure ("read_stdin arguments", Range.norange)
      end
    ; pc = None
    }
  ; "open_read",
    { pure = false
    ; func = begin function
      | env, [VStr s] ->
        let chan = open_in s in
        env, VChanR (s, chan, in_channel_length chan)
      | _ -> raise @@ TypeFailure ("open_read arguments", Range.norange)
      end
    ; pc = None
    }
  ; "open_write",
    { pure = false
    ; func = begin function
      | env, [VStr s] ->
        env, VChanW (s, open_out s)
      | _ -> raise @@ TypeFailure ("open_write arguments", Range.norange)
      end
    ; pc = None
    }
  ; "close", 
    { pure = false
    ; func = begin function
      | env, [VChanR (_,chan,_)] ->
        close_in chan;
        env, VVoid
      | env, [VChanW (_,chan)] ->
        close_out chan;
        env, VVoid
      | _ -> raise @@ TypeFailure ("close arguments", Range.norange)
      end
    ; pc = None
    }
  ; "read_line", 
    { pure = false
    ; func = begin function
      | env, [VChanR (_,chan,_)] ->
        env, VStr (input_line chan)
      | _ -> raise @@ TypeFailure ("read_line arguments", Range.norange)
      end
    ; pc = None
    }
  ; "has_line",
    { pure = false
    ; func = begin function
      | env, [VChanR (_,chan,len)] ->
        env, VBool (pos_in chan < len)
      | _ -> raise @@ TypeFailure ("has_line arguments", Range.norange)
      end
    ; pc = None
    }
  ; "write",
    { pure = false
    ; func = begin function
      | env, [VChanW (_,chan); VStr s] ->
        output_string chan s;
        flush chan;
        env, VVoid
      | _ -> raise @@ TypeFailure ("write arguments", Range.norange)
      end
    ; pc = None
    }
  ]


let lib_mutex : method_library =
  [ "mutex_init",
    { pure = false
    ; func = begin function
      | env, [VInt v] ->
        if List.mem_assoc v !mutexes
        then raise @@ ValueFailure ("mutex " ^ Int64.to_string v ^ " already exists", Range.norange)
        else
          mutexes := (v, Mutex.create ()) :: !mutexes;
          env, VVoid
      | _ -> raise @@ TypeFailure ("counter_init arguments", Range.norange)
      end
    ; pc = None
    }
  ; "mutex_lock",
    { pure = false
    ; func = begin function
      | env, [VInt index] ->
        begin match List.assoc_opt index !mutexes with
        | None -> raise @@ ValueFailure ("unknown mutex " ^ Int64.to_string index, Range.norange)
        | Some m ->
          Mutex.lock m;
          env, VVoid
        end
      | _ -> raise @@ TypeFailure ("mutex_lock arguments", Range.norange)
      end
    ; pc = None
    }
  ; "mutex_unlock",
    { pure = false
    ; func = begin function
      | env, [VInt index] ->
        begin match List.assoc_opt index !mutexes with
        | None -> raise @@ ValueFailure ("unknown mutex " ^ Int64.to_string index, Range.norange)
        | Some m ->
          Mutex.unlock m;
          env, VVoid
        end
      | _ -> raise @@ TypeFailure ("mutex_unlock arguments", Range.norange)
      end
    ; pc = None
    }
  ]
 
let lib_methods =
  lib_string @
  lib_counter @
  lib_array @
  lib_debug @ 
  lib_hashtable @
  lib_io @
  lib_mutex

let pure_methods : id list =
  List.filter_map
    (fun (id,{pure;_} : lib_method binding) -> 
      if pure then Some id else None) 
  lib_methods

type lib_condition =
  (env * value list * value list) -> bool

let lib_phis : ((id * id) * lib_condition) list =
  [ (* TODO impure method commutativity conditions *)
  ]

let commute_condition (id1 : id) (id2 : id) : lib_condition option =
  if      List.mem id1 pure_methods && List.mem id2 pure_methods
  then    Some (fun _ -> true)
  else match List.assoc_opt (id1,id2) lib_phis with
  | Some f -> Some f
  | None   -> List.assoc_opt (id2,id1) lib_phis

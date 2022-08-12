type 'd htdata =
  | HTD of 'd
  | HTint of int

(*** Naively implemented concurrent hashtable; each operation is wrapped in a lock/unlock ***)
module Hashtable_naive = struct
  type 'd t = ('d htdata, 'd htdata) Hashtbl.t * Mutex.t

  let initial_size = 16

  let make () : _ t = 
    Hashtbl.create initial_size,
    Mutex.create ()

  let mem (tbl, m : _ t) k =
    Mutex.lock m;
      let res = Hashtbl.mem tbl k in
    Mutex.unlock m;
    res

  let put (tbl, m : _ t) k v = 
    Mutex.lock m;
      let replaced = Hashtbl.mem tbl k in
      Hashtbl.replace tbl k v;
    Mutex.unlock m;
    replaced

  let get (tbl, m : _ t) k = 
    Mutex.lock m;
      let res = Hashtbl.find_opt tbl k in
    Mutex.unlock m;
    res

  let size (tbl, m : _ t) = 
    Mutex.lock m;
      let res = Hashtbl.length tbl in
    Mutex.unlock m;
    res
end

(*** Hashtable with no locking or concurrent capabilities ***)
module Hashtable_seq = struct
  type 'd t = ('d htdata, 'd htdata) Hashtbl.t

  let initial_size = 16

  let make () = Hashtbl.create initial_size

  let mem = Hashtbl.mem

  let put t k v = 
    let replaced = mem t k in
    Hashtbl.replace t k v;
    replaced

  let get = Hashtbl.find_opt

  let size = Hashtbl.length

end
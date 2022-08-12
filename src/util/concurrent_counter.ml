type t = int64 ref * Mutex.t

let init () : t =
  ref 0L, Mutex.create ()

let increment ((c, m) : t) =
  Mutex.lock m;
  c := Int64.add !c 1L;
  Mutex.unlock m

let decrement ((c, m) : t) =
  Mutex.lock m;
  c := max (Int64.sub !c 1L) 0L;
  Mutex.unlock m

let read ((c, m) : t) =
  Mutex.lock m;
  let res = !c in
  Mutex.unlock m;
  res
type t = unit Domain.t

let create : (unit -> unit) -> t =
  Domain.spawn

let join : t -> unit =
  Domain.join
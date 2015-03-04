module type S = sig

  type time
  val time0: time
  val string_of_time: time -> string

  type addr
  val addr0: addr
  val string_of_addr: addr -> string
  module AddrSet : Set.S with type elt = addr
  module AddrMap : Map.S with type key = addr

  val dummy_pos: Prelude.Pos.t
  val string_of_pos: Prelude.Pos.t -> string

end

(*
module Base = struct

  type pos = Prelude.Pos.t
  type contour = X of string | P of pos
  type time = contour list
  type addr = T of time | I of int | E of int
  module AddrSet =
    Set.Make(struct type elt = addr let compare = Pervasives.compare end)
  module AddrMap =
    Map.Make(struct type key = addr let compare = Pervasives.compare end)
  
  let time0 = []
  let addr0 = T time0

  let string_of_pos = Prelude.Pos.string_of_pos
  let string_of_contour c = match c with
    | X s -> s
    | P p -> string_of_pos p
  let string_of_time t = (SH.string_of_list t string_of_contour)
  let string_of_addr a = "@" ^ (match a with
    | E i -> "λS5{"^(string_of_int i)^"}"
    | I i -> "{"^(string_of_int i)^"}"
    | T t -> string_of_time t)

end
*)

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

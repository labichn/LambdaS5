module type Lattice = sig

  include Map.OrderedType

  val subsumes: t -> t -> bool
  val join: t -> t -> t

end

module type S = sig
  type key
  type value
  type t
  val empty: t
  val is_empty: t -> bool
  val join: key -> value -> t -> t
  val clobber: key -> value -> t -> t
  val choose: t -> value
  val exists: (key -> value -> bool) -> t -> bool
  val find: key -> t -> value
  val fold: (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val mem: key -> t -> bool
end

module Make (Key : Lattice) (Value : Lattice) : S with type key = Key.t and type value = Value.t

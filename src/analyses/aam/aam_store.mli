module type S = sig

  type t
  type addr

  val empty: t

  type objekt
  type value
  type hand
  type kont
  type attrsv
  type propv

  type objekts
  type values
  type hands
  type konts
  type attrsvs
  type propvs

  module AddrSet : Set.S with type elt = addr

  val get_objs: addr -> t -> objekts
  val get_obj_addrs: t -> AddrSet.t
  val get_vals: addr -> t -> values
  val get_hands: addr -> t -> hands
  val get_konts: addr -> t -> konts
  val get_attrsvs: addr -> t -> attrsvs
  val get_propvs: addr -> t -> propvs

  val join_obj: addr -> objekt -> t -> t
  val join_val: addr -> value -> t -> t
  val join_hand: addr -> hand -> t -> t
  val join_kont: addr -> kont -> t -> t
  val join_attrsv: addr -> attrsv -> t -> t
  val join_propv: addr -> propv -> t -> t

  val set_obj: addr -> objekt -> t -> t
  val set_val: addr -> value -> t -> t
  val set_hand: addr -> hand -> t -> t
  val set_kont: addr -> kont -> t -> t
  val set_attrsv: addr -> attrsv -> t -> t
  val set_propv: addr -> propv -> t -> t

  val subsumes: t -> t -> bool
  val string_of: t -> string
  val to_top: t -> t

end

module MakeT
  (Conf : Aam_conf.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Value : Aam_lattices.S) : sig
    module type T =
      S with type addr = Conf.addr
      and module AddrSet = Conf.AddrSet
      and type objekt = Object.t
      and type attrsv = Object.attrsv
      and type propv = Object.propv
      and type value = Value.t
      and type hand = Hand.t
      and type kont = Kont.t
      and type objekts = Object.OSet.t
      and type attrsvs = Object.ASet.t
      and type propvs = Object.PSet.t
      and type values = Value.VSet.t
      and type hands = Hand.HSet.t
      and type konts = Kont.KSet.t
end

module Make
  (Conf : Aam_conf.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Value : Aam_lattices.S)
  : MakeT(Conf)(Hand)(Kont)(Object)(Value).T

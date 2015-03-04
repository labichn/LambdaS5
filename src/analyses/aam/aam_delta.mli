module type S = sig
  type store
  type value
  val op1: store -> string -> value -> value
  val op2: store -> string -> value -> value -> value
end

module MakeT
  (Conf : Aam_conf.S)
  (Env : Aam_env.S)
  (Err : Aam_error.S
   with type addr = Conf.addr)
  (Value : Aam_lattices.S
   with type addr = Conf.addr
   and type env = Conf.addr Env.t)
  (Object : Aam_object.S
   with type value = Value.t)
  (Store : Aam_store.S
   with type addr = Conf.addr
   and type objekt = Object.t
   and type value = Value.t
   and type attrsv = Object.attrsv
   and type propv = Object.propv
   and type objekts = Object.OSet.t
   and type values = Value.VSet.t
   and type attrsvs = Object.ASet.t
   and type propvs = Object.PSet.t
   and module AddrSet = Conf.AddrSet) : sig
    module type T = S with type store = Store.t and type value = Value.t
end

module Make
  (C : Aam_conf.S)
  (E : Aam_env.S)
  (Err : Aam_error.S
   with type addr = C.addr)
  (V : Aam_lattices.S
   with type addr = C.addr
   and type env = C.addr E.t)
  (O : Aam_object.S
   with type value = V.t)
  (S : Aam_store.S
   with type addr = C.addr
   and type objekt = O.t
   and type value = V.t
   and type attrsv = O.attrsv
   and type propv = O.propv
   and type objekts = O.OSet.t
   and type values = V.VSet.t
   and type attrsvs = O.ASet.t
   and type propvs = O.PSet.t
   and module AddrSet = C.AddrSet) : MakeT(C)(E)(Err)(V)(O)(S).T

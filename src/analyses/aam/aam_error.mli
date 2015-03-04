module type S = sig
  type addr
  type pos = Prelude.Pos.t
  exception Throw of addr
  exception PrimErr of string
  exception Break of string * addr
  val string_of: exn -> string
  val interp_error: pos -> string -> exn
  val err: string -> 'a
end

module MakeT(Conf : Aam_conf.S) : sig
  module type T = S with type addr = Conf.addr and type pos = Prelude.Pos.t
end

module Make(Conf : Aam_conf.S) : MakeT(Conf).T

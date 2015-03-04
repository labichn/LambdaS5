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

module MakeT(Conf : Aam_conf.S) = struct
  module type T = S with type addr = Conf.addr
end

module Make(Conf : Aam_conf.S) = struct

  type addr = Conf.addr
  type pos = Prelude.Pos.t

  exception Throw of addr
  exception PrimErr of string
  exception Break of string * addr

  let string_of ex = match ex with
    | Throw _ -> "throw"
    | PrimErr s -> "primerr("^s^")"
    | Break (l, _) -> "break("^l^")"
    | _ -> "some other error"

  let interp_error pos message =
    raise (PrimErr ("[interp] (" ^ Conf.string_of_pos pos ^ ") " ^ message))

  let err message = 
    Prelude.eprintf "%s\n" message;
    failwith "Runtime error"

end

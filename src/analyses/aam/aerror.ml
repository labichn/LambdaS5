type exp = Ljs_syntax.exp
type addr = Ashared.addr
type value = addr
type env = addr Prelude.IdMap.t
type store = Astore.store

exception Throw of value
exception PrimErr of string
exception Break of string * value

let interp_error pos message =
  raise (PrimErr ("[interp] (" ^ Prelude.Pos.string_of_pos pos ^ ") " ^ message))
let arity_mismatch_err p xs args =
  interp_error p "Arity mismatch"
let err message = 
    Prelude.eprintf "%s\n" message;
    failwith "Runtime error"

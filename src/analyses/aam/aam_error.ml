type exp = Ljs_syntax.exp
type addr = Aam_shared.addr
type value = addr
type env = Aam_env.env
type store = Aam_store.store

exception Throw of value
exception PrimErr of string
exception Break of string * value

let string_of ex = match ex with
  | Throw _ -> "throw"
  | PrimErr s -> "primerr("^s^")"
  | Break (l, _) -> "break("^l^")"

let interp_error pos message =
  raise (PrimErr ("[interp] (" ^ Prelude.Pos.string_of_pos pos ^ ") " ^ message))
let arity_mismatch_err p xs args =
  interp_error p "Arity mismatch"
let err message = 
    Prelude.eprintf "%s\n" message;
    failwith "Runtime error"

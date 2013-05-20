module IS = IntStore
module V = Avalues
module S = Shared

type exp = Ljs_syntax.exp
type avalue = V.avalue
type store = IS.store
type env = Avalues.env

exception Break of exp list * string * avalue
exception Throw of exp list * avalue
exception PrimErr of exp list * avalue
exception Snapshot of avalue * env * store
  
let interp_error pos message =
  raise (PrimErr ([], V.String ("[interp] (" ^ S.Pos.string_of_pos pos ^ ") " ^ message)))
let arity_mismatch_err p xs args =
  interp_error p
    ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^
     " arguments and expected " ^ string_of_int (List.length xs) ^
     ". Arg names were: " ^ (List.fold_right (^) (List.map (fun s -> " " ^ s ^ " ") xs) "") ^
     ". Values were: " ^
     (List.fold_right (^) (List.map (fun v -> " " ^ V.pretty_value v ^ " ") args) ""))
let err message = 
    S.eprintf "%s\n" message;
    failwith "Runtime error"

open Prelude
open Ljs_syntax
open Cvalue

type value = Cvalue.value
type addr = Cshared.addr
type env = addr IdMap.t
type store = Cstore.t
  
exception Throw of exp list * value
exception PrimErr of exp list * value
exception Break of exp list * string * value
exception Snapshot of value * env * store

let interp_error pos message =
  raise (PrimErr ([], String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))
let arity_mismatch_err p xs args =
  interp_error p
    ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^
     " arguments and expected " ^ string_of_int (List.length xs) ^
     ". Arg names were: " ^ (List.fold_right (^) (List.map (fun s -> " " ^ s ^ " ") xs) "") ^
     ". Values were: " ^
     (List.fold_right (^) (List.map (fun v -> " " ^ string_of_value v ^ " ") args) ""))
let err message = 
    eprintf "%s\n" message;
    failwith "Runtime error"

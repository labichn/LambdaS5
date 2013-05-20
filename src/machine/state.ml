module SYN = Ljs_syntax
module V = Avalues
module S = Shared

type loc = S.loc

type state =
| Ev of SYN.exp * V.env * loc * loc (* K.handl * K.kont *)
| EvA of SYN.attrs * V.env * loc * loc (* K.handl * K.kont *)
| EvP of (string * SYN.prop) * V.env * loc * loc (* K.handl * K.kont *)
| Co of loc (* K.kont *) * V.avalue * loc (* K.handl *)
| CoA of loc (* K.kont *) * V.attrsv * loc (* K.handl *)
| CoP of loc (* K.kont *) * (string * V.propv) * loc (* K.handl *)
| Ap of S.Pos.t * V.avalue * V.avalue list * loc * loc (* K.handl * K.kont *)
| Exn of exn * V.env * loc (* K.handl *)
| Ans of V.avalue

let hloc_of_state state = match state with
  | Ev (_, _, h, _) -> h
  | EvA (_, _, h, _) -> h
  | EvP (_, _, h, _) -> h
  | Co (_, _, h) -> h
  | CoA (_, _, h) -> h
  | CoP (_, _, h) -> h
  | Ap (_, _, _, h, _) -> h
  | Exn (_, _, h) -> h
  | Ans _ -> failwith "no hloc in ans, something's wrong!"
let kloc_of_state state = match state with
  | Ev (_, _, _, k) -> k
  | EvA (_, _, _, k) -> k
  | EvP (_, _, _, k) -> k
  | Ap (_, _, _, _, k) -> k
  | Co (k, _, _) -> k
  | CoA (k, _, _) -> k
  | CoP (k, _, _) -> k
  | Exn _ -> failwith "no kloc in exn, something's wrong!"
  | Ans _ -> failwith "no kloc in ans, something's wrong!"

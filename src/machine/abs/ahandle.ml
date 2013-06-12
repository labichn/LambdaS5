
type exp = Ljs_syntax.exp
type addr = Ashared.addr
type time = Ashared.time
type env = addr Prelude.IdMap.t
type pos = Prelude.Pos.t
type hand =
| MtH of pos * time
| Cat of pos * time * exp * env * (*k*)addr * (*h*)addr
| Lab of pos * time * Prelude.id * env * (*k*)addr * (*h*)addr
| Fin of pos * time * exp * env * (*k*)addr * (*h*)addr

let zero t0 = MtH (Prelude.Pos.dummy, t0)

let hand_of han = match han with
  | Cat (_, _, _, _, _, h) -> h
  | Lab (_, _, _, _, _, h) -> h
  | Fin (_, _, _, _, _, h) -> h
  | MtH _ -> failwith "no hand in mth"

let time_of han = match han with
  | Cat (_, t, _, _, _, _) -> t
  | Lab (_, t, _, _, _, _) -> t
  | Fin (_, t, _, _, _, _) -> t
  | MtH (_, t) -> t

let pos_of han = match han with
  | Cat (p, _, _, _, _, _) -> p
  | Lab (p, _, _, _, _, _) -> p
  | Fin (p, _, _, _, _, _) -> p
  | MtH (p, _) -> p

let string_of han = "I'm lazy"

open Prelude
open Ljs_syntax
open Cshared

type addr = Cshared.addr
type time = Cshared.time
type env = addr IdMap.t
type t =
| MtH of Pos.t * time
| Cat of Pos.t * time * exp * env * (*k*)addr * (*h*)addr
| Lab of Pos.t * time * id * env * (*k*)addr * (*h*)addr
| Fin of Pos.t * time * exp * env * (*k*)addr * (*h*)addr

let zero = MtH (Pos.dummy, Cshared.addr0)

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

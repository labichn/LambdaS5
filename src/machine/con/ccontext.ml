module P = Prelude
module SH = Cshared
module S = Cstate
module V = Cvalue
module ST = Cstore
module K = Ckont

type addr = SH.addr
type time = SH.time
type env = addr P.IdMap.t
type state = S.t

let zero : time = 0
let tick state store okont ohand = match state, okont with
  | S.Ap (_, V.Clos (_, xs, _), _, _, _, t), _ -> t+(List.length xs)+1
  | S.Co (_, V.Obj addr, _, _), Some (K.Eval2 (_, t, _, _, _)) ->
    let _, props = ST.get_obj addr store in t+(P.IdMap.cardinal props)+1
  | _ -> (S.time_of state)+1
let alloc state store okont ohand = S.time_of state
let alloc' state store okont ohand = match state, okont with
  | S.Ap (_, V.Clos (_, xs, _), _, _, _, t), _ ->
    let l, _ = List.fold_right (fun _ (l, n) -> let m = n+1 in m::l, m) xs ([], t) in l
  | S.Co (_, V.Obj addr, _, _), Some (K.Eval2 (_, t, _, _, _)) ->
    let _, props = ST.get_obj addr store in
    let l, _ = P.IdMap.fold (fun _ _ (l, n) -> let m = n+1 in m::l, m) props ([], t) in l
  | _ -> failwith "nope"
let alloc_kont state store okont ohand = S.time_of state
let alloc_hand state store okont ohand = S.time_of state

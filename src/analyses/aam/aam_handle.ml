type exp = Ljs_syntax.exp
type addr = Aam_shared.addr
type time = Aam_shared.time
type env = Aam_env.env
type pos = Prelude.Pos.t
type hand =
| Mt
| Cat of pos * time * exp * env * (*k*)addr * (*h*)addr
| Lab of pos * time * Prelude.id * env * (*k*)addr * (*h*)addr
| Fin of pos * time * exp * env * (*k*)addr * (*h*)addr

let empty h = match h with
  | Mt -> Mt, None
  | Cat (p, t, e, env, k, h) -> Cat (p, t, e, Aam_env.empty, k, h), Some env
  | Lab (p, t, x, env, k, h) -> Lab (p, t, x, Aam_env.empty, k, h), Some env
  | Fin (p, t, e, env, k, h) -> Fin (p, t, e, Aam_env.empty, k, h), Some env

let subsumes h h' = match h, h' with
  | Mt, Mt -> true
  | Cat (p, t, e, en, k, h), Cat (p', t', e', en', k', h') ->
    p = p' && t = t' && compare e e' = 0 && Aam_env.subsumes en en' && k = k' &&
      h = h'
  | Lab (p, t, x, en, k, h), Lab (p', t', x', en', k', h') ->
    p = p' && t = t' && x = x' && Aam_env.subsumes en en' && k = k' && h = h'
  | Fin (p, t, e, en, k, h), Fin (p', t', e', en', k', h') ->
    p = p' && t = t' && compare e e' = 0 && Aam_env.subsumes en en' && k = k' &&
      h = h'
  | _, _ -> false

let kont_of han = match han with
  | Cat (_, _, _, _, k, _) -> k
  | Lab (_, _, _, _, k, _) -> k
  | Fin (_, _, _, _, k, _) -> k
  | Mt -> failwith "no kont in mth"

let hand_of han = match han with
  | Cat (_, _, _, _, _, h) -> h
  | Lab (_, _, _, _, _, h) -> h
  | Fin (_, _, _, _, _, h) -> h
  | Mt -> failwith "no hand in mth"

let time_of han = match han with
  | Cat (_, t, _, _, _, _) -> t
  | Lab (_, t, _, _, _, _) -> t
  | Fin (_, t, _, _, _, _) -> t
  | Mt -> failwith "no time in mth"

let pos_of han = match han with
  | Cat (p, _, _, _, _, _) -> p
  | Lab (p, _, _, _, _, _) -> p
  | Fin (p, _, _, _, _, _) -> p
  | Mt -> failwith "no pos in mth"

let string_of han = match han with
  | Cat _ -> "cat"
  | Lab _ -> "lab"
  | Fin _ -> "fin"
  | Mt -> "mt"

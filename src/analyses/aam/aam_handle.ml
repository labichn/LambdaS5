module type S = sig
  type addr
  type time
  type pos = Prelude.Pos.t
  type env
  type t =
  | Mt
  | Cat of pos * time * Ljs_syntax.exp * env * (*k*)addr * (*h*)addr
  | Lab of pos * time * string * env * (*k*)addr * (*h*)addr
  | Fin of pos * time * Ljs_syntax.exp * env * (*k*)addr * (*h*)addr
  module HSet : Set.S with type elt = t
  val hand_of: t -> addr
  val kont_of: t -> addr
  val subsumes: t -> t -> bool
  val string_of: t -> string
  val compare: t -> t -> int
end

module MakeT(C : Aam_conf.S)(E : Aam_env.S) = struct
  module type T = S with type addr = C.addr
                    and type time = C.time
                    and type env = C.addr E.t
end

module Make(Conf : Aam_conf.S)(Env : Aam_env.S) = struct

  type env = Conf.addr Env.t
  type addr = Conf.addr
  type pos = Prelude.Pos.t
  type time = Conf.time

  type t =
  | Mt
  | Cat of pos * time * Ljs_syntax.exp * env * (*k*)addr * (*h*)addr
  | Lab of pos * time * string * env * (*k*)addr * (*h*)addr
  | Fin of pos * time * Ljs_syntax.exp * env * (*k*)addr * (*h*)addr
  module HSet =
    Set.Make(struct type tmp = t type t = tmp let compare = Pervasives.compare end)

  let subsumes h h' = match h, h' with
    | Mt, Mt -> true
    | Cat (p, t, e, en, k, h), Cat (p', t', e', en', k', h') ->
      p = p' && t = t' && compare e e' = 0 && Env.subsumes en en' && k = k' &&
    h = h'
    | Lab (p, t, x, en, k, h), Lab (p', t', x', en', k', h') ->
      p = p' && t = t' && x = x' && Env.subsumes en en' && k = k' && h = h'
    | Fin (p, t, e, en, k, h), Fin (p', t', e', en', k', h') ->
      p = p' && t = t' && compare e e' = 0 && Env.subsumes en en' && k = k' &&
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

  let string_of han = match han with
    | Cat _ -> "cat"
    | Lab _ -> "lab"
    | Fin _ -> "fin"
    | Mt -> "mt"

  let compare = Pervasives.compare

(*  let time_of han = match han with
    | Cat (_, t, _, _, _, _) -> t
    | Lab (_, t, _, _, _, _) -> t
    | Fin (_, t, _, _, _, _) -> t
    | Mt -> failwith "no time in mth"

  let pos_of han = match han with
    | Cat (p, _, _, _, _, _) -> p
    | Lab (p, _, _, _, _, _) -> p
    | Fin (p, _, _, _, _, _) -> p
    | Mt -> failwith "no pos in mth"

  let empty h = match h with
    | Mt -> Mt, None
    | Cat (p, t, e, env, k, h) -> Cat (p, t, e, Env.empty, k, h), Some env
    | Lab (p, t, x, env, k, h) -> Lab (p, t, x, Env.empty, k, h), Some env
    | Fin (p, t, e, env, k, h) -> Fin (p, t, e, Env.empty, k, h), Some env *)

end

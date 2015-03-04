module type S = sig
  type attrsv type env
  type hand  type kont   type propv
  type store type time   type value
  type t = 
    | Ev of Ljs_syntax.exp * env * store * hand * kont * time
    | EvA of Prelude.Pos.t * Ljs_syntax.attrs * env * store * hand * kont * time
    | EvP of Prelude.Pos.t * (string * Ljs_syntax.prop) * env * store * hand * kont * time
    | Co of kont * Prelude.Pos.t * value * store * hand * time
    | CoA of kont * Prelude.Pos.t * attrsv * store * hand * time
    | CoP of kont * Prelude.Pos.t * (string * propv) * store * hand * time
    | Ap of Prelude.Pos.t * value * value list * store * hand * kont * time
    | Ex of exn * env * store * hand * time
    | NAP of exn
    | Ans of value * store * time
  module CSet : Set.S with type elt = t
  val ev: store -> Ljs_syntax.exp -> env -> hand -> kont -> time -> t
  val eva: store -> Prelude.Pos.t -> Ljs_syntax.attrs -> env -> hand -> kont -> time -> t
  val evp: store -> Prelude.Pos.t -> string * Ljs_syntax.prop -> env -> hand -> kont -> time -> t
  val co: store -> Prelude.Pos.t -> value -> hand -> kont -> time -> t
  val coa: store -> Prelude.Pos.t -> attrsv -> hand -> kont -> time -> t
  val cop: store -> Prelude.Pos.t -> string -> propv -> hand -> kont -> time -> t
  val ap: store -> Prelude.Pos.t -> value -> value list -> hand -> kont -> time -> t
  val ex: store -> exn -> env -> hand -> time -> t
  val ans: store -> value -> time -> t
  val hand_of: t -> hand
  val kont_of: t -> kont
  val store_of: t -> store
  val time_of: t -> time
  val with_store: store -> t -> t
  val subsumes: t -> t -> bool
  val compare: t -> t -> int
  val string_of: t -> string
end

module MakeT(Conf : Aam_conf.S)
  (Env : Aam_env.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Store : Aam_store.S)
  (Value : Aam_lattices.S) = struct
    module type T = S with type attrsv = Object.attrsv
                      and type env = Conf.addr Env.t
                      and type hand = Hand.t
                      and type kont = Kont.t
                      and type propv = Object.propv
                      and type store = Store.t
                      and type time = Conf.time
                      and type value = Value.t
end
  
module Make(Conf : Aam_conf.S)
  (Env : Aam_env.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Store : Aam_store.S)
  (Value : Aam_lattices.S) = struct
    type time = Conf.time
    type env = Conf.addr Env.t
    type hand = Hand.t
    type kont = Kont.t
    type attrsv = Object.attrsv
    type propv = Object.propv
    type store = Store.t
    type value = Value.t
    type t = 
    | Ev of Ljs_syntax.exp * env * store * hand * kont * time
    | EvA of Prelude.Pos.t * Ljs_syntax.attrs * env * store * hand * kont * time
    | EvP of Prelude.Pos.t * (string * Ljs_syntax.prop) * env * store * hand * kont * time
    | Co of kont * Prelude.Pos.t * value * store * hand * time
    | CoA of kont * Prelude.Pos.t * attrsv * store * hand * time
    | CoP of kont * Prelude.Pos.t * (string * propv) * store * hand * time
    | Ap of Prelude.Pos.t * value * value list * store * hand * kont * time
    | Ex of exn * env * store * hand * time
    | NAP of exn
    (* ^ not actually possible exception that is precluded by desugaring, but
       possible due to imprecision *)
    | Ans of value * store * time
    module CSet = Set.Make(struct type t' = t type t = t' let compare = Pervasives.compare end)

    let ev sto exp env han kon tim =
      Ev (exp, env, sto, han, kon, tim)
    let eva sto pos att env han kon tim =
      EvA (pos, att, env, sto, han, kon, tim)
    let evp sto pos pair env han kon tim =
      EvP (pos, pair, env, sto, han, kon, tim)
    let co sto p va han kon tim =
      Co (kon, p, va, sto, han, tim)
    let coa sto p va han kon tim =
      CoA (kon, p, va, sto, han, tim)
    let cop sto p name pv han kon tim =
      CoP (kon, p, (name, pv), sto, han, tim)
    let ap sto pos va vals han kon tim =
      Ap (pos, va, vals, sto, han, kon, tim)
    let ex sto e env han tim =
      Ex (e, env, sto, han, tim)
    let ans sto va tim =
      Ans (va, sto, tim)

    let hand_of sta = match sta with
      | Ev (_, _, _, h, _, _)
      | EvA (_, _, _, _, h, _, _)
      | EvP (_, _, _, _, h, _, _)
      | Co (_, _, _, _, h, _)
      | CoA (_, _, _, _, h, _)
      | CoP (_, _, _, _, h, _)
      | Ap (_, _, _, _, h, _, _)
      | Ex (_, _, _, h, _) -> h
      | Ans _ -> failwith "no hand in ans!"

    let kont_of sta = match sta with
      | Ev (_, _, _, _, k, _)
      | EvA (_, _, _, _, _, k, _)
      | EvP (_, _, _, _, _, k, _)
      | Ap (_, _, _, _, _, k, _)
      | Co (k, _, _, _, _, _)
      | CoA (k, _, _, _, _, _)
      | CoP (k, _, _, _, _, _) -> k
      | Ex _ -> failwith "no kont in exn"
      | Ans _ -> failwith "no kont in ans"

    let store_of sta = match sta with
      | Ev (_, _, sto, _, _, _)
      | EvA (_, _, _, sto, _, _, _)
      | EvP (_, _, _, sto, _, _, _)
      | CoA (_, _, _, sto, _, _)
      | CoP (_, _, _, sto, _, _)
      | Co (_, _, _, sto, _, _)
      | Ap (_, _, _, sto, _, _, _)
      | Ex (_, _, sto, _, _)
      | Ans (_, sto, _) -> sto

    let time_of sta = match sta with
      | Ev (_, _, _, _, _, t)
      | EvA (_, _, _, _, _, _, t)
      | EvP (_, _, _, _, _, _, t)
      | CoA (_, _, _, _, _, t)
      | CoP (_, _, _, _, _, t)
      | Co (_, _, _, _, _, t)
      | Ap (_, _, _, _, _, _, t)
      | Ex (_, _, _, _, t)
      | Ans (_, _, t) -> t

    let with_store sto sta = match sta with
      | Ev (exp, env, _, han, kon, tim) ->
        Ev (exp, env, sto, han, kon, tim)
      | EvA (pos, att, env, _, han, kon, tim) ->
        EvA (pos, att, env, sto, han, kon, tim)
      | EvP (pos, pair, env, _, han, kon, tim) ->
        EvP (pos, pair, env, sto, han, kon, tim)
      | Co (kon, p, va, _, han, tim) ->
        Co (kon, p, va, sto, han, tim)
      | CoA (kon, p, va, _, han, tim) ->
        CoA (kon, p, va, sto, han, tim)
      | CoP (kon, p, pair, _, han, tim) ->
        CoP (kon, p, pair, sto, han, tim)
      | Ap (pos, va, vals, _, han, kon, tim) ->
        Ap (pos, va, vals, sto, han, kon, tim)
      | Ex (e, env, _, han, tim) ->
        Ex (e, env, sto, han, tim)
      | Ans (va, _, tim) ->
        Ans (va, sto, tim)
      | NAP _ -> sta
        
    let subsumes c1 c2 = match c1, c2 with
      | Ev (e, en, s, h, k, t), Ev (e', en', s', h', k', t') ->
        compare e e' = 0 && (Env.subsumes en en') && (Store.subsumes s s') &&
      Hand.subsumes h h' && Kont.subsumes k k' && t = t'              
      | EvA (p, a, en, s, h, k, t), EvA (p', a', en', s', h', k', t') ->
        p = p' && compare a a' = 0 && (Env.subsumes en en') && (Store.subsumes s s') &&
      Hand.subsumes h h' && Kont.subsumes k k' && t = t'
      | EvP (p, (n, pr), en, s, h, k, t), EvP (p', (n', pr'), en', s', h', k', t') ->
        p = p' && n = n' && compare pr pr' = 0 && (Env.subsumes en en') &&
      (Store.subsumes s s') && Hand.subsumes h h' && Kont.subsumes k k' && t = t'
      | Co (k, p, v, s, h, t), Co (k', p', v', s', h', t') ->
        Kont.subsumes k k' && p = p' && Value.subsumes v v' &&
      Store.subsumes s s' && Hand.subsumes h h' && t = t'
      | CoA (k, p, at, s, h, t), CoA (k', p', at', s', h', t') ->
        Kont.subsumes k k' && p = p' && Object.attrs_subsumes at at' &&
      Store.subsumes s s' && Hand.subsumes h h' && t = t'
      | CoP (k, p, (n, pv), s, h, t), CoP (k', p', (n', pv'), s', h', t') ->
        Kont.subsumes k k' && p = p' && n = n' &&
      Object.prop_subsumes pv pv' && Store.subsumes s s' &&
      Hand.subsumes h h' && t = t'
      | Ap (p, v, vs, s, h, k, t), Ap (p', v', vs', s', h', k', t') ->
        p = p' && Value.subsumes v v' &&
      List.fold_left2 (fun a v' v -> a && Value.subsumes v v') true vs vs' &&
      Store.subsumes s s' && Hand.subsumes h h' && Kont.subsumes k k' &&
      t = t'
      | Ex (e, en, s, h, t), Ex (e', en', s', h', t') ->
        Store.subsumes s s' && e = e' && Env.subsumes en en' &&
      Hand.subsumes h h' && t = t'
      | Ans (v, s, t), Ans (v', s', t') ->
        Value.subsumes v v' && Store.subsumes s s' && t = t'
      | NAP ex, NAP ex' -> ex = ex'
      | _, _ -> false

    let compare = Pervasives.compare

    let string_of c = match c with
      | Ev _ -> "ev"
      | EvA _ -> "eva"
      | EvP _ -> "evp"
      | CoA _ -> "coa"
      | CoP _ -> "cop"
      | Co _ -> "co"
      | Ap _ -> "ap"
      | Ex _ -> "ex"
      | Ans _ -> "ans"
      | NAP _ -> "nap"
        
  end

(*
let string_of_xs xs = List.fold_right (fun x a -> x^" "^a) xs ""

let rec string_of_exp exp = match exp with
  | Ljs_syntax.Null _ -> "null"
  | Ljs_syntax.Undefined _ -> "undef"
  | Ljs_syntax.String (_, v) -> "string("^v^")"
  | Ljs_syntax.Num (_, v) -> "num("^(string_of_float v)^")"
  | Ljs_syntax.True _ -> "true"
  | Ljs_syntax.False _ -> "false"
  | Ljs_syntax.Id (_, x) -> "id: "^x^" "
  | Ljs_syntax.Object _ -> "object"
  | Ljs_syntax.GetAttr _ -> "getattr"
  | Ljs_syntax.SetAttr _ -> "setattr"
  | Ljs_syntax.GetObjAttr _ -> "getobjattr"
  | Ljs_syntax.SetObjAttr _ -> "setobjattr"
  | Ljs_syntax.GetField _ -> "getfield"
  | Ljs_syntax.SetField _ -> "setfield"
  | Ljs_syntax.DeleteField _ -> "deletefield"
  | Ljs_syntax.OwnFieldNames _ -> "ownfieldnames"
  | Ljs_syntax.SetBang _ -> "setbang"
  | Ljs_syntax.Op1 _ -> "op1"
  | Ljs_syntax.Op2 _ -> "op2"
  | Ljs_syntax.If _ -> "if"
  | Ljs_syntax.App _ -> "app"
  | Ljs_syntax.Seq _ -> "seq"
  | Ljs_syntax.Let _ -> "let"
  | Ljs_syntax.Rec _ -> "rec"
  | Ljs_syntax.Label _ -> "label"
  | Ljs_syntax.Break _ -> "break"
  | Ljs_syntax.TryCatch _ -> "catch"
  | Ljs_syntax.TryFinally _ -> "fin"
  | Ljs_syntax.Throw _ -> "throw"
  | Ljs_syntax.Lambda _ -> "lam"
  | Ljs_syntax.Eval _ -> "eval"
  | Ljs_syntax.Hint _ -> "hint"
    *)

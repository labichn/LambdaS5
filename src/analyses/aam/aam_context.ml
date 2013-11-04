open Aam_lattices
open Aam_shared
module SYN = Ljs_syntax
module H = Aam_handle
module K = Aam_kont
module E = Aam_error
module EN = Aam_env
module O = Aam_object
module S = Aam_store

type addr = Aam_shared.addr
type time = Aam_shared.time

type exp = Ljs_syntax.exp
type syn_attrs = Ljs_syntax.attrs
type syn_prop = Ljs_syntax.prop

type pos = Prelude.Pos.t
type env = addr Prelude.IdMap.t

type store = Aam_store.store
type hand = H.hand
type kont = K.kont
type value = Aam_lattices.AValue.t
type attrs = O.attrs
type prop = O.prop

let string_of_value = Aam_lattices.AValue.string_of

type context =
| Ev of exp * env * store * hand * kont * time
| EvA of pos * syn_attrs * env * store * hand * kont * time
| EvP of pos * (string * syn_prop) * env * store * hand * kont * time
| Co of kont * pos * value * store * hand * time
| CoA of kont * pos * attrs * store * hand * time
| CoP of kont * pos * (string * prop) * store * hand * time
| Ap of pos * value * value list * store * hand * kont * time
| Ex of exn * env * store * hand * time
| NAP of exn
(* ^ not actually possible exception that is precluded by desugaring, but
   possible due to imprecision *)
| Ans of value * store * time

module Context = struct type t = context let compare = Pervasives.compare end
module CSet = Set.Make(Context)

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

(*
let empty c = match c with
  | Ev (e, _, _, _, _, t) ->
    Ev (e, Env.empty, Astore.empty, Ahandle.Mt, K..Mt, t)
  | EvA (p, at, _, _, _, _, t) ->
    EvA (p, at, Env.empty, Astore.empty, Ahandle.Mt, K..Mt, t)
  | EvP (p, np, _, _, _, _, t) ->
    EvP (p, np, Env.empty, Astore.empty, Ahandle.Mt, K..Mt, t)
  | Co (_, p, _, _, _, t) ->
    Co (K..Mt, p, `Bot, Astore.empty, Ahandle.Mt, t)
  | CoA (_, p, _, _, _, t) ->
    CoA (K..Mt, p, `Bot, Astore.empty, Ahandle.Mt, t)
  | CoP (_, p, (name, _), _, _, t) ->
    CoP (K..Mt, p, (name, Aobject.TopProp), Astore.empty, Ahandle.Mt, t)
  | Ap (p, _, _, _, _, _, t) ->
    Ap (p, `Bot, [], Astore.empty, Ahandle.Mt, K..Mt, t)
  | Ex (e, _, _, _, t) ->
    Ex (e, Env.empty, Astore.empty, Ahandle.Mt, t)
  | Ans (_, _, t) -> Ans (`Bot, Astore.empty, t) *)

let tock sta tim = match sta with
  | Ev (exp, env, sto, han, kon, _) ->
    Ev (exp, env, sto, han, kon, tim)
  | EvA (pos, att, env, sto, han, kon, _) ->
    EvA (pos, att, env, sto, han, kon, tim)
  | EvP (pos, pair, env, sto, han, kon, _) ->
    EvP (pos, pair, env, sto, han, kon, tim)
  | Co (kon, p, va, sto, han, _) ->
    Co (kon, p, va, sto, han, tim)
  | CoA (kon, p, va, sto, han, _) ->
    CoA (kon, p, va, sto, han, tim)
  | CoP (kon, p, pair, sto, han, _) ->
    CoP (kon, p, pair, sto, han, tim)
  | Ap (pos, va, vals, sto, han, kon, _) ->
    Ap (pos, va, vals, sto, han, kon, tim)
  | Ex (e, env, sto, han, _) ->
    Ex (e, env, sto, han, tim)
  | Ans (va, sto, _) ->
    Ans (va, sto, tim)

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

let string_of_xs xs = List.fold_right (fun x a -> x^" "^a) xs ""

let rec string_of_exp exp = match exp with
  | SYN.Null _ -> "null"
  | SYN.Undefined _ -> "undef"
  | SYN.String (_, v) -> "string("^v^")"
  | SYN.Num (_, v) -> "num("^(string_of_float v)^")"
  | SYN.True _ -> "true"
  | SYN.False _ -> "false"
  | SYN.Id (_, x) -> "id: "^x^" "
  | SYN.Object _ -> "object"
  | SYN.GetAttr _ -> "getattr"
  | SYN.SetAttr _ -> "setattr"
  | SYN.GetObjAttr _ -> "getobjattr"
  | SYN.SetObjAttr _ -> "setobjattr"
  | SYN.GetField _ -> "getfield"
  | SYN.SetField _ -> "setfield"
  | SYN.DeleteField _ -> "deletefield"
  | SYN.OwnFieldNames _ -> "ownfieldnames"
  | SYN.SetBang _ -> "setbang"
  | SYN.Op1 _ -> "op1"
  | SYN.Op2 _ -> "op2"
  | SYN.If _ -> "if"
  | SYN.App _ -> "app"
  | SYN.Seq _ -> "seq"
  | SYN.Let _ -> "let"
  | SYN.Rec _ -> "rec"
  | SYN.Label _ -> "label"
  | SYN.Break _ -> "break"
  | SYN.TryCatch _ -> "catch"
  | SYN.TryFinally _ -> "fin"
  | SYN.Throw _ -> "throw"
  | SYN.Lambda _ -> "lam"
  | SYN.Eval _ -> "eval"
  | SYN.Hint _ -> "hint"

let string_of con = match con with
  | Ev (exp, _, _, _, k, _) ->
    "ev("^(Prelude.Pos.string_of_pos (SYN.pos_of exp))^", "^
      (string_of_exp exp)^", "^(K.string_of k)^")"
  | EvA (_, _, _, _, _, k, _) -> "eva("^(K.string_of k)^")"
  | EvP (_, _, _, _, _, k, _) -> "evp("^(K.string_of k)^")"
  | Co (k, _, v, _, _, _) -> "co("^(K.string_of k)^", "^(string_of_value v)^")"
  | CoA (k, _, _, _, _, _) -> "coa("^(K.string_of k)^")"
  | CoP (k, _, (n, v), _, _, _) ->
    "cop("^(K.string_of k)^", "^n^"="^(O.string_of_prop v)^")"
  | Ap (_, f, vlds, _, _, _, _) ->
    "ap("^(string_of_value f)^", "^
      (string_of_list vlds string_of_value)^")"
  | Ex (ex, _, _, han, _) ->
    "ex("^(E.string_of ex)^", "^(H.string_of han)^")"
  | NAP (ex) -> "NAP"
  | Ans (vld, _, _) -> "ans("^(string_of_value vld)^")"


let subsumes c1 c2 = match c1, c2 with
  | Ev (e, en, s, h, k, t), Ev (e', en', s', h', k', t') ->
    compare e e' = 0 && (EN.subsumes en en') && (S.subsumes s s') &&
      H.subsumes h h' && K.subsumes k k' && t = t'              
  | EvA (p, a, en, s, h, k, t), EvA (p', a', en', s', h', k', t') ->
    p = p' && compare a a' = 0 && (EN.subsumes en en') && (S.subsumes s s') &&
      H.subsumes h h' && K.subsumes k k' && t = t'
  | EvP (p, (n, pr), en, s, h, k, t), EvP (p', (n', pr'), en', s', h', k', t') ->
    p = p' && n = n' && compare pr pr' = 0 && (EN.subsumes en en') &&
    (S.subsumes s s') && H.subsumes h h' && K.subsumes k k' && t = t'
  | Co (k, p, v, s, h, t), Co (k', p', v', s', h', t') ->
    K.subsumes k k' && p = p' && AValue.subsumes v v' &&
      S.subsumes s s' && H.subsumes h h' && t = t'
  | CoA (k, p, at, s, h, t), CoA (k', p', at', s', h', t') ->
    K.subsumes k k' && p = p' && O.attrs_subsumes at at' &&
      S.subsumes s s' && H.subsumes h h' && t = t'
  | CoP (k, p, (n, pv), s, h, t), CoP (k', p', (n', pv'), s', h', t') ->
    K.subsumes k k' && p = p' && n = n' &&
      O.prop_subsumes pv pv' && S.subsumes s s' &&
      H.subsumes h h' && t = t'
  | Ap (p, v, vs, s, h, k, t), Ap (p', v', vs', s', h', k', t') ->
    p = p' && AValue.subsumes v v' &&
      List.fold_left2 (fun a v' v -> a && AValue.subsumes v v') true vs vs' &&
      S.subsumes s s' && H.subsumes h h' && K.subsumes k k' &&
      t = t'
  | Ex (e, en, s, h, t), Ex (e', en', s', h', t') ->
    S.subsumes s s' && e = e' && EN.subsumes en en' &&
      H.subsumes h h' && t = t'
  | Ans (v, s, t), Ans (v', s', t') ->
    AValue.subsumes v v' && S.subsumes s s' && t = t'
  | NAP ex, NAP ex' -> ex = ex'
  | _, _ -> false

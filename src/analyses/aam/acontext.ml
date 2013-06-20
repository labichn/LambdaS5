module SYN = Ljs_syntax
module K = Akont

type addr = Ashared.addr
type time = Ashared.time

type exp = Ljs_syntax.exp
type syn_attrs = Ljs_syntax.attrs
type syn_prop = Ljs_syntax.prop

type pos = Prelude.Pos.t
type env = addr Prelude.IdMap.t

type store = Astore.store
type hand = Ahandle.hand
type kont = Akont.kont
type value = Lattices.AValue.t
type attrs = Aobject.attrs
type prop = Aobject.prop

let string_of_value = Lattices.AValue.string_of

type context =
| Ev of exp * env * store * hand * kont * time
| EvA of pos * syn_attrs * env * store * hand * kont * time
| EvP of pos * (string * syn_prop) * env * store * hand * kont * time
| Co of kont * pos * value * store * hand * time
| CoA of kont * pos * attrs * store * hand * time
| CoP of kont * pos * (string * prop) * store * hand * time
| Ap of pos * value * value list * store * hand * kont * time
| Ex of exn * env * store * hand * time
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

let with_store sta sto = match sta with
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
  | Ev (exp, _, _, _, k, _) -> "ev("^(Prelude.Pos.string_of_pos (SYN.pos_of exp))^", "^(string_of_exp exp)^", "^(K.string_of k)^")"
  | EvA (_, _, _, _, _, k, _) -> "eva("^(K.string_of k)^")"
  | EvP (_, _, _, _, _, k, _) -> "evp("^(K.string_of k)^")"
  | Co (k, _, v, _, _, _) -> "co("^(K.string_of k)^", "^(string_of_value v)^")"
  | CoA (k, _, _, _, _, _) -> "coa("^(K.string_of k)^")"
  | CoP (k, _, (n, v), _, _, _) -> "cop("^(K.string_of k)^", "^n^"="^(Aobject.string_of_prop v)^")"
  | Ap (_, f, vlds, _, _, _, _) ->
    "ap("^(string_of_value f)^", "^(Ashared.string_of_list vlds string_of_value)^")"
  | Ex _ -> "ex"
  | Ans (vld, _, _) -> "ans("^(string_of_value vld)^")"

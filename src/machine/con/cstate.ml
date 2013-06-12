module SYN = Ljs_syntax
module P = Prelude
module SH = Cshared
module V = Cvalue

type addr = SH.addr
type time = SH.time
type env = addr P.IdMap.t
type hand = addr
type kont = addr
type value = V.value
type attrs = V.attrs
type prop = V.prop

type t =
| Ev of SYN.exp * env * hand * kont * time
| EvA of P.Pos.t * SYN.attrs * env * hand * kont * time
| EvP of P.Pos.t * (string * SYN.prop) * env * hand * kont * time
| Co of kont * value * hand * time
| CoA of kont * attrs * hand * time
| CoP of kont * (string * prop) * hand * time
| Ap of P.Pos.t * value * value list * hand * kont * time
| Ex of exn * env * hand * time
| Ans of value * time

let ev exp env han kon tim =
  Ev (exp, env, han, kon, tim)
let eva pos att env han kon tim =
  EvA (pos, att, env, han, kon, tim)
let evp pos pair env han kon tim =
  EvP (pos, pair, env, han, kon, tim)
let co va han kon tim =
  Co (kon, va, han, tim)
let coa va han kon tim =
  CoA (kon, va, han, tim)
let cop pair han kon tim =
  CoP (kon, pair, han, tim)
let ap pos va vals han kon tim =
  Ap (pos, va, vals, han, kon, tim)
let ex e env han tim =
  Ex (e, env, han, tim)
let ans va tim =
  Ans (va, tim)

let tock sta tim = match sta with
  | Ev (exp, env, han, kon, _) ->
    Ev (exp, env, han, kon, tim)
  | EvA (pos, att, env, han, kon, _) ->
    EvA (pos, att, env, han, kon, tim)
  | EvP (pos, pair, env, han, kon, _) ->
    EvP (pos, pair, env, han, kon, tim)
  | Co (kon, va, han, _) ->
    Co (kon, va, han, tim)
  | CoA (kon, va, han, _) ->
    CoA (kon, va, han, tim)
  | CoP (kon, pair, han, _) ->
    CoP (kon, pair, han, tim)
  | Ap (pos, va, vals, han, kon, _) ->
    Ap (pos, va, vals, han, kon, tim)
  | Ex (e, env, han, _) ->
    Ex (e, env, han, tim)
  | Ans (va, _) ->
    Ans (va, tim)

let hand_of sta = match sta with
  | Ev (_, _, h, _, _)
  | EvA (_, _, _, h, _, _)
  | EvP (_, _, _, h, _, _)
  | Co (_, _, h, _)
  | CoA (_, _, h, _)
  | CoP (_, _, h, _)
  | Ap (_, _, _, h, _, _)
  | Ex (_, _, h, _) -> h
  | Ans _ -> failwith "no hand in ans!"

let kont_of sta = match sta with
  | Ev (_, _, _, k, _)
  | EvA (_, _, _, _, k, _)
  | EvP (_, _, _, _, k, _)
  | Ap (_, _, _, _, k, _)
  | Co (k, _, _, _)
  | CoA (k, _, _, _)
  | CoP (k, _, _, _) -> k
  | Ex _ -> failwith "no kont in exn"
  | Ans _ -> failwith "no kont in ans"

let time_of sta = match sta with
  | Ev (_, _, _, _, t)
  | EvA (_, _, _, _, _, t)
  | EvP (_, _, _, _, _, t)
  | CoA (_, _, _, t)
  | CoP (_, _, _, t)
  | Co (_, _, _, t)
  | Ap (_, _, _, _, _, t)
  | Ex (_, _, _, t)
  | Ans (_, t) -> t

let string_of_xs xs = List.fold_right (fun x a -> x^" "^a) xs ""

let rec string_of_exp exp = match exp with
  | SYN.Null _ -> "null"
  | SYN.Undefined _ -> "undef"
  | SYN.String (_, _) -> "string"
  | SYN.Num (_, _) -> "num"
  | SYN.True _ -> "true"
  | SYN.False _ -> "false"
  | SYN.Id (_, x) -> "id: "^x^" "
  | SYN.Object (_, _, _) -> "object"
  | SYN.GetAttr (_, _, _, _) -> "getattr"
  | SYN.SetAttr (_, _, _, _, _) -> "setattr"
  | SYN.GetObjAttr (_, _, _) -> "getobjattr"
  | SYN.SetObjAttr (_, _, _, _) -> "setobjattr"
  | SYN.GetField (_, _, _, _) -> "getfield"
  | SYN.SetField (_, _, _, _, _) -> "setfield"
  | SYN.DeleteField (_, _, _) -> "deletefield"
  | SYN.OwnFieldNames (_, _) -> "ownfieldnames"
  | SYN.SetBang (_, _, _) -> "setbang"
  | SYN.Op1 (_, _, _) -> "op1"
  | SYN.Op2 (_, _, _, _) -> "op2"
  | SYN.If (_, _, _, _) -> "if"
  | SYN.App (_, _, _) -> "app"
  | SYN.Seq (_, _, _) -> "seq"
  | SYN.Let (_, x, e, _) -> "(let "^x^" "^(string_of_exp e)^")"
  | SYN.Rec (_, x, e1, e2) -> "rec("^x^", "^(string_of_exp e1)^", "^(string_of_exp e2)^")"
  | SYN.Label (_, _, _) -> "label"
  | SYN.Break (_, _, _) -> "break"
  | SYN.TryCatch (_, _, _) -> "catch"
  | SYN.TryFinally (_, _, _) -> "fin"
  | SYN.Throw (_, _) -> "thrwo"
  | SYN.Lambda (_, xs, e) -> "lam("^(string_of_xs xs)^", "^(string_of_exp e)^")"
  | SYN.Eval (_, _, _) -> "eval"
  | SYN.Hint (_, _, _) -> "hint"

let string_of sta = match sta with
  | Ev (exp, env, han, kon, tim) ->
    "ev ("^(string_of_exp exp)^", "^(string_of_int tim)^")"
  | EvA (pos, att, env, han, kon, tim) ->
    "eva ("^", "^(string_of_int tim)^")"
  | EvP (pos, (str, pro), env, han, kon, tim) ->
    "evp ("^", "^(string_of_int tim)^")"
  | Co (kon, va, han, tim) ->
    "co ("^(string_of_int kon)^", "^(V.string_of_value va)^", "^(string_of_int han)^", "^(string_of_int tim)^")"
  | CoA (kon, att, han, tim) ->
    "coa ("^", "^(string_of_int tim)^")"
  | CoP (kon, (str, pro), han, tim) ->
    "cop ("^", "^(string_of_int tim)^")"
  | Ap (pos, va, vals, han, kon, tim) ->
    "ap ("^", "^(string_of_int tim)^")"
  | Ex (er, env, han, tim) ->
    "ex ("^", "^(string_of_int tim)^")"
  | Ans (va, tim) ->
    "ans ("^", "^(string_of_int tim)^")"

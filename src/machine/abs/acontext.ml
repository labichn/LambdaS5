module SYN = Ljs_syntax

type addr = Ashared.addr
type time = Ashared.time

type exp = Ljs_syntax.exp
type syn_attrs = Ljs_syntax.attrs
type syn_prop = Ljs_syntax.prop

type pos = Prelude.Pos.t
type env = addr Prelude.IdMap.t

type hand = addr
type kont = addr
type value = Avalue.value_ld
type attrs = Avalue.attrs
type prop = Avalue.prop

type context =
| Ev of exp * env * hand * kont * time
| EvA of pos * syn_attrs * env * hand * kont * time
| EvP of pos * (string * syn_prop) * env * hand * kont * time
| Co of kont * pos * value * hand * time
| CoA of kont * attrs * hand * time
| CoP of kont * pos * (string * prop) * hand * time
| Ap of pos * value * value list * hand * kont * time
| Ex of exn * env * hand * time
| Ans of value * time

let ev exp env han kon tim =
  Ev (exp, env, han, kon, tim)
let eva pos att env han kon tim =
  EvA (pos, att, env, han, kon, tim)
let evp pos pair env han kon tim =
  EvP (pos, pair, env, han, kon, tim)
let co p va han kon tim =
  Co (kon, p, va, han, tim)
let coa va han kon tim =
  CoA (kon, va, han, tim)
let cop p pair han kon tim =
  CoP (kon, p, pair, han, tim)
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
  | Co (kon, p, va, han, _) ->
    Co (kon, p, va, han, tim)
  | CoA (kon, va, han, _) ->
    CoA (kon, va, han, tim)
  | CoP (kon, p, pair, han, _) ->
    CoP (kon, p, pair, han, tim)
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
  | Co (_, _, _, h, _)
  | CoA (_, _, h, _)
  | CoP (_, _, _, h, _)
  | Ap (_, _, _, h, _, _)
  | Ex (_, _, h, _) -> h
  | Ans _ -> failwith "no hand in ans!"

let kont_of sta = match sta with
  | Ev (_, _, _, k, _)
  | EvA (_, _, _, _, k, _)
  | EvP (_, _, _, _, k, _)
  | Ap (_, _, _, _, k, _)
  | Co (k, _, _, _, _)
  | CoA (k, _, _, _)
  | CoP (k, _, _, _, _) -> k
  | Ex _ -> failwith "no kont in exn"
  | Ans _ -> failwith "no kont in ans"

let time_of sta = match sta with
  | Ev (_, _, _, _, t)
  | EvA (_, _, _, _, _, t)
  | EvP (_, _, _, _, _, t)
  | CoA (_, _, _, t)
  | CoP (_, _, _, _, t)
  | Co (_, _, _, _, t)
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
  | SYN.Let (_, _, _, _) -> "let"
  | SYN.Rec (_, _, _, _) -> "rec"
  | SYN.Label (_, _, _) -> "label"
  | SYN.Break (_, _, _) -> "break"
  | SYN.TryCatch (_, _, _) -> "catch"
  | SYN.TryFinally (_, _, _) -> "fin"
  | SYN.Throw (_, _) -> "throw"
  | SYN.Lambda (_, _, _) -> "lam"
  | SYN.Eval (_, _, _) -> "eval"
  | SYN.Hint (_, _, _) -> "hint"

let string_of con = match con with
  | Ev (exp, _, _, _, _) -> "ev("^(string_of_exp exp)^")"
  | EvA _ -> "eva"
  | EvP _ -> "evp"
  | Co (_, _, v, _, _) -> "co("^(Avalue.string_of_valueld v)^")"
  | CoA _ -> "coa"
  | CoP _ -> "cop"
  | Ap (_, f, vlds, _, _, _) ->
    "ap("^(Avalue.string_of_valueld f)^", "^(Ashared.string_of_list vlds Avalue.string_of_valueld)^")"
  | Ex _ -> "ex"
  | Ans (vld, _) -> "ans("^(Avalue.string_of_valueld vld)^")"

(*
let string_of sta = match sta with
  | Ev (exp, env, han, kon, tim) ->
    "ev ("^(string_of_exp exp)^", "^(string_of_int tim)^")"
  | EvA (pos, att, env, han, kon, tim) ->
    "eva ("^", "^(string_of_int tim)^")"
  | EvP (pos, (str, pro), env, han, kon, tim) ->
    "evp ("^", "^(string_of_int tim)^")"
  | Co (kon, va, han, tim) ->
    "co ("^(string_of_int kon)^", "^(string_of_value va)^", "^(string_of_int han)^", "^(string_of_int tim)^")"
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
*)

type exp = Ljs_syntax.exp
type addr = Ashared.addr
type env = addr Prelude.IdMap.t
type time = Ashared.time
type konta = addr
type value = addr
type attrs = addr
type prop = addr
type pos = Prelude.Pos.t
type pattr = Ljs_syntax.pattr
type oattr = Ljs_syntax.oattr
type syn_prop = Ljs_syntax.prop
type id = Prelude.id

(*

can remove:
- let2
- app3
- getfield4
- setfield5
- catch2
- eval3

*)

type kont =
| Mt of pos * time
| SetBang of pos * time * addr * konta
| GetAttr  of pos * time * pattr * exp * env * konta
| GetAttr2 of pos * time * pattr * value * env * konta
| SetAttr  of pos * time * pattr * exp * exp * env * konta
| SetAttr2 of pos * time * pattr * exp * value * env * konta
| SetAttr3 of pos * time * pattr * value * value * env * konta
| GetObjAttr of pos * time * oattr * env * konta
| SetObjAttr  of pos * time * oattr * exp * env * konta
| SetObjAttr2 of pos * time * oattr * value * env * konta
| GetField  of pos * time * exp * exp * env * konta
| GetField2 of pos * time * exp * value * env * konta
| GetField3 of pos * time * value * value * env * konta
| SetField  of pos * time * exp * exp * exp * env * konta
| SetField2 of pos * time * exp * exp * value * env * konta
| SetField3 of pos * time * exp * value * value * env * konta
| SetField4 of pos * time * value * value * value * env * konta
| OwnFieldNames of pos * time * konta
| DeleteField  of pos * time * exp * env * konta
| DeleteField2 of pos * time * value * env * konta
| OpOne of pos * time * string * env * konta
| OpTwo  of pos * time * string * exp * env * konta
| OpTwo2 of pos * time * string * value * env * konta
| If of pos * time * env * exp * exp * konta
| App  of pos * time * env * exp list * konta
| App2 of pos * time * value * env * value list * exp list * konta
| Seq of pos * time * exp * env * konta
| Let of pos * time * id * exp * env * konta
| Rec of pos * time * addr * exp * env * konta
| Label of pos * time * id * env * konta
| Break of pos * time * id * env * konta
| Catch of pos * time * value * env * konta
| Finally of pos * time * exn * env * konta
| Finally2 of pos * time * value * konta
| Throw of pos * time * env * konta
| Eval  of pos * time * exp * env * konta
| Eval2 of pos * time * value * env * konta
| Hint of pos * time * env * konta
| Object  of pos * time * (string * syn_prop) list * env * konta
| Object2 of pos * time * attrs * (string * syn_prop) list *
    (string * prop) list * env * konta
| Attrs of pos * time * string * (string * exp) list *
    (string * value) list * string * bool * env * konta
| DataProp of pos * time * string * bool * bool * bool * konta
| AccProp  of pos * time * string * exp * bool * bool * env * konta
| AccProp2 of pos * time * string * value * bool * bool * env * konta

let time_of kont = match kont with
  | Mt (_, t)
  | SetBang (_, t, _, _)
  | GetAttr (_, t, _, _, _, _)
  | GetAttr2 (_, t, _, _, _, _)
  | SetAttr (_, t, _, _, _, _, _)
  | SetAttr2 (_, t, _, _, _, _, _)
  | SetAttr3 (_, t, _, _, _, _, _)
  | GetObjAttr (_, t, _, _, _)
  | SetObjAttr (_, t, _, _, _, _)
  | SetObjAttr2 (_, t, _, _, _, _)
  | GetField (_, t, _, _, _, _)
  | GetField2 (_, t, _, _, _, _)
  | GetField3 (_, t, _, _, _, _)
  | SetField (_, t, _, _, _, _, _)
  | SetField2 (_, t, _, _, _, _, _)
  | SetField3 (_, t, _, _, _, _, _)
  | SetField4 (_, t, _, _, _, _, _)
  | OwnFieldNames (_, t, _)
  | DeleteField (_, t, _, _, _)
  | DeleteField2 (_, t, _, _, _)
  | OpOne (_, t, _, _, _)
  | OpTwo (_, t, _, _, _, _)
  | OpTwo2 (_, t, _, _, _, _)
  | If (_, t, _, _, _, _)
  | App (_, t, _, _, _)
  | App2 (_, t, _, _, _, _, _)
  | Seq (_, t, _, _, _)
  | Let (_, t, _, _, _, _)
  | Rec (_, t, _, _, _, _)
  | Label (_, t, _, _, _)
  | Break (_, t, _, _, _)
  | Catch (_, t, _, _, _)
  | Finally (_, t, _, _, _)
  | Finally2 (_, t, _, _)
  | Throw (_, t, _, _)
  | Eval (_, t, _, _, _)
  | Eval2 (_, t, _, _, _)
  | Hint (_, t, _, _)
  | Object (_, t, _, _, _)
  | Object2 (_, t, _, _, _, _, _)
  | Attrs (_, t, _, _, _, _, _, _, _)
  | DataProp (_, t, _, _, _, _, _)
  | AccProp (_, t, _, _, _, _, _, _)
  | AccProp2 (_, t, _, _, _, _, _, _) -> t

let zero t0 = Mt (Prelude.Pos.dummy, t0)

let pos_of kont = match kont with
  | Mt (p, _)
  | SetBang (p, _, _, _)
  | GetAttr (p, _, _, _, _, _)
  | GetAttr2 (p, _, _, _, _, _)
  | SetAttr (p, _, _, _, _, _, _)
  | SetAttr2 (p, _, _, _, _, _, _)
  | SetAttr3 (p, _, _, _, _, _, _)
  | GetObjAttr (p, _, _, _, _)
  | SetObjAttr (p, _, _, _, _, _)
  | SetObjAttr2 (p, _, _, _, _, _)
  | GetField (p, _, _, _, _, _)
  | GetField2 (p, _, _, _, _, _)
  | GetField3 (p, _, _, _, _, _)
  | SetField (p, _, _, _, _, _, _)
  | SetField2 (p, _, _, _, _, _, _)
  | SetField3 (p, _, _, _, _, _, _)
  | SetField4 (p, _, _, _, _, _, _)
  | OwnFieldNames (p, _, _)
  | DeleteField (p, _, _, _, _)
  | DeleteField2 (p, _, _, _, _)
  | OpOne (p, _, _, _, _)
  | OpTwo (p, _, _, _, _, _)
  | OpTwo2 (p, _, _, _, _, _)
  | If (p, _, _, _, _, _)
  | App (p, _, _, _, _)
  | App2 (p, _, _, _, _, _, _)
  | Seq (p, _, _, _, _)
  | Let (p, _, _, _, _, _)
  | Rec (p, _, _, _, _, _)
  | Label (p, _, _, _, _)
  | Break (p, _, _, _, _)
  | Catch (p, _, _, _, _)
  | Finally (p, _, _, _, _)
  | Finally2 (p, _, _, _)
  | Throw (p, _, _, _)
  | Eval (p, _, _, _, _)
  | Eval2 (p, _, _, _, _)
  | Hint (p, _, _, _)
  | Object (p, _, _, _, _)
  | Object2 (p, _, _, _, _, _, _)
  | Attrs (p, _, _, _, _, _, _, _, _)
  | DataProp (p, _, _, _, _, _, _)
  | AccProp (p, _, _, _, _, _, _, _)
  | AccProp2 (p, _, _, _, _, _, _, _) -> p

let string_of kon = "I'm lazy"

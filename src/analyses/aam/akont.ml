type exp = Ljs_syntax.exp
type addr = Ashared.addr
type env = addr Prelude.IdMap.t
type time = Ashared.time
type kaddr = addr
type vaddr = addr
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

(* INVARIANT: |exp list| + |vaddr list| will always be internally equal
   for every kont but app *)
type kont =
| Mt
| SetBang of pos * time * addr * kaddr
| GetAttr of pos * time * pattr * exp list * vaddr list * env * kaddr
| SetAttr  of pos * time * pattr * exp list * vaddr list * env * kaddr
| GetObjAttr of pos * time * oattr * env * kaddr
| SetObjAttr  of pos * time * oattr * exp list * vaddr list * env * kaddr
| GetField  of pos * time * exp list * vaddr list * env * kaddr
| SetField  of pos * time * exp list * vaddr list * env * kaddr
| OwnFieldNames of pos * time * kaddr
| DeleteField  of pos * time * exp list * vaddr list * env * kaddr
| OpOne of pos * time * string * env * kaddr
| OpTwo  of pos * time * string * exp list * vaddr list * env * kaddr
| If of pos * time * env * exp * exp * kaddr
| App  of pos * time * env * exp list * vaddr list * kaddr
| Seq of pos * time * exp * env * kaddr
| Let of pos * time * id * exp * env * kaddr
| Rec of pos * time * addr * exp * env * kaddr
| Label of pos * time * id * env * kaddr
| Break of pos * time * id * env * kaddr
| Catch of pos * time * vaddr * env * kaddr
| Finally of pos * time * exn list * vaddr list * env * kaddr
| Throw of pos * time * env * kaddr
| Eval  of pos * time * exp list * vaddr list * env * kaddr
| Hint of pos * time * env * kaddr
| Object of pos * time * attrs list * (string * syn_prop) list *
    (string * prop) list * env * kaddr
| Attrs of pos * time * string * (string * exp) list *
    (string * vaddr) list * string * bool * env * kaddr
| DataProp of pos * time * string * bool * bool * bool * kaddr
| AccProp  of pos * time * string * exp list * vaddr list * bool * bool * env * kaddr

let time_of kont = match kont with
  | Mt -> failwith "no time in mt"
  | SetBang (_, t, _, _)
  | GetAttr (_, t, _, _, _, _, _)
  | SetAttr (_, t, _, _, _, _, _)
  | GetObjAttr (_, t, _, _, _)
  | SetObjAttr (_, t, _, _, _, _, _)
  | GetField (_, t, _, _, _, _)
  | SetField (_, t, _, _, _, _)
  | OwnFieldNames (_, t, _)
  | DeleteField (_, t, _, _, _, _)
  | OpOne (_, t, _, _, _)
  | OpTwo (_, t, _, _, _, _, _)
  | If (_, t, _, _, _, _)
  | App (_, t, _, _, _, _)
  | Seq (_, t, _, _, _)
  | Let (_, t, _, _, _, _)
  | Rec (_, t, _, _, _, _)
  | Label (_, t, _, _, _)
  | Break (_, t, _, _, _)
  | Catch (_, t, _, _, _)
  | Finally (_, t, _, _, _, _)
  | Throw (_, t, _, _)
  | Eval (_, t, _, _, _, _)
  | Hint (_, t, _, _)
  | Object (_, t, _, _, _, _, _)
  | Attrs (_, t, _, _, _, _, _, _, _)
  | DataProp (_, t, _, _, _, _, _)
  | AccProp (_, t, _, _, _, _, _, _, _) -> t

let pos_of kont = match kont with
  | Mt -> failwith "no pos in an mt kont"
  | SetBang (p, _, _, _)
  | GetAttr (p, _, _, _, _, _, _)
  | SetAttr (p, _, _, _, _, _, _)
  | GetObjAttr (p, _, _, _, _)
  | SetObjAttr (p, _, _, _, _, _, _)
  | GetField (p, _, _, _, _, _)
  | SetField (p, _, _, _, _, _)
  | OwnFieldNames (p, _, _)
  | DeleteField (p, _, _, _, _, _)
  | OpOne (p, _, _, _, _)
  | OpTwo (p, _, _, _, _, _, _)
  | If (p, _, _, _, _, _)
  | App (p, _, _, _, _, _)
  | Seq (p, _, _, _, _)
  | Let (p, _, _, _, _, _)
  | Rec (p, _, _, _, _, _)
  | Label (p, _, _, _, _)
  | Break (p, _, _, _, _)
  | Catch (p, _, _, _, _)
  | Finally (p, _, _, _, _, _)
  | Throw (p, _, _, _)
  | Eval (p, _, _, _, _, _)
  | Hint (p, _, _, _)
  | Object (p, _, _, _, _, _, _)
  | Attrs (p, _, _, _, _, _, _, _, _)
  | DataProp (p, _, _, _, _, _, _)
  | AccProp (p, _, _, _, _, _, _, _, _) -> p

let string_of kon = match kon with
  | Mt ->
    "mt"
  | SetBang (pos, time, addr, kaddr) ->
    "setbang"
  | GetAttr _ ->
    "getattr"
  | SetAttr _ ->
    "setattr"
  | GetObjAttr _ ->
    "getobjattr"
  | SetObjAttr _ ->
    "setobjattr"
  | GetField  _ ->
    "getfield"
  | SetField _ ->
    "setfield"
  | OwnFieldNames (pos, time, kaddr) ->
    "ownfieldnames"
  | DeleteField _ ->
    "deletefield"
  | OpOne (pos, time, string, env, kaddr) ->
    "opone"
  | OpTwo (p, t, op, wat, vaddr, env, kaddr) ->
    "optwo("^(Prelude.Pos.string_of_pos p)^", "^op^")"
  | If (pos, time, env, exp, exp2, kaddr) ->
    "if"
  | App _ ->
    "app"
  | Seq (pos, time, exp, env, kaddr) ->
    "seq"
  | Let (pos, time, id, exp, env, kaddr) ->
    "let"
  | Rec (pos, time, addr, exp, env, kaddr) ->
    "rec"
  | Label (pos, time, id, env, kaddr) ->
    "label"
  | Break (pos, time, id, env, kaddr) ->
    "break"
  | Catch (pos, time, vaddr, env, kaddr) ->
    "catch"
  | Finally _ ->
    "finally"
  | Throw (pos, time, env, kaddr) ->
    "throw"
  | Eval _ ->
    "eval"
  | Hint (pos, time, env, kaddr) ->
    "hint"
  | Object  _ ->
    "object"
  | Attrs (pos, time, string, pairs, pairs2, string2, bool, env, kaddr) ->
    "attrs"
  | DataProp (pos, time, string, bool, bool2, bool3, kaddr) ->
    "dataprop"
  | AccProp _ ->
    "accprop"


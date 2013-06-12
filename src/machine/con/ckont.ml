open Prelude
open Ljs_syntax

type addr = Cshared.addr
type env = addr IdMap.t
type time = Cshared.time
type value = Cvalue.value
type attrs = Cvalue.attrs
type prop = Cvalue.prop
type t =
| Mt of Pos.t * time
| SetBang of Pos.t * time * addr * addr
| GetAttr  of Pos.t * time * pattr * exp * env * addr
| GetAttr2 of Pos.t * time * pattr * value * env * addr
| SetAttr  of Pos.t * time * pattr * exp * exp * env * addr
| SetAttr2 of Pos.t * time * pattr * exp * value * env * addr
| SetAttr3 of Pos.t * time * pattr * value * value * env * addr
| GetObjAttr of Pos.t * time * oattr * env * addr
| SetObjAttr  of Pos.t * time * oattr * exp * env * addr
| SetObjAttr2 of Pos.t * time * oattr * value * env * addr
| GetField  of Pos.t * time * exp * exp * env * addr
| GetField2 of Pos.t * time * exp * value * env * addr
| GetField3 of Pos.t * time * value * value * env * addr
| SetField  of Pos.t * time * exp * exp * exp * env * addr
| SetField2 of Pos.t * time * exp * exp * value * env * addr
| SetField3 of Pos.t * time * exp * value * value * env * addr
| SetField4 of Pos.t * time * value * value * value * env * addr
| OwnFieldNames of Pos.t * time * addr
| DeleteField  of Pos.t * time * exp * env * addr
| DeleteField2 of Pos.t * time * value * env * addr
| OpOne of Pos.t * time * string * env * addr
| OpTwo  of Pos.t * time * string * exp * env * addr
| OpTwo2 of Pos.t * time * string * value * env * addr
| If of Pos.t * time * env * exp * exp * addr
| App  of Pos.t * time * env * exp list * addr
| App2 of Pos.t * time * value * env * value list * exp list * addr
| Seq of Pos.t * time * exp * env * addr
| Let of Pos.t * time * id * exp * env * addr
| Rec of Pos.t * time * addr * exp * env * addr
| Label of Pos.t * time * id * env * addr
| Break of Pos.t * time * id * env * addr
| Catch of Pos.t * time * value * env * addr
| Catch2 of Pos.t * time * env * addr
| Finally of Pos.t * time * exn * env * addr
| Finally2 of Pos.t * time * value * addr
| Throw of Pos.t * time * env * addr
| Eval  of Pos.t * time * exp * env * addr
| Eval2 of Pos.t * time * value * env * addr
| Hint of Pos.t * time * env * addr
| Object  of Pos.t * time * (string * Ljs_syntax.prop) list * env * addr
| Object2 of Pos.t * time * attrs * (string * Ljs_syntax.prop) list *
    (string * prop) list * env * addr
| Attrs of Pos.t * time * string * (string * exp) list *
    (string * value) list * string * bool * env * addr
| DataProp of Pos.t * time * string * bool * bool * bool * addr
| AccProp  of Pos.t * time * string * exp * bool * bool * env * addr
| AccProp2 of Pos.t * time * string * value * bool * bool * env * addr

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
  | Catch2 (_, t, _, _)
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

let zero = Mt (Pos.dummy, Cshared.addr0)

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
  | Catch2 (p, _, _, _)
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

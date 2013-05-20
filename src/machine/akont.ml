module S = Shared
module SYN = Ljs_syntax
module V = Avalues

type loc = S.loc
type pos = S.Pos.t

type kont =
  | Mt
  | SetBang of loc * loc
  | GetAttr  of SYN.pattr * SYN.exp * V.env * loc
  | GetAttr2 of SYN.pattr * V.avalue * V.env * loc
  | SetAttr  of SYN.pattr * SYN.exp * SYN.exp * V.env * loc
  | SetAttr2 of SYN.pattr * SYN.exp * V.avalue * V.env * loc
  | SetAttr3 of SYN.pattr * V.avalue * V.avalue * V.env * loc
  | GetObjAttr of SYN.oattr * V.env * loc
  | SetObjAttr  of SYN.oattr * SYN.exp * V.env * loc
  | SetObjAttr2 of SYN.oattr * V.avalue * V.env * loc
  | GetField  of pos * SYN.exp * SYN.exp * V.env * loc
  | GetField2 of pos * SYN.exp * V.avalue * V.env * loc
  | GetField3 of pos * V.avalue * V.avalue * V.env * loc
  | GetField4 of V.env * loc
  | SetField  of pos * SYN.exp * SYN.exp * SYN.exp * V.env * loc
  | SetField2 of pos * SYN.exp * SYN.exp * V.avalue * V.env * loc
  | SetField3 of pos * SYN.exp * V.avalue * V.avalue * V.env * loc
  | SetField4 of pos * V.avalue * V.avalue * V.avalue * V.env * loc
  | SetField5 of V.env * loc
  | OwnFieldNames of loc
  | DeleteField  of pos * SYN.exp * V.env * loc
  | DeleteField2 of pos * V.avalue * V.env * loc
  | OpOne of string * V.env * loc
  | OpTwo  of string * SYN.exp * V.env * loc
  | OpTwo2 of string * V.avalue * V.env * loc
  | If of V.env * SYN.exp * SYN.exp * loc
  | App  of pos * V.env * SYN.exp list * loc
  | App2 of pos * V.avalue * V.env * V.avalue list * SYN.exp list * loc
  | App3 of V.env * loc
  | Seq of SYN.exp * V.env * loc
  | Let of S.id * SYN.exp * V.env * loc
  | Let2 of V.env * loc
  | Rec of loc * SYN.exp * V.env * loc
  | Label of S.id * V.env * loc
  | Break of S.id * V.env * loc
  | Catch of pos * V.avalue * V.env * loc
  | Catch2 of V.env * loc
  | Finally of exn * V.env * loc
  | Finally2 of V.avalue
  | Throw of V.env * loc
  | Eval  of pos * SYN.exp * V.env * loc
  | Eval2 of pos * V.avalue * V.env * loc
  | Eval3 of V.env * loc
  | Hint of V.env * loc
  | Object  of (string * SYN.prop) list * V.env * loc
  | Object2 of V.attrsv * (string * SYN.prop) list *
      (string * V.propv) list * V.env * loc
  | Attrs of string * (string * SYN.exp) list * (string * V.avalue) list *
      string * bool * V.env * loc
  | DataProp of string * bool * bool * bool * loc
  | AccProp  of string * SYN.exp * bool * bool * V.env * loc
  | AccProp2 of string * V.avalue * bool * bool * V.env * loc

type handl =
 | MtH
 | Cat of pos * SYN.exp * V.env * loc * loc
 | Lab of S.id * V.env * loc * loc
 | Fin of SYN.exp * V.env * loc * loc

let hloc_of_handl handl = match handl with
 | Cat (_, _, _, _, h) -> h
 | Lab (_, _, _, h) -> h
 | Fin (_, _, _, h) -> h
 | MtH -> failwith "no hloc in mth, something's wrong!"

let shed h = match h with
 | MtH -> failwith "cannot shed an empty handle"
 | Cat (_, _, _, _, h) -> h
 | Lab (_, _, _, h) -> h
 | Fin (_, _, _, h) -> h

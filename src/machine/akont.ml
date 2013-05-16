module S = Shared
module SYN = Ljs_syntax
module V = Avalues

type pos = S.Pos.t

type kont =
  | Mt
  | SetBang of S.loc * kont
  | GetAttr  of SYN.pattr * SYN.exp * V.env * kont
  | GetAttr2 of SYN.pattr * V.avalue * V.env * kont
  | SetAttr  of SYN.pattr * SYN.exp * SYN.exp * V.env * kont
  | SetAttr2 of SYN.pattr * SYN.exp * V.avalue * V.env * kont
  | SetAttr3 of SYN.pattr * V.avalue * V.avalue * V.env * kont
  | GetObjAttr of SYN.oattr * V.env * kont
  | SetObjAttr  of SYN.oattr * SYN.exp * V.env * kont
  | SetObjAttr2 of SYN.oattr * V.avalue * V.env * kont
  | GetField  of pos * SYN.exp * SYN.exp * V.env * kont
  | GetField2 of pos * SYN.exp * V.avalue * V.env * kont
  | GetField3 of pos * V.avalue * V.avalue * V.env * kont
  | GetField4 of V.env * kont
  | SetField  of pos * SYN.exp * SYN.exp * SYN.exp * V.env * kont
  | SetField2 of pos * SYN.exp * SYN.exp * V.avalue * V.env * kont
  | SetField3 of pos * SYN.exp * V.avalue * V.avalue * V.env * kont
  | SetField4 of pos * V.avalue * V.avalue * V.avalue * V.env * kont
  | SetField5 of V.env * kont
  | OwnFieldNames of kont
  | DeleteField  of pos * SYN.exp * V.env * kont
  | DeleteField2 of pos * V.avalue * V.env * kont
  | OpOne of string * V.env * kont
  | OpTwo  of string * SYN.exp * V.env * kont
  | OpTwo2 of string * V.avalue * V.env * kont
  | If of V.env * SYN.exp * SYN.exp * kont
  | App  of pos * V.env * SYN.exp list * kont
  | App2 of pos * V.avalue * V.env * V.avalue list * SYN.exp list * kont
  | App3 of V.env * kont
  | Seq of SYN.exp * V.env * kont
  | Let of S.id * SYN.exp * V.env * kont
  | Let2 of V.env * kont
  | Rec of S.loc * SYN.exp * V.env * kont
  | Label of S.id * V.env * kont
  | Break of S.id * V.env * kont
  | Catch of pos * V.avalue * V.env * kont
  | Catch2 of V.env * kont
  | Finally of exn * V.env * kont
  | Finally2 of V.avalue
  | Throw of V.env * kont
  | Eval  of pos * SYN.exp * V.env * kont
  | Eval2 of pos * V.avalue * V.env * kont
  | Eval3 of V.env * kont
  | Hint of V.env * kont
  | Object  of (string * SYN.prop) list * V.env * kont
  | Object2 of V.attrsv * (string * SYN.prop) list *
      (string * V.propv) list * V.env * kont
  | Attrs of string * (string * SYN.exp) list * (string * V.avalue) list *
      string * bool * V.env * kont
  | DataProp of string * bool * bool * bool * kont
  | AccProp  of string * SYN.exp * bool * bool * V.env * kont
  | AccProp2 of string * V.avalue * bool * bool * V.env * kont

type handl =
 | MtH
 | Cat of pos * SYN.exp * V.env * kont * handl
 | Lab of S.id * V.env * kont * handl
 | Fin of SYN.exp * V.env * kont * handl

let shed h = match h with
 | MtH -> failwith "cannot shed an empty handle"
 | Cat (_, _, _, _, h) -> h
 | Lab (_, _, _, h) -> h
 | Fin (_, _, _, h) -> h

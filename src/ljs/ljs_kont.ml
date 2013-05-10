module GC = Ljs_gc
module P = Prelude
module S = Ljs_syntax
module ST = Store
module V = Ljs_values
module LocSet = Store.LocSet

type id = string

type kont =
  | Mt
  | SetBang of ST.loc * kont
  | GetAttr  of S.pattr * S.exp * V.env * kont
  | GetAttr2 of S.pattr * V.value * V.env * kont
  | SetAttr  of S.pattr * S.exp * S.exp * V.env * kont
  | SetAttr2 of S.pattr * S.exp * V.value * V.env * kont
  | SetAttr3 of S.pattr * V.value * V.value * V.env * kont
  | GetObjAttr of S.oattr * V.env * kont
  | SetObjAttr  of S.oattr * S.exp * V.env * kont
  | SetObjAttr2 of S.oattr * V.value * V.env * kont
  | GetField  of P.Pos.t * S.exp * S.exp * V.env * kont
  | GetField2 of P.Pos.t * S.exp * V.value * V.env * kont
  | GetField3 of P.Pos.t * V.value * V.value * V.env * kont
  | GetField4 of V.env * kont
  | SetField  of P.Pos.t * S.exp * S.exp * S.exp * V.env * kont
  | SetField2 of P.Pos.t * S.exp * S.exp * V.value * V.env * kont
  | SetField3 of P.Pos.t * S.exp * V.value * V.value * V.env * kont
  | SetField4 of P.Pos.t * V.value * V.value * V.value * V.env * kont
  | SetField5 of V.env * kont
  | OwnFieldNames of kont
  | DeleteField  of P.Pos.t * S.exp * V.env * kont
  | DeleteField2 of P.Pos.t * V.value * V.env * kont
  | OpOne of string * V.env * kont
  | OpTwo  of string * S.exp * V.env * kont
  | OpTwo2 of string * V.value * V.env * kont
  | If of V.env * S.exp * S.exp * kont
  | App  of P.Pos.t * V.env * S.exp list * kont
  | App2 of P.Pos.t * V.value * V.env * V.value list * S.exp list * kont
  | App3 of V.env * kont
  | Seq of S.exp * V.env * kont
  | Let of id * S.exp * V.env * kont
  | Let2 of V.env * kont
  | Rec of ST.loc * S.exp * V.env * kont
  | Label of id * V.env * kont
  | Break of id * V.env * kont
  | Catch of P.Pos.t * V.value * V.env * kont
  | Catch2 of V.env * kont
  | Finally of exn * V.env * kont
  | Throw of V.env * kont
  | Eval  of P.Pos.t * S.exp * V.env * kont
  | Eval2 of P.Pos.t * V.value * V.env * kont
  | Eval3 of V.env * kont
  | Hint of V.env * kont
  | Object  of (string * S.prop) list * V.env * kont
  | Object2 of V.attrsv * (string * S.prop) list *
      (string * V.propv) list * V.env * kont
  | Attrs of string * (string * S.exp) list * (string * V.value) list *
      string * bool * V.env * kont
  | DataProp of string * bool * bool * bool * kont
  | AccProp  of string * S.exp * bool * bool * V.env * kont
  | AccProp2 of string * V.value * bool * bool * V.env * kont

type handl =
 | MtH
 | Cat of P.Pos.t * S.exp * V.env * kont * handl
 | Lab of string * V.env * kont * handl
 | Fin of S.exp * V.env * kont * handl

let shed h = match h with
 | MtH -> failwith "cannot shed an empty handle"
 | Cat (_, _, _, _, h) -> h
 | Lab (_, _, _, h) -> h
 | Fin (_, _, _, h) -> h

(* from src/util/prelude.ml *)
module P = Prelude
type id = P.id (* = string *)
module IdSet = P.IdSet
module IdMap = P.IdMap
module Pos = P.Pos
module PosSet = P.PosSet
module PosMap = P.PosMap
let printf = P.printf
let eprintf = P.eprintf
let sprintf = P.sprintf
let intersperse = P.intersperse
let iota = P.iota

(* from src/util/store.ml *)
module ST = Store
type loc = ST.loc (* = int *)
module LocMap = ST.LocMap
module LocSet = ST.LocSet
let print_loc = ST.print_loc

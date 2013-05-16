module LV = Ljs_values
module MV = Avalues
module IS = IntStore
module SYN = Ljs_syntax
open Shared

type answer =
| Answer of SYN.exp list * LV.value * LV.env list * LV.store
| MAnswer of MV.avalue * loc IdMap.t option * IS.store

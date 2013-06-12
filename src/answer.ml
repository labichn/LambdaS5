module LV = Ljs_values
module SYN = Ljs_syntax
module CV = Cvalue
module CC = Ccontext
module P = Prelude

type answer =
| Answer of SYN.exp list * LV.value * LV.env list * LV.store
| CAnswer of CV.value * Cshared.env option * Cstore.t

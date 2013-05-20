module K = Akont
module S = Shared
module V = Avalues

type 'a t = 'a S.LocMap.t * int
let empty_t n = (S.LocMap.empty, n)
let bindings (m, _) = S.LocMap.bindings m

type store =
  V.objectv t * V.avalue t * K.handl t * K.kont t
let (empty : store) = (empty_t 0, empty_t 1, empty_t 2, empty_t 3)


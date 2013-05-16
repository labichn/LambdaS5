module K = Akont
module S = Shared
module V = Avalues

type 'a t = 'a S.LocMap.t * int
let empty_t = (S.LocMap.empty, 0)
let bindings (m, _) = S.LocMap.bindings m

type store =
  V.objectv t * V.avalue t * K.handl t * K.kont t
let (empty : store) = (empty_t, empty_t, empty_t, empty_t)


module P = Prelude

type time = int
type addr = int
let time0 = 0
let addr0 = 0

module Addr = struct type t = addr;; let compare = Pervasives.compare end
module AddrMap = MapExt.Make (Addr)

type env = addr P.IdMap.t

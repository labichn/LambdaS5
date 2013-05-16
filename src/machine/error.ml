type exp = Ljs_syntax.exp
type avalue = Avalues.avalue
type store = IntStore.store
type env = Avalues.env

exception Break of exp list * string * avalue
exception Throw of exp list * avalue
exception PrimErr of exp list * avalue
exception Snapshot of avalue * env * store


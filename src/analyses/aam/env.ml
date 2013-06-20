
type env = Ashared.addr Prelude.IdMap.t
let mt_env = Prelude.IdMap.empty
let env_add = Prelude.IdMap.add
let env_find = Prelude.IdMap.find
let env_filter = Prelude.IdMap.filter
let ids_mem = Prelude.IdSet.mem

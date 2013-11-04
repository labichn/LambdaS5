module P = Prelude
type env = Aam_shared.addr P.IdMap.t
let empty = P.IdMap.empty
let env_add = P.IdMap.add
let env_find = P.IdMap.find
let env_filter = P.IdMap.filter
let env_mem = P.IdMap.mem
let ids_mem = P.IdSet.mem

let subsumes en en' =
  P.IdMap.fold
    (fun x a acc -> acc && try env_find x en = a with _ -> false)
    en' true

let string_of_env e =
  if P.IdMap.cardinal e > 0 then
    "env{\n"^
      (P.IdMap.fold
        (fun str addr a -> str^"-->"^(Aam_shared.string_of_addr addr)^"\n"^a)
        e "") ^ "}"
  else "env{}"

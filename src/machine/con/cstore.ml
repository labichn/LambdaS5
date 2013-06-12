open Ckont
open Prelude
open Cshared
open Ljs_syntax
open Cvalue

type addr = Cshared.addr
type kont = Ckont.t
type hand = Chandle.t
type value = Cvalue.value
type objekt = Cvalue.objekt
type attrs = Cvalue.attrs
type prop = Cvalue.prop
type t = objekt AddrMap.t *
  value AddrMap.t *
  hand AddrMap.t *
  kont AddrMap.t
  
let empty = (AddrMap.empty, AddrMap.empty, AddrMap.empty, AddrMap.empty)
let add = AddrMap.add
let add_obj addr new_obj ((os, vs, hs, ks) : t) =
  begin
(*    print_endline ("adding "^(string_of_int addr));*)
  (add addr new_obj os, vs, hs, ks)
    end
let add_val addr new_val ((os, vs, hs, ks) : t) =
  begin
(*    print_endline ("adding "^(string_of_int addr));*)
    (os, add addr new_val vs, hs, ks)
  end
let add_hand addr new_handl ((os, vs, hs, ks) : t) = (os, vs, add addr new_handl hs, ks)
let add_kont addr new_kont ((os, vs, hs, ks) : t) =  (os, vs, hs, add addr new_kont ks)
let get k m = AddrMap.find k m
let get_obj k ((os, _, _, _) : t) = get k os
let get_val k ((_, vs, _, _) : t) = get k vs
let get_hand k ((_, _, hs, _) : t) = get k hs
let get_kont k ((_, _, _, ks) : t) = get k ks
let set = add
let set_obj k v ((os, vs, hs, ks) : t) = 
  begin
(*    print_endline ("rebinding "^(string_of_int k));*)
  (set k v os, vs, hs, ks)
    end
let set_val k v ((os, vs, hs, ks) : t) = 
  begin
(*    print_endline ("setting "^(string_of_int k)^" to "^(Cvalue.string_of_value v));*)
    (os, set k v vs, hs, ks)
  end
let set_hand k v ((os, vs, hs, ks) : t) = (os, vs, set k v hs, ks)
let set_kont k v ((os, vs, hs, ks) : t) = (os, vs, hs, set k v ks)
let max (os, vs, hs, ks) =
  let safe_max m = try let n, _ = AddrMap.max_binding m in n with Not_found -> 0 in
  let omax = safe_max os in
  let vmax = safe_max vs in
  let hmax = safe_max hs in
  let kmax = safe_max ks in
  max (max omax vmax) (max hmax kmax)

let filter f (os, vs, hs, ks) =
  (AddrMap.filter f os,
   AddrMap.filter f vs,
   AddrMap.filter f hs,
   AddrMap.filter f ks)

let envstore_of_obj addrs (_, props) store =
  let _, env, store' =
    IdMap.fold (fun id prop (addr::addrs', env, store) -> match prop with
    | Data ({value=v}, _, _) ->
      let env' = IdMap.add id addr env in
      let store' = add_val addr v store in
      (addrs', env', store')
    | _ -> failwith "Non-data value in env_of_obj")
      props
      (addrs, IdMap.empty, store) in env, store'

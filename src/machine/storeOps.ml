module E = Error
module S = Shared
module SYN = Ljs_syntax
module V = Avalues

let bool b = match b with
  | true -> V.True
  | false -> V.False

let unbool b = match b with
  | V.True -> true
  | V.False -> false
  | _ -> failwith "tried to unbool a non-bool"

let add_loc m k a = S.IdMap.add k a m
let get_loc m k = S.IdMap.find k m
let add v (vs, next) = next, (S.LocMap.add next v vs, next+1)
let add_obj (os, vs, hs, ks) new_obj =
  let loc, os' = add new_obj os in loc, (os', vs, hs, ks)
let add_val (os, vs, hs, ks) new_val =
  let loc, vs' = add new_val vs in loc, (os, vs', hs, ks)
let add_handl (os, vs, hs, ks) new_handl =
  let loc, hs' = add new_handl hs in loc, (os, vs, hs', ks)
let add_kont (os, vs, hs, ks) new_kont =
  let loc, ks' = add new_kont ks in loc, (os, vs, hs, ks')
let get k (m, _) = S.LocMap.find k m
let get_obj (os, _, _, _) k = get k os
let rec get_attr store attr obj field = match obj, field with
  | V.ObjLoc loc, V.String s -> (match get_obj store loc with
    | attrs, props ->
      if (not (S.IdMap.mem s props)) then V.Undefined
      else (match (S.IdMap.find s props), attr with
      | V.Data (_, _, config), SYN.Config
      | V.Accessor (_, _, config), SYN.Config -> bool config
      | V.Data (_, enum, _), SYN.Enum
      | V.Accessor (_, enum, _), SYN.Enum -> bool enum
      | V.Data ({ V.writable = b; }, _, _), SYN.Writable -> bool b
      | V.Data ({ V.value = v; }, _, _), SYN.Value -> v
      | V.Accessor ({ V.getter = gv; }, _, _), SYN.Getter -> gv
      | V.Accessor ({ V.setter = sv; }, _, _), SYN.Setter -> sv
      | _ -> failwith "bad access of attribute"))
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")
let get_obj_attr attrs attr = match attrs, attr with
  | { V.proto=proto }, SYN.Proto -> proto
  | { V.extensible=extensible} , SYN.Extensible -> bool extensible
  | { V.code=Some code}, SYN.Code -> code
  | { V.code=None}, SYN.Code -> V.Null
  | { V.primval=Some primval}, SYN.Primval -> primval
  | { V.primval=None}, SYN.Primval ->
      failwith "[interp] Got Primval attr of None"
  | { V.klass=klass }, SYN.Klass -> V.String klass
let rec get_prop p store obj field = match obj with
  | V.Null -> None
  | V.ObjLoc loc -> (match get_obj store loc with
    | ({ V.proto = pvalue; }, props) ->
      try Some (S.IdMap.find field props)
      with Not_found -> get_prop p store pvalue field)
  | _ -> failwith "get_prop on a non-object."
let get_val (_, vs, _, _) k = get k vs
let get_handl (_, _, hs, _) k = get k hs
let get_kont (_, _, _, ks) k = get k ks
let set k v (vs, next) = (S.LocMap.add k v vs, next)
let set_obj (os, vs, hs, ks) k v = (set k v os, vs, hs, ks)
let rec set_attr store attr obj field newval = match obj, field with
  | V.ObjLoc loc, V.String f_str -> (match get_obj store loc with
    | ({ V.extensible = ext; } as attrsv, props) ->
      if not (S.IdMap.mem f_str props) then
        if ext then 
          let newprop = match attr with
            | SYN.Getter -> 
              V.Accessor ({ V.getter = newval; V.setter = V.Undefined; },  false, false)
            | SYN.Setter -> 
              V.Accessor ({ V.getter = V.Undefined; V.setter = newval; },  false, false)
            | SYN.Value -> 
              V.Data ({ V.value = newval; V.writable = false; }, false, false)
            | SYN.Writable ->
              V.Data ({ V.value = V.Undefined; V.writable = unbool newval }, false, false) 
            | SYN.Enum ->
              V.Data ({ V.value = V.Undefined; V.writable = false }, unbool newval, true) 
            | SYN.Config ->
              V.Data ({ V.value = V.Undefined; V.writable = false }, true, unbool newval) in
          let store = set_obj store loc (attrsv, S.IdMap.add f_str newprop props) in
          true, store
        else
          failwith "[interp] Extending inextensible object."
      else
        let newprop = match (S.IdMap.find f_str props), attr, newval with
            (* SYN.Writable true -> false when configurable is false *)
          | V.Data ({ V.writable = true } as d, enum, config), SYN.Writable, new_w -> 
            V.Data ({ d with V.writable = unbool new_w }, enum, config)
          | V.Data (d, enum, true), SYN.Writable, new_w ->
            V.Data ({ d with V.writable = unbool new_w }, enum, true)
            (* Updating V.values only checks V.writable *)
          | V.Data ({ V.writable = true } as d, enum, config), SYN.Value, v ->
            V.Data ({ d with V.value = v }, enum, config)
            (* If we had a data property, update it to an accessor *)
          | V.Data (d, enum, true), SYN.Setter, setterv ->
            V.Accessor ({ V.getter = V.Undefined; V.setter = setterv }, enum, true)
          | V.Data (d, enum, true), SYN.Getter, getterv ->
            V.Accessor ({ V.getter = getterv; V.setter = V.Undefined }, enum, true)
            (* V.Accessors can update their getter and setter properties *)
          | V.Accessor (a, enum, true), SYN.Getter, getterv ->
            V.Accessor ({ a with V.getter = getterv }, enum, true)
          | V.Accessor (a, enum, true), SYN.Setter, setterv ->
            V.Accessor ({ a with V.setter = setterv }, enum, true)
            (* An accessor can be changed into a data property *)
          | V.Accessor (a, enum, true), SYN.Value, v ->
            V.Data ({ V.value = v; V.writable = false; }, enum, true)
          | V.Accessor (a, enum, true), SYN.Writable, w ->
            V.Data ({ V.value = V.Undefined; V.writable = unbool w; }, enum, true)
            (* enumerable and configurable need configurable=true *)
          | V.Data (d, _, true), SYN.Enum, new_enum ->
            V.Data (d, unbool new_enum, true)
          | V.Data (d, enum, true), SYN.Config, new_config ->
            V.Data (d, enum, unbool new_config)
          | V.Data (d, enum, false), SYN.Config, V.False -> 
            V.Data (d, enum, false)
          | V.Accessor (a, enum, true), SYN.Config, new_config ->
            V.Accessor (a, enum, unbool new_config)
          | V.Accessor (a, enum, true), SYN.Enum, new_enum ->
            V.Accessor (a, unbool new_enum, true)
          | V.Accessor (a, enum, false), SYN.Config, V.False ->
            V.Accessor (a, enum, false)
          | _ -> raise (E.PrimErr ([], V.String "[interp] bad property set"))
        in
        let store = set_obj store loc (attrsv, S.IdMap.add f_str newprop props) in
        true, store)
  | _ -> raise (E.PrimErr ([], V.String ("[interp] set-attr didn't get
                             ^ an object and a string")))
let set_val (os, vs, hs, ks) k v = (os, set k v vs, hs, ks)
let set_handl (os, vs, hs, ks) k v = (os, vs, set k v hs, ks)
let set_kont (os, vs, hs, ks) k v = (os, vs, hs, set k v ks)
let lookup x e s = get (get_loc e x) s
let look_obj x e (os, _, _, _) = lookup x e os
let look_val x e (_, vs, _, _) = lookup x e vs
let envstore_of_obj p (_, props) store =
  S.IdMap.fold (fun id prop (env, store) -> match prop with
  | V.Data ({V.value=v}, _, _) ->
    let new_loc, store = add_val store v in
    let env = S.IdMap.add id new_loc env in
    env, store
  | _ -> failwith "Non-data value in env_of_obj")
    props
    (S.IdMap.empty, store)

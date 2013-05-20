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

let add_loc = S.IdMap.add
let get_loc = S.IdMap.find
let add v (vs, next) = next, (S.LocMap.add next v vs, next+4)
let add_obj new_obj (os, vs, hs, ks) =
  let loc, os' = add new_obj os in loc, (os', vs, hs, ks)
let add_val new_val (os, vs, hs, ks) =
  let loc, vs' = add new_val vs in loc, (os, vs', hs, ks)
let add_handl new_handl (os, vs, hs, ks) =
  let loc, hs' = add new_handl hs in loc, (os, vs, hs', ks)
let add_kont new_kont (os, vs, hs, ks) =
  let loc, ks' = add new_kont ks in loc, (os, vs, hs, ks')
let get k (m, _) = S.LocMap.find k m
let get_obj k (os, _, _, _) = get k os
let rec get_attr attr obj field store = match obj, field with
  | V.ObjLoc loc, V.String s -> (match get_obj loc store with
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
  | V.ObjLoc loc -> (match get_obj loc store with
    | ({ V.proto = pvalue; }, props) ->
      try Some (S.IdMap.find field props)
      with Not_found -> get_prop p store pvalue field)
  | _ -> failwith "get_prop on a non-object."
let get_val k (_, vs, _, _) = get k vs
let get_handl k (_, _, hs, _) = get k hs
let get_kont k (_, _, _, ks) = get k ks
let get_maybe f l s = try Some (f l s) with Not_found -> None
let get_maybe_obj l s = get_maybe get_obj l s
let get_maybe_val l s = get_maybe get_val l s
let get_maybe_handl l s = get_maybe get_handl l s
let get_maybe_kont l s = get_maybe get_kont l s
let set k v (vs, next) = (S.LocMap.add k v vs, next)
let set_obj k v (os, vs, hs, ks) = (set k v os, vs, hs, ks)
let rec set_attr attr obj field newval store = match obj, field with
  | V.ObjLoc loc, V.String f_str -> (match get_obj loc store with
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
          let store = set_obj loc (attrsv, S.IdMap.add f_str newprop props) store in
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
        let store = set_obj loc (attrsv, S.IdMap.add f_str newprop props) store in
        true, store)
  | _ -> raise (E.PrimErr ([], V.String ("[interp] set-attr didn't get
                             ^ an object and a string")))
let set_val k v (os, vs, hs, ks) = (os, set k v vs, hs, ks)
let set_handl k v (os, vs, hs, ks) = (os, vs, set k v hs, ks)
let set_kont k v (os, vs, hs, ks) = (os, vs, hs, set k v ks)
let lookup x e s = get (get_loc x e) s
let look_obj x e (os, _, _, _) = lookup x e os
let look_val x e (_, vs, _, _) = lookup x e vs
let envstore_of_obj p (_, props) store =
  S.IdMap.fold (fun id prop (env, store) -> match prop with
  | V.Data ({V.value=v}, _, _) ->
    let new_loc, store = add_val v store in
    let env = S.IdMap.add id new_loc env in
    env, store
  | _ -> failwith "Non-data value in env_of_obj")
    props
    (S.IdMap.empty, store)
let filter f ((os, a), (vs, b), (hs, c), (ks, d)) =
  ((S.LocMap.filter f os, a),
   (S.LocMap.filter f vs, b),
   (S.LocMap.filter f hs, c),
   (S.LocMap.filter f ks, d))

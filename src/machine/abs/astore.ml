open Akont
open Prelude
open Ashared
open Ljs_syntax
open Avalue
open Collects
module L = Clattice

type addr = Ashared.addr
type kont = Akont.kont
type hand = Ahandle.hand
type value = Avalue.value_l
type objekt = Avalue.objekt
type attrs = Avalue.attrs
type prop = Avalue.prop
type store = OSet.t AddrMap.t *
             VLSet.t AddrMap.t *
             HSet.t AddrMap.t *
             KSet.t AddrMap.t *
             ASet.t AddrMap.t *
             PSet.t AddrMap.t
  
let empty =
  (AddrMap.empty, AddrMap.empty, AddrMap.empty,
   AddrMap.empty, AddrMap.empty, AddrMap.empty)

let get k m = AddrMap.find k m
let get_objs k ((os, _, _, _, _, _) : store) =
  try get k os with Not_found -> OSet.empty
let get_vals k ((_, vs, _, _, _, _) : store) =
  try get k vs with Not_found -> VLSet.empty
let get_hands k ((_, _, hs, _, _, _) : store) =
  try get k hs with Not_found -> HSet.empty
let get_konts k ((_, _, _, ks, _, _) : store) =
  try get k ks with Not_found -> KSet.empty
let get_attrs k ((_, _, _, _, ats, _) : store) =
  try get k ats with Not_found -> ASet.empty
let get_props k ((_, _, _, _, _, ps) : store) =
  try get k ps with Not_found -> PSet.empty

let set = AddrMap.add
let set_objs addr objs (os, vs, hs, ks, ats, ps) =
  (set addr objs os, vs, hs, ks, ats, ps)
let set_vals addr vals (os, vs, hs, ks, ats, ps) =
  (os, set addr vals vs, hs, ks, ats, ps)
let set_hands addr hands (os, vs, hs, ks, ats, ps) =
  (os, vs, set addr hands hs, ks, ats, ps)
let set_konts addr konts (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, set addr konts ks, ats, ps)
let set_attrs addr attrs (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, ks, set addr attrs ats, ps)
let set_props addr props (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, ks, ats, set addr props ps)

let join_obj addr obj ((os, _, _, _, _, _) as sto) =
  let objs = try get addr os with Not_found -> OSet.empty in
  set_objs addr (OSet.add obj objs) sto
let join_val addr vl ((_, vs, _, _, _, _) as sto) =
  let vals = try get addr vs with Not_found -> VLSet.empty in
  set_vals addr (VLSet.add vl vals) sto
let join_obj_d addr od ((os, _, _, _, _, _) as sto) = match od with
  | O obj -> join_obj addr obj sto
  | OA a ->
    set_objs addr (OSet.union (get_objs a sto) (get_objs addr sto)) sto
let join_val_ld addr vld ((_, vs, _, _, _, _) as sto) = match vld with
  | VL vl -> join_val addr vl sto
  | VA a ->
    set_vals addr (VLSet.union (get_vals a sto) (get_vals addr sto)) sto
let join_hand addr hand ((_, _, hs, _, _, _) as sto) =
  let hands = try get addr hs with Not_found -> HSet.empty in
  set_hands addr (HSet.add hand hands) sto
let join_kont addr kont ((_, _, _, ks, _, _) as sto) =
  let konts = try get addr ks with Not_found -> KSet.empty in
  set_konts addr (KSet.add kont konts) sto
let join_attrs addr attrs ((_, _, _, _, ats, _) as sto) =
  let attrss = try get addr ats with Not_found -> ASet.empty in
  set_attrs addr (ASet.add attrs attrss) sto
let join_prop addr prop ((_, _, _, _, _, ps) as sto) =
  let props = try get addr ps with Not_found -> PSet.empty in
  set_props addr (PSet.add prop props) sto

let filter f (os, vs, hs, ks, ats, ps) =
  (AddrMap.filter f os,
   AddrMap.filter f vs,
   AddrMap.filter f hs,
   AddrMap.filter f ks,
   AddrMap.filter f ats,
   AddrMap.filter f ps)

let envstore_of_obj addrs (_, props) store =
  let _, env, store' =
    IdMap.fold
      (fun id prop (addr::addrs', env, store) -> match prop with
      | Data ({value=v}, _, _) ->
        let env' = IdMap.add id addr env in
        let store' = join_val addr v store in
        (addrs', env', store')
      | _ -> failwith "Non-data value in env_of_obj")
      props
      (addrs, IdMap.empty, store) in env, store'

(*
  let get_attr attr obj field store = match obj, field with
  | Obj (L.Con addr), String (L.Con s) ->
  let objs = get_obj addr store in
  ObjektSet.fold (fun elt acc -> get_attr
  | Obj _, String _ -> L.Top
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

  let get_attr' attr (attrs, props) store =
  if (not (IdMap.mem s props)) then Undef
  else (match (IdMap.find s props), attr with
  | Data (_, _, config), Config
  | Accessor (_, _, config), Config -> bool config
  | Data (_, enum, _), Enum
  | Accessor (_, enum, _), Enum -> bool enum
  | Data ({ writable = b; }, _, _), Writable -> bool b
  | Data ({ value = v; }, _, _), Value -> v
  | Accessor ({ getter = gv; }, _, _), Getter -> gv
  | Accessor ({ setter = sv; }, _, _), Setter -> sv
  | _ -> failwith "bad access of attribute"))

  let get_obj_attr attrs attr = match attrs, attr with
  | { proto=proto }, Proto -> proto
  | { extensible=extensible} , Extensible -> bool extensible
  | { code=Some code}, Code -> code
  | { code=None}, Code -> Null
  | { primval=Some primval}, Primval -> primval
  | { primval=None}, Primval ->
  failwith "[interp] Got Primval attr of None"
  | { klass=klass }, Klass -> String klass
  let rec get_prop p obj field store = match obj with
  | Null -> None
  | Obj (L.Con addr) -> (match get_obj addr store with
  | ({ proto = pvalue; }, props) ->
  try Some (IdMap.find field props)
  with Not_found -> get_prop p pvalue field store)
  | Obj _ -> None
  | _ -> failwith "get_prop on a non-object."
  let rec set_attr attr obj field newval store = match obj, field with
  | Obj (L.Con addr), String (L.Con f_str) -> (match get_obj addr store with
  | ({ extensible = ext; } as attrsv, props) ->
  if not (IdMap.mem f_str props) then
  if ext then
  let newprop = match attr with
  | Getter ->
  Accessor ({ getter = newval; setter = Undef; },  false, false)
  | Setter ->
  Accessor ({ getter = Undef; setter = newval; },  false, false)
  | Value ->
  Data ({ value = newval; writable = false; }, false, false)
  | Writable ->
  Data ({ value = Undef; writable = unbool newval }, false, false)
  | Enum ->
  Data ({ value = Undef; writable = false }, unbool newval, true)
  | Config ->
  Data ({ value = Undef; writable = false }, true, unbool newval) in
  let store =
  set_obj addr (attrsv, IdMap.add f_str newprop props) store in
  true, store
  else
  failwith "[interp] Extending inextensible object."
  else
  let newprop = match (IdMap.find f_str props), attr, newval with
          (* Writable true -> false when configurable is false *)
  | Data ({ writable = true } as d, enum, config), Writable, new_w ->
  Data ({ d with writable = unbool new_w }, enum, config)
  | Data (d, enum, true), Writable, new_w ->
  Data ({ d with writable = unbool new_w }, enum, true)
          (* Updating values only checks writable *)
  | Data ({ writable = true } as d, enum, config), Value, v ->
  Data ({ d with value = v }, enum, config)
          (* If we had a data property, update it to an accessor *)
  | Data (d, enum, true), Setter, setterv ->
  Accessor ({ getter = Undef; setter = setterv }, enum, true)
  | Data (d, enum, true), Getter, getterv ->
  Accessor ({ getter = getterv; setter = Undef }, enum, true)
          (* Accessors can update their getter and setter properties *)
  | Accessor (a, enum, true), Getter, getterv ->
  Accessor ({ a with getter = getterv }, enum, true)
  | Accessor (a, enum, true), Setter, setterv ->
  Accessor ({ a with setter = setterv }, enum, true)
          (* An accessor can be changed into a data property *)
  | Accessor (a, enum, true), Value, v ->
  Data ({ value = v; writable = false; }, enum, true)
  | Accessor (a, enum, true), Writable, w ->
  Data ({ value = Undef; writable = unbool w; }, enum, true)
          (* enumerable and configurable need configurable=true *)
  | Data (d, _, true), Enum, new_enum ->
  Data (d, unbool new_enum, true)
  | Data (d, enum, true), Config, new_config ->
  Data (d, enum, unbool new_config)
  | Data (d, enum, false), Config, Bool false ->
  Data (d, enum, false)
  | Accessor (a, enum, true), Config, new_config ->
  Accessor (a, enum, unbool new_config)
  | Accessor (a, enum, true), Enum, new_enum ->
  Accessor (a, unbool new_enum, true)
  | Accessor (a, enum, false), Config, Bool false ->
  Accessor (a, enum, false)
  | _ -> raise (PrimErr ([], String (L.Con "[interp] bad property set")))
  in
  let store =
  set_obj addr (attrsv, IdMap.add f_str newprop props) store in
  true, store)
  | Obj _, String _ -> false, store
  (* NRL: probably need to revisit the false here *)
  | _ -> raise (PrimErr ([], String (L.Con ("[interp] set-attr didn't get"
  ^ " an object and a string"))))
*)

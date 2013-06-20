open Lattices
open Collects
open Aobject
module VLJS = Ljs_values
module S = Astore
module SLJS = Store

let opt_map f o = match o with
  | Some a -> (f a)
  | None -> `Bot

let env_to_a env =
  Prelude.IdMap.fold
    (fun k v a -> begin
(*      print_endline (k^" --> "^(Ashared.string_of_addr (Ashared.I v))^"\n");*)
      Prelude.IdMap.add k (Ashared.I v) a end)
    env Prelude.IdMap.empty
let val_to_a (valu : VLJS.value) : AValue.t = match valu with
  | VLJS.Null -> `Null
  | VLJS.Undefined -> `Undef
  | VLJS.Num f -> `Num f
  | VLJS.String s -> `Str s
  | VLJS.True -> `True
  | VLJS.False -> `False
  | VLJS.ObjLoc l -> `Obj (Ashared.I l)
  | VLJS.Closure (e, xs, b) -> `Clos (env_to_a e, xs, b)
  | _ -> `Top
let attrsv_to_a ({ VLJS.code=c; VLJS.proto=p; VLJS.extensible=e;
                   VLJS.klass=k; VLJS.primval=pv } : VLJS.attrsv) : attrs =
  { code=opt_map val_to_a c; proto=val_to_a p; exten=AValue.bool e;
    klass=`Str k; primv=opt_map val_to_a pv }

let datav_to_a ({ VLJS.value=v; VLJS.writable=w } : VLJS.datav) : data =
  { value=val_to_a v; writable=AValue.bool w }

let accessorv_to_a
    ({ VLJS.getter=g; VLJS.setter=s } : VLJS.accessorv) : accessor =
  { getter=val_to_a g; setter=val_to_a s }

let propv_to_a (pv : VLJS.propv) : prop = match pv with
  | VLJS.Data (dv, b0, b1) -> Data (datav_to_a dv, AValue.bool b0, AValue.bool b1)
  | VLJS.Accessor (av, b0, b1) ->
    Accessor (accessorv_to_a av, AValue.bool b0, AValue.bool b1)

let objectv_to_a ((asv, pvmap) : VLJS.objectv) : objekt =
  (attrsv_to_a asv,
   Prelude.IdMap.fold
     (fun k v m -> Prelude.IdMap.add k (propv_to_a v) m)
     pvmap
     Prelude.IdMap.empty)

let store_to_a (((omap, m), (vmap, n)) : VLJS.store) : S.store =
  SLJS.LocMap.fold
     (fun k v a -> AddrMap.add (Ashared.I k) (OSet.singleton (objectv_to_a v)) a)
     omap
     AddrMap.empty,
   SLJS.LocMap.fold
     (fun k v a -> begin
(*       print_endline ((Ashared.string_of_addr (Ashared.I k))^" --> "^(Lattices.AValue.string_of (val_to_a v))^"\n");*)
       AddrMap.add (Ashared.I k) (VSet.singleton (val_to_a v)) a end)
     vmap
     AddrMap.empty,
   AddrMap.empty,
   AddrMap.empty,
   AddrMap.empty,
   AddrMap.empty

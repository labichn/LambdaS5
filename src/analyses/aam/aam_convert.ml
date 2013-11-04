open Aam_lattices
open Aam_collects
open Aam_object
open Aam_store
module VLJS = Ljs_values
module SLJS = Store

let opt_map f o = match o with
  | Some a -> (f a)
  | None -> `Bot

let env_to_a env =
  Prelude.IdMap.fold
    (fun k v a -> Prelude.IdMap.add k (Aam_shared.E v) a)
    env Prelude.IdMap.empty

let val_to_a (valu : VLJS.value) : AValue.t = match valu with
  | VLJS.Null -> `Null
  | VLJS.Undefined -> `Undef
  | VLJS.Num f -> `Num f
  | VLJS.String s -> `Str s
  | VLJS.True -> `True
  | VLJS.False -> `False
  | VLJS.ObjLoc l -> `Obj (Aam_shared.E l)
  | VLJS.Closure (e, xs, b) -> `Clos (env_to_a e, xs, b)
  | _ -> `Top

let attrsv_to_a { VLJS.code=c; VLJS.proto=p; VLJS.extensible=e;
                   VLJS.klass=k; VLJS.primval=pv } : attrs =
  { code=opt_map val_to_a c; proto=val_to_a p; exten=AValue.bool e;
    klass=`Str k; primv=opt_map val_to_a pv }

let datav_to_a { VLJS.value=v; VLJS.writable=w } =
  { value=val_to_a v; writable=AValue.bool w }

let accessorv_to_a { VLJS.getter=g; VLJS.setter=s } =
  { getter=val_to_a g; setter=val_to_a s }

let propv_to_a pv = match pv with
  | VLJS.Data (dv, b0, b1) ->
    Data (datav_to_a dv, AValue.bool b0, AValue.bool b1)
  | VLJS.Accessor (av, b0, b1) ->
    Accessor (accessorv_to_a av, AValue.bool b0, AValue.bool b1)

let objectv_to_a (asv, pvmap) =
  (attrsv_to_a asv,
   Prelude.IdMap.fold
     (fun k v m -> PropMap.unsafe_set (`Str k) (propv_to_a v) m)
     pvmap
     PropMap.empty)

let store_to_a ((omap, m), (vmap, n)) =
  SLJS.LocMap.fold
    (fun k v a ->
      OStore.unsafe_set (Aam_shared.E k) (OSet.singleton (objectv_to_a v)) a)
    omap
    OStore.empty,
  VStore.empty,
  SLJS.LocMap.fold
    (fun k v a ->
      SStore.unsafe_set (Aam_shared.E k) (VSet.singleton (val_to_a v)) a)
    vmap
    SStore.empty,
  HStore.empty,
  KStore.empty,
  AStore.empty,
  PStore.empty

module V = Avalues
module VLJS = Ljs_values
module IS = IntStore
module SLJS = Store
module S = Shared

(* many are identity maps for now, but will be necessary as avalues change *)
(* known issue: referential equality is not preserved in heap *)

let opt_map f o = match o with
  | Some a -> Some (f a)
  | None -> None

let env_to_a (env : SLJS.loc S.IdMap.t) : V.env = env
let env_to_ljs (env : V.env) : SLJS.loc S.IdMap.t = env
let val_to_a (valu : VLJS.value) : V.avalue = match valu with
  | VLJS.Null -> V.Null
  | VLJS.Undefined -> V.Undefined
  | VLJS.Num f -> V.Num f
  | VLJS.String s -> V.String s
  | VLJS.True -> V.True
  | VLJS.False -> V.False
  | VLJS.ObjLoc l -> V.ObjLoc l
  | VLJS.Closure (e, xs, b) -> V.Closure (e, xs, b)
let val_to_ljs (valu : V.avalue) : VLJS.value = match valu with
  | V.Null -> VLJS.Null
  | V.Undefined -> VLJS.Undefined
  | V.Num f -> VLJS.Num f
  | V.String s -> VLJS.String s
  | V.True -> VLJS.True
  | V.False -> VLJS.False
  | V.ObjLoc l -> VLJS.ObjLoc l
  | V.Closure (e, xs, b) -> VLJS.Closure (e, xs, b)
let attrsv_to_a ({ VLJS.code=c; VLJS.proto=p; VLJS.extensible=e;
                   VLJS.klass=k; VLJS.primval=pv } : VLJS.attrsv) : V.attrsv =
  { V.code=opt_map val_to_a c; V.proto=val_to_a p; V.extensible=e;
    V.klass=k; V.primval=opt_map val_to_a pv }
let attrsv_to_ljs ({ V.code=c; V.proto=p; V.extensible=e;
                     V.klass=k; V.primval=pv } : V.attrsv) : VLJS.attrsv =
  { VLJS.code=opt_map val_to_ljs c; VLJS.proto=val_to_ljs p;
    VLJS.extensible=e; VLJS.klass=k; VLJS.primval=opt_map val_to_ljs pv }
let datav_to_a ({ VLJS.value=v; VLJS.writable=w } : VLJS.datav) : V.datav =
  { V.value=val_to_a v; V.writable=w }
let datav_to_ljs ({ V.value=v; V.writable=w } : V.datav) : VLJS.datav =
  { VLJS.value=val_to_ljs v; VLJS.writable=w }
let accessorv_to_a
    ({ VLJS.getter=g; VLJS.setter=s } : VLJS.accessorv) : V.accessorv =
  { V.getter=val_to_a g; V.setter=val_to_a s }
let accessorv_to_ljs
    ({ V.getter=g; V.setter=s } : V.accessorv) : VLJS.accessorv =
  { VLJS.getter=val_to_ljs g; VLJS.setter=val_to_ljs s }
let propv_to_a (pv : VLJS.propv) : V.propv = match pv with
  | VLJS.Data (dv, b0, b1) -> V.Data (datav_to_a dv, b0, b1)
  | VLJS.Accessor (av, b0, b1) -> V.Accessor (accessorv_to_a av, b0, b1)
let propv_to_ljs (pv : V.propv) : VLJS.propv = match pv with
  | V.Data (dv, b0, b1) -> VLJS.Data (datav_to_ljs dv, b0, b1)
  | V.Accessor (av, b0, b1) -> VLJS.Accessor (accessorv_to_ljs av, b0, b1)
let objectv_to_a ((asv, pvmap) : VLJS.objectv) : V.objectv =
  (attrsv_to_a asv,
   S.IdMap.fold
     (fun k v m -> S.IdMap.add k (propv_to_a v) m)
     pvmap
     S.IdMap.empty)
let objectv_to_ljs ((asv, pvmap) : V.objectv) : VLJS.objectv =
  (attrsv_to_ljs asv,
   S.IdMap.fold
     (fun k v m -> S.IdMap.add k (propv_to_ljs v) m)
     pvmap
     S.IdMap.empty)
let store_to_a (((omap, m), (vmap, n)) : VLJS.store) : IS.store =
  ((S.LocMap.fold
      (fun k v a -> S.LocMap.add k (objectv_to_a v) a)
      omap
      S.LocMap.empty,
    m),
   (S.LocMap.fold
      (fun k v a -> S.LocMap.add k (val_to_a v) a)
      vmap
      S.LocMap.empty,
    n),
   IS.empty_t,
   IS.empty_t)
let store_to_ljs (((omap, m), (vmap, n), _, _) : IS.store) : VLJS.store =
  ((S.LocMap.fold
      (fun k v a -> S.LocMap.add k (objectv_to_ljs v) a)
      omap
      S.LocMap.empty,
    m),
   (S.LocMap.fold
      (fun k v a -> S.LocMap.add k (val_to_ljs v) a)
      vmap
      S.LocMap.empty,
    n))

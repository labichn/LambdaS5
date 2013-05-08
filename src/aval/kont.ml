module GC = Ljs_gc
module P = Prelude
module S = Ljs_syntax
module ST = Store
module V = Ljs_values
module LocSet = ST.LocSet

type id = string

(* aval continuations *)
type akont =
| Mt
| SetBang of ST.loc * ST.loc
| GetAttr  of S.pattr * S.exp * ST.loc
| GetAttr2 of S.pattr * V.value * ST.loc
| SetAttr  of S.pattr * S.exp * S.exp * ST.loc
| SetAttr2 of S.pattr * S.exp * V.value * ST.loc
| SetAttr3 of S.pattr * V.value * V.value * ST.loc
| GetObjAttr of S.oattr * ST.loc
| SetObjAttr  of S.oattr * S.exp * ST.loc
| SetObjAttr2 of S.oattr * V.value * ST.loc
| GetField  of P.Pos.t * S.exp * S.exp * V.env * ST.loc
| GetField2 of P.Pos.t * S.exp * V.value * V.env * ST.loc
| GetField3 of P.Pos.t * V.value * V.value * V.env * ST.loc
| GetField4 of V.env * ST.loc
| SetField  of P.Pos.t * S.exp * S.exp * S.exp * V.env * ST.loc
| SetField2 of P.Pos.t * S.exp * S.exp * V.value * V.env * ST.loc
| SetField3 of P.Pos.t * S.exp * V.value * V.value * V.env * ST.loc
| SetField4 of P.Pos.t * V.value * V.value * V.value * V.env * ST.loc
| SetField5 of V.env * ST.loc
| OwnFieldNames of ST.loc
| DeleteField  of P.Pos.t * S.exp * ST.loc
| DeleteField2 of P.Pos.t * V.value * ST.loc
| OpOne of string * ST.loc
| OpTwo  of string * S.exp * ST.loc
| OpTwo2 of string * V.value * ST.loc
| If of V.env * S.exp * S.exp * ST.loc
| App  of P.Pos.t * V.env * S.exp list * ST.loc
| App2 of P.Pos.t * V.value * V.env * V.value list * S.exp list * ST.loc
| App3 of V.env * ST.loc
| Seq of S.exp * ST.loc
| Let of id * S.exp * ST.loc
| Let2 of V.env * ST.loc
| Rec of ST.loc * S.exp * ST.loc
| Label of id * V.env * ST.loc
| Break of id * ST.loc
| TryCatch  of P.Pos.t * S.exp * V.env * ST.loc
| TryCatch2 of P.Pos.t * V.value * V.env * ST.loc
| TryCatch3 of V.env * ST.loc
| TryFinally  of S.exp * V.env * ST.loc
| TryFinally2 of exn * V.env * ST.loc
| Throw of ST.loc
| Eval  of P.Pos.t * S.exp * ST.loc
| Eval2 of P.Pos.t * V.value * ST.loc
| Eval3 of ST.loc
| Hint of ST.loc
| Object  of (string * S.prop) list * ST.loc
| Object2 of V.attrsv * (string * S.prop) list *
    (string * V.propv) list * ST.loc
| Attrs of string * (string * S.exp) list * (string * V.value) list *
    string * bool * ST.loc
| DataProp of string * bool * bool * bool * ST.loc
| AccProp  of string * S.exp * bool * bool * ST.loc
| AccProp2 of string * V.value * bool * bool * ST.loc

(* for control flow *)
let shed k = match k with
  | SetBang (_, k) -> k
  | GetAttr (_, _, k) -> k
  | GetAttr2 (_, _, k) -> k
  | SetAttr (_, _, _, k) -> k
  | SetAttr2 (_, _, _, k) -> k
  | SetAttr3 (_, _, _, k) -> k
  | GetObjAttr (_, k) -> k
  | SetObjAttr (_, _, k) -> k
  | SetObjAttr2 (_, _, k) -> k
  | GetField (_, _, _, _, k) -> k
  | GetField2 (_, _, _, _, k) -> k
  | GetField3 (_, _, _, _, k) -> k
  | GetField4 (_, k) -> k
  | SetField (_, _, _, _, _, k) -> k
  | SetField2 (_, _, _, _, _, k) -> k
  | SetField3 (_, _, _, _, _, k) -> k
  | SetField4 (_, _, _, _, _, k) -> k
  | SetField5 (_, k) -> k
  | OwnFieldNames k -> k
  | DeleteField (_, _, k) -> k
  | DeleteField2 (_, _, k) -> k
  | OpOne (_, k) -> k
  | OpTwo (_, _, k) -> k
  | OpTwo2 (_, _, k) -> k
  | Mt -> ST.dummy_loc
  | If (_, _, _, k) -> k
  | App (_, _, _, k) -> k
  | App2 (_, _, _, _, _, k) -> k
  | App3 (_, k) -> k
  | Seq (_, k) -> k
  | Let (_, _, k) -> k
  | Let2 (_, k) -> k
  | Rec (_, _, k) -> k
  | Break (_, k) -> k
  | TryCatch (_, _, _, k) -> k
  | TryCatch2 (_, _, _, k) -> k
  | TryCatch3 (_, k) -> k
  | TryFinally (_, _, k) -> k
  | TryFinally2 (_, _, k) -> k
  | Throw k -> k
  | Eval (_, _, k) -> k
  | Eval2 (_, _, k) -> k
  | Eval3 k -> k
  | Hint k -> k
  | Object (_, k) -> k
  | Object2 (_, _, _, k) -> k
  | Attrs (_, _, _, _, _, k) -> k
  | DataProp (_, _, _, _, k) -> k
  | AccProp (_, _, _, _, k) -> k
  | AccProp2 (_, _, _, _, k) -> k
  | Label (_, _, k) -> k

let string_of_kont k = match k with
  | SetBang (_, _) -> "k.setbang"
  | GetAttr (_, _, _) -> "k.getattr"
  | GetAttr2 (_, _, _) -> "k.getattr2"
  | SetAttr (_, _, _, _) -> "k.setattr"
  | SetAttr2 (_, _, _, _) -> "k.setattr2"
  | SetAttr3 (_, _, _, _) -> "k.setattr3"
  | GetObjAttr (_, _) -> "k.getobjattr"
  | SetObjAttr (_, _, _) -> "k.setobjattr"
  | SetObjAttr2 (_, _, _) -> "k.setobjattr2"
  | GetField (_, _, _, _, _) -> "k.getfield"
  | GetField2 (_, _, _, _, _) -> "k.getfield2"
  | GetField3 (_, _, _, _, _) -> "k.getfield3"
  | GetField4 (_, _) -> "k.getfield4"
  | SetField (_, _, _, _, _, _) -> "k.setfield"
  | SetField2 (_, _, _, _, _, _) -> "k.setfield2"
  | SetField3 (_, _, _, _, _, _) -> "k.setfield3"
  | SetField4 (_, _, _, _, _, _) -> "k.setfield4"
  | SetField5 (_, _) -> "k.setfield5"
  | OwnFieldNames _ -> "k.ownfieldnames"
  | DeleteField (_, _, _) -> "k.deletefield"
  | DeleteField2 (_, _, _) -> "k.deletefield2"
  | OpOne (_, _) -> "k.opone"
  | OpTwo (_, _, _) -> "k.optwo"
  | OpTwo2 (_, _, _) -> "k.optwo2"
  | Mt -> "k.mt"
  | If (_, _, _, _) -> "k.if"
  | App (_, _, _, _) -> "k.app"
  | App2 (_, _, _, _, _, _) -> "k.app2"
  | App3 (_, _) -> "k.app3"
  | Seq (_, _) -> "k.seq"
  | Let (_, _, _) -> "k.let"
  | Let2 (_, _) -> "k.let2"
  | Rec (_, _, _) -> "k.rec"
  | Break (label, _) -> "k.break: "^label
  | TryCatch (_, _, _, _) -> "k.trycatch"
  | TryCatch2 (_, _, _, _) -> "k.trycatch2"
  | TryCatch3 (_, _) -> "k.trycatch3"
  | TryFinally (_, _, _) -> "k.tryfinally"
  | TryFinally2 (_, _, _) -> "k.tryfinally2"
  | Throw _ -> "k.throw"
  | Eval (_, _, _) -> "k.eval"
  | Eval2 (_, _, _) -> "k.eval2"
  | Eval3 _ -> "k.eval3"
  | Hint _ -> "k.hint"
  | Object (_, _) -> "k.object"
  | Object2 (_, _, _, _) -> "k.object2"
  | Attrs (_, _, _, _, _, _) -> "k.attrs"
  | DataProp (_, _, _, _, _) -> "k.dataprop"
  | AccProp (_, _, _, _, _) -> "k.accprop"
  | AccProp2 (_, _, _, _, _) -> "k.accprop2"
  | Label (_, _, _) -> "k.label"

let locs_of_values vs a =
  List.fold_left (fun a n -> (GC.locs_of_value n)::a) a vs

let locs_of_opt ox locs_of_x = match ox with
  | Some v -> locs_of_x v
  | None -> LocSet.empty

let locs_of_opt_val ov = locs_of_opt ov GC.locs_of_value

let locs_of_propv pv = match pv with
  | V.Data ({ V.value=v }, _, _) -> GC.locs_of_value v
  | V.Accessor ({ V.getter=gv; V.setter=sv }, _, _) ->
    LocSet.union (GC.locs_of_value gv) (GC.locs_of_value sv)

let locs_of_propvs pvs a = List.fold_left (fun a (_, n) -> (locs_of_propv n)::a) a pvs

let locs_of_attrsv av =
  let { V.code=ov; V.proto=v; V.primval=ov' } = av in
  LocSet.unions [locs_of_opt_val ov; GC.locs_of_value v; locs_of_opt_val ov']

let rec locs_of_kont ko : LocSet.t = match ko with
  | SetBang (l, k) -> LocSet.union (LocSet.singleton l) (LocSet.singleton k)
  | GetAttr (_, _, k) -> LocSet.singleton k
  | GetAttr2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (LocSet.singleton k)
  | SetAttr (_, _, _, k) -> LocSet.singleton k
  | SetAttr2 (_, _, v, k) -> LocSet.union (GC.locs_of_value v) (LocSet.singleton k)
  | SetAttr3 (_, v1, v2, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; LocSet.singleton k]
  | GetObjAttr (_, k) -> LocSet.singleton k
  | SetObjAttr (_, _, k) -> LocSet.singleton k
  | SetObjAttr2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (LocSet.singleton k)
  | GetField (_, _, _, e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | GetField2 (_, _, v, e, k) -> LocSet.unions [GC.locs_of_value v; GC.locs_of_env e; LocSet.singleton k]
  | GetField3 (_, v1, v2, e, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; GC.locs_of_env e; LocSet.singleton k]
  | GetField4 (e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | SetField (_, _, _, _, e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | SetField2 (_, _, _, v, e, k) ->
    LocSet.unions [GC.locs_of_value v; GC.locs_of_env e; LocSet.singleton k]
  | SetField3 (_, _, v1, v2, e, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; GC.locs_of_env e; LocSet.singleton k]
  | SetField4 (_, v1, v2, v3, e, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; GC.locs_of_value v3; GC.locs_of_env e;
                   LocSet.singleton k]
  | SetField5 (e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | OwnFieldNames k -> LocSet.singleton k
  | DeleteField (_, _, k) -> LocSet.singleton k
  | DeleteField2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (LocSet.singleton k);
  | OpOne (_, k) -> LocSet.singleton k
  | OpTwo (_, _, k) -> LocSet.singleton k
  | OpTwo2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (LocSet.singleton k)
  | If (e, _, _, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | App (_, e, _, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | App2 (_, v, e, vs, _, k) ->
    LocSet.unions (locs_of_values vs [GC.locs_of_value v; GC.locs_of_env e; LocSet.singleton k])
  | App3 (e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | Seq (_, k) -> LocSet.singleton k
  | Let (_, _, k) -> LocSet.singleton k
  | Let2 (_, k) -> LocSet.singleton k
  | Rec (l, _, k) -> LocSet.add l (LocSet.singleton k)
  | Break (_, k) -> LocSet.singleton k
  | TryCatch (_, _, e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | TryCatch2 (_, v, e, k) -> LocSet.unions [GC.locs_of_value v; GC.locs_of_env e; LocSet.singleton k]
  | TryCatch3 (e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | TryFinally (_, e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | TryFinally2 (_, e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | Throw k -> LocSet.singleton k
  | Eval (_, _, k) -> LocSet.singleton k
  | Eval2 (_, _, k) -> LocSet.singleton k
  | Eval3 k -> LocSet.singleton k
  | Hint k -> LocSet.singleton k
  | Object (_, k) -> LocSet.singleton k
  | Object2 (attrsv, _, propvs, k) ->
    LocSet.unions (locs_of_propvs propvs [locs_of_attrsv attrsv; LocSet.singleton k])
  | Attrs (_, _, nvs, _, _, k) ->
    LocSet.unions (List.fold_left (fun a (_, n) -> (GC.locs_of_value n)::a) [LocSet.singleton k] nvs)
  | DataProp (_, _, _, _, k) -> LocSet.singleton k
  | AccProp (_, _, _, _, k) -> LocSet.singleton k
  | AccProp2 (_, v, _, _, k) -> LocSet.union (GC.locs_of_value v) (LocSet.singleton k)
  | Label (_, e, k) -> LocSet.union (GC.locs_of_env e) (LocSet.singleton k)
  | Mt -> LocSet.empty

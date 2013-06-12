open Collects

type context = Acontext.context
type store = Astore.store
type addr = Ashared.addr
type time = Ashared.time
type exp = Ljs_syntax.exp
type prop = Avalue.prop
type attrs = Avalue.attrs
type value = Avalue.value_ld
type simple_value = Avalue.value
type objekt = Avalue.objekt_d
type kont = Akont.kont
type hand = Ahandle.hand
type env = addr Prelude.IdMap.t
let env_add = Prelude.IdMap.add
let env_find = Prelude.IdMap.find
let env_filter = Prelude.IdMap.filter

type version = int
type state = context * store
type 'a binding = addr * 'a
type delta =
  objekt binding list *
    value binding list *
    hand binding list *
    kont binding list *
    attrs binding list *
    prop binding list
let mtd : delta = ([], [], [], [], [], [])
let join_obj a o (os, vs, hs, ks, ats, ps) = ((a, o)::os, vs, hs, ks, ats, ps)
let join_val a v (os, vs, hs, ks, ats, ps) = (os, (a, v)::vs, hs, ks, ats, ps)
let join_hand a h (os, vs, hs, ks, ats, ps) = (os, vs, (a, h)::hs, ks, ats, ps)
let join_kont a k (os, vs, hs, ks, ats, ps) = (os, vs, hs, (a, k)::ks, ats, ps)
let join_attrs a at (os, vs, hs, ks, ats, ps) = (os, vs, hs, ks, (a, at)::ats, ps)
let join_prop a p (os, vs, hs, ks, ats, ps) = (os, vs, hs, ks, ats, (a, p)::ps)

module ContextDelta = struct
  type t = context * delta
  let compare = Pervasives.compare
end
(* output of step *)
module CDSet = Set.Make(ContextDelta)

module VersionedContext = struct
  type t = context * version
  let compare = Pervasives.compare
end
(* seen set *)
module VCSet = Set.Make(VersionedContext)

(* graph stuff *)
module Vert_Context = struct
  type t = context
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end
module G = Graph.Persistent.Digraph.ConcreteBidirectional (Vert_Context)

module SH = Ashared
module C = Acontext
module L = Clattice
module ST = Kcfa (* ST read strategy *)
module V = Avalue
module H = Ahandle
module K = Akont
module E = Aerror
module SYN = Ljs_syntax
module S = Astore

type system = VCSet.t * CSet.t * store * store list * version

(**
 * Analyzes the given expression.
 * @param k           the k in kCFA
 * @param op1         unary primitive operation
 * @param op2         binary primitive operation
 * @param exp         the expression to analyze
 * @param desugar     desugars a string of JavaScript into an λS5 exp
 * @param init_env    the initial JS environment
 * @param init_store  the initial JS store
 * @param log         whether or not to log to stdout
 * @return a digraph of contexts
 *)
let analyze
    (k : int)
    (op1 : store -> string -> simple_value -> simple_value)
    (op2 : store -> string -> simple_value -> simple_value -> simple_value)
    (exp : exp)
    (desugar : (string -> Ljs_syntax.exp))
    (init_env : env)
    (init_store : store)
    (log : bool) : G.t =
  begin
    if log then print_string "Analyzing... ";
    
    let kcfa_tick = ST.tick k in
    let kcfa_alloc = ST.alloc k in
    let kcfa_alloc' = ST.alloc' k in
    let kcfa_alloc_kont = ST.alloc_kont k in
    let kcfa_alloc_hand = ST.alloc_hand k in

    let inject exp env store = begin
      if log then print_endline "injecting... ";
      let t0 = [] in
      let handl0, kont0 = H.zero t0, K.zero t0 in
      let addr0 = SH.T t0 in
      let store0 =
        Astore.join_kont addr0 kont0 (Astore.join_hand addr0 handl0 store) in
      let context0 = C.Ev (exp, env, addr0, addr0, t0) in
      (VCSet.empty, CSet.singleton context0, store0, [], 0)
    end in

    let append_deltas ds =
      List.fold_left
        (fun (vs', os', hs', ks', ats', ps') (vs, os, hs, ks, ats, ps) ->
          (vs @ vs', os @ os', hs @ hs', ks @ ks', ats @ ats', ps @ ps'))
        mtd ds in

    let replay_delta ((ods, vds, hds, kds, atds, pds) : delta)
        ((os, vs, hs, ks, ats, ps) as store : store) : store * bool =
      let force_val vld store = match vld with
        | V.VL vl -> VLSet.singleton vl
        | V.VA addr -> Astore.get_vals addr store in
      let force_obj old store = match old with
        | V.O obj -> OSet.singleton obj
        | V.OA addr -> Astore.get_objs addr store in
      let force_join ds map empty union force =
        List.fold_left
          (fun ((_, m) as acc) (a, xd) ->
            let xs = force xd store in
            let xs' = try AddrMap.find a m with Not_found -> empty in
            if xs = xs' then acc
            else true, AddrMap.add a (union xs xs') m)
          (false, map) ds in
      let join ds map empty mem add =
        List.fold_left
          (fun ((_, m) as acc) (a, x) ->
            let xs = try AddrMap.find a m with Not_found -> empty in
            if mem x xs then acc
            else true, AddrMap.add a (add x xs) m)
          (false, map) ds in
      let ochange, os' = force_join ods os OSet.empty OSet.union force_obj in
      let vchange, vs' = force_join vds vs VLSet.empty VLSet.union force_val in
      let hchange, hs' = join hds hs HSet.empty HSet.mem HSet.add in
      let kchange, ks' = join kds ks KSet.empty KSet.mem KSet.add in
      let atchange, ats' = join atds ats ASet.empty ASet.mem ASet.add in
      let pchange, ps' = join pds ps PSet.empty PSet.mem PSet.add in
      ((os', vs', hs', ks', ats', ps'),
       ochange || vchange || hchange || kchange || atchange || pchange) in
    
    (* This is a direct tranlation of COAAM, section 5.2, save for splitting
     * deltas from I and holding onto the predecessor for graph generation. *)
    let rec transition (seen, frontier, store, stores, version) graph = begin
      if log then print_endline "stepping...";
      let i, deltas =
        CSet.fold
          (fun con (i, ds) ->
            let succs = step con store in
            CDSet.fold (fun (c,d) (i,ds)->(con, c)::i, d::ds) succs (i, ds))
          frontier ([], []) in
      let store', changed = replay_delta (append_deltas deltas) store in
      let version', stores' =
        if changed then version+1, store'::stores else version, stores in
      let seen', frontier', graph' =
        List.fold_left
          (fun ((seen', frontier', graph') as acc) (pred, succ) ->
            let cv = (succ, version') in
            if not (VCSet.mem cv seen') then
              (VCSet.add cv seen',
               CSet.add succ frontier',
               G.add_edge graph' pred succ)
            else acc)
          (seen, CSet.empty, graph) i in
      if CSet.cardinal frontier' > 0 then
        transition (seen', frontier', store', stores', version') graph'
      else begin if log then print_endline "done.\n"; graph' end
    end
      
    and step context store =
      begin
        if log then print_endline ("  "^(C.string_of context)) ;
        let topv = V.VL L.Top in
        let conv v = V.VL (L.Con v) in
        let single = CDSet.singleton in
        let tick ?(old_kont=None) ?(old_hand=None) (ccon, delta) =
          ccon (kcfa_tick context store old_kont old_hand), delta in
        let with_kont ?(old_kont=None) ?(old_hand=None) (ccon, delta) kont =
          let kaddr = kcfa_alloc_kont context store old_kont old_hand in
          ccon kaddr, join_kont kaddr kont delta in
        let with_hand ?(old_kont=None) ?(old_hand=None) (ccon, delta) hand =
          let haddr = kcfa_alloc_hand context store old_kont old_hand in
          ccon haddr (SH.addr0), join_hand haddr hand delta in
        let with_vld ?(old_kont=None) ?(old_hand=None) ckont vld =
          let addr = kcfa_alloc context store old_kont old_hand in addr, ckont addr in
        let val_branch addr acc cds_folder =
          let vls = S.get_vals addr store in VLSet.fold cds_folder vls acc in
        match context with
        | C.Ans _ -> CDSet.empty
        | C.Ap (p, V.VL L.Top, vlds, h, k, t) ->
          single (tick (C.co p topv h k, mtd))
        | C.Ap (p, V.VA a, vlds, h, k, t) ->
          val_branch a CDSet.empty
            (fun vl cds -> CDSet.add (tick (C.ap p (V.VL vl) vlds h k, mtd)) cds)
        | C.Ap (p, V.VL (L.Con (V.Clos (env, xs, body))), vlds, h, k, t) ->
          if (List.length vlds) != (List.length xs) then
            E.arity_mismatch_err p xs vlds
          else
            let rec foldr_3 f b xs ys zs = match xs, ys, zs with
              | [], [], [] -> b
              | x::xs', y::ys', z::zs' -> f x y z (foldr_3 f b xs' ys' zs')
              | _, _, _ -> failwith "different length lists, you doofus" in
            let addrs = kcfa_alloc' context store None None in
            let env', delta =
              foldr_3
                (fun x a lvd (env', s) -> env_add x a env', join_val a lvd s)
                (env, mtd) xs addrs vlds in
            single (tick (C.ev body env' h k, delta))
        | C.Ap (p, V.VL (L.Con (V.Obj a)), vlds, h, k, t) ->
          (* REVISIT with better object model *)
          single (tick (C.ap p (V.VL L.Top) vlds h k, mtd))
        | C.Ap (p, f, vlds, h, k, t) ->
          failwith (E.interp_error p ("Applied non-function: "^(V.string_of_valueld f)))
        | C.Ev (SYN.Undefined p, _, h, k, t) ->
          single (tick (C.co p (conv V.Undef) h k, mtd))
        | C.Ev (SYN.Null p, _, h, k, t) ->
          single (tick (C.co p (conv V.Null) h k, mtd))
        | C.Ev (SYN.String (p, s), _, h, k, t) ->
          single (tick (C.co p (conv (V.String (L.Con s))) h k, mtd))
        | C.Ev (SYN.Num (p, n), _, h, k, t) ->
          single (tick (C.co p (conv (V.Num (L.Con n))) h k, mtd))
        | C.Ev (SYN.True p, _, h, k, t) ->
          single (tick (C.co p (conv (V.Bool (L.Con true))) h k, mtd))
        | C.Ev (SYN.False p, _, h, k, t) ->
          single (tick (C.co p (conv (V.Bool (L.Con false))) h k, mtd))
        | C.Ev (SYN.Id (p, x), env, h, k, t) ->
          single (tick (C.co p (V.VA (env_find x env)) h k, mtd))
        | C.Ev (SYN.Lambda (p, xs, body), env, h, k, t) ->
          let free = SYN.free_vars body in
          let env' = env_filter (fun var _ -> Prelude.IdSet.mem var free) env in
          single (tick (C.co p (conv (V.Clos (env', xs, body))) h k, mtd))
        | C.Ev (SYN.SetBang (p, x, new_val_exp), env, h, k, t) ->
          (match try Some (env_find x env) with Not_found -> None with
          | Some a -> single (tick (with_kont (C.ev new_val_exp env h, mtd)
                                      (K.SetBang (p, t, a, k))))
          | None -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (Prelude.Pos.string_of_pos p)))
        | C.Ev (SYN.Object (p, attrs, props), env, h, k, t) ->
          (* REVISIT with better object model *)
          single (tick (C.co p (V.VL L.Top) h k, mtd))
(*          single (tick (with_kont (C.eva p attrs env h, mtd)
                          (K.Object (p, t, props, env, k))*)
        | C.Ev (SYN.GetAttr (p, attr, obj, field), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.GetAttr (p, t, attr, field, env, k))))*)
        | C.Ev (SYN.SetAttr (p, pattr, obj, field, next), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.SetAttr (p, t, pattr, field, next, env, k))))*)
        | C.Ev (SYN.GetObjAttr (p, oattr, obj), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.GetObjAttr (p, t, oattr, env, k))))*)
        | C.Ev (SYN.SetObjAttr (p, oattr, obj, next), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.SetObjAttr (p, t, oattr, next, env, k))))*)
        | C.Ev (SYN.GetField (p, obj, field, body), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.GetField (p, t, field, body, env, k))))*)
        | C.Ev (SYN.OwnFieldNames (p, obj), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd) (K.OwnFieldNames (p, t, k))))*)
        | C.Ev (SYN.DeleteField (p, obj, field), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.DeleteField (p, t, field, env, k))))*)
        | C.Ev (SYN.SetField (p, obj, field, next, body), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.SetField (p, t, field, next, body, env, k))))*)
        | C.Ev (SYN.Op1 (p, name, arg), env, h, k, t) ->
          single (tick (with_kont (C.ev arg env h, mtd)
                          (K.OpOne (p, t, name, env, k))))
        | C.Ev (SYN.Op2 (p, name, arg1, arg2), env, h, k, t) ->
          single (tick (with_kont (C.ev arg1 env h, mtd)
                          (K.OpTwo (p, t, name, arg2, env, k))))
        | C.Ev (SYN.If (p, pred, than, elze), env, h, k, t) ->
          single (tick (with_kont (C.ev pred env h, mtd)
                          (K.If (p, t, env, than, elze, k))))
        | C.Ev (SYN.App (p, func, args), env, h, k, t) ->
          single (tick (with_kont (C.ev func env h, mtd)
                          (K.App (p, t, env, args, k))))
        | C.Ev (SYN.Seq (p, left, right), env, h, k, t) ->
          single (tick (with_kont (C.ev left env h, mtd)
                          (K.Seq (p, t, right, env, k))))
        | C.Ev (SYN.Let (p, name, expr, body), env, h, k, t) ->
          single (tick (with_kont (C.ev expr env h, mtd)
                          (K.Let (p, t, name, body, env, k))))
        | C.Ev (SYN.Rec (p, name, expr, body), env, h, k, t) ->
          let new_loc = kcfa_alloc context store None None in
          let env' = env_add name new_loc env in
          (* REVISIT: do I need to join in an undef here? I don't think so.
          let delta = join_val new_loc (conv V.Undef) mtd in *)
          single (tick (with_kont (C.ev expr env' h, mtd)
                          (K.Rec (p, t, new_loc, body, env', k))))
        | C.Ev (SYN.Label (p, name, exp), env, h, k, t) ->
          single (tick (with_hand (C.ev exp env, mtd)
                          (H.Lab (p, t, name, env, k, h))))
        | C.Ev (SYN.Break (p, label, expr), env, h, k, t) ->
          single (tick (with_kont (C.ev expr env h, mtd)
                          (K.Break (p, t, label, env, k))))
        | C.Ev (SYN.TryCatch (p, body, catch), env, h, k, t) ->
          single (tick (with_hand (C.ev body env, mtd)
                          (H.Cat (p, t, catch, env, k, h))))
        | C.Ev (SYN.TryFinally (p, body, fin), env, h, k, t) ->
          single (tick (with_hand (C.ev body env, mtd)
                          (H.Fin (p, t, fin, env, k, h))))
        | C.Ev (SYN.Throw (p, expr), env, h, k, t) ->
          single (tick (with_kont (C.ev expr env h, mtd)
                          (K.Throw (p, t, env, k))))
        | C.Ev (SYN.Eval (p, str, bindings), env, h, k, t) ->
          single (tick (C.co p (V.VL L.Top) h k, mtd))
          (* REVISIT
          single (tick (with_kont (C.ev str env h, mtd)
                          (K.Eval (p, t, bindings, env, k))))*)
        | C.Ev (SYN.Hint (p, _, expr), env, h, k, t) ->
          single (tick (C.ev expr env h k, mtd))
        | C.Ex _ ->
          let hands = S.get_hands (C.hand_of context) store in
          HSet.fold
            (fun hand cds ->
              let (* thank you sir, may I have *) another cd = CDSet.add cd cds in
              (match hand, context with
              | H.Lab (p, _, name, _, k, h), C.Ex ((E.Break (label, a) as brk), env, _, _) ->
                if name = label then another (tick (C.co p (V.VA a) h k, mtd))
                else another (tick (C.ex brk env h, mtd))
              | H.Cat (p, t, catch, env, k, h), C.Ex (E.Throw throw_val, _, _, _) ->
                let addr, kont =
                  with_vld ~old_hand:(Some hand)
                    (fun a -> (K.Catch (p, t, a, env, k))) throw_val in
                another (tick (with_kont ~old_hand:(Some hand)
                                 (C.ev catch env h,
                                  join_val addr (V.VA throw_val) mtd)
                                 kont))
              | H.Fin (p, t, fin, env, k, h), C.Ex (ex, _, _, _) ->
                another (tick (with_kont ~old_hand:(Some hand)
                                 (C.ev fin env h, mtd)
                                 (K.Finally (p, t, ex, env, k))))
              | H.MtH _, C.Ex (ex, env, _, t) -> raise ex
              | h, C.Ex ((E.Break _ as brk), env, _, t) ->
                another (tick (C.ex brk env (H.hand_of h), mtd))
              | h, C.Ex ((E.Throw _ as thr), env, _, t) ->
                another (tick (C.ex thr env (H.hand_of h), mtd))
              | h, C.Ex (ex, env, _, t) ->
                another (tick (C.ex ex env (H.hand_of h), mtd))
              | _ -> failwith "Encountered an unmatched exn machine state."))
            hands CDSet.empty
        | _ -> (* hit a Co* state, and need at least the kont *)
          let konts = S.get_konts (C.kont_of context) store in
          KSet.fold
            (fun kont cds ->
              let another cd = CDSet.add cd cds in
              (match context, kont with
              | C.Co (_, _, v, h, _), K.SetBang (p, t, loc, k) ->
                another (tick (C.co p v h k, join_val loc v mtd))
              | C.Co (k, _, V.VA a, h, _), K.OpOne (p, t, name, env, _) ->
                val_branch a cds
                  (fun arg_val cds ->
                    CDSet.add (tick (C.co p (V.VL arg_val) h k, mtd)) cds)
              | C.Co (_, _, V.VL L.Top, h, _), K.OpOne (p, t, name, env, k) ->
                another (tick (C.co p topv h k, mtd))
              | C.Co (_, _, V.VL (L.Con arg_val), h, _), K.OpOne (p, t, name, env, k) ->
                another (tick (C.co p (conv (op1 store name arg_val)) h k, mtd))
              | C.Co (_, _, arg1_val, h, _), K.OpTwo (p, t, name, arg2, env, k) ->
                let addr, kont' =
                  (with_vld ~old_kont:(Some kont)
                     (fun a -> K.OpTwo2 (p, t, name, a, env, k)) arg1_val) in
                another (tick (with_kont ~old_kont:(Some kont)
                                 (C.ev arg2 env h, join_val addr arg1_val mtd) kont'))
              | C.Co (k, p, V.VA arg2_val, h, t), K.OpTwo2 (_, _, _, arg1_val, _, _) ->
                val_branch arg2_val cds
                  (fun arg2_val cds -> CDSet.add (tick (C.co p (V.VL arg2_val) h k, mtd)) cds)
              | C.Co (_, _, V.VL (L.Con arg2_val), h, _),
                K.OpTwo2 (p, t, name, arg1_val, env, k) ->
                val_branch arg1_val cds
                  (fun arg1_val cds -> match arg1_val with
                  | L.Top -> CDSet.add (tick (C.co p topv h k, mtd)) cds
                  | L.Con a1val ->
                    CDSet.add (tick (C.co p (conv (op2 store name a1val arg2_val)) h k,
                                     mtd))
                      cds)
              | C.Co (_, _, V.VL L.Top, h, _), K.OpTwo2 (p, _, _, _, _, k) ->
                another (tick (C.co p topv h k, mtd))
              | C.Co (_, _, V.VA a, h, _), K.If (p, t, env, than, elze, k) ->
                val_branch a cds
                  (fun pred_val cds ->
                    CDSet.add
                      (tick (C.co p (V.VL pred_val) h (C.kont_of context), mtd))
                      cds)
              | C.Co (_, _, V.VL L.Top, h, _), K.If (p, t, env, than, elze, k) ->
                CDSet.add (tick (C.ev than env h k, mtd))
                  (CDSet.add (tick (C.ev elze env h k, mtd)) cds)
              | C.Co (_, _, V.VL (L.Con pred_val), h, _), K.If (p, t, env, than, elze, k) ->
                (match pred_val with
                | V.Bool L.Top ->
                  CDSet.add (tick (C.ev than env h k, mtd))
                    (another (tick (C.ev elze env h k, mtd)))
                | V.Bool (L.Con true) -> another (tick (C.ev than env h k, mtd))
                | _ -> another (tick (C.ev elze env h k, mtd)))
              | C.Co (_, _, func, h, _), K.App (p, t, env, [], k) -> (* no arg app *)
                another (tick (C.ap p func [] h k, mtd))
              | C.Co (_, _, func, h, _), K.App (p, t, env, expr::exprs, k) ->
                let addr, kont' =
                  (with_vld ~old_kont:(Some kont)
                     (fun a -> K.App2 (p, t, a, env, [] , exprs, k)) func) in
                another (tick (with_kont ~old_kont:(Some kont)
                                 (C.ev expr env h, join_val addr func mtd) kont'))
              | C.Co (_, _, arg_val, h, _), K.App2 (p, t, func, env, vs, expr::exprs, k) ->
                let addr, kont' =
                  (with_vld ~old_kont:(Some kont)
                     (fun a -> K.App2 (p, t, func, env, a::vs, exprs, k)) arg_val) in
                another (tick (with_kont ~old_kont:(Some kont)
                                 (C.ev expr env h, join_val addr arg_val mtd) kont'))
              | C.Co (_, _, arg_val, h, _), K.App2 (p, t, func, env, vs, [], k) ->
                let vlds = List.fold_left (fun a n -> (V.VA n)::a) [arg_val] vs in
                another (tick (C.ap p (V.VA func) vlds h k, mtd))
              | C.Co (_, _, _, h, _), K.Seq (p, t, right, env, k) ->
                another (tick (C.ev right env h k, mtd))
              | C.Co (_, _, v, h, _), K.Let (p, t, name, body, env, k) ->
                let new_loc = kcfa_alloc context store (Some kont) None in
                another (tick (C.ev body (env_add name new_loc env) h k,
                               join_val new_loc v mtd))
              | C.Co (_, _, v, h, _), K.Rec (p, t, new_loc, body, env, k) ->
                another (tick (C.ev body env h k, join_val new_loc v mtd))
              | C.Co (_, _, v, h, _), K.Break (p, t, label, env, k) ->
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.ex (E.Break (label, addr)) env h,
                               join_val addr v mtd))
              | C.Co (_, _, catch_val, h, _), K.Catch (p, t, throw_val, env, k) ->
                another (tick (C.ap p catch_val [V.VA throw_val] h k, mtd))
              | C.Co (_, _, _, h, _), K.Finally (p, t, ex, env, k) ->
                another (tick (C.ex ex env h, mtd))
              | C.Co (_, _, _, h, _), K.Finally2 (p, t, valu, k) ->
                another (tick (C.co p (V.VA valu) h k, mtd))
              | C.Co (_, _, valu, h, _), K.Throw (p, t, env, k) ->
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.ex (E.Throw addr) env h, join_val addr valu mtd))
              | _, _ -> (* need kont and handle *)
                let hands = S.get_hands (C.hand_of context) store in
                HSet.fold
                  (fun hand cds ->
                    let another cd = CDSet.add cd cds in
                    (match context, kont, hand with
                    | C.Co (_, _, valu, _, _), K.Mt _, H.MtH _ ->
                      another (tick (C.ans valu, mtd))
                    | C.Co (_, _, valu, _, _), K.Mt _, H.Lab (p, t, name, env, k, h) ->
                      another (tick (C.co p valu h k, mtd))
                    | C.Co (_, _, valu, _, _), K.Mt _, H.Cat (p, t, _, _, k, h) ->
                      another (tick (C.co p valu h k, mtd))
                    | C.Co (_, _, valu, _, _), K.Mt _, H.Fin (p, t, exp, env, k, h) ->
                      let addr, kont' =
                        (with_vld ~old_kont:(Some kont) ~old_hand:(Some hand)
                           (fun a -> K.Finally2 (p, t, a, k)) valu) in
                      another (tick (with_kont (C.ev exp env h, join_val addr valu mtd)
                                       kont'))
                    | _ ->
                      failwith "Encountered an unmatched co hk machine context."))
                  hands cds)) konts CDSet.empty
        | _ -> failwith "unfinished"
      end in
    
    transition (inject exp init_env init_store) G.empty
      
  end
    

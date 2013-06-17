open Collects
open Lattices
open Aobject

type context = Acontext.context
type store = Astore.store
type addr = Ashared.addr
type time = Ashared.time
type exp = Ljs_syntax.exp
type prop = Aobject.prop
type attrs = Aobject.attrs
type objekt = Aobject.objekt
type value = AValue.t
type kont = Akont.kont
type hand = Ahandle.hand
type env = addr Prelude.IdMap.t
let env_add = Prelude.IdMap.add
let env_find = Prelude.IdMap.find
let env_filter = Prelude.IdMap.filter
type prop_map = Aobject.PSet.t Prelude.IdMap.t
let mt_props = Prelude.IdMap.empty
let props_add = Prelude.IdMap.add
let props_find = Prelude.IdMap.find
let props_mem = Prelude.IdMap.mem
let props_filter = Prelude.IdMap.filter
let props_fold = Prelude.IdMap.fold

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
module ST = Kcfa (* ST read strategy *)
module H = Ahandle
module K = Akont
module E = Aerror
module SYN = Ljs_syntax
module S = Astore
module D = Adelta

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
    (op1 : store -> string -> value -> value)
    (op2 : store -> string -> value -> value -> value)
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

let alpha_unique exp =
  let fp = let count = ref 0 in fun () -> begin
    count := !count + 1 ;
    let pos = 
      { Lexing.pos_fname="fp";
        Lexing.pos_lnum=(!count);
        Lexing.pos_bol=0;
        Lexing.pos_cnum=0 } in
    pos, pos, true
  end in
  let rec au_exp env i ex =
    let mk_ident n = "var_"^(string_of_int n) in
    let au_exp' = au_exp env i in
    match ex with
    | SYN.Null _
    | SYN.Undefined _
    | SYN.String _
    | SYN.Num _
    | SYN.True _
    | SYN.False _ -> ex, env, i
    | SYN.Object (p, attrs, nps) ->
      let aue, env', i' = au_attrs env i attrs in
      let aunps, env', i' =
        List.fold_right
          (fun (n, p) (aunps, env', i') ->
            let p', env'', i'' = au_prop env' i' p in (n, p')::aunps, env'', i'')
          nps
          ([], env', i') in
      SYN.Object (p, aue, aunps), env', i'
    | SYN.GetAttr (p, pa, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.GetAttr (p, pa, aue, aue'), env', i'
    | SYN.SetAttr (p, pa, e, e', e'') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      let aue'', env', i' = au_exp env' i' e'' in
      SYN.SetAttr (p, pa, aue, aue', aue''), env', i'
    | SYN.GetObjAttr (p, oa, e) ->
      let aue, env', i' = au_exp' e in
      SYN.GetObjAttr (p, oa, aue), env', i'
    | SYN.SetObjAttr (p, oa, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.SetObjAttr (p, oa, aue, aue'), env', i'
    | SYN.GetField (p, e, e', e'') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      let aue'', env', i' = au_exp env' i' e'' in
      SYN.GetField (p, aue, aue', aue''), env', i'
    | SYN.SetField (p, e, e', e'', e''') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      let aue'', env', i' = au_exp env' i' e'' in
      let aue''', env', i' = au_exp env' i' e''' in
      SYN.SetField (p, aue, aue', aue'', aue'''), env', i'
    | SYN.DeleteField (p, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.DeleteField (p, aue, aue'), env', i'
    | SYN.OwnFieldNames (p, e) ->
      let aue, env', i' = au_exp' e in
      SYN.OwnFieldNames (p, aue), env', i'
    | SYN.Op1 (p, op, e) ->
      let aue, env', i' = au_exp' e in
      SYN.Op1 (p, op, aue), env', i'
    | SYN.Op2 (p, op, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.Op2 (p, op, aue, aue'), env', i'
    | SYN.If (p, e, e', e'') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      let aue'', env', i' = au_exp env' i' e'' in
      SYN.If (p, aue, aue', aue''), env', i'
    | SYN.App (p, e, es) ->
      let aue, env', i' = au_exp' e in
      let aues, env', i' =
        List.fold_right
          (fun e (aues, env', i') ->
            let aue, env', i' = au_exp env' i' e in aue::aues, env', i')
          es ([], env', i') in
      SYN.App (p, aue, aues), env', i'
    | SYN.Seq (p, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.Seq (p, aue, aue'), env', i'
    | SYN.Label (p, id, e) ->
      let aue, env', i' = au_exp' e in
      SYN.Label (p, id, aue), env', i'
    | SYN.Break (p, id, e) ->
      let aue, env', i' = au_exp' e in
      SYN.Break (p, id, aue), env', i'
    | SYN.TryCatch (p, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.TryCatch (p, aue, aue'), env', i'
    | SYN.TryFinally (p, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.TryFinally (p, aue, aue'), env', i'
    | SYN.Throw (p, e) ->
      let aue, env', i' = au_exp' e in
      SYN.Throw (p, aue), env', i'
    | SYN.Eval (p, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.EvalAU (p, aue, aue', env'), env', i'
    | SYN.Id (p, x) ->
      let x' = try env_find x env with Not_found -> begin
        print_endline ("warning! unbound id during alpha unique pass: "^x); x
      end in
      SYN.Id (p, x'), env, i
    | SYN.SetBang (p, x, e) ->
      let x' = try env_find x env with Not_found -> begin
        print_endline ("warning! unbound id during alpha unique pass: "^x); x
      end in
      let aue, env', i' = au_exp' e in
      SYN.SetBang (p, x', aue), env', i'
    | SYN.Let (p, x, e, e') ->
      let x' = mk_ident i in
      let env' = env_add x x' env in
      let aue, env', i' = au_exp env' (i+1) e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.Let (p, x', aue, aue'), env', i'
    | SYN.Rec (p, x, e, e') -> begin
      let x' = mk_ident i in
      let env' = env_add x x' env in
      let aue, env', i' = au_exp env' (i+1) e in
      let aue', env', i' = au_exp env' i' e' in
      SYN.Rec (p, x', aue, aue'), env', i'
    end
    | SYN.Lambda (p, xs, e) ->
      let xs', env', i' =
        List.fold_right
          (fun x (xs', env', i') ->
            let x' = mk_ident i' in x'::xs', env_add x x' env, i'+1)
          xs ([], env, i) in
      let aue, env', i' = au_exp env' i' e in
      SYN.Lambda (p, xs', aue), env', i'
  and au_prop env i prop = match prop with
    | SYN.Data ({ SYN.value=exp; SYN.writable=w }, e, c) ->
      let aue, env', i' = au_exp env i exp in
      SYN.Data ({ SYN.value=aue; SYN.writable=w }, e, c), env', i'
    | SYN.Accessor ({ SYN.getter=g; SYN.setter=s }, e, c) ->
      let aug, env', i' = au_exp env i g in
      let aus, env', i' = au_exp env' i' s in
      SYN.Accessor ({ SYN.getter=aug; SYN.setter=aus }, e, c), env', i'
  and au_attrs (env : string Prelude.IdMap.t) (i : int) ({ SYN.primval=eo; SYN.code=eo'; SYN.proto=eo'';
                                                           SYN.klass=k; SYN.extensible=ext } : Ljs_syntax.attrs) =
    let opt_au_exp env i eo = match eo with
      | Some e -> let aue, env', i' = au_exp env i e in Some aue, env', i'
      | None -> None, env, i in
    let aueo, env', i' = opt_au_exp env i eo in
    let aueo', env', i' = opt_au_exp env' i' eo' in
    let aueo'', env', i' = opt_au_exp env' i' eo'' in
    { SYN.primval=aueo; SYN.code=aueo'; SYN.proto=aueo'';
      SYN.klass=k; SYN.extensible=ext }, env', i' in
  let auexp, _, _ = au_exp Prelude.IdMap.empty 0 exp in auexp in
      
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
      let force_val v store = match v with
        | `Delay addr -> Astore.get_vals addr store
        | _ -> VSet.singleton v in
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
      let vchange, vs' = force_join vds vs VSet.empty VSet.union force_val in
      let ochange, os' = join ods os OSet.empty OSet.mem OSet.add in
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

    (* Anywhere with a commented out failwith is a location that represents a
       code point that cannot occur due to λS5 desugaring. If we reach one
       during the course of analysis, we are not taking advantage of the assumptions
       that can be made based on the desugaring process. *)
    and step context store =
      begin
        if log then print_endline ("  "^(C.string_of context)) ;
        let single = CDSet.singleton in
        let tick ?(old_kont=None) ?(old_hand=None) (ccon, delta) =
          ccon (kcfa_tick context store old_kont old_hand), delta in
        let with_kont ?(old_kont=None) ?(old_hand=None) (ccon, delta) kont =
          let kaddr = kcfa_alloc_kont context store old_kont old_hand in
          ccon kaddr, join_kont kaddr kont delta in
        let with_hand ?(old_kont=None) ?(old_hand=None) (ccon, delta) hand =
          let haddr = kcfa_alloc_hand context store old_kont old_hand in
          ccon haddr (SH.addr0), join_hand haddr hand delta in
        let with_addr ?(old_kont=None) ?(old_hand=None) v ckont = match v with
          | `Delay addr -> addr, ckont addr
          | _ ->
            let addr = kcfa_alloc context store old_kont old_hand in
            addr, ckont addr in
        let with_addr' ?(old_kont=None) ?(old_hand=None) ckont = (* bot not used *)
          with_addr ~old_kont:(old_kont) ~old_hand:(old_hand) `Bot ckont in
        let val_branch addr acc cds_folder =
          let vls = S.get_vals addr store in VSet.fold cds_folder vls acc in
        let obj_branch addr acc cds_folder =
          let objs = S.get_objs addr store in OSet.fold cds_folder objs acc in
        match context with
        | C.Ans _ -> CDSet.empty
        | C.Ap (p, `Top, vs, h, k, t) ->
          single (tick (C.co p `Top h k, mtd))
        | C.Ap (p, `Delay a, vs, h, k, t) ->
          val_branch a CDSet.empty
            (fun v cds -> CDSet.add (tick (C.ap p v vs h k, mtd)) cds)
        | C.Ap (p, `Clos (env, xs, body), vs, h, k, t) ->
          if (List.length vs) != (List.length xs) then
            E.arity_mismatch_err p xs vs
          else
            let rec foldr_3 f b xs ys zs = match xs, ys, zs with
              | [], [], [] -> b
              | x::xs', y::ys', z::zs' -> f x y z (foldr_3 f b xs' ys' zs')
              | _, _, _ -> failwith "different length lists, you doofus" in
            let addrs = kcfa_alloc' context store None None in
            let env', delta =
              foldr_3
                (fun x a v (env', s) -> env_add x a env', join_val a v s)
                (env, mtd) xs addrs vs in
            single (tick (C.ev body env' h k, delta))
        | C.Ap (p, `Obj a, vs, h, k, t) ->
          OSet.fold
            (fun ({ code=code }, _) acc -> match code with
            | `Bot -> failwith ("Applied an object without a code attribute at "^
                                   (Ashared.string_of_addr a))
              (* The above case shouldn't be possible due to desugaring. Let's 
                 see if it ever comes up in testing. *)
            | _ -> CDSet.add (tick (C.ap p code vs h k, mtd)) acc)
            (S.get_objs a store) CDSet.empty
        | C.Ap (p, f, vlds, h, k, t) ->
         failwith (E.interp_error p ("Applied non-function: "^(AValue.string_of f)))
        | C.Ev (SYN.Undefined p, _, h, k, t) ->
          single (tick (C.co p `Undef h k, mtd))
        | C.Ev (SYN.Null p, _, h, k, t) ->
          single (tick (C.co p `Null h k, mtd))
        | C.Ev (SYN.String (p, s), _, h, k, t) ->
          single (tick (C.co p (`Str s) h k, mtd))
        | C.Ev (SYN.Num (p, n), _, h, k, t) ->
          single (tick (C.co p (`Num  n) h k, mtd))
        | C.Ev (SYN.True p, _, h, k, t) ->
          single (tick (C.co p `True h k, mtd))
        | C.Ev (SYN.False p, _, h, k, t) ->
          single (tick (C.co p `False h k, mtd))
        | C.Ev (SYN.Id (p, x), env, h, k, t) ->
          single (tick (C.co p (`Delay (env_find x env)) h k, mtd))
        | C.Ev (SYN.Lambda (p, xs, body), env, h, k, t) ->
          let free = SYN.free_vars body in
          let env' = env_filter (fun var _ -> Prelude.IdSet.mem var free) env in
          single (tick (C.co p (`Clos (env', xs, body)) h k, mtd))
        | C.Ev (SYN.SetBang (p, x, new_val_exp), env, h, k, t) ->
          (match try Some (env_find x env) with Not_found -> None with
          | Some a -> single (tick (with_kont (C.ev new_val_exp env h, mtd)
                                      (K.SetBang (p, t, a, k))))
          | None -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (Prelude.Pos.string_of_pos p)))
        | C.Ev (SYN.Object (p, attrs, props), env, h, k, t) ->
          single (tick (with_kont (C.eva p attrs env h, mtd)
                          (K.Object (p, t, props, env, k))))
        | C.Ev (SYN.GetAttr (p, attr, obj, field), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.GetAttr (p, t, attr, field, env, k))))
        | C.Ev (SYN.SetAttr (p, pattr, obj, field, next), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.SetAttr (p, t, pattr, field, next, env, k))))
        | C.Ev (SYN.GetObjAttr (p, oattr, obj), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.GetObjAttr (p, t, oattr, env, k))))
        | C.Ev (SYN.SetObjAttr (p, oattr, obj, next), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.SetObjAttr (p, t, oattr, next, env, k))))
        | C.Ev (SYN.GetField (p, obj, field, body), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.GetField (p, t, field, body, env, k))))
        | C.Ev (SYN.OwnFieldNames (p, obj), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd) (K.OwnFieldNames (p, t, k))))
        | C.Ev (SYN.DeleteField (p, obj, field), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.DeleteField (p, t, field, env, k))))
        | C.Ev (SYN.SetField (p, obj, field, next, body), env, h, k, t) ->
          single (tick (with_kont (C.ev obj env h, mtd)
                          (K.SetField (p, t, field, next, body, env, k))))
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
          single (tick (C.co p `Top h k, mtd))
          (* REVISIT!!! This is a lie, especially the mtd!!!
          single (tick (with_kont (C.ev str env h, mtd)
                          (K.Eval (p, t, bindings, env, k))))*)
        | C.Ev (SYN.Hint (p, _, expr), env, h, k, t) -> (* ignore hints, no snaps *)
          single (tick (C.ev expr env h k, mtd))
        | C.EvA (p, attrs, env, h, k, t) ->
          let { SYN.primval = pexp;
                SYN.code = cexp;
                SYN.proto = proexp;
                SYN.klass = kls;
                SYN.extensible = ext; } = attrs in
          let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
          let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
          (match aes with
          | [] ->
            let attrsv = { code=`Bot; proto=`Undef;
                           primv=`Bot; klass=`Str kls; exten=AValue.bool ext } in
            single (tick (C.coa attrsv h k, mtd))
          | (name, exp)::pairs ->
            single (tick (with_kont (C.ev exp env h, mtd)
                            (K.Attrs (p, t, name, pairs, [], kls, ext, env, k)))))
        | C.EvP (p, (name, prop), env, h, k, t) ->
          (match prop with
          | SYN.Data ({ SYN.value = valu; SYN.writable = writable; }, enum, config) ->
            single (tick (with_kont (C.ev valu env h, mtd)
                            (K.DataProp (SYN.pos_of valu, t, name, writable, enum, config, k))))
          | SYN.Accessor ({ SYN.getter = getter; SYN.setter = setter; }, enum, config) ->
            single (tick (with_kont (C.ev getter env h, mtd)
                            (K.AccProp (SYN.pos_of getter, t, name, setter,
                                        enum, config, env, k)))))
        | C.Ex _ ->
          let hands = S.get_hands (C.hand_of context) store in
          HSet.fold
            (fun hand cds ->
              let (* thank you sir, may I have *) another cd = CDSet.add cd cds in
              (match hand, context with
              | H.Lab (p, _, name, _, k, h), C.Ex ((E.Break (label, a) as brk), env, _, _) ->
                if name = label then another (tick (C.co p (`Delay a) h k, mtd))
                else another (tick (C.ex brk env h, mtd))
              | H.Cat (p, t, catch, env, k, h), C.Ex (E.Throw throw_val, _, _, _) ->
                let vld = `Delay throw_val in
                let addr, kont =
                  with_addr ~old_hand:(Some hand) vld
                    (fun a -> (K.Catch (p, t, a, env, k))) in
                another (tick (with_kont ~old_hand:(Some hand)
                                 (C.ev catch env h, join_val addr vld mtd) kont))
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
              | C.Co (k, _, `Delay a, h, _), K.OpOne (p, t, name, env, _) ->
                val_branch a cds
                  (fun arg_val cds ->
                    CDSet.add (tick (C.co p arg_val h k, mtd)) cds)
              | C.Co (_, _, `Top, h, _), K.OpOne (p, t, name, env, k) ->
                another (tick (C.co p `Top h k, mtd))
              | C.Co (_, _, arg_val, h, _), K.OpOne (p, t, name, env, k) ->
                another (tick (C.co p (op1 store name arg_val) h k, mtd))
              | C.Co (_, _, arg1_val, h, _), K.OpTwo (p, t, name, arg2, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) arg1_val
                     (fun a -> K.OpTwo2 (p, t, name, a, env, k)) in
                another (tick (with_kont ~old_kont:(Some kont)
                                 (C.ev arg2 env h, join_val addr arg1_val mtd) kont'))
              | C.Co (k, p, `Delay arg2_val, h, t), K.OpTwo2 (_, _, _, arg1_val, _, _) ->
                val_branch arg2_val cds
                  (fun arg2_val cds -> CDSet.add (tick (C.co p arg2_val h k, mtd)) cds)
              | C.Co (_, _, arg2_val, h, _),
                K.OpTwo2 (p, t, name, arg1_val, env, k) ->
                val_branch arg1_val cds
                  (fun arg1_val cds -> match arg1_val with
                  | `Top -> CDSet.add (tick (C.co p `Top h k, mtd)) cds
                  | _ ->
                    CDSet.add (tick (C.co p (op2 store name arg1_val arg2_val) h k,
                                     mtd))
                      cds)
              | C.Co (_, _, `Top, h, _), K.OpTwo2 (p, _, _, _, _, k) ->
                another (tick (C.co p `Top h k, mtd))
              | C.Co (k, _, `Delay a, h, _), K.If (p, t, env, than, elze, _) ->
                val_branch a cds
                  (fun pred_val cds ->
                    CDSet.add
                      (tick (C.co p pred_val h k, mtd))
                      cds)
              | C.Co (_, _, `Top, h, _), K.If (p, t, env, than, elze, k) ->
                CDSet.add (tick (C.ev than env h k, mtd))
                  (CDSet.add (tick (C.ev elze env h k, mtd)) cds)
              | C.Co (_, _, pred_val, h, _), K.If (p, t, env, than, elze, k) ->
                (match pred_val with
                | `Top ->
                  CDSet.add (tick (C.ev than env h k, mtd))
                    (another (tick (C.ev elze env h k, mtd)))
                | `True -> another (tick (C.ev than env h k, mtd))
                | _ -> another (tick (C.ev elze env h k, mtd)))
              | C.Co (_, _, func, h, _), K.App (p, t, env, [], k) -> (* no arg app *)
                another (tick (C.ap p func [] h k, mtd))
              | C.Co (_, _, func, h, _), K.App (p, t, env, expr::exprs, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) func
                     (fun a -> K.App2 (p, t, a, env, [] , exprs, k)) in
                another (tick (with_kont ~old_kont:(Some kont)
                                 (C.ev expr env h, join_val addr func mtd) kont'))
              | C.Co (_, _, arg_val, h, _), K.App2 (p, t, func, env, vs, expr::exprs, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) arg_val
                     (fun a -> K.App2 (p, t, func, env, a::vs, exprs, k)) in
                another (tick (with_kont ~old_kont:(Some kont)
                                 (C.ev expr env h, join_val addr arg_val mtd) kont'))
              | C.Co (_, _, arg_val, h, _), K.App2 (p, t, func, env, vs, [], k) ->
                let vlds = List.fold_left (fun a n -> (`Delay n)::a) [arg_val] vs in
                another (tick (C.ap p (`Delay func) vlds h k, mtd))
              | C.Co (_, _, _, h, _), K.Seq (p, t, right, env, k) ->
                another (tick (C.ev right env h k, mtd))
              | C.Co (_, _, v, h, _), K.Let (p, t, name, body, env, k) ->
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.ev body (env_add name addr env) h k,
                               join_val addr v mtd))
              | C.Co (_, _, v, h, _), K.Rec (p, t, new_loc, body, env, k) ->
                another (tick (C.ev body env h k, join_val new_loc v mtd))
              | C.Co (_, _, v, h, _), K.Break (p, t, label, env, k) ->
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.ex (E.Break (label, addr)) env h,
                               join_val addr v mtd))
              | C.Co (_, _, catch_val, h, _), K.Catch (p, t, throw_val, env, k) ->
                another (tick (C.ap p catch_val [`Delay throw_val] h k, mtd))
              | C.Co (_, _, _, h, _), K.Finally (p, t, ex, env, k) ->
                another (tick (C.ex ex env h, mtd))
              | C.Co (_, _, _, h, _), K.Finally2 (p, t, valu, k) ->
                another (tick (C.co p (`Delay valu) h k, mtd))
              | C.Co (_, _, valu, h, _), K.Throw (p, t, env, k) ->
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.ex (E.Throw addr) env h, join_val addr valu mtd))
              | C.CoA (_, attrs, h, _), K.Object (p, t, [], _, k) -> (* empty props case *)
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.co p (`Obj addr) h k,
                               join_obj addr (attrs, mt_props) mtd))
              | C.CoA (_, attrsv, h, _), K.Object (p, t, prop::ps, env, k) ->
                let addr, kont' =
                  with_addr' ~old_kont:(Some kont)
                    (fun a -> K.Object2 (p, t, a, ps, [], env, k)) in
                another (tick (with_kont (C.evp p prop env h, join_attrs addr attrsv mtd)
                                 kont'))
              | C.CoP (_, _, (n, pv), h, _), K.Object2 (p, t, attrsv, prop::ps, pvs, env, k) ->
                let addr, kont' =
                  with_addr' ~old_kont:(Some kont)
                    (fun a -> K.Object2 (p, t, attrsv, ps, (n, a)::pvs, env, k)) in
                another (tick (with_kont (C.evp p prop env h, join_prop addr pv mtd) kont'))
              | C.CoP (_, p, (name, pv), h, _), K.Object2 (p', t, attrsv, [], pvs, env, k) ->
                let attrsv = Aobject.combine_attrs (S.get_attrs attrsv store) in
                let props =
                  List.fold_left
                    (fun acc (name, addr) ->
                      props_add name (Aobject.combine_props (S.get_props addr store)) acc)
                    (props_add name pv mt_props)
                    pvs in
                let addr = kcfa_alloc context store (Some kont) None in
                another (tick (C.co p' (`Obj addr) h k, join_obj addr (attrsv, props) mtd))
              | C.Co (k, p, `Delay a, h, t), K.DataProp _ ->
                val_branch a cds
                  (fun vl cds -> CDSet.add (tick (C.co p vl h k, mtd)) cds)
              | C.Co (_, _, vl, h, _), K.DataProp (p, t, name, w, enum, config, k) ->
                another (tick (C.cop p name (Data ({ value=vl;
                                                     writable=AValue.bool w; },
                                                   AValue.bool enum,
                                                   AValue.bool config)) h k,
                               mtd))
              | C.Co (_, _, getter_val, h, _),
                K.AccProp (p, t, name, setter, enum, config, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) getter_val
                    (fun a -> K.AccProp2 (p, t, name, a, enum, config, env, k)) in
                another (tick (with_kont (C.ev setter env h, join_val addr getter_val mtd)
                                 kont'))
              | C.Co (k, p, `Delay a, h, t), K.AccProp2 _ ->
                val_branch a cds
                  (fun vl cds -> CDSet.add (tick (C.co p vl h k, mtd)) cds)
              | C.Co (_, _, sv, h, _), K.AccProp2 (p, t, name, gv, enum, config, env, k) ->
                val_branch gv cds
                  (fun vl cds ->
                    CDSet.add (tick (C.cop p name
                                       (Accessor ({ getter=vl;
                                                    setter=sv },
                                                  AValue.bool enum,
                                                  AValue.bool config)) h k, mtd))
                      cds)
              | C.Co (_, _, valu, h, _),
                K.Attrs (p, t, name, (name', exp)::pairs, valus, kls, ext, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) valu
                    (fun a -> K.Attrs (p, t, name', pairs,
                                       (name, a)::valus, kls, ext, env, k)) in
                another (tick (with_kont (C.ev exp env h, join_val addr valu mtd) kont'))
              | C.Co (_, _, `Delay a, h, _), K.Attrs (p, t, name, [], valus, kls, ext, env, k) ->
                let assoc_vls = (name, a)::valus in
                let join_get str =
                  if List.mem_assoc str assoc_vls then
                    VSet.fold
                      (fun v acc -> AValue.join v acc)
                      (S.get_vals (List.assoc str assoc_vls) store)
                      `Bot
                  else `Bot in
                let code = join_get "code" in
                let prim = join_get "prim" in
                let proto =
                  let v = join_get "proto" in
                  match v with `Bot -> `Undef | _ -> v in
                let attrsv = { code=code; primv=prim; proto=proto;
                               klass=`Str kls; exten=AValue.bool ext } in
                another (tick (C.coa attrsv h k, mtd))
              | C.Co (_, _, obj_val, h, _), K.GetAttr (p, t, attr, field, env, k) ->
                let addr, kont' = 
                  with_addr ~old_kont:(Some kont) obj_val
                    (fun a -> K.GetAttr2 (p, t, attr, a, env, k)) in
                another (tick (with_kont (C.ev field env h, join_val addr obj_val mtd) kont'))
              | C.Co (k, p, `Delay a, h, t), K.GetAttr2 _ ->
                val_branch a cds
                  (fun vl cds -> CDSet.add (tick (C.co p vl h k, mtd)) cds)
              | C.Co (_, _, fv, h, _), K.GetAttr2 (p, t, attr, obj, env, k) ->
                val_branch obj cds
                  (fun ov cds -> match ov, fv with
                  | _, `Top -> CDSet.add (tick (C.co p `Top h k, mtd)) cds
                  | `Obj a, `Str str ->
                    obj_branch a cds
                      (fun (attrs, props) cds ->
                        if not (props_mem str props) then
                          CDSet.add (tick (C.co p `Undef h k, mtd)) cds
                        else
                          let valu = match props_find str props, attr with
                            | Data (_, _, config), SYN.Config
                            | Accessor (_, _, config), SYN.Config -> config
                            | Data (_, enum, _), SYN.Enum
                            | Accessor (_, enum, _), SYN.Enum -> enum
                            | Data ({ writable = b; }, _, _), SYN.Writable -> b
                            | Data ({ value = v; }, _, _), SYN.Value -> v
                            | Accessor ({ getter = gv; }, _, _), SYN.Getter -> gv
                            | Accessor ({ setter = sv; }, _, _), SYN.Setter -> sv
                            | _ -> failwith "bad access of attribute" in
                          CDSet.add (tick (C.co p valu h k, mtd)) cds)
                  | _ -> failwith "get_attr did not get an object and a string")
              | C.Co (_, _, obj_val, h, _), K.SetAttr (p, t, pattr, field, next, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) obj_val
                    (fun a -> K.SetAttr2 (p, t, pattr, next, a, env, k)) in
                another (tick (with_kont (C.ev field env h, join_val addr obj_val mtd) kont'))
              | C.Co (_, _, field_val, h, _), K.SetAttr2 (p, t, pattr, next, obj_val, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) field_val
                    (fun a -> K.SetAttr3 (p, t, pattr, obj_val, a, env, k)) in
                another (tick (with_kont (C.ev next env h, join_val addr field_val mtd) kont'))
              | C.Co (k, p, `Delay a, h, t), K.SetAttr3 _ ->
                val_branch a cds (fun v cds -> CDSet.add (tick (C.co p v h k, mtd)) cds)
              | C.Co (_, _, vl, h, _), K.SetAttr3 (p, t, pattr, ovaddr, field, env, k) ->
                let set_attrs addr objs attr fv cds =
                  OSet.fold
                    (fun ((attrs, props) as obj) cds ->
                      let fields = match fv with
                        | `Top -> props_fold (fun k _ a -> k::a) props []
                        | `Str str -> [str]
                        | _ -> failwith "Did not get a string in setattr!" in
                      let props' =
                        List.fold_left
                          (fun props' fstr ->
                            let prop = D.set_attr pattr obj fstr vl in
                            props_add fstr prop props')
                          props fields in
                      CDSet.add (tick (C.co p `True h k, join_obj addr (attrs, props') mtd))
                        cds)
                    objs cds in
                val_branch ovaddr cds
                  (fun ovl cds ->
                    val_branch field cds
                      (fun fv cds -> match ovl with
                      | `Top ->
                        let (os, _, _, _, _, _) = store in
                        AddrMap.fold (fun a objs cds -> set_attrs a objs pattr fv cds) os cds
                      | `Obj oaddr ->
                        set_attrs oaddr (S.get_objs oaddr store) pattr fv cds
                      | _ -> failwith "Didn't get an object in setattr!"))
              | C.Co (k, p, `Delay a, h, t), K.GetObjAttr _ ->
                val_branch a cds (fun ov cds -> CDSet.add (tick (C.co p ov h k, mtd)) cds)
              | C.Co (_, _, objv, h, _), K.GetObjAttr (p, t, oattr, env, k) ->
                let get_obj_attr attrs oattr = match attrs, oattr with
                  | { proto=proto }, SYN.Proto -> proto
                  | { exten=exten} , SYN.Extensible -> exten
                  | { code=`Bot}, SYN.Code -> `Null
                  | { code=code}, SYN.Code -> code
                  | { primv=`Bot}, SYN.Primval -> failwith "[interp] Got Primval attr of Bot"
                  | { primv=primv}, SYN.Primval -> primv
                  | { klass=klass }, SYN.Klass -> klass in
                (match objv with
                | `Top -> another (tick (C.co p `Top h k, mtd))
                | `Obj oaddr ->
                  obj_branch oaddr cds
                    (fun (attrs, _) cds ->
                      let v = get_obj_attr attrs oattr in
                      CDSet.add (tick (C.co p v h k, mtd)) cds)
                | _ -> failwith "[interp] GetObjAttr got a non-object.")
              | C.Co (_, _, ov, h, _), K.SetObjAttr (p, t, oattr, next, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) ov
                    (fun a -> K.SetObjAttr2 (p, t, oattr, a, env, k)) in
                another (tick (with_kont (C.ev next env h, join_val addr ov mtd) kont'))
              | C.Co (k, p, `Delay a, h, t), K.SetObjAttr2 _ ->
                val_branch a cds (fun vl cds -> CDSet.add (tick (C.co p vl h k, mtd)) cds)
              | C.Co (_, _, vl, h, _), K.SetObjAttr2 (p, t, oattr, ovaddr, env, k) ->
                let set_attr ({ code=cod; proto=pro; exten=ext; klass=kls; primv=pri } as attrs)
                    oattr = (match oattr with
                  | SYN.Proto -> { attrs with proto=AValue.join pro vl }
                  | SYN.Extensible -> { attrs with exten=AValue.join ext vl }
                  | SYN.Primval -> { attrs with primv=AValue.join pri vl }
                  | _ -> failwith "set object attr failed") in
                let set_obj_attr addr (attrs, props) =
                  let attrsv = set_attr attrs oattr in
                  tick (C.co p vl h k, join_obj addr (attrsv, props) mtd) in
                let set_objs_attr addr objs cds =
                  OSet.fold (fun obj cds -> CDSet.add (set_obj_attr addr obj) cds) objs cds in
                val_branch ovaddr cds
                  (fun vl cds -> match vl with
                  | `Top -> failwith "got a top obj... fuck"
(*                    let (os, _, _, _, _, _) = store in
                    AddrMap.fold (fun addr objs cds -> set_objs_attr addr objs cds) os cds*)
                  | `Obj oaddr ->
                    let objs = S.get_objs oaddr store in set_objs_attr oaddr objs cds
                  | _ -> failwith "[interp] SetObjAttr got a non-object")
              | C.Co (_, _, obj_val, h, _), K.GetField (p, t, field, body, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) obj_val
                    (fun a -> K.GetField2 (p, t, body, a, env, k)) in
                another (tick (with_kont (C.ev field env h, join_val addr obj_val mtd) kont'))
              | C.Co (_, _, field_val, h, _), K.GetField2 (p, t, body, obj_val, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) field_val
                    (fun a -> K.GetField3 (p, t, obj_val, a, env, k)) in
                another (tick (with_kont (C.ev body env h, join_val addr field_val mtd) kont'))
              | C.Co (_, _, body_val, h, _), K.GetField3 (p, t, ovaddr, faddr, env, k) ->
                let fields (_, props) fv = match fv with
                  | `Top -> props_fold (fun k _ a -> k::a) props []
                  | `Str str -> [str]
                  | _ -> failwith "Did not get a string in fields!" in
                let get_props objs fstr =
                  OSet.fold
                    (fun (attrs, props) ps ->
                      if props_mem fstr props then
                        PSet.add (props_find fstr props) ps
                      else ps)
                    objs PSet.empty in
                val_branch ovaddr cds
                  (fun ovl cds ->
                    val_branch faddr cds
                      (fun fvl cds -> match ovl with
                      | `Top ->
                        CDSet.add
                          (tick (C.co p `Top h k, mtd))
                          (CDSet.add (tick (C.ap p `Top [ovl; body_val] h k, mtd))
                             (CDSet.add (tick (C.co p `Undef h k, mtd)) cds))
                      | `Obj oaddr ->
                        let objs = S.get_objs oaddr store in
                        let props =
                          List.fold_left
                            (fun a fstr -> PSet.union (get_props objs fstr) a)
                            PSet.empty (OSet.fold (fun o a -> (fields o fvl)@a) objs []) in
                        if PSet.is_empty props then
                          CDSet.add (tick (C.co p `Undef h k, mtd)) cds
                        else
                          PSet.fold
                            (fun prop cds -> match prop with
                            | Data ({ value=v }, _, _) ->
                              CDSet.add (tick (C.co p v h k, mtd)) cds
                            | Accessor ({ getter=g }, _, _) ->
                              CDSet.add (tick (C.ap p g [ovl; body_val] h k, mtd)) cds
                            | TopProp ->
                              CDSet.add (tick (C.co p `Top h k, mtd))
                                (CDSet.add (tick (C.ap p `Top [ovl; body_val] h k, mtd))
                                   cds))
                            props
                            cds
                      | _ -> failwith ("[interp] Get field didn't get an object and a " ^
                                          "string at " ^ Prelude.Pos.string_of_pos p ^ ".")))
              | C.Co (k, p, `Delay a, h, t), K.OwnFieldNames _ ->
                val_branch a cds (fun vl cds -> CDSet.add (tick (C.co p vl h k, mtd)) cds)
              | C.Co (_, _, ovl, h, _), K.OwnFieldNames (p, t, k) ->
                let get_props objs =
                  OSet.fold
                    (fun (_, props) l -> props_fold (fun k _ l -> k::l) props [])
                    objs [] in
                let add_name n x m = props_add (string_of_int x)
                  (Data ({ value=`Str n; writable = `False; }, `False, `False)) m in
                let addr = kcfa_alloc context store (Some kont) None in
                let names, len = match ovl with
                  | `Top ->
                    let (os, _, _, _, _, _) = store in
                    AddrMap.fold
                      (fun _ objs names -> (get_props objs) @ names) os [], `Top
                  | `Obj oaddr ->
                    let names = get_props (S.get_objs oaddr store) in
                    names, `Num (float_of_int (List.length names))
                  | _ -> failwith "did not get object in ownfieldnames" in
                let props = List.fold_right2 add_name names
                  (Prelude.iota (List.length names)) mt_props in
                let final_props =
                  props_add "length"
                    (Data ({ value=len; writable=`False }, `False, `False)) props in
                CDSet.add (tick (C.co p (`Obj addr) h k,
                                 join_obj addr (default_attrs, final_props) mtd)) cds
              | C.Co (_, _, vld, h, _), K.DeleteField (p, t, field, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) vld
                    (fun a -> K.DeleteField2 (p, t, a, env, k)) in
                another (tick (with_kont (C.ev field env h, join_val addr vld mtd) kont'))
              | C.Co (k, p, `Delay a, h, t), K.DeleteField2 _ ->
                val_branch a cds (fun vl cds -> CDSet.add (tick (C.co p vl h k, mtd)) cds)
              | C.Co (_, _, fvl, h, _), K.DeleteField2 (p, t, ovladdr, env, k) ->
                val_branch ovladdr cds
                  (fun ovl cds -> match ovl, fvl with
                  | _, `Top | `Top, _ ->
                    CDSet.add (tick (C.co p `True h k, mtd)) cds
                  | `Obj oaddr, `Str str ->
                    obj_branch oaddr cds
                      (fun (attrs, props) cds ->
                        if props_mem str props then
                          match props_find str props with
                          | Data (_, _, `True)
                          | Accessor (_, _, `True) ->
                            CDSet.add (tick (C.co p `True h k, mtd)) cds
                          | _ ->
                            let addr = kcfa_alloc context store (Some kont) None in
                            CDSet.add
                              (tick (C.ex (E.Throw addr) env h,
                                     join_val addr (`Str "unconfigurable-delete") mtd))
                              cds
                        else CDSet.add (tick (C.co p `False h k, mtd)) cds)
                  | _, _ -> failwith "fell through deletefield2")
              | C.Co (_, _, vld, h, _), K.SetField (p, t, field, next, body, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) vld
                    (fun a -> K.SetField2 (p, t, next, body, a, env, k)) in
                another (tick (with_kont (C.ev field env h, join_val addr vld mtd) kont'))
              | C.Co (_, _, vld, h, _), K.SetField2 (p, t, next, body, obj_val, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) vld
                    (fun a -> K.SetField3 (p, t, body, obj_val, a, env, k)) in
                another (tick (with_kont (C.ev next env h, join_val addr vld mtd) kont'))
              | C.Co (_, _, vld, h, _), K.SetField3 (p, t, body, obj_val, field_val, env, k) ->
                let addr, kont' =
                  with_addr ~old_kont:(Some kont) vld
                    (fun a -> K.SetField4 (p, t, obj_val, field_val, a, env, k)) in
                another (tick (with_kont (C.ev body env h, join_val addr vld mtd) kont'))
              | C.Co (_, _, body, h, _), K.SetField4 (p, t, ovladdr, fvladdr, nvladdr, env, k) ->
                let nv =
                  VSet.fold (fun v v' -> AValue.join v v') (S.get_vals nvladdr store) `Bot in
                let set_field addr ({ exten=ext } as attrs, props) fstr cds =
                  if props_mem fstr props then match props_find fstr props with
                  | Data ({ writable=`True; value=v } as dat, enum, config) ->
                    let nv' = AValue.join v nv in
                    let props' = props_add fstr
                      (Data ({ dat with value=nv' }, enum, config)) props in
                    CDSet.add (tick (C.co p nv' h k, join_obj addr (attrs, props') mtd)) cds
                  | Data _
                  | Accessor ({ setter=`Undef }, _, _) ->
                    let addr = kcfa_alloc context store (Some kont) None in
                    CDSet.add (tick (C.ex (E.Throw addr) env h,
                                     join_val addr (`Str "unwritable-field") mtd)) cds
                  | Accessor ({ setter=sv }, _, _) ->
                    CDSet.add (tick (C.ap p sv [`Obj addr; body] h k, mtd)) cds
                  | _ -> failwith "fell through setfield"
                  else
                    let iftrue =
                      let prop = Data ({ value=nv; writable=`True }, `True, `True) in
                      let props' = props_add fstr prop props in
                      tick (C.co p nv h k, join_obj addr (attrs, props') mtd) in
                    let iffalse = tick (C.co p `Undef h k, mtd) in
                    if ext = `Top then CDSet.add iftrue (CDSet.add iffalse cds)
                    else if ext = `True then CDSet.add iftrue cds
                    else CDSet.add iffalse cds in
                val_branch ovladdr cds
                  (fun ovl cds ->
                    val_branch fvladdr cds
                      (fun fvl cds -> match ovl, fvl with
                      | `Top, _ -> failwith "got a top object in setfield"
                      | `Obj oaddr, `Top ->
                        obj_branch oaddr cds
                          (fun ((_, props) as obj) cds ->
                            props_fold
                              (fun fstr _ cds -> set_field oaddr obj fstr cds)
                              props cds)
                      | `Obj oaddr, `Str fstr ->
                        obj_branch oaddr cds
                          (fun obj cds -> set_field oaddr obj fstr cds)
                      | _ -> failwith "set-field didn't get obj and string"))
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
                        with_addr ~old_kont:(Some kont) ~old_hand:(Some hand) valu
                           (fun a -> K.Finally2 (p, t, a, k)) in
                      another (tick (with_kont (C.ev exp env h, join_val addr valu mtd)
                                       kont'))
                    | _ ->
                      failwith "Encountered an unmatched co hk machine context."))
                  hands cds)) konts CDSet.empty
        | _ -> failwith "unfinished"
      end in
    
    transition (inject (alpha_unique exp) init_env init_store) G.empty
      
  end
    

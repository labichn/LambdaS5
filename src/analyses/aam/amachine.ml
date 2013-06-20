open Collects
open Lattices
open Aobject
open Acontext

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
type env = Env.env
let env_add = Env.env_add
let env_find = Env.env_find
let env_filter = Env.env_filter
let ids_mem = Env.ids_mem
type prop_map = Aobject.prop_map
let mt_props = Aobject.mt_props
let props_add = Aobject.props_add
let props_find = Aobject.props_find
let props_mem = Aobject.props_mem
let props_filter = Aobject.props_filter
let props_fold = Aobject.props_fold

let string_of_pos = Prelude.Pos.string_of_pos

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
let join_obj a o (os, vs, hs, ks, ats, ps) = begin
  print_endline ("binding "^(Ashared.string_of_addr a));
  ((a, o)::os, vs, hs, ks, ats, ps) end
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
  type t = context * version
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
    if log then begin print_string "Analyzing:\n" end;
    
    let kcfa_tick = ST.tick k in
    let kcfa_alloc = ST.alloc k in
    let kcfa_alloc' = ST.alloc' k in
    let kcfa_alloc_kont = ST.alloc_kont k in
    let kcfa_alloc_hand = ST.alloc_hand k in
    
    let inject exp env store = begin
      if log then print_endline "injecting... ";
      let au_exp = Au.alpha_unique exp in
      let t0 = [] in
      let context0 = C.Ev (au_exp, env, store, H.Mt, K.Mt, t0) in
      (VCSet.empty, CSet.singleton context0, store, [], 0)
    end in

    let append_deltas ds =
      List.fold_left
        (fun (vs', os', hs', ks', ats', ps') (vs, os, hs, ks, ats, ps) ->
          (vs @ vs', os @ os', hs @ hs', ks @ ks', ats @ ats', ps @ ps'))
        mtd ds in

    let replay_delta ((ods, vds, hds, kds, atds, pds) : delta)
        ((os, vs, hs, ks, ats, ps) as store : store) : store * bool =
      let force_val v store = match v with
        | `Delay addr -> begin
          if log then print_endline ("forcing val: "^(Ashared.string_of_addr addr));
          let vs = Astore.get_vals addr store in
          if log then print_endline ("got vals: "^(VSet.fold (fun v a -> (AValue.string_of v)^", ") vs ""));
          vs end
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
            else
              (true, AddrMap.add a (add x xs) m))
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
            let succs = step (with_store con store) in begin
            (if log then
              let size = CDSet.cardinal succs in 
                print_endline ("resulting in "^(string_of_int size)^
                                  (if size = 1 then " state:" else " states:"));
                CDSet.fold (fun (c, _) _ -> print_endline (C.string_of c)) succs (););
            CDSet.fold (fun (c,d) (i,ds)->((con, version), c)::i, d::ds) succs (i, ds) end)
          frontier ([], []) in
      let store', changed = replay_delta (append_deltas deltas) store in
      let version', stores' =
        if changed then version+1, store'::stores else version, stores in
      let seen', frontier', graph' =
        List.fold_left
          (fun ((seen', frontier', graph') as acc) ((pred, v), succ) ->
            let cv = (succ, version') in
            if not (VCSet.mem cv seen') then
              (VCSet.add cv seen',
               CSet.add succ frontier',
               G.add_edge graph' (pred, v) (succ, version'))
            else acc)
          (seen, CSet.empty, graph) i in
(*      let lls =
        CSet.fold (fun c lls -> Gc.union (Gc.locs_of_context c store') lls)
          frontier' Gc.mts in
      let gc_store = Gc.gc store' lls in*)
      if CSet.cardinal frontier' > 0 then
        transition (seen', frontier', store', stores', version') graph'
      else begin if log then print_endline "done.\n"; graph' end
    end

    (* Anywhere with a commented out failwith is a location that represents a
       code point that cannot occur due to λS5 desugaring. If we reach one
       during the course of analysis, we are not taking advantage of the assumptions
       that can be made based on the desugaring process. *)
    and step context =
      begin
        if log then print_endline ("  "^(C.string_of context)) ;
        let single = CDSet.singleton in
        
        (* helpers for ending a step
           macros would make this much cheaper *)
        let tick (ccon, delta) =
          ccon (kcfa_tick context), delta in
        let with_kont (ccon, delta) ckont =
          let kaddr = kcfa_alloc_kont context in
          ccon (ckont kaddr), join_kont kaddr (C.kont_of context) delta in
        let with_hand (ccon, delta) chand =
          let hkaddr = kcfa_alloc_hand context in
          ccon (chand hkaddr) K.Mt,
          join_hand hkaddr (C.hand_of context)
            (join_kont hkaddr (C.kont_of context) delta) in
        let with_addr v ckont = match v with
          | `Delay addr -> addr, ckont addr
          | _ -> let addr = kcfa_alloc context in addr, ckont addr in
        let with_addr' ckont =
          with_addr `Bot (* bot not used *) ckont in
        let branch lookup folder addr f = begin
          let xs = lookup addr (store_of context) in
          folder (fun x acc' -> CDSet.union (f x) acc') xs CDSet.empty end in
        let val_branch (*addr f*) = branch S.get_vals VSet.fold in
(*          f (VSet.fold (fun v absv -> AValue.join v absv) (S.get_vals addr store) `Bot) in*)
        let obj_branch = branch S.get_objs OSet.fold in
        let kont_branch = branch S.get_konts KSet.fold in
        let hand_branch = branch S.get_hands HSet.fold in

        match context with
        | C.Ans _ -> CDSet.empty (* if we try to step an ans, we've already added it to seen *)
        (* leaves *)
        | C.Ev (SYN.Undefined p, _, store, h, k, t) ->
          single (tick (C.co store p `Undef h k, mtd))
        | C.Ev (SYN.Null p, _, store, h, k, t) ->
          single (tick (C.co store p `Null h k, mtd))
        | C.Ev (SYN.String (p, s), _, store, h, k, t) ->
          single (tick (C.co store p (`Str s) h k, mtd))
        | C.Ev (SYN.Num (p, n), _, store, h, k, t) ->
          single (tick (C.co store p (`Num  n) h k, mtd))
        | C.Ev (SYN.True p, _, store, h, k, t) ->
          single (tick (C.co store p `True h k, mtd))
        | C.Ev (SYN.False p, _, store, h, k, t) ->
          single (tick (C.co store p `False h k, mtd))
        | C.Ev (SYN.Id (p, x), env, store, h, k, t) ->
          single (tick (C.co store p (`Delay (env_find x env)) h k, mtd))
        | C.Ev (SYN.Lambda (p, xs, body), env, store, h, k, t) ->
          let free = SYN.free_vars body in
          let env' = env_filter (fun var _ -> ids_mem var free) env in
          single (tick (C.co store p (`Clos (env', xs, body)) h k, mtd))

        (* SYN.SetBang (pos, name, next)
           Set name to next. *)
        | C.Ev (SYN.SetBang (p, x, new_val_exp), env, store, h, k, t) ->
          (match try Some (env_find x env) with Not_found -> None with
          | Some a ->
            single (tick (with_kont (C.ev store new_val_exp env h, mtd)
                                      (fun k -> K.SetBang (p, t, a, k))))
          | None -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (string_of_pos p)))
        | C.Co (K.SetBang (p, t, loc, k), _, v, store, h, _) ->
          kont_branch k
            (fun kont -> single (tick (C.co store p v h kont, join_val loc v mtd)))

        (* SYN.Object (pos, attrs, props)
           Evaluates the attrs, props, then adds the object to the store *)
        | C.Ev (SYN.Object (p, attrs, props), env, store, h, k, t) ->
          let attrs_p =
            let { SYN.proto=oe } = attrs in
            match oe with
            | Some e -> SYN.pos_of e
            | None -> failwith "no proto in attrs" in
          single (tick (with_kont (C.eva store attrs_p attrs env h, mtd)
                          (fun k -> K.Object (p, t, [], props, [], env, k))))
        | C.CoA (K.Object (p, t, [], [], [], _, k), _, attrs, store, h, _) ->
          (* empty props case *)
          let addr = kcfa_alloc context in
          kont_branch k
            (fun kont -> single (tick (C.co store p (`Obj addr) h kont,
                                       join_obj addr (attrs, mt_props) mtd)))
        | C.CoA (K.Object (p, t, [], prop::ps, [], env, k), _, attrsv, store, h, _) ->
          let addr, kont' =
            with_addr' (fun atta -> K.Object (p, t, [atta], ps, [], env, k)) in
          single (tick (C.evp store p prop env h kont', join_attrs addr attrsv mtd))
        | C.CoP (K.Object (p, t, atta, prop::ps, pvs, env, k), _, (n, pv), store, h, _) ->
          let addr, kont' =
            with_addr' (fun a -> K.Object (p, t, atta, ps, (n, a)::pvs, env, k)) in
          single (tick (C.evp store p prop env h kont', join_prop addr pv mtd))
        | C.CoP (K.Object (p', t, [atta], [], pvs, env, k), p, (name, pv), store, h, _) ->
          let attrsv = Aobject.combine_attrs (S.get_attrs atta store) in
          let props =
            List.fold_left
              (fun acc (name, addr) ->
                props_add name (Aobject.combine_props (S.get_props addr store)) acc)
              (props_add name pv mt_props)
              pvs in
          let addr = kcfa_alloc context in
          kont_branch k
            (fun kont ->
              single (tick (C.co store p' (`Obj addr) h kont, join_obj addr (attrsv, props) mtd)))

        (* SYN.Data ({ exp; writable }, enum, config)
           Evaluates exp, then continues with the propv to object creation.
           SYN.Accessor ({ getter; setter }, enum, config)
           Same as SYN.Data, but with getter and setter. *)
        | C.EvP (p, (name, prop), env, store, h, k, t) ->
          (match prop with
          | SYN.Data ({ SYN.value = valu; SYN.writable = writable; }, enum, config) ->
            single (tick (with_kont (C.ev store valu env h, mtd)
                            (fun k ->
                              K.DataProp (SYN.pos_of valu, t, name, writable, enum, config, k))))
          | SYN.Accessor ({ SYN.getter = getter; SYN.setter = setter; }, enum, config) ->
            single (tick (with_kont (C.ev store getter env h, mtd)
                            (fun k -> K.AccProp (SYN.pos_of getter, t, name, [setter], [],
                                                 enum, config, env, k)))))
        | C.Co (K.DataProp _ as k, p, `Delay a, store, h, t) ->
          val_branch a (fun vl -> single (tick (C.co store p vl h k, mtd)))
        | C.Co (K.DataProp (_, t, name, w, enum, config, k), p, vl, store, h, _) ->
          let datp =
            let ({ Lexing.pos_fname=n } as datp0, _, syn) = p in
            let datp1 = { datp0 with Lexing.pos_fname=(n^"done") } in
            (datp1, datp1, syn) in
          kont_branch k
            (fun kont ->
              single (tick (C.cop store datp name (Data ({ value=vl; writable=AValue.bool w; },
                                                   AValue.bool enum, AValue.bool config)) h kont,
                            mtd)))
        | C.Co (K.AccProp (p, t, name, [setter], [], e, c, env, k), _, getterv, store, h, _) ->
          let addr, kont' =
            with_addr getterv
              (fun gettera -> K.AccProp (p, t, name, [], [gettera], e, c, env, k)) in
          single (tick (C.ev store setter env h kont', join_val addr getterv mtd))
        | C.Co (K.AccProp (_, _, _, [], _, _, _, _, _) as k, p, `Delay a, store, h, t) ->
          val_branch a (fun vl -> single (tick (C.co store p vl h k, mtd)))
        | C.Co (K.AccProp (p, t, name, [], [ga], e, c, env, k), _, sv, store, h, _) ->
          kont_branch k
            (fun kont ->
              val_branch ga
                (fun gv -> single (tick (C.cop store p name
                                           (Accessor ({ getter=gv; setter=sv },
                                                      AValue.bool e, AValue.bool c)) h kont, mtd))))

        (* SYN.attrs : { primval; code; proto; class; extensible }
           Evaluates optional exps primval, code, and proto, then continues
           with an S.arrtsv. *)
        | C.EvA (p, attrs, env, store, h, k, t) ->
          let { SYN.primval = pexp;
                SYN.code = cexp;
                SYN.proto = proexp;
                SYN.klass = kls;
                SYN.extensible = ext; } = attrs in
          let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
          let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in begin print_endline ("$$$"^(List.fold_right (fun (str, syn) acc -> str^"="^(C.string_of_exp syn)^", "^acc) aes ""));
          (match aes with
          | [] ->
            let attrsv = { code=`Bot; proto=`Undef;
                           primv=`Bot; klass=`Str kls; exten=AValue.bool ext } in
            single (tick (C.coa store p attrsv h k, mtd))
          | (name, exp)::pairs ->
            single (tick (with_kont (C.ev store exp env h, mtd)
                            (fun k -> K.Attrs (p, t, name, pairs, [], kls, ext, env, k))))) end
        | C.Co (K.Attrs (p, t, name, (name', exp)::pairs, valus, kls, ext, env, k),
                _, valu, store, h, _) ->
          let addr, kont' =
            with_addr valu
              (fun a -> K.Attrs (p, t, name', pairs,
                                 (name, a)::valus, kls, ext, env, k)) in
          single (tick (C.ev store exp env h kont', join_val addr valu mtd))
        | C.Co (K.Attrs (p, t, name, [], valus, kls, ext, env, k), _, `Delay a, store, h, _)  ->
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
          let attp =
            let ({ Lexing.pos_fname=n } as attp0, _, syn) = p in
            let attp1 = { attp0 with Lexing.pos_fname=(n^"done") } in
            (attp1, attp1, syn) in
          kont_branch k (fun kont -> single (tick (C.coa store attp attrsv h kont, mtd)))
        | C.Co (K.Attrs (p, t, name, [], valus, kls, ext, env, k), _, v, store, h, _) ->
          let assoc_vls =
            (name, v)::(List.fold_left (fun a (n, ad) -> (n, `Delay ad)::a) [] valus) in
          let join_get str =
            if List.mem_assoc str assoc_vls then
              match List.assoc str assoc_vls with
              | `Delay a -> VSet.fold (fun v acc -> AValue.join v acc) (S.get_vals a store) `Bot
              | v -> v
            else `Bot in
          let code = join_get "code" in
          let prim = join_get "prim" in
          let proto =
            let v = join_get "proto" in
            match v with `Bot -> `Undef | _ -> v in
          let attrsv = { code=code; primv=prim; proto=proto;
                         klass=`Str kls; exten=AValue.bool ext } in
          let attp =
            let ({ Lexing.pos_fname=n } as attp0, _, syn) = p in
            let attp1 = { attp0 with Lexing.pos_fname=(n^"done") } in
            (attp1, attp1, syn) in
          kont_branch k (fun kont -> single (tick (C.coa store attp attrsv h kont, mtd)))

        (* SYN.GetAttr (pos, pattr, obj, field)
           Get the pattr for the obj's field. *)
        | C.Ev (SYN.GetAttr (p, pattr, obj, field), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k ->
                            K.GetAttr (p, t, pattr, [field], [], env, k))))
        | C.Co (K.GetAttr (p, t, pattr, [field], [], env, k), _, objv, store, h, _) ->
          let addr, kont' =  with_addr objv (fun a -> K.GetAttr (p, t, pattr, [], [a], env, k)) in
          single (tick (C.ev store field env h kont', join_val addr objv mtd))
        | C.Co (K.GetAttr (_, _, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
          val_branch a (fun vl -> single (tick (C.co store p vl h k, mtd)))
        | C.Co (K.GetAttr (p, t, attr, [], [obja], env, k), _, fieldv, store, h, _) ->
          val_branch obja
            (fun objv -> match objv, fieldv with
            | _, `Top -> kont_branch k (fun kont -> single (tick (C.co store p `Top h kont, mtd)))
            | `Obj a, `Str str ->
              obj_branch a
                (fun (attrs, props) ->
                  if not (props_mem str props) then
                    kont_branch k (fun kont -> single (tick (C.co store p `Undef h kont, mtd)))
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
                    kont_branch k (fun kont -> single (tick (C.co store p valu h kont, mtd))))
            | _ -> failwith "get_attr did not get an object and a string")

        (* SYN.SetAttr (pos, pattr, obj, field, next)
           The pattr for the obj's field is set to next *)
        | C.Ev (SYN.SetAttr (p, pattr, obj, field, next), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k -> K.SetAttr (p, t, pattr, [field; next], [], env, k))))
        | C.Co (K.SetAttr (p, t, pattr, [field; next], [], env, k), _, objv, store, h, _) ->
          let addr, kont' =
            with_addr objv (fun obja -> K.SetAttr (p, t, pattr, [next], [obja], env, k)) in
          single (tick (C.ev store field env h kont', join_val addr objv mtd))
        | C.Co (K.SetAttr (p, t, pattr, [next], [obja], env, k), _, fieldv, store, h, _) ->
          let addr, kont' =
            with_addr fieldv (fun fielda -> K.SetAttr (p, t, pattr, [], [obja; fielda], env, k)) in
          single (tick (C.ev store next env h kont', join_val addr fieldv mtd))
        | C.Co (K.SetAttr (_, _, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
          val_branch a (fun v -> single (tick (C.co store p v h k, mtd)))
        | C.Co (K.SetAttr (p, t, pattr, [], [obja; fielda], env, k), _, vl, store, h, _) ->
          let set_attr ((attrs, props) as obj) attr fv =
            let fields = match fv with
              | `Top -> props_fold (fun k _ a -> k::a) props []
              | `Str str -> [str]
              | _ -> failwith "Did not get a string in setattr!" in
            let props' =
              List.fold_left
                (fun props' fstr ->
                  let prop = D.set_attr pattr obj fstr vl in props_add fstr prop props')
                props fields in
            (attrs, props') in
          val_branch obja
            (fun objv ->
              val_branch fielda
                (fun fieldv -> match objv with
                | `Top ->
                  let (os, _, _, _, _, _) = store in
                  AddrMap.fold
                    (fun a objs cds ->
                      CDSet.union cds
                        (obj_branch a
                           (fun obj ->
                             let obj' = set_attr obj pattr fieldv in
                             kont_branch k
                               (fun kont ->
                                 single (tick (C.co store p `True h kont, join_obj a obj' mtd))))))
                    os CDSet.empty
                | `Obj oaddr ->
                  obj_branch oaddr
                    (fun obj -> begin
                      print_endline ((Ashared.string_of_addr oaddr)^" one obj getting attr set!");
                      kont_branch k
                        (fun kont ->
                          let obj' = set_attr obj pattr fieldv in
                          single (tick (C.co store p `True h kont, join_obj oaddr obj' mtd))) end)
                | _ -> failwith "Didn't get an object in setattr!"))

        (* SYN.GetObjAttr (pos, oattr, obj)
           Get the oattr for obj. *)
        | C.Ev (SYN.GetObjAttr (p, oattr, obj), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k -> K.GetObjAttr (p, t, oattr, env, k))))
        | C.Co (K.GetObjAttr _ as k, p, `Delay a, store, h, t) ->
          val_branch a (fun ov -> single (tick (C.co store p ov h k, mtd)))
        | C.Co (K.GetObjAttr (p, t, oattr, env, k), _, objv, store, h, _) ->
          let get_obj_attr attrs oattr = match attrs, oattr with
            | { proto=proto }, SYN.Proto -> proto
            | { exten=exten} , SYN.Extensible -> exten
            | { code=`Bot}, SYN.Code -> `Null
            | { code=code}, SYN.Code -> code
            | { primv=`Bot}, SYN.Primval -> failwith "[interp] Got Primval attr of Bot"
            | { primv=primv}, SYN.Primval -> primv
            | { klass=klass }, SYN.Klass -> klass in
          (match objv with
          | `Top -> kont_branch k (fun kont -> single (tick (C.co store p `Top h kont, mtd)))
          | `Obj oaddr ->
            obj_branch oaddr
              (fun (attrs, _) ->
                let v = get_obj_attr attrs oattr in
                kont_branch k (fun kont -> single (tick (C.co store p v h kont, mtd))))
          | _ -> failwith "[interp] GetObjAttr got a non-object.")

        (* SYN.SetObjAttr (pos, oattr, obj, next)
           The oattr for obj is set to next. *)
        | C.Ev (SYN.SetObjAttr (p, oattr, obj, next), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k ->
                            K.SetObjAttr (p, t, oattr, [next], [], env, k))))
        | C.Co (K.SetObjAttr (p, t, oattr, [next], [], env, k), _, ov, store, h, _) ->
          let addr, kont' =
            with_addr ov (fun obja -> K.SetObjAttr (p, t, oattr, [], [obja], env, k)) in
          single (tick (C.ev store next env h kont', join_val addr ov mtd))
        | C.Co (K.SetObjAttr (_, _, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
          val_branch a (fun vl -> single (tick (C.co store p vl h k, mtd)))
        | C.Co (K.SetObjAttr (p, t, oattr, [], [obja], env, k), _, vl, store, h, _) ->
          let set_attr ({ code=cod; proto=pro; exten=ext; klass=kls; primv=pri } as attrs)
              oattr = (match oattr with
              | SYN.Proto -> { attrs with proto=AValue.join pro vl }
              | SYN.Extensible -> { attrs with exten=AValue.join ext vl }
              | SYN.Primval -> { attrs with primv=AValue.join pri vl }
              | _ -> failwith "set object attr failed") in
          let set_obj_attr (attrs, props) =
            let attrsv = set_attr attrs oattr in (attrsv, props) in
          val_branch obja
            (fun vl -> match vl with
            | `Top -> failwith "got a top obj... fuck"
                  (*                    let (os, _, _, _, _, _) = store in
                                        AddrMap.fold (fun addr objs cds -> set_objs_attr addr objs cds) os cds*)
            | `Obj oaddr ->
              obj_branch oaddr
                (fun obj ->
                  kont_branch k
                    (fun kont -> single (tick (C.co store p vl h kont,
                                               join_obj oaddr (set_obj_attr obj) mtd))))
            | _ -> failwith "[interp] SetObjAttr got a non-object")

        (* SYN.GetField (pos, obj, field, body)
           If the getter field in obj is evaluated and, is a data
           property, continues with the value; if an accessor, evaluates
           the getter with the body and the obj values as arguments. *)
        | C.Ev (SYN.GetField (p, obj, field, body), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k -> 
                            K.GetField (p, t, [field; body], [], env, k))))
        | C.Co (K.GetField (p, t, [field; body], [], env, k), _, objv, store, h, _) ->
          let addr, kont' =
            with_addr objv (fun obja -> K.GetField (p, t, [body], [obja], env, k)) in
          single (tick (C.ev store field env h kont', join_val addr objv mtd))
        | C.Co (K.GetField (p, t, [body], [obja], env, k), _, fieldv, store, h, _) ->
          let addr, kont' =
            with_addr fieldv (fun fielda -> K.GetField (p, t, [], [obja; fielda], env, k)) in
          single (tick (C.ev store body env h kont', join_val addr fieldv mtd))
        | C.Co (K.GetField (p, t, [], [obja; fielda], env, k), _, bodyv, store, h, _) ->
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
          val_branch obja
            (fun objv ->
              val_branch fielda
                (fun fieldv -> match objv with
                | `Top ->
                  kont_branch k
                    (fun kont ->
                      (CDSet.add (tick (C.co store p `Top h kont, mtd))
                         (CDSet.add (tick (C.ap store p `Top [objv; bodyv] h kont, mtd))
                            (single (tick (C.co store p `Undef h kont, mtd))))))
                | `Obj oaddr ->
                  let objs = S.get_objs oaddr store in
                  let props =
                    List.fold_left
                      (fun a fstr -> PSet.union (get_props objs fstr) a)
                      PSet.empty (OSet.fold (fun o a -> (fields o fieldv)@a) objs []) in
                  if PSet.is_empty props then
                    kont_branch k (fun kont -> single (tick (C.co store p `Undef h kont, mtd)))
                  else
                    PSet.fold
                      (fun prop cds -> match prop with
                      | Data ({ value=v }, _, _) ->
                        kont_branch k (fun kont -> CDSet.add (tick (C.co store p v h kont, mtd)) cds)
                      | Accessor ({ getter=g }, _, _) ->
                        kont_branch k
                          (fun kont -> CDSet.add (tick (C.ap store p g [objv; bodyv] h kont, mtd)) cds)
                      | TopProp ->
                        kont_branch k
                          (fun kont ->
                            CDSet.add (tick (C.co store p `Top h kont, mtd))
                              (CDSet.add (tick (C.ap store p `Top [objv; bodyv] h kont, mtd)) cds)))
                      props
                      CDSet.empty
                | _ -> failwith ("[interp] Get field didn't get an object and a " ^
                                    "string at " ^ string_of_pos p ^ ".")))

        (* SYN.OwnFieldNames (pos, obj)
           Create an object in the store with a map of indices to all
           obj's properties and the count of that map. *)
        | C.Ev (SYN.OwnFieldNames (p, obj), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k -> K.OwnFieldNames (p, t, k))))
        | C.Co (K.OwnFieldNames _ as k, p, `Delay a, store, h, t) ->
          val_branch a (fun vl -> single (tick (C.co store p vl h k, mtd)))
        | C.Co (K.OwnFieldNames (p, t, k), _, ovl, store, h, _) ->
          let get_props objs =
            OSet.fold
              (fun (_, props) l -> props_fold (fun k _ l -> k::l) props [])
              objs [] in
          let add_name n x m = props_add (string_of_int x)
            (Data ({ value=`Str n; writable = `False; }, `False, `False)) m in
          let addr = kcfa_alloc context in
          let names, len = match ovl with
            | `Top ->
              let (os, _, _, _, _, _) = store in
              AddrMap.fold (fun _ objs names -> (get_props objs) @ names) os [], `Top
            | `Obj oaddr ->
              let names = get_props (S.get_objs oaddr store) in
              names, `Num (float_of_int (List.length names))
            | _ -> failwith "did not get object in ownfieldnames" in
          let props = List.fold_right2 add_name names
            (Prelude.iota (List.length names)) mt_props in
          let final_props =
            props_add "length"
              (Data ({ value=len; writable=`False }, `False, `False)) props in
          kont_branch k
            (fun kont ->
              single (tick (C.co store p (`Obj addr) h kont,
                            join_obj addr (default_attrs, final_props) mtd)))

        (* SYN.DeleteField(pos, obj, field)
           Deletes field from obj. *)
        | C.Ev (SYN.DeleteField (p, obj, field), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k -> K.DeleteField (p, t, [field], [], env, k))))
        | C.Co (K.DeleteField (p, t, [field], [], env, k), _, objv, store, h, _) ->
          let addr, kont' =
            with_addr objv (fun obja -> K.DeleteField (p, t, [], [obja], env, k)) in
          single (tick (C.ev store field env h kont', join_val addr objv mtd))
        | C.Co (K.DeleteField (_, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
          val_branch a (fun vl -> single (tick (C.co store p vl h k, mtd)))
        | C.Co (K.DeleteField (p, t, [], [obja], env, k), _, fieldv, store, h, _) ->
          val_branch obja
            (fun objv -> match objv, fieldv with
            | _, `Top | `Top, _ ->
              kont_branch k (fun kont -> single (tick (C.co store p `True h kont, mtd)))
            | `Obj oaddr, `Str str ->
              obj_branch oaddr
                (fun (attrs, props) ->
                  if props_mem str props then
                    match props_find str props with
                    | Data (_, _, `True)
                    | Accessor (_, _, `True) ->
                      kont_branch k (fun kont -> single (tick (C.co store p `True h kont, mtd)))
                    | _ ->
                      let addr = kcfa_alloc context in
                      single (tick (C.ex store (E.Throw addr) env h,
                                    join_val addr (`Str "unconfigurable-delete") mtd))
                  else kont_branch k (fun kont -> single (tick (C.co store p `False h kont, mtd))))
            | _, _ -> failwith "fell through deletefield2")

        (* SYN.SetField (pos, obj, field, next, body)
           Sets obj's field to next by executing body. *)
        | C.Ev (SYN.SetField (p, obj, field, next, body), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store obj env h, mtd)
                          (fun k -> K.SetField (p, t, [field; next; body], [], env, k))))
        | C.Co (K.SetField (p, t, [field; next; body], [], env, k), _, objv, store, h, _) ->
          let addr, kont' =
            with_addr objv (fun obja -> K.SetField (p, t, [next; body], [obja], env, k)) in
          single (tick (C.ev store field env h kont', join_val addr objv mtd))
        | C.Co (K.SetField (p, t, [next; body], [obja], env, k), _, fieldv, store, h, _) ->
          let addr, kont' =
            with_addr fieldv (fun fielda -> K.SetField (p, t, [body], [obja; fielda], env, k)) in
          single (tick (C.ev store next env h kont', join_val addr fieldv mtd))
        | C.Co (K.SetField (p, t, [body], [obja; fielda], env, k), _, nextv, store, h, _) ->
          let addr, kont' =
            with_addr nextv (fun nexta -> K.SetField (p, t, [], [obja; fielda; nexta], env, k)) in
          single (tick (C.ev store body env h kont', join_val addr nextv mtd))
        | C.Co (K.SetField (p, t, [], [obja; fielda; nexta], env, k), _, bodyv, store, h, _) ->
          let nextv =
            VSet.fold (fun v v' -> AValue.join v v') (S.get_vals nexta store) `Bot in
          let set_field addr ({ exten=ext } as attrs, props) fstr =
            if props_mem fstr props then match props_find fstr props with
            | Data ({ writable=`True; value=v } as dat, enum, config) ->
              let nextv' = AValue.join v nextv in
              let props' = props_add fstr
                (Data ({ dat with value=nextv' }, enum, config)) props in
              kont_branch k
                (fun kont -> single (tick (C.co store p nextv' h kont,
                                           join_obj addr (attrs, props') mtd)))
            | Data _
            | Accessor ({ setter=`Undef }, _, _) ->
              let addr = kcfa_alloc context in
              single (tick (C.ex store (E.Throw addr) env h,
                            join_val addr (`Str "unwritable-field") mtd))
            | Accessor ({ setter=sv }, _, _) ->
              kont_branch k (fun kont -> single (tick (C.ap store p sv [`Obj addr; bodyv] h kont, mtd)))
            | _ -> failwith "fell through setfield"
            else
              let iftrue = fun () ->
                let prop = Data ({ value=nextv; writable=`True }, `True, `True) in
                let props' = props_add fstr prop props in
                kont_branch k
                  (fun kont -> single (tick (C.co store p nextv h kont,
                                             join_obj addr (attrs, props') mtd))) in
              let iffalse = fun () ->
                kont_branch k (fun kont -> single (tick (C.co store p `Undef h kont, mtd))) in
              if ext = `Top then CDSet.union (iftrue()) (iffalse())
              else if ext = `True then (iftrue())
              else (iffalse()) in
          val_branch obja
            (fun objv ->
              val_branch fielda
                (fun fieldv -> match objv, fieldv with
                | `Top, _ -> failwith "got a top object in setfield"
                | `Obj oaddr, `Top ->
                  obj_branch oaddr
                    (fun ((_, props) as obj) ->
                      props_fold
                        (fun fstr _ cds -> CDSet.union (set_field oaddr obj fstr) cds)
                        props CDSet.empty)
                | `Obj oaddr, `Str fstr ->
                  obj_branch oaddr
                    (fun obj -> set_field oaddr obj fstr)
                | _ -> failwith "set-field didn't get obj and string"))

        (* SYN.Op1 (pos, name, arg)
           Evaluates a unary operation name on arg. *)
        | C.Ev (SYN.Op1 (p, name, arg), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store arg env h, mtd)
                          (fun k -> K.OpOne (p, t, name, env, k))))
        | C.Co (K.OpOne (p, t, name, env, _) as k, _, `Delay a, store, h, _) ->
          val_branch a (fun argv -> single (tick (C.co store p argv h k, mtd)))
        | C.Co (K.OpOne (p, t, name, env, k), _, `Top, store, h, _) ->
          kont_branch k (fun kont -> single (tick (C.co store p `Top h kont, mtd)))
        | C.Co (K.OpOne (p, t, name, env, k), _, argv, store, h, _) ->
          kont_branch k (fun kont -> single (tick (C.co store p (op1 store name argv) h kont, mtd)))

        (* SYN.Op2 (pos, name, arg1, arg2)
           Evaluates a binary operation name on arg1 and arg2. *)
        | C.Ev (SYN.Op2 (p, name, arg1, arg2), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store arg1 env h, mtd)
                          (fun k -> K.OpTwo (p, t, name, [arg2], [], env, k))))
        | C.Co (K.OpTwo (p, t, name, [arg2], [], env, k), _, arg1v, store, h, _) ->
          let addr, kont' =
            with_addr arg1v (fun arg1a -> K.OpTwo (p, t, name, [], [arg1a], env, k)) in
          single (tick (C.ev store arg2 env h kont', join_val addr arg1v mtd))
        | C.Co (K.OpTwo (_, _, _, [], _, _, _) as k, p, `Delay arg2a, store, h, t) ->
          val_branch arg2a (fun arg2v -> single (tick (C.co store p arg2v h k, mtd)))
        | C.Co (K.OpTwo (p, t, name, [], [arg1a], env, k), _, arg2v, store, h, _) ->
          val_branch arg1a
            (fun arg1v ->
              kont_branch k
                (fun kont -> match arg1v with
                | `Top -> single (tick (C.co store p `Top h kont, mtd))
                | _ -> single (tick (C.co store p (op2 store name arg1v arg2v) h kont, mtd))))

        (* SYN.If (pos, pred, then, else)
           Evaluates then if pred, else otherwise. *)
        | C.Ev (SYN.If (p, pred, than, elze), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store pred env h, mtd)
                          (fun k -> K.If (p, t, env, than, elze, k))))
        | C.Co (K.If (p, t, env, than, elze, _) as k, _, `Delay a, store, h, _) ->
          val_branch a (fun predv -> single (tick (C.co store p predv h k, mtd)))
        | C.Co (K.If (p, t, env, than, elze, k), _, `Top, store, h, _) ->
          kont_branch k
            (fun kont -> CDSet.add (tick (C.ev store than env h kont, mtd))
              (single (tick (C.ev store elze env h kont, mtd))))
        | C.Co (K.If (p, t, env, than, elze, k), _, predv, store, h, _) ->
          kont_branch k
            (fun kont ->match predv with
            | `Top ->
              CDSet.add (tick (C.ev store than env h kont, mtd))
                (single (tick (C.ev store elze env h kont, mtd)))
            | `True -> single (tick (C.ev store than env h kont, mtd))
            | _ ->     single (tick (C.ev store elze env h kont, mtd)))

        (* SYN.App (pos, func, args)
           Applies the body of func with the given args. *)
        | C.Ev (SYN.App (p, func, args), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store func env h, mtd)
                          (fun k -> K.App (p, t, env, args, [], k))))
        | C.Co (K.App (p, t, env, [], [], k), _, funcv, store, h, _) -> (* no arg app *)
          kont_branch k (fun kont -> single (tick (C.ap store p funcv [] h kont, mtd)))
        | C.Co (K.App (p, t, env, expr::exprs, [], k), _, funcv, store, h, _) ->
          let addr, kont' =
            with_addr funcv (fun funca -> K.App (p, t, env, exprs, [funca], k)) in
          single (tick (C.ev store expr env h kont', join_val addr funcv mtd))
        | C.Co (K.App (p, t, env, expr::exprs, vas, k), _, argv, store, h, _) ->
          let addr, kont' =
            with_addr argv
              (fun arga -> K.App (p, t, env, exprs, arga::vas, k)) in
          single (tick (C.ev store expr env h kont', join_val addr argv mtd))
        | C.Co (K.App (p, t, env, [], vas, k), _, argv, store, h, _) ->
          let funcv, argvs = 
            let rec last_is_funca vas (not_yet_funcv, argvs) = match vas with
              | [funca] -> `Delay funca, argvs
              | arga::vas -> last_is_funca vas (not_yet_funcv, (`Delay arga)::argvs) in
            last_is_funca vas (`Bot, [argv]) in
          kont_branch k (fun kont -> single (tick (C.ap store p funcv argvs h kont, mtd)))
        | C.Ap (p, `Top, vs, store, h, k, t) ->
          single (tick (C.co store p `Top h k, mtd))
        | C.Ap (p, `Delay a, vs, store, h, k, t) ->
          val_branch a (fun v -> single (tick (C.ap store p v vs h k, mtd)))
        | C.Ap (p, `Clos (env, xs, body), vs, store, h, k, t) ->
          if (List.length vs) != (List.length xs) then
            E.arity_mismatch_err p xs vs
          else
            let rec foldr_3 f b xs ys zs = match xs, ys, zs with
              | [], [], [] -> b
              | x::xs', y::ys', z::zs' -> f x y z (foldr_3 f b xs' ys' zs')
              | _, _, _ -> failwith "different length lists, you doofus" in
            let addrs = kcfa_alloc' context in
            let env', delta =
              foldr_3
                (fun x a v (env', s) -> env_add x a env', join_val a v s)
                (env, mtd) xs addrs vs in
            single (tick (C.ev store body env' h k, delta))
        | C.Ap (p, `Obj a, vs, store, h, k, t) ->
          obj_branch a
            (fun ({ code=code }, _) -> match code with
            | `Bot -> failwith ("Applied an object without a code attribute at "^
                                   (Ashared.string_of_addr a))
            (* The above case shouldn't be possible due to desugaring. Let's 
                 see if it ever comes up in testing. *)
            | _ -> single (tick (C.ap store p code vs h k, mtd)))
        | C.Ap (p, f, vlds, store, h, k, t) ->
         failwith (E.interp_error p ("Applied non-function: "^(AValue.string_of f)))

        (* SYN.Seq (pos, left, right)
           Evaluates left then right, continuing with right's value. *)
        | C.Ev (SYN.Seq (p, left, right), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store left env h, mtd)
                          (fun k -> K.Seq (p, t, right, env, k))))
        | C.Co (K.Seq (p, t, right, env, k), _, _, store, h, _) ->
          kont_branch k (fun kont -> single (tick (C.ev store right env h kont, mtd)))

        (* SYN.Let (pos, name, expr, body)
           Evaluates body with name bound to expr. *)
        | C.Ev (SYN.Let (p, name, expr, body), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store expr env h, mtd)
                          (fun k -> K.Let (p, t, name, body, env, k))))
        | C.Co (K.Let (p, t, name, body, env, k), _, v, store, h, _) ->
          let addr = kcfa_alloc context in
          kont_branch k
            (fun kont ->
              single (tick (C.ev store body (env_add name addr env) h kont, join_val addr v mtd)))

        (* SYN.Rec (pos, name, expr, body)
           Evaluates body with name bound to expr, which may contain
           recursive references to name. *)
        | C.Ev (SYN.Rec (p, name, expr, body), env, store, h, k, t) ->
          let new_loc = kcfa_alloc context in
          let env' = env_add name new_loc env in
          single (tick (with_kont (C.ev store expr env' h, mtd)
                          (fun k -> K.Rec (p, t, new_loc, body, env', k))))
        | C.Co (K.Rec (p, t, new_loc, body, env, k), _, v, store, h, _) ->
          kont_branch k (fun kont -> single (tick (C.ev store body env h kont, join_val new_loc v mtd)))

        (* SYN.Label (pos, name, expr)
           Evaluates expr, catching any Breaks with the matching name. *)
        | C.Ev (SYN.Label (p, name, exp), env, store, h, k, t) ->
          single (tick (with_hand (C.ev store exp env, mtd)
                          (fun hk -> H.Lab (p, t, name, env, hk, hk))))
        | C.Ex ((E.Break (label, a) as brk), env, store, H.Lab (p, _, name, _, k, h), _) ->
          hand_branch h
            (fun hand ->
              if name = label then 
                kont_branch k (fun kont -> single (tick (C.co store p (`Delay a) hand kont, mtd)))
              else single (tick (C.ex store brk env hand, mtd)))

        (* SYN.Break (pos, label, expr)
           Breaks to label with expr as the value passed back. *)
        | C.Ev (SYN.Break (p, label, expr), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store expr env h, mtd)
                          (fun k -> K.Break (p, t, label, env, k))))
        | C.Co (K.Break (p, t, label, env, k), _, v, store, h, _) ->
          let addr = kcfa_alloc context in
          single (tick (C.ex store (E.Break (label, addr)) env h, join_val addr v mtd))

        (* SYN.TryCatch (pos, body, catch)
           Evaluates body, evaluating catch with the thrown value as an
           argument if a Throw is lobbed up. *)
        | C.Ev (SYN.TryCatch (p, body, catch), env, store, h, k, t) ->
          single (tick (with_hand (C.ev store body env, mtd)
                          (fun hk -> H.Cat (p, t, catch, env, hk, hk))))
        | C.Ex (E.Throw throwa, _, store, H.Cat (p, t, catch, env, k, h), _) ->
          (*          let vld = `Delay throwv in
                      let addr, ckont = with_addr vld (fun a k -> (K.Catch (p, t, a, env, k))) in*)
          hand_branch h
            (fun hand -> single (tick (with_kont (C.ev store catch env hand, mtd)
                                         (fun k -> K.Catch (p, t, throwa, env, k)))))
        | C.Co (K.Catch (p, t, throwv, env, k), _, catchv, store, h, _) ->
          kont_branch k (fun kont -> single (tick (C.ap store p catchv [`Delay throwv] h kont, mtd)))

        (* SYN.TryFinally (pos, body, fin)
           Evaluates body then fin; if an exception is thrown from body
           fin will be executed and the exn's store is updated. *)
        | C.Ev (SYN.TryFinally (p, body, fin), env, store, h, k, t) ->
          single (tick (with_hand (C.ev store body env, mtd)
                          (fun hk -> H.Fin (p, t, fin, env, hk, hk))))
        | C.Ex (ex, _, store, H.Fin (p, t, fin, env, k, h), _) ->
          hand_branch h
            (fun hand -> single (tick (with_kont (C.ev store fin env hand, mtd)
                                         (fun k -> K.Finally (p, t, [ex], [], env, k)))))
        | C.Co (K.Finally (p, t, [ex], [], env, k), _, _, store, h, _) ->
          single (tick (C.ex store ex env h, mtd))
        | C.Co (K.Finally (p, t, [], [valu], env, k), _, _, store, h, _) ->
          kont_branch k (fun kont -> single (tick (C.co store p (`Delay valu) h kont, mtd)))

        (* SYN.Throw (pos, expr)
           Lobs expr up through the handles. *)
        | C.Ev (SYN.Throw (p, expr), env, store, h, k, t) ->
          single (tick (with_kont (C.ev store expr env h, mtd)
                          (fun k -> K.Throw (p, t, env, k))))
        | C.Co (K.Throw (p, t, env, k), _, valu, store, h, _) ->
          let addr = kcfa_alloc context in
          single (tick (C.ex store (E.Throw addr) env h, join_val addr valu mtd))

        (* SYN.Eval (pos, str_expr, bindings)
           Evaluates str_expr with the fields defined in the object *)
        | C.Ev (SYN.Eval (p, str, bindings), env, store, h, k, t) ->
          single (tick (C.co store p `Top h k, mtd))
          (* REVISIT!!! This is a lie, especially the mtd!!!
          single (tick (with_kont (C.ev store str env h, mtd)
             (K.Eval (p, t, bindings, env, k))))*)

        (* SYN.Hint (pos, str, expr)
           Evaluates expr, continuing with a Snapshot if str is
           "___takeS5Snapshot", or just continues with expr's val. *)
        | C.Ev (SYN.Hint (p, _, expr), env, store, h, k, t) -> (* ignore hints, no snaps *)
          single (tick (C.ev store expr env h k, mtd))

        (* shedding handles... *)
        | C.Ex (ex, env, store, H.Mt, t) -> CDSet.empty
        | C.Ex (ex, env, store, h, t) ->
          hand_branch (H.hand_of h) (fun hand -> single (tick (C.ex store ex env hand, mtd)))
        | C.Co (K.Mt, _, valu, store, H.Mt, _) -> single (tick (C.ans store valu, mtd))
        | C.Co (K.Mt, _, valu, store, H.Lab (p, t, name, env, k, h), _) ->
          kont_branch k
            (fun kont -> hand_branch h (fun hand -> single (tick (C.co store p valu hand kont, mtd))))
        | C.Co (K.Mt, _, valu, store, H.Cat (p, t, _, _, k, h), _) ->
          kont_branch k
            (fun kont -> hand_branch h (fun hand -> single (tick (C.co store p valu hand kont, mtd))))
        | C.Co (K.Mt, _, valu, store, H.Fin (p, t, exp, env, k, h), _) ->
          let addr, kont' = with_addr valu (fun a -> K.Finally (p, t, [], [a], env, k)) in
          hand_branch h
            (fun hand -> single (tick (C.ev store exp env hand kont', join_val addr valu mtd)))

        (* you really screwed up. *)
        | _ ->
          print_endline "oh noes!";
          print_endline (Acontext.string_of context);
          print_endline (Akont.string_of (C.kont_of context));
          print_endline (Ahandle.string_of (C.hand_of context));
          failwith "Encountered an unmatched machine context."
      end in

    (* here we go *)
    transition (inject exp init_env init_store) G.empty
      
  end
    

module SYN = Ljs_syntax

(** Ties an AAM into the step function, by lifting a context up into the result
 *  expected by the AAM's transition. *)
module type LOCK = sig
  type addr type time type context type objekt type value type kont
  type hand type attrsv type propv type 'a lcon type input type output
  val context_of_input: input -> context
  val add_obj: addr -> objekt -> context lcon -> context lcon
  val add_val: addr -> value -> context lcon -> context lcon
  val set_obj: addr -> objekt -> context lcon -> context lcon
  val set_val: addr -> value -> context lcon -> context lcon
  val add_attrsv: addr -> attrsv -> context lcon -> context lcon
  val add_propv: addr -> propv -> context lcon -> context lcon
  val desugar: string -> SYN.exp
  val tick: context -> (time -> context) lcon -> context lcon
  val clift: 'a -> 'a lcon
  val olift: context lcon -> output
  val alloc: context -> addr
  val clos_alloc: context -> addr list
  val eval_alloc: context -> addr list list
  val with_hand: context -> (hand -> kont -> time -> context) lcon ->
    (addr -> hand) -> (time -> context) lcon
  val with_kont: context -> (kont -> time -> context) lcon ->
    (addr -> kont) -> (time -> context) lcon
  val another: context lcon -> output -> output
  val empty: output
  val union: output -> output -> output
  val verbose: bool
end

module type S = sig
  type input
  type output
  val step: input -> output
end

module Make
  (Conf : Aam_conf.S)
  (ERR : Aam_error.S
   with type addr = Conf.addr)
  (E : Aam_env.S)
  (V : Aam_lattices.S
   with type addr = Conf.addr
   and type env = Conf.addr E.t)
  (O : Aam_object.S
   with type value = V.t)
  (H : Aam_handle.S
   with type addr = Conf.addr
   and type time = Conf.time
   and type env = Conf.addr E.t)
  (K : Aam_kont.S
   with type addr = Conf.addr
   and type time = Conf.time
   and type env = Conf.addr E.t)
  (S : Aam_store.S
   with type addr = Conf.addr
   and type objekt = O.t
   and type value = V.t
   and type hand = H.t
   and type kont = K.t
   and type attrsv = O.attrsv
   and type propv = O.propv
   and type objekts = O.OSet.t
   and type values = V.VSet.t
   and type hands = H.HSet.t
   and type konts = K.KSet.t
   and type attrsvs = O.ASet.t
   and type propvs = O.PSet.t
   and module AddrSet = Conf.AddrSet)
  (D : Aam_delta.S
   with type store = S.t
   and type value = V.t)
  (C : Aam_context.S
   with type attrsv = O.attrsv
   and type env = Conf.addr E.t
   and type hand = H.t
   and type kont = K.t
   and type propv = O.propv
   and type store = S.t
   and type time = Conf.time
   and type value = V.t)
  (LS : LOCK
   with type addr = Conf.addr
   and type time = Conf.time
   and type context = C.t
   and type objekt = O.t
   and type value = V.t
   and type kont = K.t
   and type hand = H.t
   and type attrsv = O.attrsv
   and type propv = O.propv) = struct

  type input = LS.input
  type output = LS.output

  let nap exn = LS.olift (LS.clift (C.NAP exn))

  let step input = begin
    let context = LS.context_of_input input in
    
    (* helpers for ending a step *)
    let tick = LS.tick context in
    let with_kont = LS.with_kont context in
    let with_hand = LS.with_hand context in
    let with_addr v ckont = match v with
      | `Delay addr -> addr, ckont addr
      | _ -> let addr = LS.alloc context in addr, ckont addr in
    let with_addr' ckont = with_addr `Bot (* bot not used *) ckont in
    let branch lookup folder addr f = begin
      let xs = lookup addr (C.store_of context) in
      folder (fun x acc' -> LS.union (f x) acc') xs LS.empty end in
    let  val_branch = branch S.get_vals  V.VSet.fold in
    let kont_branch = branch S.get_konts K.KSet.fold in
    let hand_branch = branch S.get_hands H.HSet.fold in
    let  obj_branch = branch S.get_objs  O.OSet.fold in
    let objs_branch store f =
      Conf.AddrSet.fold (fun a outs -> LS.union (obj_branch a (f a)) outs)
        (S.get_obj_addrs store) LS.empty in

    match context with
    | C.Ans _ -> LS.empty

    (* leaves *)
    | C.Ev (SYN.Undefined p, _, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.co store p `Undef h k)))
    | C.Ev (SYN.Null p, _, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.co store p `Null h k)))
    | C.Ev (SYN.String (p, s), _, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.co store p (V.str s) h k)))
    | C.Ev (SYN.Num (p, n), _, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.co store p (V.num n) h k)))
    | C.Ev (SYN.True p, _, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.co store p (V.bool true) h k)))
    | C.Ev (SYN.False p, _, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.co store p (V.bool false) h k)))
    | C.Ev (SYN.Id (p, x), env, store, h, k, t) ->
      print_endline ("Var: "^x);
      LS.olift (tick (LS.clift (C.co store p (V.delay (E.find x env)) h k)))
    | C.Ev (SYN.Lambda (p, xs, body), env, store, h, k, t) ->
      let free = SYN.free_vars body in
      let env' = E.filter (fun var _ -> Prelude.IdSet.mem var free) env in
      LS.olift (tick (LS.clift (C.co store p (`Clos (env', xs, body)) h k)))

    (* function application *)
    | C.Ap (p, `Top, vs, store, h, k, t) ->
      (* TODO: is there a good reason to keep going here? Why not just halt with
         some "anything can happen" state? *)
      LS.olift (tick (LS.clift (C.co (S.to_top store) p `Top h k)))
    | C.Ap (p, `Delay a, vs, store, h, k, t) ->
      val_branch a
        (fun v -> LS.olift (tick (LS.clift (C.ap store p v vs h k))))
    | C.Ap (p, `Clos (env, xs, body), vs, store, h, k, t) ->
      if (List.length vs) != (List.length xs) then
        raise (ERR.interp_error p "arity mismatch!!!")
      else
        let rec foldr_3 f b xs ys zs = match xs, ys, zs with
          | [], [], [] -> b
          | x::xs', y::ys', z::zs' -> f x y z (foldr_3 f b xs' ys' zs')
          | _, _, _ -> failwith "ap arity mismatch" in
        let addrs = LS.clos_alloc context in
        let env', avs =
          foldr_3
            (fun x a v (env', avs) -> E.add x a env', (a, v)::avs)
            (env, []) xs addrs vs in
        let lifted_con =
          List.fold_left
            (fun lcon (a, v) -> LS.add_val a v lcon)
            (tick (LS.clift (C.ev store body env' h k))) avs in
        LS.olift lifted_con
    | C.Ap (p, `Obj a, vs, store, h, k, t) ->
      obj_branch a
        (fun ({ O.code=code }, _) -> match code with
        | `Bot -> nap (Failure ("Applied an object without a code "^
                                   "attribute at "^ (Conf.string_of_addr a)))
        | _ -> LS.olift (tick (LS.clift (C.ap store p code vs h k))))
    | C.Ap (p, f, vlds, store, h, k, t) -> begin
      print_endline ("gah! what did I try to apply??: "^(V.string_of f));
      nap (Failure ("Applied non-function: "^(V.string_of f))) end

    (* SYN.SetBang (pos, name, next)
       Set name to next. *)
    | C.Ev (SYN.SetBang (p, x, new_val_exp), env, store, h, k, t) ->
      (match try Some (E.find x env) with Not_found -> None with
      | Some a ->
        LS.olift (tick (with_kont (LS.clift (C.ev store new_val_exp env h))
                          (fun k -> K.SetBang (p, t, a, k))))
      | None -> failwith ("[interp1] Unbound identifier: " ^ x
                          ^ " in identifier lookup at " ^
                            (Conf.string_of_pos p)))
    | C.Co (K.SetBang (p, t, loc, k), _, v, store, h, _) ->
      kont_branch k
        (fun kont ->
          LS.olift (LS.set_val loc v (tick (LS.clift (C.co store p v h kont)))))

    (* SYN.Object (pos, attrs, props)
       Evaluates the attrs, props, then adds the object to the store *)
    | C.Ev (SYN.Object (p, attrs, props), env, store, h, k, t) ->
      let attrs_p =
        let { SYN.proto=oe } = attrs in
        match oe with
        | Some e -> SYN.pos_of e
        | None -> failwith "no proto in attrs" in
      LS.olift (tick (with_kont (LS.clift (C.eva store attrs_p attrs env h))
                     (fun k -> K.Object (p, t, [], props, [], env, k))))
    | C.CoA (K.Object (p, t, [], [], [], _, k), _, attrs, store, h, _) ->
      let addr = LS.alloc context in
      kont_branch k
        (fun kont ->
          LS.olift (LS.add_obj addr (attrs, O.PMap.empty)
                      (tick (LS.clift (C.co store p (V.obj addr) h kont)))))
    | C.CoA (K.Object (p, t, [], prop::ps, [], env, k),
             _, attrsv, store, h, _) ->
      let addr, kont' =
        with_addr' (fun atta -> K.Object (p, t, [atta], ps, [], env, k)) in
      LS.olift (LS.add_attrsv addr attrsv
                  (tick (LS.clift (C.evp store p prop env h kont'))))
    | C.CoP (K.Object (p, t, atta, prop::ps, pvs, env, k),
             _, (n, pv), store, h, _) ->
      let addr, kont' =
        with_addr' (fun a -> K.Object (p, t, atta, ps, (n, a)::pvs, env, k)) in
      LS.olift (LS.add_propv addr pv
                  (tick (LS.clift (C.evp store p prop env h kont'))))
    | C.CoP (K.Object (p', t, [atta], [], pvs, env, k),
             p, (name, pv), store, h, _) ->
      let obj = O.make_obj (S.get_attrsvs atta store)
        (List.fold_left
           (fun nps (n, a) -> (n, S.get_propvs a store)::nps)
           [(name, O.PSet.singleton pv)] pvs) in
      let addr = LS.alloc context in
      kont_branch k
        (fun kont -> LS.olift
          (LS.add_obj addr obj
             (tick (LS.clift (C.co store p' (V.obj addr) h kont)))))

    (* SYN.Data ({ exp; writable }, enum, config)
       Evaluates exp, then continues with the propv to object creation.
       SYN.Accessor ({ getter; setter }, enum, config)
       Same as SYN.Data, but with getter and setter. *)
    | C.EvP (p, (n, prop), env, store, h, k, t) ->
      (match prop with
      | SYN.Data ({ SYN.value=v; SYN.writable=w; }, e, c) ->
        LS.olift (tick (with_kont (LS.clift (C.ev store v env h))
                       (fun k -> K.DataProp (p, t, n, w, e, c, k))))
      | SYN.Accessor ({ SYN.getter=g; SYN.setter=s; }, e, c) ->
        LS.olift (tick (with_kont (LS.clift (C.ev store g env h))
                       (fun k -> K.AccProp (p, t, n, [s], [], e, c, env, k)))))
    | C.Co (K.DataProp _ as k, p, `Delay a, store, h, t) ->
      val_branch a (fun vl -> LS.olift (tick (LS.clift (C.co store p vl h k))))
    | C.Co (K.DataProp (p, t, name, w, enum, config, k), _, vl, store, h, _) ->
      kont_branch k
        (fun kont ->
          let dat = O.Data ({ O.value=vl; O.writable=V.bool w; },
                            V.bool enum, V.bool config) in
          LS.olift (tick (LS.clift (C.cop store p name dat h kont))))
    | C.Co (K.AccProp (p, t, name, [setter], [], e, c, env, k),
            _, getterv, store, h, _) ->
      let addr, kont' =
        with_addr getterv
          (fun gettera ->
            K.AccProp (p, t, name, [], [gettera], e, c, env, k)) in
      LS.olift (LS.add_val addr getterv
                  (tick (LS.clift (C.ev store setter env h kont'))))
    | C.Co (K.AccProp (_, _, _, [], _, _, _, _, _) as k,
            p, `Delay a, store, h, t) ->
      val_branch a (fun vl -> LS.olift (tick (LS.clift (C.co store p vl h k))))
    | C.Co (K.AccProp (p, t, name, [], [ga], e, c, env, k),
            _, sv, store, h, _) ->
      kont_branch k
        (fun kont ->
          val_branch ga
            (fun gv ->
              let acc = O.Accessor ({ O.getter=gv; O.setter=sv },
                                  V.bool e, V.bool c) in
              LS.olift (tick (LS.clift (C.cop store p name acc h kont)))))

    (* SYN.attrs : { primval; code; proto; class; extensible }
       Evaluates optional exps primval, code, and proto, then continues
       with an S.arrtsv. *)
    | C.EvA (p, attrs, env, store, h, k, t) ->
      let { SYN.primval = pexp;
            SYN.code = cexp;
            SYN.proto = proexp;
            SYN.klass = kls;
            SYN.extensible = ext; } = attrs in
      let opt_add name ox xs =
        match ox with Some x -> (name, x)::xs | _ -> xs in
      let aes =
        opt_add "prim" pexp
          (opt_add "code" cexp
             (opt_add "proto" proexp [])) in 
      (match aes with
      | [] ->
        let attrsv = { O.code=`Bot; O.proto=`Undef;
                       O.primv=`Bot; O.klass=`Str kls;
                       O.exten=`Bool ext } in
        LS.olift (tick (LS.clift (C.coa store p attrsv h k)))
      | (name, exp)::pairs ->
        LS.olift
          (tick (with_kont (LS.clift (C.ev store exp env h))
                   (fun k ->
                     K.Attrs (p, t, name, pairs, [], kls, ext, env, k)))))
    | C.Co (K.Attrs (p, t, name, (name', exp)::pairs, valus, kls, ext, env, k),
            _, valu, store, h, _) ->
      let addr, kont' =
        with_addr valu
          (fun a -> K.Attrs (p, t, name', pairs,
                             (name, a)::valus, kls, ext, env, k)) in
      LS.olift (LS.add_val addr valu
                  (tick (LS.clift (C.ev store exp env h kont'))))
    | C.Co (K.Attrs (p, t, name, [], valus, kls, ext, env, k),
            _, v, store, h, _) ->
      let assoc_vls =
        (name, v)::(List.fold_left
                      (fun a (n, ad) -> (n, V.delay ad)::a) [] valus) in
      let join_get str =
        if List.mem_assoc str assoc_vls then
          match List.assoc str assoc_vls with
          | `Delay a ->
            V.VSet.fold
              (fun v acc -> V.join v acc)
              (S.get_vals a store) `Bot
          | v -> v
        else `Bot in
      let code = join_get "code" in
      let prim = join_get "prim" in
      let proto =
        let v = join_get "proto" in
        match v with `Bot -> `Undef | _ -> v in
      let attrsv = { O.code=code; O.primv=prim; O.proto=proto;
                     O.klass=V.str kls; O.exten=V.bool ext } in
      kont_branch k
        (fun kont ->
          LS.olift (tick (LS.clift (C.coa store p attrsv h kont))))

    (* SYN.GetAttr (pos, pattr, obj, field)
       Get the pattr for the obj's field. *)
    | C.Ev (SYN.GetAttr (p, pattr, obj, field), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                        (fun k -> K.GetAttr (p, t, pattr, [field], [], env, k))))
    | C.Co (K.GetAttr (p, t, pattr, [field], [], env, k),
            _, objv, store, h, _) ->
      let addr, kont' =
        with_addr objv (fun a -> K.GetAttr (p, t, pattr, [], [a], env, k)) in
      LS.olift (LS.add_val addr objv
                  (tick (LS.clift (C.ev store field env h kont'))))
    | C.Co (K.GetAttr (_, _, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
      val_branch a (fun vl -> LS.olift (tick (LS.clift (C.co store p vl h k))))
    | C.Co (K.GetAttr (p, t, attr, [], [obja], env, k),
            _, fieldv, store, h, _) ->
      val_branch obja
        (fun objv -> match objv, fieldv with
        | _, `Top ->
          kont_branch k
            (fun kont -> LS.olift (tick (LS.clift (C.co store p `Top h kont))))
        | `Obj a, `Str str ->
          obj_branch a
            (fun o ->
              let valu = O.get_prop_attr o fieldv attr in
              kont_branch k
                (fun kont -> LS.olift (tick (LS.clift (C.co store p valu h kont)))))
        | _ -> nap (Failure "get_attr did not get object and string"))

    (* SYN.SetAttr (pos, pattr, obj, field, next)
       The pattr for the obj's field is set to next *)
    | C.Ev (SYN.SetAttr (p, pattr, obj, field, next), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k ->
                       K.SetAttr (p, t, pattr, [field; next], [], env, k))))
    | C.Co (K.SetAttr (p, t, pattr, [field; next], [], env, k),
            _, objv, store, h, _) ->
      let addr, kont' =
        with_addr objv
          (fun obja -> K.SetAttr (p, t, pattr, [next], [obja], env, k)) in
      LS.olift (LS.add_val addr objv
                  (tick (LS.clift (C.ev store field env h kont'))))
    | C.Co (K.SetAttr (p, t, pattr, [next], [obja], env, k),
            _, fieldv, store, h, _) ->
      let addr, kont' =
        with_addr fieldv
          (fun fielda ->
            K.SetAttr (p, t, pattr, [], [obja; fielda], env, k)) in
      LS.olift (LS.add_val addr fieldv
                  (tick (LS.clift (C.ev store next env h kont'))))
    | C.Co (K.SetAttr (_, _, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
      val_branch a (fun v -> LS.olift (tick (LS.clift (C.co store p v h k))))
    | C.Co (K.SetAttr (p, t, pattr, [], [obja; fielda], env, k),
            _, vl, store, h, _) ->
      let set_obj_field_attr addr obj fieldv =
        try
          kont_branch k
            (fun kont ->
              LS.olift (LS.set_obj addr (O.set_prop_attr obj fieldv pattr vl)
                          (tick (LS.clift (C.co store p (V.bool true) h kont)))))
        with ex -> nap ex in
      val_branch obja
        (fun objv ->
          val_branch fielda
            (fun fieldv -> match objv with
            | `Top | `ObjT -> (* ugh. set all objects' fieldv attr to vl *)
              objs_branch store
                (fun addr obj -> set_obj_field_attr addr obj fieldv)
            | `Obj oaddr ->
              obj_branch oaddr (fun obj -> set_obj_field_attr oaddr obj fieldv)
            | _ -> nap (Failure "Didn't get an object in setattr!")))

    (* SYN.GetObjAttr (pos, oattr, obj)
       Get the oattr for obj. *)
    | C.Ev (SYN.GetObjAttr (p, oattr, obj), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k -> K.GetObjAttr (p, t, oattr, env, k))))
    | C.Co (K.GetObjAttr _ as k, p, `Delay a, store, h, t) ->
      val_branch a (fun ov -> LS.olift (tick (LS.clift (C.co store p ov h k))))
    | C.Co (K.GetObjAttr (p, t, oattr, env, k), _, objv, store, h, _) ->
      (match objv with
      | `Top ->
        kont_branch k
          (fun kont -> LS.olift (tick (LS.clift (C.co store p `Top h kont))))
      | `Obj oaddr ->
        obj_branch oaddr
          (fun o ->
            let v = O.get_obj_attr o oattr in
            kont_branch k
              (fun kont -> LS.olift (tick (LS.clift (C.co store p v h kont)))))
      | _ -> nap (Failure "GetObjAttr got a non-object."))

    (* SYN.SetObjAttr (pos, oattr, obj, next)
       The oattr for obj is set to next. *)
    | C.Ev (SYN.SetObjAttr (p, oattr, obj, next), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k ->
                       K.SetObjAttr (p, t, oattr, [next], [], env, k))))
    | C.Co (K.SetObjAttr (p, t, oattr, [next], [], env, k),
            _, ov, store, h, _) ->
      let addr, kont' =
        with_addr ov
          (fun obja -> K.SetObjAttr (p, t, oattr, [], [obja], env, k)) in
      LS.olift (LS.add_val addr ov
                  (tick (LS.clift (C.ev store next env h kont'))))
    | C.Co (K.SetObjAttr (_, _, _, [], _, _, _) as k,
            p, `Delay a, store, h, t) ->
      val_branch a (fun vl -> LS.olift (tick (LS.clift (C.co store p vl h k))))
    | C.Co (K.SetObjAttr (p, t, oattr, [], [obja], env, k),
            _, vl, store, h, _) ->
      let brancher oaddr obj =
        kont_branch k
          (fun kont ->
            LS.olift (LS.set_obj oaddr (O.set_obj_attr obj oattr vl)
                        (tick (LS.clift (C.co store p vl h kont))))) in
      val_branch obja
        (fun vl -> match vl with
        | `Top | `ObjT -> objs_branch store brancher
        | `Obj oaddr -> obj_branch oaddr (brancher oaddr)
        | _ -> nap (Failure "SetObjAttr got a non-object"))

    (* SYN.GetField (pos, obj, field, body)
       If the getter field in obj is evaluated and, is a data
       property, continues with the value; if an accessor, evaluates
       the getter with the body and the obj values as arguments. *)
    | C.Ev (SYN.GetField (p, obj, field, body), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k ->  K.GetField (p, t, [field; body], [], env, k))))
    | C.Co (K.GetField (p, t, e::es, vas, env, k), _, v, store, h, _) ->
      let addr, kont' =
        with_addr v (fun va -> K.GetField (p, t, es, va::vas, env, k)) in
      LS.olift (LS.add_val addr v (tick (LS.clift (C.ev store e env h kont'))))
    | C.Co (K.GetField (p, t, [], [fielda; obja], env, k),
            _, bodyv, store, h, _) ->
      let data_lcon v kont =
        tick (LS.clift (C.co store p v h kont)) in
      let acc_lcon gv ov bv kont =
        tick (LS.clift (C.ap store p gv [ov; bv] h kont)) in
      let undef_lcon kont = tick (LS.clift (C.co store p `Undef h kont)) in
      val_branch obja
        (fun objv ->
          val_branch fielda
            (fun fieldv -> begin
              (if LS.verbose then
                  print_endline ("getting field: "^(V.string_of fieldv)));
              match objv with
              | `Top | `ObjT ->
                kont_branch k
                  (fun kont ->
                    (LS.another (data_lcon `Top kont)
                       (LS.another (acc_lcon `Top objv bodyv kont)
                          (LS.olift (undef_lcon kont)))))
              | `Obj oaddr ->
                let props =
                  let objs = S.get_objs oaddr store in
                  O.OSet.fold
                    (fun (_, props) ps ->
                      try O.PSet.add (O.PMap.find fieldv props) ps
                      with Not_found -> ps)
                    objs O.PSet.empty in
                if O.PSet.is_empty props then
                  kont_branch k (fun kont -> LS.olift (undef_lcon kont))
                else
                  O.PSet.fold
                    (fun prop outs ->
                      kont_branch k
                        (fun kont -> match prop with
                        | O.Data ({ O.value=v }, _, _) ->
                          LS.another (data_lcon v kont) outs
                        | O.Accessor ({ O.getter=g }, _, _) ->
                          LS.another (acc_lcon g objv bodyv kont) outs
                        | O.TopProp ->
                          LS.another (data_lcon `Top kont)
                            (LS.another (acc_lcon `Top objv bodyv kont) outs)))
                    props LS.empty
              | _ -> nap (Failure ((Conf.string_of_pos p)^" getfield got obj: "^
                                      (V.string_of objv)^" and field: "^
                                      (V.string_of fieldv))) end))

    (* SYN.OwnFieldNames (pos, obj)
       Create an object in the store with a map of indices to all
       obj's properties and the count of that map. *)
    | C.Ev (SYN.OwnFieldNames (p, obj), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k -> K.OwnFieldNames (p, t, k))))
    | C.Co (K.OwnFieldNames _ as k, p, `Delay a, store, h, t) ->
      val_branch a (fun vl -> LS.olift (tick (LS.clift (C.co store p vl h k))))
    | C.Co (K.OwnFieldNames (p, t, k), _, ovl, store, h, _) ->
      let addr = LS.alloc context in
      let objs_ofns objs =
        O.OSet.fold (fun o a -> O.OSet.add (O.own_field_names o) a)
          objs O.OSet.empty in
      (try
         let objs = match ovl with
           | `Top | `ObjT ->
             Conf.AddrSet.fold
               (fun a acc -> O.OSet.union (objs_ofns (S.get_objs a store)) acc)
               (S.get_obj_addrs store)
               O.OSet.empty
           | `Obj oaddr -> objs_ofns (S.get_objs oaddr store)
           | _ -> failwith "did not get obj in ownfieldnames" in
         kont_branch k
           (fun kont ->
             LS.olift (O.OSet.fold
                         (fun ofn out -> LS.add_obj addr ofn out)
                         objs
                         (tick (LS.clift (C.co store p (V.obj addr) h kont)))))
      with exn -> nap exn)

    (* SYN.DeleteField(pos, obj, field)
       Deletes field from obj. *)
    | C.Ev (SYN.DeleteField (p, obj, field), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k -> K.DeleteField (p, t, [field], [], env, k))))
    | C.Co (K.DeleteField (p, t, [field], [], env, k), _, objv, store, h, _) ->
      let addr, kont' =
        with_addr objv
          (fun obja -> K.DeleteField (p, t, [], [obja], env, k)) in
      LS.olift (LS.add_val addr objv
                  (tick (LS.clift (C.ev store field env h kont'))))
    | C.Co (K.DeleteField (_, _, [], _, _, _) as k,
            p, `Delay a, store, h, t) ->
      val_branch a (fun vl -> LS.olift (tick (LS.clift (C.co store p vl h k))))
    | C.Co (K.DeleteField (p, t, [], [obja], env, k),
            _, fieldv, store, h, _) ->
      val_branch obja
        (fun objv -> match objv with
        | `Top | `ObjT | `Obj _ when not (V.singletonp fieldv) ->
          kont_branch k
            (fun kont -> LS.olift (tick (LS.clift (C.co store p (V.bool true) h kont))))
        | `Obj oaddr ->
          obj_branch oaddr
            (fun (attrs, props) ->
              if O.PMap.mem fieldv props then
                match O.PMap.find fieldv props with
                | O.Data (_, _, `Bool true)
                | O.Accessor (_, _, `Bool true) ->
                  kont_branch k
                    (fun kont ->
                      LS.olift (tick (LS.clift (C.co store p (`Bool true) h kont))))
                | _ ->
                  let addr = LS.alloc context in
                  LS.olift (LS.add_val addr (V.str "unconfigurable-delete")
                              (tick (LS.clift (C.ex store (ERR.Throw addr) env h))))
              else kont_branch k
                (fun kont ->
                  LS.olift (tick (LS.clift (C.co store p (`Bool false) h kont)))))
        | _ -> nap (Failure "didn't receive obj in deletefield"))

    (* SYN.SetField (pos, obj, field, next, body)
       Sets obj's field to next by executing body. *)
    | C.Ev (SYN.SetField (p, obj, field, next, body), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store obj env h))
                     (fun k -> K.SetField (p, t, [field; next; body],
                                           [], env, k))))
    | C.Co (K.SetField (p, t, e::es, vas, env, k), _, v, store, h, _) ->
      let addr, kont' =
        with_addr v (fun va -> K.SetField (p, t, es, va::vas, env, k)) in
      LS.olift (LS.add_val addr v (tick (LS.clift (C.ev store e env h kont'))))
    | C.Co (K.SetField (p, t, [], [nexta; fielda; obja], env, k),
            _, bodyv, store, h, _) ->
      let nextv =
        V.VSet.fold (fun v v' -> V.join v v')
          (S.get_vals nexta store) `Bot in
      let acc_lcon sv addr kont =
        tick (LS.clift (C.ap store p sv [V.obj addr; bodyv] h kont)) in
      let unwrite_lcon addr =
         LS.add_val addr (V.str "unwritable-field")
           (tick (LS.clift (C.ex store (ERR.Throw addr) env h))) in
      let set_field addr ({ O.exten=ext } as attrs, props) fieldv nextv =
        if O.PMap.mem fieldv props then match O.PMap.find fieldv props with
        | O.Data ({ O.writable=`Bool true; value=v } as dat, enum, config) ->
          let props' = O.PMap.join fieldv
            (O.Data ({ dat with O.value=nextv }, enum, config)) props in
          kont_branch k
            (fun kont ->
              LS.olift (LS.set_obj addr (attrs, props')
                          (tick (LS.clift (C.co store p nextv h kont)))))
        | O.Data _
        | O.Accessor ({ O.setter=`Undef }, _, _) ->
          let eaddr = LS.alloc context in LS.olift (unwrite_lcon eaddr)
        | O.Accessor ({ O.setter=sv }, _, _) ->
          kont_branch k (fun kont -> LS.olift (acc_lcon sv addr kont))
        | O.TopProp ->
          let eaddr = LS.alloc context in
          LS.another (unwrite_lcon eaddr)
            (kont_branch k
               (fun kont ->
                 LS.union (LS.olift (acc_lcon `Top addr kont))
                   (LS.olift (tick (LS.clift (C.co store p nextv h kont))))))
        else
          let iftrue = fun () ->
            let tru = V.bool true in
            let prop =
              O.Data ({ O.value=nextv; O.writable=tru }, tru, tru) in
            let props' = O.PMap.join fieldv prop props in
            kont_branch k
              (fun kont ->
                LS.olift (LS.set_obj addr (attrs, props')
                            (tick (LS.clift (C.co store p nextv h kont))))) in
          let iffalse = fun () ->
            kont_branch k
              (fun kont ->
                LS.olift (tick (LS.clift (C.co store p `Undef h kont)))) in
          if ext = `Top || ext = `BoolT then LS.union (iftrue()) (iffalse())
          else if ext = `Bool true then (iftrue())
          else (iffalse()) in
      val_branch obja
        (fun objv ->
          val_branch fielda
            (fun fieldv -> match objv with
            | `Top | `ObjT ->
              Conf.AddrSet.fold
                (fun oaddr outs ->
                  LS.union outs
                    (obj_branch oaddr
                       (fun obj -> set_field oaddr obj fieldv nextv)))
                (S.get_obj_addrs store) LS.empty
            | `Obj oaddr ->
              obj_branch oaddr (fun obj -> set_field oaddr obj fieldv nextv)
            | _ -> nap (Failure "did not receive object in setfield")))

    (* SYN.Op1 (pos, name, arg)
       Evaluates a unary operation name on arg. *)
    | C.Ev (SYN.Op1 (p, name, arg), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store arg env h))
                     (fun k -> K.OpOne (p, t, name, env, k))))
    | C.Co (K.OpOne (p, t, name, env, _) as k, _, `Delay a, store, h, _) ->
      val_branch a
        (fun argv -> LS.olift (tick (LS.clift (C.co store p argv h k))))
    | C.Co (K.OpOne (p, t, name, env, k), _, `Top, store, h, _) ->
      kont_branch k
        (fun kont -> LS.olift (tick (LS.clift (C.co store p `Top h kont))))
    | C.Co (K.OpOne (p, t, name, env, k), _, argv, store, h, _) ->
      kont_branch k
        (fun kont ->
(*          if V.singletonp argv then*)
            try
              let resv = D.op1 store name argv in
              LS.olift (tick (LS.clift (C.co store p resv h kont)))
            with err -> nap err
(*          else LS.olift (tick (LS.clift (C.co store p `Top h kont)))*)
)

    (* SYN.Op2 (pos, name, arg1, arg2)
       Evaluates a binary operation name on arg1 and arg2. *)
    | C.Ev (SYN.Op2 (p, name, arg1, arg2), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store arg1 env h))
                     (fun k -> K.OpTwo (p, t, name, [arg2], [], env, k))))
    | C.Co (K.OpTwo (p, t, name, [arg2], [], env, k), _, arg1v, store, h, _) ->
      let addr, kont' =
        with_addr arg1v
          (fun arg1a -> K.OpTwo (p, t, name, [], [arg1a], env, k)) in
      LS.olift (LS.add_val addr arg1v
                  (tick (LS.clift (C.ev store arg2 env h kont'))))
    | C.Co (K.OpTwo (_, _, _, [], _, _, _) as k, p, `Delay a, store, h, t) ->
      val_branch a
        (fun arg2v -> LS.olift (tick (LS.clift (C.co store p arg2v h k))))
    | C.Co (K.OpTwo (p, t, op, [], [arg1a], env, k), _, arg2v, store, h, _) ->
      val_branch arg1a
        (fun arg1v ->
          kont_branch k
            (fun kont -> (*match arg1v with
            | v when V.singletonp v ->*)
              (try
                let resv = D.op2 store op arg1v arg2v in
                LS.olift (tick (LS.clift (C.co store p resv h kont)))
              with err -> nap err)
(*            | v -> LS.olift (tick (LS.clift (C.co store p `Top h kont)))*)
))

    (* SYN.If (pos, pred, then, else)
       Evaluates then if pred, else otherwise. *)
    | C.Ev (SYN.If (p, pred, than, elze), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store pred env h))
                     (fun k -> K.If (p, t, env, than, elze, k))))
    | C.Co (K.If (p, t, env, than, elze, _) as k, _, `Delay a, store, h, _) ->
      val_branch a
        (fun predv -> LS.olift (tick (LS.clift (C.co store p predv h k))))
    | C.Co (K.If (p, t, env, than, elze, k), _, `Top, store, h, _) ->
      kont_branch k
        (fun kont -> LS.another (tick (LS.clift (C.ev store than env h kont)))
          (LS.olift (tick (LS.clift (C.ev store elze env h kont)))))
    | C.Co (K.If (p, t, env, than, elze, k), _, predv, store, h, _) ->
      let ifthen kont = tick (LS.clift (C.ev store than env h kont)) in
      let ifelse kont = tick (LS.clift (C.ev store elze env h kont)) in
      kont_branch k
        (fun kont ->match predv with
        | `Top | `BoolT -> LS.another (ifthen kont) (LS.olift (ifelse kont))
        | `Bool true -> LS.olift (ifthen kont)
        | _ -> LS.olift (ifelse kont))

    (* SYN.App (pos, func, args)
       Applies the body of func with the given args. *)
    | C.Ev (SYN.App (p, func, args), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store func env h))
                     (fun k -> K.App (p, t, env, args, [], k))))
    | C.Co (K.App (p, t, env, [], [], k), _, funcv, store, h, _) ->
      kont_branch k
        (fun kont -> LS.olift (tick (LS.clift (C.ap store p funcv [] h kont))))
    | C.Co (K.App (p, t, env, e::es, vas, k), _, v, store, h, _) ->
      let addr, kont' =
        with_addr v (fun va -> K.App (p, t, env, es, va::vas, k)) in
      LS.olift (LS.add_val addr v (tick (LS.clift (C.ev store e env h kont'))))
    | C.Co (K.App (p, t, env, [], vas, k), _, argv, store, h, _) ->
      let funcv, argvs = 
        let rec last_is_funca vas (not_yet_funcv, argvs) = match vas with
          | [funca] -> `Delay funca, argvs
          | arga::vas ->
            last_is_funca vas (not_yet_funcv, (V.delay arga)::argvs)
          | [] -> failwith "Can't get an empty list here." in
        last_is_funca vas (`Bot, [argv]) in
      kont_branch k
        (fun kont ->
          LS.olift (tick (LS.clift (C.ap store p funcv argvs h kont))))

    (* SYN.Seq (pos, left, right)
       Evaluates left then right, continuing with right's value. *)
    | C.Ev (SYN.Seq (p, left, right), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store left env h))
                     (fun k -> K.Seq (p, t, right, env, k))))
    | C.Co (K.Seq (p, t, right, env, k), _, _, store, h, _) ->
      kont_branch k
        (fun kont -> LS.olift (tick (LS.clift (C.ev store right env h kont))))

    (* SYN.Let (pos, name, expr, body)
       Evaluates body with name bound to expr. *)
    | C.Ev (SYN.Let (p, name, expr, body), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store expr env h))
                     (fun k -> K.Let (p, t, name, body, env, k))))
    | C.Co (K.Let (p, t, name, body, env, k), _, v, store, h, _) ->
      let addr = LS.alloc context in
      kont_branch k
        (fun kont ->
          LS.olift (LS.add_val addr v
                      (tick (LS.clift (C.ev store body (E.add name addr env)
                                         h kont)))))

    (* SYN.Rec (pos, name, expr, body)
       Evaluates body with name bound to expr, which may contain
       recursive references to name. *)
    | C.Ev (SYN.Rec (p, name, expr, body), env, store, h, k, t) ->
      let new_loc = LS.alloc context in
      let env' = E.add name new_loc env in
      LS.olift (tick (with_kont (LS.clift (C.ev store expr env' h))
                     (fun k -> K.Rec (p, t, new_loc, body, env', k))))
    | C.Co (K.Rec (p, t, new_loc, body, env, k), _, v, store, h, _) ->
      kont_branch k
        (fun kont ->
          LS.olift (LS.add_val new_loc v
                      (tick (LS.clift (C.ev store body env h kont)))))

    (* SYN.Label (pos, name, expr)
       Evaluates expr, catching any Breaks with the matching name. *)
    | C.Ev (SYN.Label (p, name, exp), env, store, h, k, t) ->
      LS.olift (tick (with_hand (LS.clift (C.ev store exp env))
                     (fun hk -> H.Lab (p, t, name, env, hk, hk))))
    | C.Ex ((ERR.Break (l, a) as brk), _, store,
            H.Lab (p, _, name, env, k, h), _) ->
      hand_branch h
        (fun hand ->
          if name = l then
            kont_branch k
              (fun kont ->
                LS.olift (tick (LS.clift (C.co store p (V.delay a) hand kont))))
          else LS.olift (tick (LS.clift (C.ex store brk env hand))))

    (* SYN.Break (pos, label, expr)
       Breaks to label with expr as the value passed back. *)
    | C.Ev (SYN.Break (p, label, expr), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store expr env h))
                     (fun k -> K.Break (p, t, label, env, k))))
    | C.Co (K.Break (p, t, label, env, k), _, v, store, h, _) ->
      let addr = LS.alloc context in
      LS.olift (LS.add_val addr v
                  (tick (LS.clift (C.ex store (ERR.Break (label, addr)) env h))))

    (* SYN.TryCatch (pos, body, catch)
       Evaluates body, evaluating catch with the thrown value as an
       argument if a Throw is lobbed up. *)
    | C.Ev (SYN.TryCatch (p, body, catch), env, store, h, k, t) ->
      LS.olift (tick (with_hand (LS.clift (C.ev store body env))
                     (fun hk -> H.Cat (p, t, catch, env, hk, hk))))
    | C.Ex (ERR.Throw throwa, _, store, H.Cat (p, t, catch, env, k, h), _) ->
      hand_branch h
        (fun hand ->
          LS.olift (tick (with_kont (LS.clift (C.ev store catch env hand))
                         (fun k -> K.Catch (p, t, throwa, env, k)))))
    | C.Co (K.Catch (p, t, throwv, env, k), _, catchv, store, h, _) ->
      kont_branch k
        (fun kont ->
          LS.olift (tick (LS.clift (C.ap store p catchv [V.delay throwv] h kont))))

    (* SYN.TryFinally (pos, body, fin)
       Evaluates body then fin; if an exception is thrown from body
       fin will be executed and the exn's store is updated. *)
    | C.Ev (SYN.TryFinally (p, body, fin), env, store, h, k, t) ->
      LS.olift (tick (with_hand (LS.clift (C.ev store body env))
                     (fun hk -> H.Fin (p, t, fin, env, hk, hk))))
    | C.Ex (ex, _, store, H.Fin (p, t, fin, env, k, h), _) ->
      hand_branch h
        (fun hand ->
          LS.olift (tick (with_kont (LS.clift (C.ev store fin env hand))
                         (fun k -> K.Finally (p, t, [ex], [], env, k)))))
    | C.Co (K.Finally (p, t, [ex], [], env, k), _, _, store, h, _) ->
      LS.olift (tick (LS.clift (C.ex store ex env h)))
    | C.Co (K.Finally (p, t, [], [valu], env, k), _, _, store, h, _) ->
      kont_branch k
        (fun kont ->
          LS.olift (tick (LS.clift (C.co store p (V.delay valu) h kont))))

    (* SYN.Throw (pos, expr)
       Lobs expr up through the handles. *)
    | C.Ev (SYN.Throw (p, expr), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store expr env h))
                     (fun k -> K.Throw (p, t, env, k))))
    | C.Co (K.Throw (p, t, env, k), _, valu, store, h, _) ->
      let addr = LS.alloc context in
      LS.olift (LS.add_val addr valu
                  (tick (LS.clift (C.ex store (ERR.Throw addr) env h))))

    (* SYN.Eval (pos, str_expr, bindings)
       Evaluates str_expr with the fields defined in the object *)
    | C.Ev (SYN.EvalAU (p, str, bindings, auenv), env, store, h, k, t) ->
      LS.olift (tick (with_kont (LS.clift (C.ev store str env h))
                     (fun k -> K.Eval (p, t, [bindings], [], env, auenv, k))))
    | C.Co (K.Eval (p, t, [binde], [], env, auenv, k), _, strv, store, h, _) ->
      let addr = LS.alloc context in
      LS.olift (LS.add_val addr strv
                  (tick (LS.clift (C.ev store binde env h
                                     (K.Eval (p, t, [], [addr], env, auenv, k))))))
    | C.Co (K.Eval (p, t, [], [stra], env, auenv, k), _, bindv, store, h, _) ->
      (* TODO: This is terrible. *)
      let env_store_of_obj locs (_, props) =
        let _, env, store =
          O.PMap.fold
            (fun key prop (locs, env, store) -> match key with
            | `Str key -> (match locs with
              | loc::locs -> (match prop with
                | O.Data ({ O.value=v }, _, _) ->
                  let env' = E.add key loc env 
                  and store' = S.set_val loc v store in
                  locs, env', store'
                | O.TopProp -> failwith "prop too imprecise?"
                | _ -> failwith "non-data value in env_store_of_obj")
              | _ -> failwith "not enough locs for eval, check your eval_alloc")
            | _ -> failwith "obj key too imprecise?")
            props (locs, E.empty, S.empty) in env, store in
      val_branch stra
        (fun strv ->
          (match strv, bindv with
          | `Str s, `Obj o ->
            let ljs = LS.desugar s in
            let auljs, _ = Aam_au.alpha_unique ~init_env:auenv ljs in
            let locss = LS.eval_alloc context in
            let _, outs =
              O.OSet.fold
                (fun o (locss, outs) -> match locss with
                | locs::locss' ->
                  (try
                     let env', store' = env_store_of_obj locs o in
                     (locss',
                      LS.union outs
                        (kont_branch k
                           (fun kont ->
                             LS.olift
                               (tick (LS.clift (C.ev store' auljs env' h kont))))))
                   with
                   | (Failure "not enough locs for eval") as ex -> raise ex
                   | ex -> locss', LS.olift (LS.clift (C.NAP ex)))
                | _ -> failwith "not enough locs for eval")
                (S.get_objs o store) (locss, LS.empty) in outs
          | _, _ ->
            kont_branch k
              (fun kont ->
                LS.olift (tick (LS.clift (C.co (S.to_top store) p `Top h kont))))))

    (* SYN.Hint (pos, str, expr)
       Evaluates expr, continuing with a Snapshot if str is
       "___takeS5Snapshot", or just continues with expr's val. *)
    | C.Ev (SYN.Hint (p, _, expr), env, store, h, k, t) ->
      LS.olift (tick (LS.clift (C.ev store expr env h k)))

    (* shedding handles *)
    | C.Ex (ex, env, store, H.Mt, t) -> LS.empty
    | C.Ex (ex, env, store, h, t) ->
      hand_branch (H.hand_of h)
        (fun hand -> LS.olift (tick (LS.clift (C.ex store ex env hand))))
    | C.Co (K.Mt, _, valu, store, H.Mt, _) ->
      LS.olift (tick (LS.clift (C.ans store valu)))
    | C.Co (K.Mt, _, valu, store, H.Lab (p, t, name, env, k, h), _) ->
      kont_branch k
        (fun kont ->
          hand_branch h
            (fun hand ->
              LS.olift (tick (LS.clift (C.co store p valu hand kont)))))
    | C.Co (K.Mt, _, valu, store, H.Cat (p, t, _, _, k, h), _) ->
      kont_branch k
        (fun kont ->
          hand_branch h
            (fun hand ->
              LS.olift (tick (LS.clift (C.co store p valu hand kont)))))
    | C.Co (K.Mt, _, valu, store, H.Fin (p, t, exp, env, k, h), _) ->
      let addr, kont' =
        with_addr valu (fun a -> K.Finally (p, t, [], [a], env, k)) in
      hand_branch h
        (fun hand ->
          LS.olift (LS.add_val addr valu
                      (tick (LS.clift (C.ev store exp env hand kont')))))

    (* you really screwed up. *)
    | _ ->
      print_endline (C.string_of context);
      print_endline (H.string_of (C.hand_of context));
      print_endline (K.string_of (C.kont_of context));
      failwith "Encountered an unmatched machine context."

  (* ES5 environment  *)


  end
end

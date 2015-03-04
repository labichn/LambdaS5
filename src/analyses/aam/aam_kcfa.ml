module C = Aam_context
module K = Aam_kont
module H = Aam_handle
module SYN = Ljs_syntax
module SH = Aam_shared
module V = Aam_lattices
module O = Aam_object
module E = Aam_env
module S = Aam_store

let rec trunc k t = match k, t with
  | _, [] -> []
  | 0, _ -> []
  | n, t::ts -> t::(trunc (n-1) ts)

let tick k context : SH.time = match context with
  | C.Ap (p, `Clos _, _, _, _, _, t)
  | C.Co (K.Let (p, _, _, _, _, _), _, _, _, _, t)
  | C.Co (K.Rec (p, _, _, _, _, _), _, _, _, _, t)
  | C.Co (K.SetBang (p, _, _, _), _, _, _, _, t) ->
    trunc k ((SH.P p)::t)
  | C.Ex _ -> C.time_of context
  | c when C.kont_of c = K.Mt -> C.time_of context
  | C.Co (k, _, _, _, _, _)
  | C.CoP (k, _, _, _, _, _)
  | C.CoA (k, _, _, _, _, _) -> K.time_of k
  | _ -> C.time_of context

let alloc k context : SH.addr = match context with
  | C.Co (K.Eval (p, t, _, _, _, _, _), _, _, _, _, _) ->
    SH.T ((SH.P p)::(trunc k t))
  (* let and letrec binding is var-name::(trunc k time), easy *)
  | C.Ev (SYN.Rec (_, name, _, _), _, _, _, _, t)
  | C.Co (K.Let (_, t, name, _, _, _), _, _, _, _, _) ->
    SH.T ((SH.X name)::(trunc k t))
  (* other evs are simple, because konts and hands don't get derefed and
     there's no choice to be made *)
  | C.Ev (exp, _, _, _, _, t) ->
    SH.T ((SH.P (SYN.pos_of exp))::(trunc k t))
  | C.CoP (K.Object (_, t, _, _, _, _, _), p, (n, _), _, _, _) ->
    SH.T ((SH.X n)::(SH.P p)::(trunc k t))
  | C.EvA (p, _, _, _, _, _, t)
  (* apps need to allocate for each of the args, as they get stuck into
     the konts, and they are temporarily bound to their posn and trunced
     time. Hmmm.
     REVISIT: why not just bind them for application here? I've got the
       xs available, and I just have to go through the same process of
       allocation again anyway. The time shouldn't be different, as long
       as I pull it from the app kont. Try this after object redo *)
  | C.Co (K.App (_, t, _, _, _, _), p, _, _, _, _)
  (* thanks to the split store, and since objects have a single attrs rec,
     we can just use the object's position as our location head *)
  | C.CoA (K.Object (p, t, _, _, _, _, _), _, _, _, _, _)
  (* ex is a whole other animal, the time of the exception may be vastly
     different than the hand's time, but it also throws up an environment.
     the time should stay consistent with whatever environment is considered
     live, so we grab the time from there. *)
  | C.Ex (_, _, _, H.Cat (p, _, _, _, _, _), t) ->
    SH.T ((SH.P p)::(trunc k t))
  (* other cos allocate to hold intermediary values in konts, and since
     the allocation is driven by the kont, make it kont specific *)
  | C.Co (kont, _, _, _, _, _) ->
    SH.T ((SH.P (K.pos_of kont))::(trunc k (K.time_of kont)))
  | _ -> print_endline ("whoops: "^(C.string_of context)); failwith "oops"
    
let clos_alloc k context : SH.addr list = match context with
  | C.Ap (p, `Clos (_, xs, _), vs, _, _, _, t) ->
    List.fold_right (fun x a -> (SH.T ((SH.X x)::(trunc k t)))::a) xs []

let eval_alloc k context : SH.addr list list = match context with
  | C.Co (K.Eval (p, t, _, _, _, _, _), _, `Obj a, store, _, _) ->
    let os = S.get_objs a store in
    O.OSet.fold
      (fun (_, props) locss ->
        (O.PropMap.fold
           (fun key _ ls ->
             (SH.T ((SH.X (V.AValue.string_of key))::(SH.P p)::(trunc k t)))::ls)
           props [])::locss)
      os []

let alloc_kont k context = match context with
  (* to avoid conflating k.dataprops with k.object and k.attrs *)
  | C.EvP (p, (n, _), _, _, _, _, t) ->
    SH.T ((SH.X n)::(SH.P p)::(trunc k t))
  | C.Ev (exp, _, _, _, _, t) ->
    SH.T ((SH.P (SYN.pos_of exp))::(trunc k t))
  | C.EvA (p, _, _, _, _, _, t)
  | C.Ex (_, _, _, H.Cat (p, t, _, _, _, _), _)
  | C.Ex (_, _, _, H.Fin (p, t, _, _, _, _), _) ->
    SH.T ((SH.P p)::(trunc k t))

let alloc_hand k context = match context with
  | C.Ev (exp, _, _, _, _, t) -> SH.T ((SH.P (SYN.pos_of exp))::(trunc k t))

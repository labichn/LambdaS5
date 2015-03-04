(* Baseline abstract AAM implementation. *)

(* seconds elapsed, states stepped, answers found, exceptions found,
   terminated successfully *)
type result = float * int * int * int * bool

let string_of_result (me, ss, af, ef, sp) =
  " seconds elapsed: "^(string_of_float me)^"\n"^
  "  states stepped: "^(string_of_int ss)^"\n"^
  "   answers found: "^(string_of_int af)^"\n"^
  "exceptions found: "^(string_of_int ef)^"\n"^
  "     successful?: "^
    (if not sp then "false"
     else if af = 0 then "uh, you tell me..."
     else "true")

module rec ConConf : Aam_conf.S with type time = int and type addr = int = struct

  type time = int
  let time0 = 0
  let string_of_time = string_of_int

  type addr = int
  let addr0 = 0
  let string_of_addr = string_of_int
  module AddrSet = Set.Make(struct type t = addr let compare = Pervasives.compare end)
  module AddrMap = Map.Make(struct type t = addr let compare = Pervasives.compare end)

  type pos = Prelude.Pos.t
  let dummy_pos = Prelude.Pos.dummy
  let pos_of_ljs p = p
  let string_of_pos = Prelude.Pos.string_of_pos
end

and ConContext : Aam_context.S
  with type attrsv = ConObj.attrsv
  and type env = ConConf.addr ConEnv.t
  and type hand = ConHand.t
  and type kont = ConKont.t
  and type propv = ConObj.propv
  and type store = ConStore.t
  and type time = ConConf.time
  and type value = ConVal.t =
        Aam_context.Make(ConConf)(ConEnv)(ConHand)(ConKont)(ConObj)(ConStore)(ConVal)

and ConDelta : Aam_delta.S
  with type store = ConStore.t and type value = ConVal.t =
    Aam_delta.Make(ConConf)(ConEnv)(ConErr)(ConVal)(ConObj)(ConStore)

and ConEnv : Aam_env.S = Aam_env.E

and ConErr : Aam_error.S
  with type addr = ConConf.addr =
  Aam_error.Make(ConConf)

and ConHand : Aam_handle.S
  with type addr = ConConf.addr and type time = ConConf.time
  and type env = ConConf.addr ConEnv.t =
  Aam_handle.Make(ConConf)(ConEnv)

and ConVal : Aam_lattices.S
  with type addr = ConConf.addr and type env = ConConf.addr ConEnv.t =
  Aam_lattices.Make(ConConf)(ConEnv)

and ConKont : Aam_kont.S
  with type addr = ConConf.addr and type time = ConConf.time
  and type env = ConConf.addr ConEnv.t =
  Aam_kont.Make(ConConf)(ConEnv)

and ConObj : Aam_object.S
  with type value = ConVal.t =
  Aam_object.Make(ConVal)

and ConStore : Aam_store.S
  with type addr = ConConf.addr
  and module AddrSet = ConConf.AddrSet
  and type objekt = ConObj.t
  and type attrsv = ConObj.attrsv
  and type propv = ConObj.propv
  and type value = ConVal.t
  and type hand = ConHand.t
  and type kont = ConKont.t
  and type objekts = ConObj.OSet.t
  and type attrsvs = ConObj.ASet.t
  and type propvs = ConObj.PSet.t
  and type values = ConVal.VSet.t
  and type hands = ConHand.HSet.t
  and type konts = ConKont.KSet.t =
        Aam_store.Make(ConConf)(ConHand)(ConKont)(ConObj)(ConVal)

and ConLock : Aam_step.LOCK
  with type addr = ConConf.addr and type time = ConConf.time
  and type context = ConContext.t and type objekt = ConObj.t and type value = ConVal.t
  and type kont = ConKont.t and type hand = ConHand.t and type attrsv = ConObj.attrsv
  and type propv = ConObj.propv and type 'a lcon = 'a and type input = ConContext.t
  and type output = ConContext.CSet.t = struct

  type addr = ConConf.addr type time = ConConf.time
  type context = ConContext.t type objekt = ConObj.t type value = ConVal.t
  type kont = ConKont.t type hand = ConHand.t type attrsv = ConObj.attrsv
  type propv = ConObj.propv type 'a lcon = 'a type input = ConContext.t
  type output = ConContext.CSet.t

  let context_of_input (i : input) : context = i

  let set setter k v c =
    ConContext.with_store (setter k v (ConContext.store_of c)) c
  let set_obj (k : addr) (v : objekt) (c : context lcon) : context lcon =
    set ConStore.set_obj k v c
  let set_val (k : addr) (v : value) (c : context lcon) : context lcon =
    set ConStore.set_val k v c
  let add_obj (k : addr) (v : objekt) (c : context lcon) : context lcon =
    set_obj k v c
  let add_val (k : addr) (v : value) (c : context lcon) : context lcon =
    set_val k v c
  let add_hand (k : addr) (v : hand) (c : context lcon) : context lcon =
    set ConStore.set_hand k v c
  let add_kont (k : addr) (v : kont) (c : context lcon) : context lcon =
    set ConStore.set_kont k v c
  let add_attrsv (k : addr) (v : attrsv) (c : context lcon) : context lcon =
    set ConStore.set_attrsv k v c
  let add_propv (k : addr) (v : propv) (c : context lcon) : context lcon =
    set ConStore.set_propv k v c
  let desugar = Ljs_desugar.desugar ""

  let tick c cc = cc (1 + (ConContext.time_of c))
  let clift c = c
  let olift = ConContext.CSet.singleton
  let addr = ref (0)
  let fresh () = let curr = !addr in begin addr := curr+1; curr end
  let alloc _ = fresh()
  let clos_alloc c = match c with
    | ConContext.Ap (_, `Clos (_, xs, _), _, _, _, _, _) ->
      List.fold_right (fun _ a -> (fresh())::a) xs []
  let eval_alloc c = match c with
    | ConContext.Co (ConKont.Eval _, _, `Obj a, store, _, _) ->
      let os = ConStore.get_objs a store in
      ConObj.OSet.fold
        (fun (_, props) locss ->
          (ConObj.PMap.fold (fun _ _ ls -> (fresh())::ls) props [])::locss)
        os []
  let with_hand c hktc ah = let a = alloc() in hktc (ah a) ConKont.Mt
  let with_kont c ktc ak = let a = alloc() in ktc (ak a)
  let union = ConContext.CSet.union
  let another = ConContext.CSet.add
  let empty = ConContext.CSet.empty
  let verbose = false
end
and ConStep : Aam_step.S
  with type input = ConLock.input and type output = ConLock.output =
      Aam_step.Make
        (ConConf) (ConErr)
        (ConEnv)  (ConVal)
        (ConObj)  (ConHand)
        (ConKont) (ConStore)
        (ConDelta)(ConContext)
        (ConLock)

let eval exp =
  let inject e0 s0 exp =
    ConContext.Ev (exp, e0, s0, ConHand.Mt, ConKont.Mt, ConConf.time0) in
  let rec loop sys = match sys with
    | ConContext.Ans (v, _, _) -> v
    | ConContext.NAP s -> failwith ("NAP error!\n"^(ConErr.string_of s))
    | _ -> 
      let out = ConStep.step sys in match ConContext.CSet.cardinal out with
        | 0 -> failwith "no output from constep... wtf?"
        | n when n > 1 -> failwith "more than one output from constep... wtf?"
        | 1 -> loop (ConContext.CSet.choose out) in
  loop (inject ConEnv.empty ConStore.empty exp) ;;

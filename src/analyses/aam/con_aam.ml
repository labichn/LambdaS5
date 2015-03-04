(* Concrete AAM implementation. *)

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

module rec CConf : Aam_conf.S with type time = int and type addr = int = struct

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

and CContext : Aam_context.S
  with type attrsv = CObj.attrsv
  and type env = CConf.addr CEnv.t
  and type hand = CHand.t
  and type kont = CKont.t
  and type propv = CObj.propv
  and type store = CStore.t
  and type time = CConf.time
  and type value = CVal.t =
        Aam_context.Make(CConf)(CEnv)(CHand)(CKont)(CObj)(CStore)(CVal)

and CDelta : Aam_delta.S
  with type store = CStore.t and type value = CVal.t =
    Aam_delta.Make(CConf)(CEnv)(CErr)(CVal)(CObj)(CStore)

and CEnv : Aam_env.S = Aam_env.E

and CErr : Aam_error.S
  with type addr = CConf.addr =
  Aam_error.Make(CConf)

and CHand : Aam_handle.S
  with type addr = CConf.addr and type time = CConf.time
  and type env = CConf.addr CEnv.t =
  Aam_handle.Make(CConf)(CEnv)

and CVal : Aam_lattices.S
  with type addr = CConf.addr and type env = CConf.addr CEnv.t =
  Aam_lattices.Make(CConf)(CEnv)

and CKont : Aam_kont.S
  with type addr = CConf.addr and type time = CConf.time
  and type env = CConf.addr CEnv.t =
  Aam_kont.Make(CConf)(CEnv)

and CObj : Aam_object.S
  with type value = CVal.t =
  Aam_object.Make(CVal)

and CStore : Aam_store.S
  with type addr = CConf.addr
  and module AddrSet = CConf.AddrSet
  and type objekt = CObj.t
  and type attrsv = CObj.attrsv
  and type propv = CObj.propv
  and type value = CVal.t
  and type hand = CHand.t
  and type kont = CKont.t
  and type objekts = CObj.OSet.t
  and type attrsvs = CObj.ASet.t
  and type propvs = CObj.PSet.t
  and type values = CVal.VSet.t
  and type hands = CHand.HSet.t
  and type konts = CKont.KSet.t =
        Aam_store.Make(CConf)(CHand)(CKont)(CObj)(CVal)

and CLock : Aam_step.LOCK
  with type addr = CConf.addr and type time = CConf.time
  and type context = CContext.t and type objekt = CObj.t and type value = CVal.t
  and type kont = CKont.t and type hand = CHand.t and type attrsv = CObj.attrsv
  and type propv = CObj.propv and type 'a lcon = 'a and type input = CContext.t
  and type output = CContext.CSet.t = struct

  type addr = CConf.addr type time = CConf.time
  type context = CContext.t type objekt = CObj.t type value = CVal.t
  type kont = CKont.t type hand = CHand.t type attrsv = CObj.attrsv
  type propv = CObj.propv type 'a lcon = 'a type input = CContext.t
  type output = CContext.CSet.t

  let context_of_input (i : input) : context = i

  let set setter k v c =
    CContext.with_store (setter k v (CContext.store_of c)) c
  let set_obj (k : addr) (v : objekt) (c : context lcon) : context lcon =
    set CStore.set_obj k v c
  let set_val (k : addr) (v : value) (c : context lcon) : context lcon =
    set CStore.set_val k v c
  let add_obj (k : addr) (v : objekt) (c : context lcon) : context lcon =
    set_obj k v c
  let add_val (k : addr) (v : value) (c : context lcon) : context lcon =
    set_val k v c
  let add_hand (k : addr) (v : hand) (c : context lcon) : context lcon =
    set CStore.set_hand k v c
  let add_kont (k : addr) (v : kont) (c : context lcon) : context lcon =
    set CStore.set_kont k v c
  let add_attrsv (k : addr) (v : attrsv) (c : context lcon) : context lcon =
    set CStore.set_attrsv k v c
  let add_propv (k : addr) (v : propv) (c : context lcon) : context lcon =
    set CStore.set_propv k v c
  let desugar = Ljs_desugar.desugar ""

  let tick c cc = cc (1 + (CContext.time_of c))
  let clift c = c
  let olift = CContext.CSet.singleton
  let addr = ref (0)
  let fresh () = let curr = !addr in begin addr := curr+1; curr end
  let alloc _ = fresh()
  let clos_alloc c = match c with
    | CContext.Ap (_, `Clos (_, xs, _), _, _, _, _, _) ->
      List.fold_right (fun _ a -> (fresh())::a) xs []
  let eval_alloc c = match c with
    | CContext.Co (CKont.Eval _, _, `Obj a, store, _, _) ->
      let os = CStore.get_objs a store in
      CObj.OSet.fold
        (fun (_, props) locss ->
          (CObj.PMap.fold (fun _ _ ls -> (fresh())::ls) props [])::locss)
        os []
  let with_hand c hktc ah = let a = alloc() in hktc (ah a) CKont.Mt
  let with_kont c ktc ak = let a = alloc() in ktc (ak a)
  let union = CContext.CSet.union
  let another = CContext.CSet.add
  let empty = CContext.CSet.empty
  let verbose = false
end
and CStep : Aam_step.S
  with type input = CLock.input and type output = CLock.output =
      Aam_step.Make
        (CConf) (CErr)
        (CEnv)  (CVal)
        (CObj)  (CHand)
        (CKont) (CStore)
        (CDelta)(CContext)
        (CLock)

let eval exp =
  let inject e0 s0 exp =
    CContext.Ev (exp, e0, s0, CHand.Mt, CKont.Mt, CConf.time0) in
  let rec loop sys = match sys with
    | CContext.Ans (v, _, _) -> v
    | CContext.NAP s -> failwith ("NAP error!\n"^(CErr.string_of s))
    | _ -> 
      let out = CStep.step sys in match CContext.CSet.cardinal out with
        | 0 -> failwith "no output from constep... wtf?"
        | n when n > 1 -> failwith "more than one output from constep... wtf?"
        | 1 -> loop (CContext.CSet.choose out) in
  loop (inject CEnv.empty CStore.empty exp) ;;

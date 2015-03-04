module type S = sig
  type value
  type attrsv = { code: value; proto: value; exten: value; klass: value; primv: value }
  type data = { value: value; writable: value }
  type accessor = { getter: value; setter: value }
  type propv =
  | Data of data * value * value
  | Accessor of accessor * value * value
  | TopProp
  module ASet : Set.S with type elt = attrsv
  module PSet : Set.S with type elt = propv
  module PMap : Abstract_map.S with type key = value and type value = propv
  type t = attrsv * PMap.t
  module OSet : Set.S with type elt = t
  val subsumes: t -> t -> bool
  val attrs_subsumes: attrsv -> attrsv -> bool
  val prop_subsumes: propv -> propv -> bool
  val join: t -> t -> t
  val top: t
  val default_attrs: attrsv
  val string_of: t -> string
  val make_obj: ASet.t -> (string * PSet.t) list -> t
  val get_prop_attr: t -> value -> Ljs_syntax.pattr -> value
  val set_prop_attr: t -> value -> Ljs_syntax.pattr -> value -> t
  val get_obj_attr: t -> Ljs_syntax.oattr -> value
  val set_obj_attr: t -> Ljs_syntax.oattr -> value -> t
  val own_field_names: t -> t
end

module MakeT(V : Aam_lattices.S) = struct
  module type T = S with type value = V.t
end

module Make (Value : Aam_lattices.S) = struct

  type value = Value.t

  type attrsv = { code: value; proto: value; exten: value; klass: value; primv: value }
  module ASet = Set.Make(struct type t = attrsv let compare = Pervasives.compare end)

  let default_attrs =
    { code = `Bot;
      proto = `Null;
      exten = Value.bool false;
      primv = `Bot;
      klass = Value.str "λS5 internal" }

  let string_of_attrs { code=c; proto=pro; exten=e; klass=k; primv=pri } =
    "{ code="^(Value.string_of c)^", "^
      "proto="^(Value.string_of pro)^", "^
      "extensible="^(Value.string_of e)^", "^
      "class="^(Value.string_of k)^", "^
      "primval="^(Value.string_of pri)^" }"

  let attrs_subsumes { code=c; proto=pro; exten=e; klass=k; primv=pri }
      { code=c'; proto=pro'; exten=e'; klass=k'; primv=pri' } =
    Value.subsumes c c' && Value.subsumes pro pro' && Value.subsumes e e' &&
      Value.subsumes k k' && Value.subsumes pri pri'

  let attrs_join { code=c; proto=pro; exten=e; klass=k; primv=pri }
      { code=c'; proto=pro'; exten=e'; klass=k'; primv=pri' } =
    { code=Value.join c c'; proto=Value.join pro pro'; exten=Value.join e e';
      klass=Value.join k k'; primv=Value.join pri pri' }

  let aset_join aset =
    if ASet.is_empty aset then failwith "refusing to join an empty set of attrs"
    else ASet.fold attrs_join aset
      { code=`Bot; proto=`Bot; exten=`Bot; klass=`Bot; primv=`Bot }

  let attrs_top =
    { code=`Top; proto=`Top; exten=`Top; klass=`Top; primv=`Top }

  type data = { value: value; writable: value }
  type accessor = { getter: value; setter: value }
    
  let string_of_data { value=v; writable=w } =
    "{ value="^(Value.string_of v)^", writable="^(Value.string_of w)^" }"
      
  let string_of_accessor { getter=gv; setter=sv } =
    "{ getter="^(Value.string_of gv)^", setter="^(Value.string_of sv)^" }"
      
  type propv =
  | Data of data * value * value
  | Accessor of accessor * value * value
  | TopProp

  module PSet = Set.Make(struct type t = propv let compare = Pervasives.compare end)

  let string_of_prop = function
    | Data (d, e, c) ->
      "data("^(string_of_data d)^", "^(Value.string_of e)^", "^(Value.string_of c)^")"
    | Accessor (a, e, c) ->
      "accessor("^(string_of_accessor a)^", "^(Value.string_of e)^", "^(Value.string_of c)^")"
    | TopProp -> "topprop"

  let prop_subsumes p p' = match p, p' with
    | Data ({ value=v; writable=w }, e, c),
      Data ({ value=v'; writable=w' },e', c') ->
      Value.subsumes v v' && Value.subsumes w w' && Value.subsumes e e' &&
        Value.subsumes c c'
    | Accessor ({ getter=gv; setter=sv }, e, c),
      Accessor ({ getter=gv'; setter=sv' }, e', c') ->
      Value.subsumes gv gv' && Value.subsumes sv sv' && Value.subsumes e e' &&
        Value.subsumes c c'
    | TopProp, _ -> true
    | _, _ -> false

  let prop_join p p' = match p, p' with
    | Data ({ value=v; writable=w }, e, c),
      Data ({ value=v'; writable=w' },e', c') ->
      Data ({ value=Value.join v v'; writable=Value.join w w'},
            Value.join e e', Value.join c c')
    | Accessor ({ getter=gv; setter=sv }, e, c),
      Accessor ({ getter=gv'; setter=sv' }, e', c') ->
      Accessor ({ getter=Value.join gv gv'; setter=Value.join sv sv' },
                Value.join e e', Value.join c c')
    | _, _ -> TopProp

  module PMap = Abstract_map.Make(Value)(struct
    type t = propv
    let compare = Pervasives.compare
    let join = prop_join
    let subsumes = prop_subsumes
  end)

  let props_join pm pm' =
    PMap.fold (fun k v a -> PMap.join k v a) pm pm'

  let props_subsumes pm pm' =
    PMap.fold
      (fun k v a ->
        a && PMap.exists (fun k' v' -> Value.subsumes k' k && prop_subsumes v' v) pm)
      pm' true

  let props_top = PMap.clobber `Top TopProp PMap.empty

  let pset_join ps =
    if PSet.is_empty ps then failwith "refusing to join an empty set of props"
    else let prop = PSet.choose ps in PSet.fold prop_join (PSet.remove prop ps) prop
                                
  let string_of_props pm =
    PMap.fold (fun k v a -> (Value.string_of k)^" --> "^(string_of_prop v)^"\n"^a) pm ""

  type t = attrsv * PMap.t

  module OSet = Set.Make(struct
    type tmp = t
    (* This is really annoying, why are types recursive by default when functions and 
       modules aren't? *)
    type t = tmp
    let compare = Pervasives.compare
  end)

  let top = attrs_top, props_top

  let string_of (attrs, ps) =
    "objlit("^(string_of_attrs attrs)^", "^(string_of_props ps)^")"

  let join (attrs, ps) (attrs', ps') =
    attrs_join attrs attrs', props_join ps ps'

  let subsumes (attrs, ps) (attrs', ps') =
    attrs_subsumes attrs attrs' && props_subsumes ps ps'

  let make_obj ats nps =
    if ASet.is_empty ats then failwith "will not join an empty set of attrs!"
    else
      let attrsv = aset_join ats in
      let props =
        List.fold_left
          (fun props (n, ps) -> PMap.join (Value.str n) (pset_join ps) props)
          PMap.empty nps in
      attrsv, props

  let get_prop_attr (_, props) fieldv pattr =
    if not (PMap.mem fieldv props) then `Undef
    else
      match PMap.find fieldv props, pattr with
      | Data (_, _, config), Ljs_syntax.Config
      | Accessor (_, _, config), Ljs_syntax.Config -> config
      | Data (_, enum, _), Ljs_syntax.Enum
      | Accessor (_, enum, _), Ljs_syntax.Enum -> enum
      | Data ({ writable = b; }, _, _), Ljs_syntax.Writable -> b
      | Data ({ value = v; }, _, _), Ljs_syntax.Value -> v
      | Accessor ({ getter = gv; }, _, _), Ljs_syntax.Getter -> gv
      | Accessor ({ setter = sv; }, _, _), Ljs_syntax.Setter -> sv
      | p, attr -> begin 
        print_endline (Ljs_syntax.string_of_attr attr);
        print_endline (string_of_prop p);
        failwith "get field attr failed"
      end

  (* Ah, the wonders of desugaring. Anything that falls through this function
     has already had the appropriate type error thrown in the ES5 environment.
     So, a fall-through is a NAP. *)
  let set_prop_attr ({ exten=ext } as attrs, props) fv attr nv =
    let prop =
      if not (PMap.mem fv props) then
        if ext = Value.bool true then match attr with
        | Ljs_syntax.Getter ->
          Accessor ({ getter=nv; setter=`Undef }, Value.bool false, Value.bool false)
        | Ljs_syntax.Setter ->
          Accessor ({ getter=`Undef; setter=nv; }, Value.bool false, Value.bool false)
        | Ljs_syntax.Value ->
          Data ({ value=nv; writable=Value.bool false; }, Value.bool false, Value.bool false)
        | Ljs_syntax.Writable ->
          Data ({ value=`Undef; writable=nv }, Value.bool false, Value.bool false)
        | Ljs_syntax.Enum ->
          Data ({ value=`Undef; writable=Value.bool false }, nv, Value.bool true)
        | Ljs_syntax.Config ->
          Data ({ value=`Undef; writable=Value.bool false }, Value.bool true, nv)
        else failwith "trying to extend inextensible object!"
      else
        match PMap.find fv props, attr, nv with
      (* Writable true -> false when configurable is false *)
        | Data ({ writable=`Bool true } as d, enum, config), Ljs_syntax.Writable, new_w ->
          Data ({ d with writable=new_w }, enum, config)
        | Data (d, enum, `Bool true), Ljs_syntax.Writable, new_w ->
          Data ({ d with writable=new_w }, enum, Value.bool true)
      (* Updating values only checks writable *)
        | Data ({ writable=`Bool true } as d, enum, config), Ljs_syntax.Value, v ->
          Data ({ d with value=v }, enum, config)
      (* If we had a data property, update it to an accessor *)
        | Data (d, enum, `Bool true), Ljs_syntax.Setter, setterv ->
          Accessor ({ getter=`Undef; setter=setterv }, enum, Value.bool true)
        | Data (d, enum, `Bool true), Ljs_syntax.Getter, getterv ->
          Accessor ({ getter=getterv; setter=`Undef }, enum, Value.bool true)
      (* Accessors can update their getter and setter properties *)
        | Accessor (a, enum, `Bool true), Ljs_syntax.Getter, getterv ->
          Accessor ({ a with getter=getterv }, enum, Value.bool true)
        | Accessor (a, enum, `Bool true), Ljs_syntax.Setter, setterv ->
          Accessor ({ a with setter=setterv }, enum, Value.bool true)
      (* An accessor can be changed into a data property *)
        | Accessor (a, enum, `Bool true), Ljs_syntax.Value, v ->
          Data ({ value=v; writable=Value.bool false; }, enum, Value.bool true)
        | Accessor (a, enum, `Bool true), Ljs_syntax.Writable, w ->
          Data ({ value=`Undef; writable=w; }, enum, Value.bool true)
      (* enumerable and configurable need configurable=true *)
        | Data (d, _, `Bool true), Ljs_syntax.Enum, new_enum ->
          Data (d, new_enum, Value.bool true)
        | Data (d, enum, `Bool true), Ljs_syntax.Config, new_config ->
          Data (d, enum, new_config)
        | Data (d, enum, `Bool true), Ljs_syntax.Config, `Bool false ->
          Data (d, enum, Value.bool false)
        | Accessor (a, enum, `Bool true), Ljs_syntax.Config, new_config ->
          Accessor (a, enum, new_config)
        | Accessor (a, enum, `Bool true), Ljs_syntax.Enum, new_enum ->
          Accessor (a, new_enum, Value.bool true)
        | Accessor (a, enum, `Bool false), Ljs_syntax.Config, `Bool false ->
          Accessor (a, enum, Value.bool false)
        | x, y, z -> failwith "NAP bad prop attr set" in
    if Value.singletonp fv then attrs, PMap.clobber fv prop props
    else attrs, PMap.join fv prop props

  let get_obj_attr (attrs, _) oattr = match attrs, oattr with
    | { proto=proto }, Ljs_syntax.Proto -> proto
    | { exten=exten} , Ljs_syntax.Extensible -> exten
    | { code=`Bot}, Ljs_syntax.Code -> `Null
    | { code=code}, Ljs_syntax.Code -> code
    | { primv=`Bot}, Ljs_syntax.Primval ->
      failwith "[interp] Got Primval attr of Bot"
    | { primv=primv}, Ljs_syntax.Primval -> primv
    | { klass=klass }, Ljs_syntax.Klass -> klass

  let set_obj_attr (attrs, props) oattr nv =
    let set_attr ({ proto=proto; exten=ext; primv=primv } as attrs)
        oattr = (match oattr with
        | Ljs_syntax.Proto -> { attrs with proto=nv }
        | Ljs_syntax.Extensible -> { attrs with exten=nv }
        | Ljs_syntax.Primval -> { attrs with primv=nv }
        | _ -> failwith "set object attr failed") in
    let attrsv = set_attr attrs oattr in (attrsv, props)

  let own_field_names (_, props) =
    let names, n = PMap.fold (fun k _ (ks, n) -> k::ks, n+1) props ([], 0) in
    let groundp l =
      List.fold_left (fun b v -> b && Value.singletonp v) true names in
    let ofn_props =
      if groundp names then
        let add_name n x m =
          PMap.clobber
            (Value.str (string_of_int x))
            (Data ({ value=n; writable=Value.bool false; },
                   Value.bool false, Value.bool false))
            m in
        let props' = List.fold_right2 add_name names (Prelude.iota n) PMap.empty in
        PMap.clobber (Value.str "length")
          (Data ({ value=Value.num (float_of_int n); writable=Value.bool false },
                 Value.bool false, Value.bool false)) props'
      else
        props_top in
    default_attrs, ofn_props

end

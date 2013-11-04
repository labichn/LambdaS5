open Aam_lattices

type value = AValue.t
let vjoin = AValue.join
let vstring = AValue.string_of
let vsubsumes = AValue.subsumes

type attrs =
  { code: value; proto: value; exten: value; klass: value; primv: value }

module ASet =
  Set.Make(struct type t = attrs let compare = Pervasives.compare end)

let default_attrs =
  { code = `Bot;
    proto = `Null;
    exten = `False;
    primv = `Bot;
    klass = `Str "λS5 internal" }

let string_of_attrs { code=c; proto=pro; exten=e; klass=k; primv=pri } =
  "{ code="^(vstring c)^", "^
    "proto="^(vstring pro)^", "^
    "extensible="^(vstring e)^", "^
    "class="^(vstring k)^", "^
    "primval="^(vstring pri)^" }"

let attrs_subsumes { code=c; proto=pro; exten=e; klass=k; primv=pri }
    { code=c'; proto=pro'; exten=e'; klass=k'; primv=pri' } =
  vsubsumes c c' && vsubsumes pro pro' && vsubsumes e e' &&
    vsubsumes k k' && vsubsumes pri pri'

let attrs_join { code=c; proto=pro; exten=e; klass=k; primv=pri }
    { code=c'; proto=pro'; exten=e'; klass=k'; primv=pri' } =
  { code=vjoin c c'; proto=vjoin pro pro'; exten=vjoin e e';
    klass=vjoin k k'; primv=vjoin pri pri' }

let aset_join aset =
  if ASet.is_empty aset then failwith "refusing to join an empty set of attrs"
  else ASet.fold attrs_join aset
    { code=`Bot; proto=`Bot; exten=`Bot; klass=`Bot; primv=`Bot }

let attrs_top = { code=`Top; proto=`Top; exten=`Top; klass=`Top; primv=`Top }

type data = { value: value; writable: value }
type accessor = { getter: value; setter: value }

let string_of_data { value=v; writable=w } =
  "{ value="^(vstring v)^", writable="^(vstring w)^" }"

let string_of_accessor { getter=gv; setter=sv } =
  "{ getter="^(vstring gv)^", setter="^(vstring sv)^" }"

type prop =
| Data of data * value * value
| Accessor of accessor * value * value
| TopProp

module PSet =
  Set.Make(struct type t = prop let compare = Pervasives.compare end)

let string_of_prop = function
  | Data (d, e, c) ->
    "data("^(string_of_data d)^", "^(vstring e)^", "^(vstring c)^")"
  | Accessor (a, e, c) ->
    "accessor("^(string_of_accessor a)^", "^(vstring e)^", "^(vstring c)^")"
  | TopProp -> "topprop"

let prop_subsumes p p' = match p, p' with
  | Data ({ value=v; writable=w }, e, c),
    Data ({ value=v'; writable=w' },e', c') ->
    vsubsumes v v' && vsubsumes w w' && vsubsumes e e' && vsubsumes c c'
  | Accessor ({ getter=gv; setter=sv }, e, c),
    Accessor ({ getter=gv'; setter=sv' }, e', c') ->
    vsubsumes gv gv' && vsubsumes sv sv' && vsubsumes e e' && vsubsumes c c'
  | TopProp, _ -> true
  | _, _ -> false

let prop_join p p' = match p, p' with
  | Data ({ value=v; writable=w }, e, c),
    Data ({ value=v'; writable=w' },e', c') ->
    Data ({ value=vjoin v v'; writable=vjoin w w'}, vjoin e e', vjoin c c')
  | Accessor ({ getter=gv; setter=sv }, e, c),
    Accessor ({ getter=gv'; setter=sv' }, e', c') ->
    Accessor ({ getter=vjoin gv gv'; setter=vjoin sv sv' },
              vjoin e e', vjoin c c')
  | _, _ -> TopProp

module type AbsOrdered = sig
  type t
  val compare: t -> t -> int
  val subsumes: t -> t -> bool
  val join: t -> t -> t
end

module PropMap = struct

  module M = Map.Make(AValue)

  type t = prop M.t

  let empty : t = M.empty

  let rec crush m k v =
    let compact m k v =
      let interl, disjoint =
        M.partition (fun k' _ -> AValue.subsumes k k' || AValue.subsumes k' k)
          m in
      if M.is_empty interl then M.add k v disjoint, None
      else
        let k', v' =
          M.fold (fun k v (k', v') -> AValue.join k k', prop_join v v')
            interl (k, v) in
        disjoint, Some (k', v') in
    match compact m k v with
    | tmp, Some (k', v') -> crush tmp k' v'
    | res, None -> res

  let fold f m b = M.fold f m b
  let exists f m = M.exists f m

  let join k v m = crush m k v
  let unsafe_set k v m = M.add k v m (* only use if k is known not to be in m *)
  let set k v m =
    let can_clobber k m =
      fold (fun k' _ b -> b && (k' = k || not (AValue.subsumes k' k)))
        m true in
    if AValue.singletonp k && can_clobber k m then M.add k v m else join k v m

  let lookup k m =
    let tmp =
      M.fold (fun k' v vs -> if AValue.subsumes k' k then v::vs else vs) m [] in
    match tmp with
    | [] -> raise Not_found
    | [v] -> v
    | v::vs -> List.fold_left prop_join v vs

  let mem k m = M.fold (fun k' _ b -> b || AValue.subsumes k' k) m false

end

let props_join pm pm' =
  PropMap.fold (fun k v a -> PropMap.join k v a) pm pm'

let props_subsumes pm pm' =
  PropMap.fold
    (fun k v a ->
      a && PropMap.exists
        (fun k' v' -> AValue.subsumes k' k && prop_subsumes v' v) pm)
    pm' true

let props_top = PropMap.join `Top TopProp PropMap.empty

let pset_join ps =
  if PSet.is_empty ps then failwith "refusing to join an empty set of props"
  else
    let prop = PSet.choose ps in PSet.fold prop_join (PSet.remove prop ps) prop

let string_of_props pm =
  PropMap.fold
    (fun k v a -> (AValue.string_of k)^" --> "^(string_of_prop v)^"\n"^a)
    pm ""

type objekt = attrs * PropMap.t

let object_top = attrs_top, props_top

let string_of_obj (attrs, ps) =
  "objlit("^(string_of_attrs attrs)^", "^(string_of_props ps)^")"

let object_join (attrs, ps) (attrs', ps') =
  attrs_join attrs attrs', props_join ps ps'

let object_subsumes (attrs, ps) (attrs', ps') =
  attrs_subsumes attrs attrs' && props_subsumes ps ps'

let mt_props = PropMap.empty
let props_add = PropMap.set
let props_find = PropMap.lookup
let props_mem = PropMap.mem
let props_fold = PropMap.fold

let make_obj ats nps =
  if ASet.is_empty ats then failwith "will not join an empty set of attrs!"
  else
    let attrsv = aset_join ats in
    let props =
      List.fold_left
        (fun props (n, ps) -> props_add (`Str n) (pset_join ps) props)
        PropMap.empty nps in
    attrsv, props

let get_field_attr (_, props) fieldv pattr =
  if not (props_mem fieldv props) then `Undef
  else
    match props_find fieldv props, pattr with
    | Data (_, _, config), SYN.Config
    | Accessor (_, _, config), SYN.Config -> config
    | Data (_, enum, _), SYN.Enum
    | Accessor (_, enum, _), SYN.Enum -> enum
    | Data ({ writable = b; }, _, _), SYN.Writable -> b
    | Data ({ value = v; }, _, _), SYN.Value -> v
    | Accessor ({ getter = gv; }, _, _), SYN.Getter -> gv
    | Accessor ({ setter = sv; }, _, _), SYN.Setter -> sv
    | p, attr -> begin 
      print_endline (SYN.string_of_attr attr);
      print_endline (string_of_prop p);
      failwith "get field attr failed"
    end

(* Ah, the wonders of desugaring. Anything that falls through this function
   has already had the appropriate type error thrown in the ES5 environment.
   So, a fall-through is a NAP. *)
let set_field_attr ({ exten=ext } as attrs, props) fv attr nv =
  let prop =
    if not (props_mem fv props) then
      if ext = `True then match attr with
      | SYN.Getter ->
        Accessor ({ getter=nv; setter=`Undef }, `False, `False)
      | SYN.Setter ->
        Accessor ({ getter=`Undef; setter=nv; }, `False, `False)
      | SYN.Value ->
        Data ({ value=nv; writable=`False; }, `False, `False)
      | SYN.Writable ->
        Data ({ value=`Undef; writable=nv }, `False, `False)
      | SYN.Enum ->
        Data ({ value=`Undef; writable=`False }, nv, `True)
      | SYN.Config ->
        Data ({ value=`Undef; writable=`False }, `True, nv)
      else failwith "trying to extend inextensible object!"
    else
      match props_find fv props, attr, nv with
    (* Writable true -> false when configurable is false *)
      | Data ({ writable=`True } as d, enum, config), SYN.Writable, new_w ->
        Data ({ d with writable=new_w }, enum, config)
      | Data (d, enum, `True), SYN.Writable, new_w ->
        Data ({ d with writable=new_w }, enum, `True)
    (* Updating values only checks writable *)
      | Data ({ writable=`True } as d, enum, config), SYN.Value, v ->
        Data ({ d with value=v }, enum, config)
    (* If we had a data property, update it to an accessor *)
      | Data (d, enum, `True), SYN.Setter, setterv ->
        Accessor ({ getter=`Undef; setter=setterv }, enum, `True)
      | Data (d, enum, `True), SYN.Getter, getterv ->
        Accessor ({ getter=getterv; setter=`Undef }, enum, `True)
    (* Accessors can update their getter and setter properties *)
      | Accessor (a, enum, `True), SYN.Getter, getterv ->
        Accessor ({ a with getter=getterv }, enum, `True)
      | Accessor (a, enum, `True), SYN.Setter, setterv ->
        Accessor ({ a with setter=setterv }, enum, `True)
    (* An accessor can be changed into a data property *)
      | Accessor (a, enum, `True), SYN.Value, v ->
        Data ({ value=v; writable=`False; }, enum, `True)
      | Accessor (a, enum, `True), SYN.Writable, w ->
        Data ({ value=`Undef; writable=w; }, enum, `True)
    (* enumerable and configurable need configurable=true *)
      | Data (d, _, `True), SYN.Enum, new_enum ->
        Data (d, new_enum, `True)
      | Data (d, enum, `True), SYN.Config, new_config ->
        Data (d, enum, new_config)
      | Data (d, enum, `False), SYN.Config, `False ->
        Data (d, enum, `False)
      | Accessor (a, enum, `True), SYN.Config, new_config ->
        Accessor (a, enum, new_config)
      | Accessor (a, enum, `True), SYN.Enum, new_enum ->
        Accessor (a, new_enum, `True)
      | Accessor (a, enum, `False), SYN.Config, `False ->
        Accessor (a, enum, `False)
      | x, y, z -> failwith "NAP bad prop attr set" in
  if AValue.singletonp fv then attrs, PropMap.set fv prop props
  else attrs, PropMap.join fv prop props

let get_obj_attr attrs oattr = match attrs, oattr with
  | { proto=proto }, SYN.Proto -> proto
  | { exten=exten} , SYN.Extensible -> exten
  | { code=`Bot}, SYN.Code -> `Null
  | { code=code}, SYN.Code -> code
  | { primv=`Bot}, SYN.Primval ->
    failwith "[interp] Got Primval attr of Bot"
  | { primv=primv}, SYN.Primval -> primv
  | { klass=klass }, SYN.Klass -> klass

let set_obj_attr (attrs, props) oattr nv =
  let set_attr ({ proto=proto; exten=ext; primv=primv } as attrs)
      oattr = (match oattr with
      | SYN.Proto -> { attrs with proto=nv }
      | SYN.Extensible -> { attrs with exten=nv }
      | SYN.Primval -> { attrs with primv=nv }
      | _ -> failwith "set object attr failed") in
  let attrsv = set_attr attrs oattr in (attrsv, props)

let own_field_names (_, props) =
  let names, n = props_fold (fun k _ (ks, n) -> k::ks, n+1) props ([], 0) in
  let groundp l =
    List.fold_left (fun b v -> b && AValue.singletonp v) true names in
  let ofn_props =
    if groundp names then
      let add_name n x m = props_add (`Str (string_of_int x))
        (Data ({ value=n; writable=`False; }, `False, `False)) m in
      let props' = List.fold_right2 add_name names (Prelude.iota n) mt_props in
      props_add (`Str "length")
        (Data ({ value=`Num (float_of_int n); writable=`False },
               `False, `False)) props'
    else
      props_top in
  default_attrs, ofn_props
          

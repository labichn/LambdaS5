open Lattices

type value = AValue.t
let vjoin = AValue.join

type attrs =
  { code: value; proto: value; exten: value;
    klass: value; primv: value }
module Attrs = struct type t = attrs let compare = Pervasives.compare end
module ASet = Set.Make(Attrs)

let string_of_attrs { code=c; proto=pro; exten=e; klass=k; primv=pri } =
  "{ code="^(AValue.string_of c)^", "^
    "proto="^(AValue.string_of pro)^", "^
    "extensible="^(AValue.string_of e)^", "^
    "class="^(AValue.string_of k)^", "^
    "primval="^(AValue.string_of pri)^" }"

let combine_attrs ats =
  if ASet.is_empty ats then failwith "cannot combine an empty set of attrs!"
  else
    let at = ASet.choose ats in
    let ats' = ASet.remove at ats in
    let res =
      ASet.fold
        (fun { code=c; proto=p; exten=e; klass=k; primv=pv }
          { code=c'; proto=p'; exten=e'; klass=k'; primv=pv'} ->
            { code=vjoin c c'; proto=vjoin p p'; exten=vjoin e e';
              klass=vjoin k k'; primv=vjoin pv pv'})
        ats' at in
    begin print_endline ("combined attrs: "^(string_of_attrs res)); res end

type data = { value: value; writable: value }
type accessor = { getter: value; setter: value }

let string_of_data { value=v; writable=v' } =
  "{ value="^(AValue.string_of v)^", writable="^(AValue.string_of v')^" }"
let string_of_accessor { getter=gv; setter=sv } =
  "{ getter="^(AValue.string_of gv)^", setter="^(AValue.string_of sv)^" }"

type prop =
| Data of data * value * value
| Accessor of accessor * value * value
| TopProp
let string_of_prop p = match p with
  | Data (d, _, _) -> string_of_data d | Accessor (a, _, _) -> string_of_accessor a
  | _ -> "topprop"
module Prop = struct type t = prop let compare = Pervasives.compare end
module PSet = Set.Make (Prop)
let combine_props ps =
  if PSet.is_empty ps then failwith "cannot combine an empty set of props!"
  else begin
    let p = PSet.choose ps in
    print_endline ("chosen prop: "^(string_of_prop p));
    let ps' = PSet.remove p ps in
    let res = 
    PSet.fold
      (fun prop acc -> begin
        print_endline ("prop: "^(string_of_prop prop));
        match prop, acc with
      | Data _, Accessor _ | Accessor _, Data _ -> TopProp
      | Data ({ value=value; writable=writ }, enum, config),
        Data ({ value=value'; writable=writ' }, enum', config') ->
        Data ({ value=vjoin value value'; writable=vjoin writ writ' },
              vjoin enum enum', vjoin config config')
      | Accessor ({ getter=get; setter=set }, enum, config),
          Accessor ({ getter=get'; setter=set' }, enum', config') ->
        Accessor ({ getter=vjoin get get'; setter=vjoin set set' },
                  vjoin enum enum', vjoin config config')
      | _ -> TopProp end)
      ps' p in begin print_endline ("combined prop: "^(string_of_prop res)); res end end

type objekt = attrs * prop Prelude.IdMap.t

let default_attrs =
  { code = `Bot;
    proto = `Null;
    exten = `False;
    primv = `Bot;
    klass = `Str "λS5 internal" }

let string_of_obj o = "obj!"

type prop_map = PSet.t Prelude.IdMap.t
let mt_props = Prelude.IdMap.empty
let props_add = Prelude.IdMap.add
let props_find = Prelude.IdMap.find
let props_mem = Prelude.IdMap.mem
let props_filter = Prelude.IdMap.filter
let props_fold = Prelude.IdMap.fold

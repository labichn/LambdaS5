open Lattices

type value = AValue.t
let vjoin = AValue.join

type attrs =
  { code: value; proto: value; exten: value;
    klass: value; primv: value }
module Attrs = struct type t = attrs let compare = Pervasives.compare end
module ASet = Set.Make(Attrs)

let combine_attrs ats =
  if ASet.is_empty ats then failwith "cannot combine an empty set of attrs!"
  else
    let at = ASet.choose ats in let ats' = ASet.remove at ats in
    ASet.fold
      (fun { code=c; proto=p; exten=e; klass=k; primv=pv }
        { code=c'; proto=p'; exten=e'; klass=k'; primv=pv'} ->
          { code=vjoin c c'; proto=vjoin p p'; exten=vjoin e e';
            klass=vjoin k k'; primv=vjoin pv pv'})
      ats' at

type data = { value: value; writable: value }
type accessor = { getter: value; setter: value }

type prop =
| Data of data * value * value
| Accessor of accessor * value * value
| TopProp
module Prop = struct type t = prop let compare = Pervasives.compare end
module PSet = Set.Make (Prop)
let combine_props ps =
  if PSet.is_empty ps then failwith "cannot combine an empty set of props!"
  else
    let p = PSet.choose ps in let ps' = PSet.remove p ps in
    PSet.fold
      (fun prop acc -> match prop, acc with
      | Data _, Accessor _ | Accessor _, Data _ -> TopProp
      | Data ({ value=value; writable=writ }, enum, config),
        Data ({ value=value'; writable=writ' }, enum', config') ->
        Data ({ value=vjoin value value'; writable=vjoin writ writ' },
              vjoin enum enum', vjoin config config')
      | Accessor ({ getter=get; setter=set }, enum, config),
          Accessor ({ getter=get'; setter=set' }, enum', config') ->
        Accessor ({ getter=vjoin get get'; setter=vjoin set set' },
                  vjoin enum enum', vjoin config config')
      | _ -> TopProp)
      ps' p

type objekt = attrs * prop Prelude.IdMap.t

let default_attrs =
  { code = `Bot;
    proto = `Null;
    exten = `False;
    primv = `Bot;
    klass = `Str "λS5 internal" }

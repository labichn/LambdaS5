
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
  (** sets of attributes *)
  module PSet : Set.S with type elt = propv
  (** sets of properties *)
  module PMap : Abstract_map.S with type key = value and type value = propv
  (** maps of properties *)
  type t = attrsv * PMap.t
  (** the object type *)
  module OSet : Set.S with type elt = t
  (** sets of objects *)

  val subsumes: t -> t -> bool
  (** [subsumes o o'] determines whether [o] subsumes [o'], i.e. [o'] ⊑ [o] *)
  val attrs_subsumes: attrsv -> attrsv -> bool
  val prop_subsumes: propv -> propv -> bool
  val join: t -> t -> t
  (** join two objects together *)
  val top: t
  (** the dreaded top object *)
  val default_attrs: attrsv
  (** the attributes all objects start with *)
  val string_of: t -> string
  (** [string_of o] returns a string representation of [o] *)
  val make_obj: ASet.t -> (string * PSet.t) list -> t
  (** creates a new object *)
  val get_prop_attr: t -> value -> Ljs_syntax.pattr -> value
  (** gets the value associated with some property's attribute *)
  val set_prop_attr: t -> value -> Ljs_syntax.pattr -> value -> t
  (** sets the value associated with some property's attribute *)
  val get_obj_attr: t -> Ljs_syntax.oattr -> value
  (** gets the value associated with the object's attribute *)
  val set_obj_attr: t -> Ljs_syntax.oattr -> value -> t
  (** sets the value associated with the object's attribute *)
  val own_field_names: t -> t
  (** returns an object containing the field names of the given object *)

end

module MakeT(V : Aam_lattices.S) : sig
  module type T = S with type value = V.t
end

module Make (Value : Aam_lattices.S) : MakeT(Value).T

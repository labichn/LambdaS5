
(* Initial lattice will follow Coen De Roover's lead, with a single
 * concrete value between top and bottom. Delta has to jump fairly
 * quickly because of this. Another option may a precise delta with
 * an op limited lattice, where after n operations, we jump to top. *)

type 'a clattice = Con of 'a | Top | Bot
(* cl_lift: ('a -> 'b) 'b 'b 'a clattice -> 'b
     function being lifted, top output, bottom output, lattice value *)
let cl_lift f t b cl = match cl with
  | Top -> t | Bot -> b | Con a -> f a

let const_p cl = match cl with Con _ -> true | _ -> false
let const_of cl = match cl with
  | Con a -> a
  | _ -> failwith "tried to get the value of top or bottom"
let abs_p cl = not (const_p cl)

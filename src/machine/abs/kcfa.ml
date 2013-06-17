module C = Acontext
module K = Akont
module H = Ahandle
module SH = Ashared
module L = Clattice
module SYN = Ljs_syntax
type addr = Ashared.addr
let addr0 = Ashared.addr0
type time = Ashared.time
let time0 = Ashared.time0
type env = addr Prelude.IdMap.t
type context = Acontext.context
let time_of_context = Acontext.time_of
let time_of_kont = Akont.time_of
let time_of_hand = Ahandle.time_of
let pos_of_exp = Ljs_syntax.pos_of

let rec trunc k t = match k, t with
  | _, [] -> []
  | 0, _ -> []
  | n, t::ts -> t::(trunc (n-1) ts)

let tick k context store okont ohand : time = match context, okont, ohand with
  | C.Ap (p, `Clos _, _, _, _, t), _, _
  | C.Co (_, _, _, _, t), Some (K.Let (p, _, _, _, _, _)), _
  | C.Co (_, _, _, _, t), Some (K.Rec (p, _, _, _, _, _)), _
  | C.Co (_, _, _, _, t), Some (K.SetBang (p, _, _, _)), _ ->
    trunc k ((SH.P p)::t)
  | _, None, Some (hand) -> time_of_context context
  | C.Co _, _, Some (hand) -> time_of_hand hand
  | C.Co _, Some (kont), _ -> time_of_kont kont
  | _, _, _ -> time_of_context context

let alloc k context store okont ohand : addr = match context, okont, ohand with
  (* let and letrec binding is var-name::(trunc k time), easy *)
  | C.Ev (SYN.Rec (_, name, _, _), _, _, _, t), _, _
  | C.Co _, Some (K.Let (_, t, name, _, _, _)), _ ->
    SH.T ((SH.X name)::(trunc k t))
  (* other evs are simple, because konts and hands don't get derefed and
     there's no choice to be made *)
  | C.Ev (exp, _, _, _, t), _, _ ->
    SH.T ((SH.P (SYN.pos_of exp))::(trunc k t))
  | C.EvA (p, _, _, _, _, t), _, _
  (* apps need to allocate for each of the args, as they get stuck into
     the konts, and they are temporarily bound to their posn and trunced
     time. Hmmm.
     REVISIT: why not just bind them for application here? I've got the
       xs available, and I just have to go through the same process of
       allocation again anyway. The time shouldn't be different, as long
       as I pull it from the app kont. Try this after object redo *)
  | C.Co (_, p, _, _, _), Some (K.App (_, t, _, _, _)), _
  | C.Co (_, p, _, _, _), Some (K.App2 (_, t, _, _, _, _, _)), _
  (* thanks to the split store, and since objects have a single attrs rec,
     we can just use the object's position as our location head *)
  | C.CoA (_, _, _, _), Some (K.Object (p, t, _, _, _)), _
  (* data and accessors can't use object location, since there can be an
     arbitrary number of them for each object and we don't want to conflate
     them. cops pass back the position of one of the evaluated exps to use
     as the location we bind props to. Once app args are fixed to be bound
     only once, cops are the only motivation to thread pos through co*s. 
     Hmmm.
     REVISIT:
     What if I just use the name of the prop, and then I can remove
     pos entirely from context. LIE! alloc_kont needs them so app2s
     and object2s don't conflate *)
  | C.CoP (_, p, _, _, _), Some (K.Object2 (_, t, _, _, _, _, _)), _
  (* ex is a whole other animal, the time of the exception may be vastly
     different than the hand's time, but it also throws up an environment.
     the time should stay consistent with whatever environment is considered
     live, so we grab the time from there. *)
  | C.Ex (_, _, _, t), _, Some (H.Cat (p, _, _, _, _, _)) ->
    SH.T ((SH.P p)::(trunc k t))
  (* other cos allocate to hold intermediary values in konts, and since
     the allocation is driven by the kont, make it kont specific *)
  | C.Co _, Some kont, _ ->
    SH.T ((SH.P (K.pos_of kont))::(trunc k (K.time_of kont)))
    
let alloc' k context store okont ohand : addr list = match context with
  | C.Ap (p, `Clos (_, xs, _), vs, _, _, t) ->
    List.fold_right (fun x a -> (SH.T ((SH.X x)::(trunc k t)))::a) xs []

let alloc_kont k context store okont ohand = match context, okont, ohand with
  (* to avoid conflating k.dataprops and k.accprops *)
  | C.EvP (_, (_, SYN.Data ({ SYN.value=exp }, _, _)), _, _, _, t), _, _
  | C.EvP (_, (_, SYN.Accessor ({ SYN.getter=exp }, _, _)), _, _, _, t), _, _
  | C.Ev (exp, _, _, _, t), _, _ ->
    SH.T ((SH.P (pos_of_exp exp))::(trunc k t))
  | C.EvA (p, _, _, _, _, t), _, _
  | C.Ex _, _, Some (H.Cat (p, t, _, _, _, _))
  | C.Ex _, _, Some (H.Fin (p, t, _, _, _, _))
  | C.Co (_, p, _, _, _), _, Some (H.Fin (_, t, _, _, _, _)) ->
    SH.T ((SH.P p)::(trunc k t))
  | C.Co (_, p, _, _, _), Some (kont), _ ->
    SH.T ((SH.P p)::(trunc k (time_of_kont kont)))
let alloc_hand k context store okont ohand = match context with
  | C.Ev (exp, _, _, _, t) -> SH.T ((SH.P (pos_of_exp exp))::(trunc k t))

(*
Ticking occurs from a user initiated binding:
- ev let
- ev rec
- ev app
- ev setbang
The tick will set the time to the location of the binding location. This will
preserve kCFA abstraction flow information.

A value bound to a name, i.e. in a let, rec, or function application, is bound the pair of name and location binding, to feign alpha uniqueness.
A value being bound into a kont is bound by the most specific source location, e.g.:
- (string-append^1 "hello, "^2 "world"^3)^0 will cause many values with many bindings:
  - the optwo kont will be bound to 0::t
  - the optwo2 kont will be bound to 2::t, since "hello, "^2 is the most recently
      evaluated value
  - "hello, " will be bound to 2 inside the optwo2 kont
  - "hello, world"
    - if later bound to some kont will be bound to 0::t
    - if later bound to some name x will be bound to x::t

Some arbitrary let at time t
... (let (double (λ (x) (+ x x))) (double 10)) ...
(let (double^1 (λ (x) (+^4 x^5 x^6)^3)^2) (double^8 10^9)^7)^0

ev (let^0, env, k, t),
{ <k>->some_kont }
-->
ev ((λ (x) (+ x x))^2, env, 0::t, t),
{ <k>->some_kont, <0::t>->let(t, double^1, (double 10)^7) }
-->
co (0::t, (2, clos((λ (x) (+ x x)), env))),
{ <k>->some_kont, <0::t>->let(t, double^1, (double 10)^7) }
-->p
ev ((double 10)^7, env[double-><double@1>], k, t'),
{ <k>->some_kont, <0::t>->let(t, double^1, (double 10)^7), <double@1>-> }
-->
...

*)

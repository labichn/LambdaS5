(*

Strategy:

The machine is step wrapped in a fixpoint. The fixpoint testing transition
may not have the same input and output (a-la timestamped frontier + deltas), so
there should be an additional function to tie the output to the input. I also
need injection, which handles things like compilation, alpha uniqueness, et
cetera.

Step is the thing I don't want to rewrite. I need step to be abstract enough
that I can run with any setup. That means step's context can't have any widening
in it. I can do a simple widening in the fixpoint and then just convert the
context when I need to. So, step's context must be full.

I don't think I can easily do compiled and non-compiled versions of step, so there
may be two after all.

Keeping step's output as store deltas will let me do either version, by joining
them in immediately after stepping or by joining after the frontier steps.

What are my results? What information is good to know?
- time elapsed
- states stepped
- answers found
- exceptions found
- succeeded/failed (did an exception get thrown to the top?)
- state graph

*)

open Aam_collects
module C = Aam_context
module O = Aam_object
module S = Aam_store
module H = Aam_handle
module K = Aam_kont
module E = Aam_env
module DM = Aam_delta_map
module GC = Aam_gc
module AU = Aam_au
module ST = Aam_step
module SH = Aam_shared
module SYN = Ljs_syntax
module KCFA = Aam_kcfa

(* seconds elapsed, states stepped, answers found, exceptions found,
   terminated successfully, state graph *)
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

type exp = SYN.exp
type env = E.env
type store = S.store
type context = C.context
type addr = SH.addr
type time = SH.time

(** abstracted abstract machine *)
module type AAM = sig
  type system
  type output
  type input
  type step = input -> output
  (** transitions every state in the system one step *)
  val transition: bool -> step -> system -> system
  (** determines whether we've reached a fixpoint of the transitiong *)
  val fixp: system -> system -> bool
  (** given an expression, an initial environment, and an initial store,
      returns system zero for the machine *)
  val inject: env -> store -> exp -> system
  (** analyzes the given λS5 expression, with the option for verbose logging,
      initial environment & store, and output of a dot graph to file.  *)
  val analyze: ?verbose:bool -> ?env0:env -> ?store0:store -> ?path:string ->
    int -> (string -> exp) -> exp -> result
end

module CSet =
  Set.Make(struct
    type t = C.context
    let compare = Pervasives.compare
  end)

module CGraph =
  Graph.Persistent.Digraph.ConcreteBidirectional(struct
    type t = C.context
    let compare = Pervasives.compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)

module NCSet =
  Set.Make(struct
    type t = int * C.context
    let compare = Pervasives.compare
  end)

module NCGraph =
  Graph.Persistent.Digraph.ConcreteBidirectional(struct
    type t = int * C.context
    let compare = Pervasives.compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)

module WriteDot(G : Graph.Sig.G) = struct
  let to_dot str_of_v g =
    let _uid = ref 0 in
    let uid = fun () -> begin _uid := (!_uid+1); !_uid end in
    let hash = Hashtbl.create (G.nb_vertex g) in
    let vertices =
      G.fold_vertex
        (fun v a ->
          let nuid = uid() in
          Hashtbl.add hash v nuid;
          "  "^(string_of_int nuid)^" ["^
            "label=\""^(str_of_v v)^"\""^
            "shape=box"^
            "]\n"^a)
        g "" in
    let edges =
      G.fold_edges
        (fun c1 c2 a ->
          "  "^(string_of_int (Hashtbl.find hash c1))^" -> "^
            (string_of_int (Hashtbl.find hash c2))^"\n"^a)
        g "" in
    "digraph G {\n"^vertices^"\n"^edges^"}\n"

  let write g path verbose str_of_v =
    try
      let channel = open_out path in
      output_string channel (to_dot str_of_v g);
      close_out channel;
      if verbose then
        print_endline ("State graph written to "^path^".");
    with _ ->
      print_endline "An error occurring trying to write the state graph."
end

(*
Configurations provide the parameters to an AAM:
- alloc*
- tick
- deltas (eventually)
- debug printing
*)
module type Conf = sig
  val verbose: bool
  val alloc: context -> addr
  val alloc': context -> addr list
  val alloc'': context -> addr list list
  val alloc_hand: context -> addr
  val alloc_kont: context -> addr
  val desugar: string -> SYN.exp
  val tick: context -> time
end

module ConcreteConf(D : sig
  val desugar: string -> SYN.exp
  val verbose: bool
end) = struct
  include D
  let addr = ref (0)
  let all_alloc _ =
    let curr = !addr in
    begin
      addr := curr+1;
      SH.I curr
    end
  let alloc = all_alloc
  let alloc' c = match c with
    | C.Ap (_, `Clos (_, xs, _), vs, _, _, _, _) ->
      List.fold_right (fun x a -> (all_alloc c)::a) xs []
  let alloc'' c = match c with
    | C.Co (K.Eval (_, _, _, _, _, _, _), _, `Obj a, store, _, _) ->
      let os = S.get_objs a store in
      OSet.fold
        (fun (_, props) locss ->
          (O.PropMap.fold (fun _ _ ls -> (all_alloc c)::ls) props [])::locss)
        os []
  let alloc_hand = all_alloc
  let alloc_kont = all_alloc
  let tick = KCFA.tick 0
end

(*
module CLock(CONF : Conf) : ST.LOCKSTEP
  with type output = C.context and type input = C.context = struct
  include CONF

  type 'a lcon = 'a
  type input = C.context
  type output = C.context
  let context_of_input c = c
  let olift c = c
  let clift c = c
  let union x y = x
  let another x y = x
  let empty c = c
  let tick context ccon = ccon (CONF.tick context)
  let with_kont context ccon ckont =
    match context with
    | C.Ex (_, _, _, h, _) ->
      let kaddr = H.kont_of h in ccon (ckont kaddr)
    | _ -> 
      let kaddr = alloc_kont context in
      let store' = 
      (ccon (ckont kaddr),
       DM.add_kont kaddr (KSet.singleton (C.kont_of context)) delta)
  let with_hand context (ccon, delta) chand =
    let hkaddr = alloc_hand context in
    (ccon (chand hkaddr) K.Mt,
     DM.add_hand hkaddr (HSet.singleton (C.hand_of context))
       (DM.add_kont hkaddr (KSet.singleton (C.kont_of context)) delta))
  let add_obj a o c =
    let (vs, os, ss, hs, ks, ats, ps) = (C.store_of c) in
    C.with_store (vs, OStore.
    C.with_store (C.storeO (c, DM.add_obj a (OSet.singleton o) d)
  let add_val a v c = (c, DM.add_val a (VSet.singleton v) d)
  let set_obj a o c = (c, DM.set_obj a (OSet.singleton o) d)
  let set_val a v c = (c, DM.set_val a (VSet.singleton v) d)
  let add_hand a h c = (c, DM.add_hand a (HSet.singleton h) d)
  let add_kont a k c = (c, DM.add_kont a (KSet.singleton k) d)
  let add_attrs a att c = (c, DM.add_attrs a (O.ASet.singleton att) d)
  let add_prop a p c = (c, DM.add_prop a (O.PSet.singleton p) d)
end
*)

module KcfaConf(C : sig
  val desugar: string -> SYN.exp
  val k: int
  val verbose: bool
end) : Conf = struct
  include C
  let alloc = KCFA.alloc k
  let alloc' = KCFA.alloc' k
  let alloc'' = KCFA.alloc'' k
  let alloc_hand = KCFA.alloc_hand k
  let alloc_kont = KCFA.alloc_kont k
  let tick = KCFA.tick k
end

(* _counted_ context deltas  *)
module CDMSet =
  Set.Make(struct
    type t = C.context * DM.deltas
    let compare = Pervasives.compare
  end)
module CDMLock(CONF : Conf) : ST.LOCKSTEP
  with type output = CDMSet.t and type input = C.context = struct
  include CONF

  type 'a lcon = 'a * DM.deltas
  type input = C.context
  type output = CDMSet.t
  let context_of_input c = c
  let olift = CDMSet.singleton
  let clift c = c, DM.empty
  let union = CDMSet.union
  let another = CDMSet.add
  let empty _ = CDMSet.empty
  let tick context (ccon, delta) = ccon (CONF.tick context), delta
  let with_kont context (ccon, delta) ckont = match context with
    | C.Ex (_, _, _, h, _) ->
      let kaddr = H.kont_of h in ccon (ckont kaddr), delta
    | _ -> 
      let kaddr = alloc_kont context in
      (ccon (ckont kaddr),
       DM.add_kont kaddr (KSet.singleton (C.kont_of context)) delta)
  let with_hand context (ccon, delta) chand =
    let hkaddr = alloc_hand context in
    (ccon (chand hkaddr) K.Mt,
     DM.add_hand hkaddr (HSet.singleton (C.hand_of context))
       (DM.add_kont hkaddr (KSet.singleton (C.kont_of context)) delta))
  let add_obj a o (c, d) = (c, DM.add_obj a (OSet.singleton o) d)
  let add_val a v (c, d) = (c, DM.add_val a (VSet.singleton v) d)
  let set_obj a o (c, d) = (c, DM.set_obj a (OSet.singleton o) d)
  let set_val a v (c, d) = (c, DM.set_val a (VSet.singleton v) d)
  let add_hand a h (c, d) = (c, DM.add_hand a (HSet.singleton h) d)
  let add_kont a k (c, d) = (c, DM.add_kont a (KSet.singleton k) d)
  let add_attrs a att (c, d) = (c, DM.add_attrs a (O.ASet.singleton att) d)
  let add_prop a p (c, d) = (c, DM.add_prop a (O.PSet.singleton p) d)
end


(*
- frontier store widening, termination by subsumption testing
- abstract garbage collection
- abstract counting
*)

(*
module D : AAM = struct

  open C
  open O
  open S

  module DStep = ST.Make (CDMLock)
  module CGWrite = WriteDot(CGraph)

  (** seen set, frontier *)
  type system = CSet.t * CSet.t * S.store * CGraph.t

  let inject env0 store0 exp =
    begin
      let au_exp, ext = AU.alpha_unique exp in
      let t0 = [] in
      let context0 =
        C.Ev (au_exp, env0, store0, H.Mt, K.Mt, t0) in
      (CSet.empty, CSet.singleton context0, store0, CGraph.empty)
    end

  let transition ?(verbose=false) k desugar
      (seen, frontier, ((os, vs, ss, hs, ks, ats, ps) as store), graph) =
    begin
      (if verbose then
          let size = CSet.cardinal frontier in
          print_endline
            ("stepping "^(string_of_int size)^
                (if size = 1 then " state..." else " states...")));
      let i, ds =
        CSet.fold
          (fun con i -> begin
            if verbose then print_endline (string_of con);
            let succs =
              DStep.step verbose k desugar (C.with_store store con) in
            (if verbose then
                let size = CDMSet.cardinal succs in 
                print_endline ("resulting in "^(string_of_int size)^
                                  (if size = 1 then " state:"
                                   else " states:"));
                CDMSet.fold
                  (fun (c, _) _ ->
                    print_endline (C.string_of c))
                  succs (););
            CDMSet.fold (fun (c, d) (i, ds) -> (con, c)::i, d::ds)
              succs i
          end)
          frontier ([], []) in
      let store' = begin
        let (ods, vds, hds, kds, ads, pds) = DM.append_deltas ds in
        let vds' =
          List.fold_left
            (fun vds' (a, vs, b) ->
              (a, VSet.fold (fun v vs -> match v with
              | `Delay a' -> VSet.union (S.get_vals a' store) vs
              | _ -> VSet.add v vs)
                vs VSet.empty, b)::vds')
            [] vds in
(*        print_endline (VStore.string_of vs);*)
        (fst (OStore.replay_delta ods os),
         fst (VStore.replay_delta vds' vs),
         ss,
         fst (HStore.replay_delta hds hs),
         fst (KStore.replay_delta kds ks),
         fst (AStore.replay_delta ads ats),
         fst (PStore.replay_delta pds ps)) end in
        let lls =
          List.fold_left
            (fun lls (_, c) ->
              GC.union lls (GC.locs_of_context (C.with_store store' c)))
            GC.mts i in
        let store' = GC.gc store' lls in
        let seen', frontier', graph' =
          List.fold_left
            (fun (seen', frontier', graph') (pred, succ) ->
              let succ = C.with_store store' succ in
              let opt_subsumed = 
                CSet.fold
                  (fun x os -> match os with
                  | None -> if C.subsumes x succ then Some x else None
                  | Some y -> os)
                  seen' None in
              match opt_subsumed with
              | Some os ->
                seen',
                frontier',
                CGraph.add_edge graph' pred os
              | None ->
                CSet.add succ seen',
                (match succ with
                | C.NAP _ -> frontier'
                | _ -> CSet.add succ frontier'),
                CGraph.add_edge graph' pred succ)
            (seen, CSet.empty, graph) i in
        seen', frontier', store', graph'
    end

  let collect_res t0 t1 seen front =
    let duration = t1 -. t0 in
    let count = CSet.cardinal seen in
    let anss, exs =
      CSet.fold (fun c (a, e) ->
        match c with Ans _ -> a+1, e | Ex _ -> a, e+1 | _ -> a, e)
        seen (0, 0) in
    duration, count, anss, exs, CSet.is_empty front

  let fixp _ (_, f', _, _) = CSet.is_empty f'

  let analyze ?(verbose=false) ?(env0=E.empty) ?(store0=S.empty)
      ?(path="") k (desugar : (string -> exp)) exp = begin
        let t0 = Unix.gettimeofday() in
        if verbose then print_endline "Analyzing...";
        let rec loop system =
          let system' =
            transition ~verbose:verbose k desugar system in
          if fixp system system' then system'
          else if Unix.gettimeofday() -. t0 > 6000. then begin
            print_endline "failed to terminate within 100 minutes";
            system'
          end
          else loop system' in
        let (seen, front, _, g) = loop (inject env0 store0 exp) in
        let res =  collect_res t0 (Unix.gettimeofday()) seen front in
        (if path <> "" then
            try
              let dot_rep =
                CGWrite.to_dot C.string_of g in
              let channel = open_out path in
              output_string channel dot_rep;
              close_out channel;
              if verbose then
                print_endline ("State graph written to "^path^".");
            with _ ->
              print_endline "An error occurring trying to write the state graph.");
        print_endline (string_of_result res);
        (if verbose then print_endline "Done analyzing.");
        res
      end
end

module TimeStamped : AAM = struct

  module NCGWrite = WriteDot(NCGraph)

  type system = NCSet.t * CSet.t * store * store list * NCGraph.t * int
  type input = C.context
  type output = CDMSet.t
  type step = input -> output

  let inject env0 store0 exp =
    begin
      let au_exp, ext = AU.alpha_unique exp in
      let t0 = [] in
      let context0 =
        C.Ev (au_exp, env0, store0, H.Mt, K.Mt, t0) in
      (NCSet.empty, CSet.singleton context0, store0, [], NCGraph.empty, 0)
    end

  let transition verbose step
      (seen, frontier, ((os, vs, ss, hs, ks, ats, ps) as store), sts, graph, n) =
    begin
      (if verbose then
          let size = CSet.cardinal frontier in
          print_endline
            ("stepping "^(string_of_int size)^
                (if size = 1 then " state..." else " states...")));
      let i, ds =
        CSet.fold
          (fun con i -> begin
            if verbose then print_endline (C.string_of con);
            let succs = step (C.with_store store con) in
            (if verbose then
                let size = CDMSet.cardinal succs in 
                print_endline ("resulting in "^(string_of_int size)^
                                  (if size = 1 then " state:"
                                   else " states:"));
                CDMSet.fold
                  (fun (c, _) _ ->
                    print_endline (C.string_of c))
                  succs (););
            CDMSet.fold (fun (c, d) (i, ds) -> (con, c)::i, d::ds)
              succs i
          end)
          frontier ([], []) in
      let store', changedp = begin
        let (ods, vds, hds, kds, ads, pds) = DM.append_deltas ds in
        let vds' =
          List.fold_left
            (fun vds' (a, vs, b) ->
              (a, VSet.fold (fun v vs -> match v with
              | `Delay a' -> VSet.union (S.get_vals a' store) vs
              | _ -> VSet.add v vs)
                vs VSet.empty, b)::vds')
            [] vds in
(*        print_endline (VStore.string_of vs);*)
        let os', och = S.OStore.replay_delta ods os in
        let vs', vch = S.VStore.replay_delta vds' vs in
        let hs', hch = S.HStore.replay_delta hds hs in
        let ks', kch = S.KStore.replay_delta kds ks in
        let ats', ach = S.AStore.replay_delta ads ats in
        let ps', pch = S.PStore.replay_delta pds ps in
(*        (if och then print_endline "och!");
        (if vch then print_endline "vch!");
        (if hch then print_endline "hch!");
        (if kch then print_endline "kch!");
        (if ach then print_endline "ach!");
        (if pch then print_endline "pch!");*)
        (os', vs', ss, hs', ks', ats', ps'),
        och || vch || hch || kch || ach || pch end in
      let n' = if changedp then n+1 else n in
(*      print_endline ("changedp: "^(string_of_bool changedp));*)
      let seen', frontier', graph' =
        List.fold_left
          (fun (seen', frontier', graph') (pred, succ) -> begin
(*            print_endline (string_of_int (NCSet.cardinal seen'));*)
            let succ = C.with_store S.empty succ in
            let opt_subsumed = 
              NCSet.fold
                (fun (m, x) os -> match os with
                | None ->
                  if m = n' && succ = x then Some (m, x)
                  else None
                | Some _ -> os)
                seen' None in
            match opt_subsumed with
            | Some (m, os) ->
              seen',
              frontier',
              NCGraph.add_edge graph' (n, pred) (m, os)
            | None ->
              NCSet.add (n', succ) seen',
              (match succ with
              | C.NAP _ -> frontier'
              | _ -> CSet.add succ frontier'),
              NCGraph.add_edge graph' (n, pred) (n', succ) end)
          (seen, CSet.empty, graph) i in
      seen', frontier', store', (if n = n' then sts else store'::sts),
      graph', n'
    end
      
  let collect_res t0 t1 seen front =
    let duration = t1 -. t0 in
    let anss, exs, count =
      NCSet.fold (fun (_, c) (a, e, n) -> match c with
      | C.Ans _ -> a+1, e, n+1 | C.NAP _ | C.Ex _ -> a, e+1, n+1 | _ -> a, e, n+1)
        seen (0, 0, 0) in
    duration, count, anss, exs, CSet.is_empty front

  let fixp _ (_, f', _, _, _, _) = CSet.is_empty f'

  let analyze ?(verbose=false) ?(env0=E.empty) ?(store0=S.empty)
      ?(path="") k aspartame exp = begin
        let verb = verbose in
        let module Step = Aam_step.Make (CDMLock (ConcreteConf (struct
          let desugar = aspartame
          let verbose = verb
        end))) in
        let t0 = Unix.gettimeofday() in
        if verbose then print_endline "Analyzing...";
        let rec loop system =
          let system' = transition verbose Step.step system in
          if fixp system system' then system'
          else if Unix.gettimeofday() -. t0 > 300. then begin
            print_endline "failed to terminate within 5 minutes";
            system'
          end
          else loop system' in
        let (seen, front, _, _, g, _) = loop (inject env0 store0 exp) in
        let res =  collect_res t0 (Unix.gettimeofday()) seen front in
(*        (if path <> "" then
            try
              let dot_rep =
                NCGWrite.to_dot (fun (_, c) -> C.string_of c) g in
              let simple_dot_rep =
                NCGWrite.to_dot (fun (_, c) -> match c with
                | Ans (v, _, _) -> Aam_lattices.AValue.string_of v
                | _ -> "") g in
              let channel = open_out path in
              output_string channel dot_rep;
              close_out channel;
              let channel2 = open_out (path^".simple.dot") in
              output_string channel2 simple_dot_rep;
              close_out channel2;
              if verbose then
                print_endline ("State graph written to "^path^".");
            with _ ->
              print_endline "An error occurring trying to write the state graph.");*)
        print_endline (string_of_result res);
        (if verbose then print_endline "Done analyzing.");
        res
      end
end *)
(*
module Concrete : AAM = struct

(* seconds elapsed, states stepped, answers found, exceptions found,
   terminated successfully, state graph
type result = float * int * int * int * bool *)

  type system = C.context
  type input = C.context
  type output = C.context
  type step = input -> output

  let inject env0 store0 exp =
    let t0 = [] in C.Ev (exp, env0, store0, H.Mt, K.Mt, t0)

  let transition verbose step context = step context

  let fixp _ context = match context with
    | Ans _  | NAP _ -> true
    | _ -> false

  let analyze ?(verbose=false) ?(env0=E.empty) ?(store0=S.empty)
      ?(path="") kay aspartame exp =
    let module Step = Aam_step.Make (

end *)

module TimeStamped : AAM = struct

  module NCGWrite = WriteDot(NCGraph)

  type system = NCSet.t * CSet.t * store * store list * NCGraph.t * int
  type input = C.context
  type output = CDMSet.t
  type step = input -> output

  let inject env0 store0 exp =
    begin
      let au_exp, ext = AU.alpha_unique exp in
      let t0 = [] in
      let context0 =
        C.Ev (au_exp, env0, store0, H.Mt, K.Mt, t0) in
      (NCSet.empty, CSet.singleton context0, store0, [], NCGraph.empty, 0)
    end

  let transition verbose step
      (seen, frontier, ((os, vs, ss, hs, ks, ats, ps) as store), sts, graph, n) =
    begin
      (if verbose then
          let size = CSet.cardinal frontier in
          print_endline
            ("stepping "^(string_of_int size)^
                (if size = 1 then " state..." else " states...")));
      let i, ds =
        CSet.fold
          (fun con i -> begin
            if verbose then print_endline (C.string_of con);
            let succs = step (C.with_store store con) in
            (if verbose then
                let size = CDMSet.cardinal succs in 
                print_endline ("resulting in "^(string_of_int size)^
                                  (if size = 1 then " state:"
                                   else " states:"));
                CDMSet.fold
                  (fun (c, _) _ ->
                    print_endline (C.string_of c))
                  succs (););
            CDMSet.fold (fun (c, d) (i, ds) -> (con, c)::i, d::ds)
              succs i
          end)
          frontier ([], []) in
      let store', changedp = begin
        let (ods, vds, hds, kds, ads, pds) = DM.append_deltas ds in
        let vds' =
          List.fold_left
            (fun vds' (a, vs, b) ->
              (a, VSet.fold (fun v vs -> match v with
              | `Delay a' -> VSet.union (S.get_vals a' store) vs
              | _ -> VSet.add v vs)
                vs VSet.empty, b)::vds')
            [] vds in
(*        print_endline (VStore.string_of vs);*)
        let os', och = S.OStore.replay_delta ods os in
        let vs', vch = S.VStore.replay_delta vds' vs in
        let hs', hch = S.HStore.replay_delta hds hs in
        let ks', kch = S.KStore.replay_delta kds ks in
        let ats', ach = S.AStore.replay_delta ads ats in
        let ps', pch = S.PStore.replay_delta pds ps in
(*        (if och then print_endline "och!");
        (if vch then print_endline "vch!");
        (if hch then print_endline "hch!");
        (if kch then print_endline "kch!");
        (if ach then print_endline "ach!");
        (if pch then print_endline "pch!");*)
        (os', vs', ss, hs', ks', ats', ps'),
        och || vch || hch || kch || ach || pch end in
      let n' = if changedp then n+1 else n in
(*      print_endline ("changedp: "^(string_of_bool changedp));*)
      let seen', frontier', graph' =
        List.fold_left
          (fun (seen', frontier', graph') (pred, succ) -> begin
(*            print_endline (string_of_int (NCSet.cardinal seen'));*)
            let succ = C.with_store S.empty succ in
            let opt_subsumed = 
              NCSet.fold
                (fun (m, x) os -> match os with
                | None ->
                  if m = n' && succ = x then Some (m, x)
                  else None
                | Some _ -> os)
                seen' None in
            match opt_subsumed with
            | Some (m, os) ->
              seen',
              frontier',
              NCGraph.add_edge graph' (n, pred) (m, os)
            | None ->
              NCSet.add (n', succ) seen',
              (match succ with
              | C.NAP _ -> frontier'
              | _ -> CSet.add succ frontier'),
              NCGraph.add_edge graph' (n, pred) (n', succ) end)
          (seen, CSet.empty, graph) i in
      seen', frontier', store', (if n = n' then sts else store'::sts),
      graph', n'
    end
      
  let collect_res t0 t1 seen front =
    let duration = t1 -. t0 in
    let anss, exs, count =
      NCSet.fold (fun (_, c) (a, e, n) -> match c with
      | C.Ans _ -> a+1, e, n+1 | C.NAP _ | C.Ex _ -> a, e+1, n+1 | _ -> a, e, n+1)
        seen (0, 0, 0) in
    duration, count, anss, exs, CSet.is_empty front

  let fixp _ (_, f', _, _, _, _) = CSet.is_empty f'

  let analyze ?(verbose=false) ?(env0=E.empty) ?(store0=S.empty)
      ?(path="") kay aspartame exp = begin
        let verb = verbose in
        let module Step = Aam_step.Make (CDMLock (KcfaConf (struct
          let desugar = aspartame
          let verbose = verb
          let k = kay
        end))) in
        let t0 = Unix.gettimeofday() in
        if verbose then print_endline "Analyzing...";
        let rec loop system =
          let system' = transition verbose Step.step system in
          if fixp system system' then system'
          else if Unix.gettimeofday() -. t0 > 300. then begin
            print_endline "failed to terminate within 5 minutes";
            system'
          end
          else loop system' in
        let (seen, front, _, _, g, _) = loop (inject env0 store0 exp) in
        let res =  collect_res t0 (Unix.gettimeofday()) seen front in
(*        (if path <> "" then
            try
              let dot_rep =
                NCGWrite.to_dot (fun (_, c) -> C.string_of c) g in
              let simple_dot_rep =
                NCGWrite.to_dot (fun (_, c) -> match c with
                | Ans (v, _, _) -> Aam_lattices.AValue.string_of v
                | _ -> "") g in
              let channel = open_out path in
              output_string channel dot_rep;
              close_out channel;
              let channel2 = open_out (path^".simple.dot") in
              output_string channel2 simple_dot_rep;
              close_out channel2;
              if verbose then
                print_endline ("State graph written to "^path^".");
            with _ ->
              print_endline "An error occurring trying to write the state graph.");*)
        print_endline (string_of_result res);
        (if verbose then print_endline "Done analyzing.");
        res
      end
end

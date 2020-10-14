(* locEq.ml -- derive local equivalence specs *)

open Astutil
open Lib
open Annot
open Typing
open Pretrans
open Pretty

open Why3
open Why3util


(* -------------------------------------------------------------------------- *)
(* Utility functions                                                          *)
(* -------------------------------------------------------------------------- *)

exception Unknown_method of string

let kind e = e.effect_kind
let desc e = e.effect_desc

(* For any effect e, rds(e) is exactly all the read effects in e *)
let rds = List.filter ((=) Ast.Read  % kind)

(* For any effect e, wrs(e) is exactly all the write effects is e *)
let wrs = List.filter ((=) Ast.Write % kind)

(* Functions to create Effvar's and Effimg's *)
let effvar k x t   = {effect_kind = k; effect_desc = Effvar (x -: t) -: t}
let effimg k g f t = {effect_kind = k; effect_desc = Effimg (g, f) -: t}

(* get_img f k e = Some (G`f) iff e contains k G`f where k = rd or k = wr *)
let get_img fld knd eff =
  List.find_opt (fun e ->
      match (desc e).node with
      | Effimg (g, f) -> fld = f.node && knd = kind e
      | _ -> false
    ) eff

(* subtract e1 e2 = d1 @ d2 @ d3 @ d4 where

   d1 = [ rd x   | rd x in e1 and rd x notin e2 ]
   d2 = [ rd G`f | rd G`f in e1 and e2 has no f read ] 
      @ [ rd (G\H)`f | rd G`f in e1 and rd H`f in e2 ]

   d3 and d4 are similarly defined for writes.  e1 and e2 are
   normalized first.

   The implementation isn't efficient -- it's in the order of O(n^2)
   when e1 and e2 are of length n.  This can be brought down to O(n)
   if e1 and e2 are kept sorted. 
*)
let subtract (e1: effect) (e2: effect) : effect =
  let e1,e2 = map_pair Normalize_effects.normalize_effect (e1,e2) in
  let sub eff acc = match desc eff with
    | { node = Effvar x; ty } ->
      if List.mem eff e2 then acc else eff :: acc
    | { node = Effimg (g,f); ty } ->
      match get_img f.node (kind eff) e2 with
      | None -> eff :: acc
      | Some { effect_desc = { node = Effimg (h, _); ty = ty' }; _ } ->
        assert (ty = ty');
        let rgn = Ebinop (Ast.Diff, g, h) -: Trgn in
        let eff = { eff with effect_desc = Effimg (rgn, f) -: ty' } in
        eff :: acc
      | _ -> assert false in
  List.fold_right sub e1 []

(* A unary spec s is P ~> Q [e] where
   P = preconds s and Q = postconds s and e = effects s *)

(* Obtain all the precoditions in a unary spec *)
let preconds (s: spec) : formula list =
  List.filter_map (function Precond f -> Some f | _ -> None) s

(* Obtain all the postconditions in a unary spec *)
let postconds (s: spec) : formula list =
  List.filter_map (function Postcond f -> Some f | _ -> None) s

(* Obtain all the effects in a unary spec *)
let effects (s: spec) : effect =
  concat_filter_map (function Effects e -> Some e | _ -> None) s

(* bnd_plus bnd = bnd , alloc *)
let bnd_plus bnd : boundary_decl =
  let read_alloc = Effvar (Ast.Id "alloc" -: Trgn) -: Trgn in
  read_alloc :: bnd

(* eff_of_bnd { LE1, ... LEn } = { rd LE1, ... rd LEn } *)
let eff_of_bnd (bnd: boundary_decl) : effect =
  List.map (fun e -> { effect_kind = Read ; effect_desc = e }) bnd


(* -------------------------------------------------------------------------- *)
(* Derivation of local equivalence                                            *)
(* -------------------------------------------------------------------------- *)

(* agreement_list e = fs

   Invariant:
   for each rd x   in e, (x =:= x)   in fs
   for each rd G`f in e, (Agree G`f) in fs
   length fs = length (rds(e)) 
*)
let rec agreement_list eff : rformula list =
  match eff with
  | [] -> []
  | { effect_kind = Write; _} :: es -> agreement_list es
  | { effect_kind = Read ; effect_desc = desc } :: es ->
    let head = match desc.node with
      | Effvar x     -> Rbiequal (Evar x -: x.ty, Evar x -: x.ty)
      | Effimg (g,f) -> Ragree (g,f) in
    head :: agreement_list es


(* A "snapshot" is a map from (region) expressions to identifiers.

   In our current syntax, old(e) is not an expression.  The only way
   to refer to the old value of e is to assert x = old(e) or bind
   old(e) in a formula, e.g. let oe = old(e) in P(oe).  In relation
   formulas, we may say let oe|oe = old(e)|old(e) in P(oe).

   Given a snapshot S and a relation formula P(xs) with free variables
   xs in rng(S), we may construct a closed relation formula P' by
   binding each x in xs to the the old value of e where (e,x) in S.
   Example:

   if S = [f |-> s1; h union g |-> s2] then P':

      let s1|s1 = old(f)|old(f) in
      let s2|s2 = old(h union g)|old(h union g) in
      P(s1,s2)
*)
module ExpM = Map.Make (struct type t = exp Annot.t let compare = compare end)
type snapshot = ident ExpM.t


(* A value of type rf_ctx is a relation formula with a "hole" *)
type rf_ctx = RF_ctx of (rformula -> rformula)

(* Given a snapshot S, build an rf_ctx that binds each xs in rgn(S) to
   old (e) where for each x in xs, (e,x) in S.
*)
let rf_ctx_of_snapshot (s: snapshot) =
  let inner =
    ExpM.fold (fun g name acc ->
        let ty = g.ty in
        let lbind = {value = Lexp g -: ty; is_old = true} -: ty in
        let rbind = {value = Lexp g -: ty; is_old = true} -: ty in
        Rlet ((name -: ty, ty, lbind), (name -: ty, ty, rbind), acc)
      ) s in
  RF_ctx inner

(* build_rformula Ctx f = f'

   f' is closed iff Ctx contains binds all free variables in f
*)
let build_rformula (RF_ctx f) rfrm : rformula = f rfrm

(* mk_snapshot_ident G () = id

   id is an "appropriately named" identifier for G 
*)
let mk_snapshot_ident =         (* FIXME: there may be name clashes. *)
  let ident name = Ast.Id name in
  let create_name e =
    match e.node with
    | Evar {node = Id name; _} -> name
    | Esingleton {node = Evar {node = Id name; _}; _} -> name
    | Eimage (g, {node = Id f; _}) -> f
    | _ -> "r" in
  let stamp = ref (-1) in
  let names = ref [] in
  fun rgn_exp () -> begin
      let name = create_name rgn_exp in
      if List.mem name !names then begin
        incr stamp;
        let name = name ^ string_of_int !stamp in
        names := name :: !names;
        ident ("s_" ^ name)
      end else begin
        names := name :: !names;
        ident ("s_" ^ name)
      end
    end

(* snap e = S

   Computes snap as defined in the paper (Def 8.2), but returns a
   snapshot instead of of a unary formula.

   Invariant:
   For each s_G,f = G derived by snap in the logic, S contains a
   the mapping G |-> s_G,f
*)
let snap (e: effect) : snapshot =
  let walk acc = function
    | { effect_kind = Read; _ } -> acc
    | { effect_kind = Write; effect_desc = desc } ->
      match desc.node with
      | Effvar _     -> acc
      | Effimg (g,f) ->
        let name = mk_snapshot_ident g () in
        ExpM.add g name acc in
  List.fold_left walk ExpM.empty e


(* asnap S e = e'

   Given a snapshot S and an effect e, computes a read effect e' (Def
   8.2).

   Invariant:
   If S = snap(e) then
     for each (wr G`f) in e, e' contains rd (s_G,f)`f 
       where (G |-> s_G,f) in S.
     for each (wr x) in e, e' contains rd x iff x <> alloc
     length(e') = length(wrs(e)) - # of wr alloc's in e
*)
let asnap (s: snapshot) (e: effect) : effect =
  let walk = function
    | { effect_kind = Read; _} -> []
    | { effect_kind = Write; effect_desc = desc } ->
      match desc.node with
      | Effvar x ->
        if x.node <> Ast.Id "alloc"
        then [effvar Ast.Read x.node Trgn]
        else []
      | Effimg (g,f) ->
        let name = ExpM.find g s in
        let var = Evar (name -: g.ty) -: g.ty in
        [effimg Read var f desc.ty] in
  concat_map walk e

(* post_agreement0 () = Agree (rd (alloc \ s_alloc)`any)

   where s_alloc = old(alloc)
*)
let post_agreement0 () =        (* DEPRECATED *)
  let alloc = Evar (Ast.Id "alloc" -: Trgn) -: Trgn in
  let l_oalloc = {value = Lexp alloc -: Trgn; is_old = true} -: Trgn in
  let r_oalloc = {value = Lexp alloc -: Trgn; is_old = true} -: Trgn in
  let s_alloc  = Ast.Id "s_alloc" -: Trgn in
  let s_alloc_exp = Evar s_alloc -: Trgn in
  let any_datagrp = Ast.Id "any" -: Tdatagroup in
  let diff_exp = Ebinop(Ast.Diff, alloc, s_alloc_exp) -: Trgn in
  let rfrm = Ragree(diff_exp, any_datagrp) in
  Bipostcond (Rlet ((s_alloc, Trgn, l_oalloc), (s_alloc, Trgn, r_oalloc), rfrm))

let post_agreement1 eff =       (* DEPRECATED *)
  assert (Normalize_effects.is_normalized eff);
  let rec mk_rconjs = function
    | [] -> invalid_arg "mk_rconjs"
    | [f] -> f
    | f :: fs -> Rconn (Ast.Conj, f, mk_rconjs fs) in
  let snapshot  = snap eff in
  let asnap_eff = asnap snapshot eff in
  let inner = agreement_list asnap_eff in
  let inner = if inner = [] then Rboth Ftrue else mk_rconjs inner in
  Bipostcond (build_rformula (rf_ctx_of_snapshot snapshot) inner)

let rec post_agreement ctbl bnd eff =
  assert (Normalize_effects.is_normalized eff);
  let rec mk_rconjs = function
    | [] -> invalid_arg "mk_rconjs"
    | [f] -> f
    | f :: fs -> Rconn (Ast.Conj, f, mk_rconjs fs) in
  (* Build ctxt in which alloc is snapshotted *)
  let alloc = Evar (Ast.Id "alloc" -: Trgn) -: Trgn in
  let l_oalloc = {value = Lexp alloc -: Trgn; is_old = true} -: Trgn in
  let r_oalloc = {value = Lexp alloc -: Trgn; is_old = true} -: Trgn in
  let s_alloc = mk_snapshot_ident alloc () -: Trgn in
  let s_alloc_exp = Evar s_alloc -: Trgn in
  let diff_exp = Ebinop (Ast.Diff, alloc, s_alloc_exp) -: Trgn in
  let diff_eff = expand_any ctbl diff_exp in
  let snapshot = snap eff in
  let asnap_eff = asnap snapshot eff in
  let agreement_eff = subtract (diff_eff @ asnap_eff) (eff_of_bnd bnd) in
  let agreement = agreement_list agreement_eff in
  let agreement = if agreement = [] then Rboth Ftrue else mk_rconjs agreement in
  let bind_alloc frm =
    Rlet ((s_alloc, Trgn, l_oalloc), (s_alloc, Trgn, r_oalloc), frm) in
  let agreement_frm = build_rformula (rf_ctx_of_snapshot snapshot) agreement in
  Bipostcond (bind_alloc agreement_frm)

and expand_any ctbl diff : effect =
  let mk_eff f =
    {effect_kind = Read; effect_desc = Effimg (diff, f) -: Trgn} in
  let extract {field_name; field_ty; _} =
    assert (field_name.ty = field_ty);
    field_name.node -: field_ty in
  List.map (mk_eff % extract) @@ Ctbl.known_fields ctbl

(* both_postcondition fs = Ps

   where for each f in fs, Ps contains (Bipostcond (Both f))
*)
let both_postcondition = List.map (fun f -> Bipostcond (Rboth f))

(* both_precondition fs = Ps

   where for each f in fs, Ps contains (Biprecond (Both f))
*)
let both_precondition = List.map (fun f -> Biprecond (Rboth f))

(* pre_agreement bnd eff = Agree (rds(eff) \ bnd_plus bnd) *)
let pre_agreement bnd eff =
  let eff = subtract (rds eff) (eff_of_bnd (bnd_plus bnd)) in
  List.map (fun f -> Biprecond f) (agreement_list eff)

(* local_equivalence bnd spec = spec'

   where spec' is the local equivalence spec for (unary) spec under boundary
   bnd.
*)
let local_equivalence (ctbl: Ctbl.t) (bnd: boundary_decl) (spec: spec)
  : bispec =
  let pre = preconds spec and post = postconds spec and eff = effects spec in
  let eff = Normalize_effects.normalize_effect eff in
  let bi_pre  = both_precondition pre @ pre_agreement bnd eff in
  let bi_post = post_agreement ctbl bnd eff :: both_postcondition post in
  bi_pre @ bi_post @ [Bieffects (eff, eff)]

module BndS = Set.Make (struct
    type t = effect_desc Annot.t
    let compare = compare
  end)

let rec derive_locEq penv ctbl deps meth_name : bispec =
  let mdl_name, intr_name = find_method_module_name penv meth_name in
  let boundary = collective_boundaries penv deps mdl_name intr_name in
  local_equivalence ctbl boundary (find_method_spec penv mdl_name meth_name)

and find_method_module_name penv meth_name : ident * ident =
  let has_method pfrag =
    let check = function
      | Mdl_mdef (Method (mdecl,_)) -> mdecl.meth_name.node = meth_name
      | _ -> false in
    match pfrag with
    | Unary_module mdl -> List.exists check mdl.mdl_elts
    | _ -> false in
  let mdl = ref None in
  IdentM.iter (fun k v -> if has_method v then mdl := Some v else ()) penv;
  match !mdl with
  | None -> raise (Unknown_method (string_of_ident meth_name))
  | Some (Unary_module m) -> (m.mdl_name, m.mdl_interface)
  | Some _ -> assert false

and collective_boundaries penv deps mdl_name intr_name : boundary_decl =
  let imported = prefix_satisfying ((<>) mdl_name) deps in
  let imported = List.filter ((<>) intr_name) imported in
  let imported = List.filter (fun mdl ->
      match IdentM.find mdl penv with
      | Unary_module mdl -> mdl.mdl_interface <> intr_name
      | _ -> true
    ) imported in
  let rec find bnd = function
    | [] -> BndS.elements bnd
    | m :: ms -> match IdentM.find m penv with
      | Unary_module m ->
        let b = BndS.of_list @@ find_module_boundary penv m in
        find (BndS.union b bnd) ms
      | Unary_interface i ->
        let b = BndS.of_list @@ find_interface_boundary i in
        find (BndS.union b bnd) ms
      | _ -> find bnd ms in
  find BndS.empty (List.rev imported)

and find_module_boundary penv mdl : boundary_decl =
  let interface_name = mdl.mdl_interface in
  let interface = IdentM.find interface_name penv in
  match interface with
  | Unary_interface i -> find_interface_boundary i
  | _ -> failwith ("Unknown interface " ^ (string_of_ident interface_name))

and find_interface_boundary intr : boundary_decl =
  concat_filter_map (function
      | Intr_boundary bnd -> Some bnd
      | _ -> None
    ) intr.intr_elts

and find_method_spec penv mdl_name meth_name : spec =
  let mdl = IdentM.find mdl_name penv in
  match mdl with
  | Unary_module mdl ->
    let meth =
      List.filter_map (function
          | Mdl_mdef (Method (mdecl,_)) ->
            if mdecl.meth_name.node = meth_name
            then Some mdecl.meth_spec
            else None
          | _ -> None
        ) mdl.mdl_elts in
    begin match meth with
      | [] -> raise (Unknown_method (string_of_ident meth_name))
      | ss -> last ss
    end
  | _ -> failwith ("Unknown module " ^ (string_of_ident mdl_name))

and pp_derive_locEq penv ctbl deps meth_name outf : unit =
  let loc_eq = derive_locEq penv ctbl deps meth_name in
  pp_bispec outf loc_eq

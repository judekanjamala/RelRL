(** pretrans.ml -- transformations on annotated ASTs *)

open Lib
open Astutil
open Annot
open Typing

let pretrans_debug = ref false


(* -------------------------------------------------------------------------- *)
(* A type for normalized effects (not currently used)                         *)
(* -------------------------------------------------------------------------- *)

module type NORM = sig
  type t = private Normalized of effect
  val abs : effect -> t
  val rep : t -> effect
  val mk : effect -> t
end

module type NORM_FNS = sig
  val is_normalized : effect -> bool
  val normalize_effect : effect -> effect
end

module Norm (F: NORM_FNS) : NORM = struct
  (* Properties

     forall (e : normalized effect), ABS (REP e) = e
     forall (e : effect),            F.is_normalized e ==> REP (ABS a) = a


     Invariant: Every value of type Norm.t is a normalized effect
  *)

  type t = Normalized of effect

  let abs (e: effect) : t =
    if F.is_normalized e
    then Normalized e
    else failwith "abs: failure"

  let rep (Normalized e) : effect = e

  let mk (e: effect) : t = abs (F.normalize_effect e)
end


(* -------------------------------------------------------------------------- *)
(* Obtain full spec of methods in modules                                     *)
(* -------------------------------------------------------------------------- *)

module Expand_method_spec : sig
  val expand : penv -> penv
end = struct

  let find_interface_spec penv intr meth : spec option =
    let intr_str = string_of_ident intr in
    match IdentM.find intr penv with
    | Unary_interface {intr_name; intr_elts} ->
      let intr_meth_spec = List.filter_map (function
          | Intr_mdecl mdecl when mdecl.meth_name.node = meth ->
            Some mdecl.meth_spec
          | _ -> None
        ) intr_elts in
      begin match intr_meth_spec with
        | [] -> None
        | ss -> Some (last ss)
      end
    | _ | exception Not_found ->
      failwith @@ "Unknown interface: " ^ intr_str

  let expand_meth_def_in_module penv intr mdef : meth_def =
    let Method (mdecl, com) = mdef in
    let intr_spec = find_interface_spec penv intr mdecl.meth_name.node in
    let meth_spec = match intr_spec with
      | Some s -> s @ mdecl.meth_spec
      | None -> mdecl.meth_spec in
    Method ({mdecl with meth_spec}, com)

  let expand_module penv mdl : module_def =
    let intr = mdl.mdl_interface in
    let elts = List.map (function
        | Mdl_mdef mdef ->
          let mdef' = expand_meth_def_in_module penv intr mdef in
          Mdl_mdef mdef'
        | e -> e
      ) mdl.mdl_elts in
    {mdl with mdl_elts = elts}

  let expand programs = IdentM.map (fun v ->
      match v with
      | Unary_module mdl -> Unary_module (expand_module programs mdl)
      | _ -> v
    ) programs
end


(* -------------------------------------------------------------------------- *)
(* Resolve datagroups in effects and boundaries                               *)
(* -------------------------------------------------------------------------- *)

(* NOTE: This must be run after method specs have been expanded;
   otherwise, a method might not contain all of its effects clauses. *)

module Resolve_datagroups : sig
  exception Resolve_datagroups_exn of string
  val is_resolved : effect -> bool
  val resolve_effect : Ctbl.t -> effect -> effect
  val resolve : Ctbl.t * penv -> penv
end = struct

  open List

  exception Resolve_datagroups_exn of string

  let all_fields ctbl =
    let extract {field_name; field_ty; _} =
      assert (field_name.ty = field_ty);
      (field_name.node -: field_ty) in
    map extract (Ctbl.known_fields ctbl)

  let is_datagroup {node; ty} = (node = Ast.Id "any") && (ty = Tdatagroup)

  let no_datagroups effs =
    for_all (fun {effect_desc;_} -> match effect_desc.node with
        | Effimg (_, f) -> not (is_datagroup f)
        | _ -> true
      ) effs

  let is_resolved eff = no_datagroups eff

  let resolve_effect' fields es =
    let resolve k t g f =
      {effect_kind = k; effect_desc = Effimg (g, f) -: t} in

    let walk ({effect_kind=k; effect_desc=eff} as e) =
      match eff.node with
      | Effimg (g, f) when is_datagroup f -> map (resolve k eff.ty g) fields
      | _ -> [e] in

    let res = concat_map walk es in
    assert (no_datagroups res);
    res

  let resolve_effect ctbl eff = resolve_effect' (all_fields ctbl) eff

  let resolve_boundary fields (bnd: boundary_decl) : boundary_decl =
    let resolve = function
      | {node = Effimg (g, f); ty } when is_datagroup f ->
        map (fun f' -> Effimg (g, f') -: ty) fields
      | e -> [e] in
    concat_map resolve bnd

  let resolve_spec fields spec : spec =
    let rec walk = function
      | [] -> []
      | Effects es :: ss -> Effects (resolve_effect' fields es) :: walk ss
      | s :: ss -> s :: walk ss in
    walk spec

  let rec resolve_command fields com : command =
    let ( ~! ) = resolve_command fields in
    match com with
    | Assume f -> Assume f
    | Assert f -> Assert f
    | Acommand ac -> Acommand ac
    | Vardecl (x, m, t, c) -> Vardecl (x, m, t, ~! c)
    | Seq (c1, c2) -> Seq (~! c1, ~! c2)
    | If (e, c1, c2) -> If  (e, ~! c1, ~! c2)
    | While (e, {winvariants; wframe}, c) ->
      While (e, {winvariants; wframe = resolve_effect' fields wframe}, ~! c)

  let resolve_command_opt fields = function
    | None -> None
    | Some c -> Some (resolve_command fields c)

  let rec resolve_bicommand fields bicom : bicommand =
    let ( ~! ) = resolve_bicommand fields in
    match bicom with
    | Bisplit (c1, c2) ->
      Bisplit (resolve_command fields c1, resolve_command fields c2)
    | Bisync ac -> Bisync ac
    | Bivardecl (x, x', cc) -> Bivardecl (x, x', ~! cc)
    | Biseq (cc1, cc2) -> Biseq (~! cc1, ~! cc2)
    | Biif (g, g', cc, dd) -> Biif (g, g', ~! cc, ~! dd)
    | Biwhile (e, e', ag, {biwinvariants; biwframe}, cc) ->
      let biwframe = map_pair (resolve_effect' fields) biwframe in
      Biwhile (e, e', ag, {biwinvariants; biwframe}, ~! cc)
    | Biassume rf -> Biassume rf
    | Biassert rf -> Biassert rf
    | Biupdate (x, x') -> Biupdate (x, x')

  let resolve_bicommand_opt fields = function
    | None -> None
    | Some cc -> Some (resolve_bicommand fields cc)

  let resolve_meth_decl fields mdecl : meth_decl =
    let meth_spec = resolve_spec fields mdecl.meth_spec in
    { mdecl with meth_spec }

  let resolve_meth_def fields mdef : meth_def =
    let Method (mdecl, com) = mdef in
    let mdecl' = resolve_meth_decl fields mdecl in
    Method (mdecl', resolve_command_opt fields com)

  let resolve_bispec fields bispec : bispec =
    let rec walk = function
      | [] -> []
      | Bieffects (es1, es2) :: ss ->
        let es1' = resolve_effect' fields es1 in
        let es2' = resolve_effect' fields es2 in
        Bieffects (es1', es2') :: walk ss
      | s :: ss -> s :: walk ss in
    walk bispec

  let resolve_bimeth_decl fields bimdecl : bimeth_decl =
    let bimeth_spec = resolve_bispec fields bimdecl.bimeth_spec in
    { bimdecl with bimeth_spec }

  let resolve_bimeth_def fields bimdef : bimeth_def =
    let Bimethod (bimdecl, cc) = bimdef in
    let bimdecl' = resolve_bimeth_decl fields bimdecl in
    Bimethod (bimdecl', resolve_bicommand_opt fields cc)

  let resolve_interface fields intr : interface_def =
    let aux = function
      | Intr_mdecl mdecl -> Intr_mdecl (resolve_meth_decl fields mdecl)
      | Intr_boundary bnd -> Intr_boundary (resolve_boundary fields bnd)
      | e -> e in
    let elts = fold_right (fun e es -> aux e :: es) intr.intr_elts [] in
    { intr with intr_elts = elts }

  let resolve_module fields mdl : module_def =
    let aux = function
      | Mdl_mdef mdef -> Mdl_mdef (resolve_meth_def fields mdef)
      | e -> e in
    let elts = fold_right (fun e es -> aux e :: es) mdl.mdl_elts [] in
    { mdl with mdl_elts = elts }

  let resolve_bimodule fields bimdl : bimodule_def =
    let aux = function
      | Bimdl_mdef mdef -> Bimdl_mdef (resolve_bimeth_def fields mdef)
      | e -> e in
    let elts = fold_right (fun e es -> aux e :: es) bimdl.bimdl_elts [] in
    { bimdl with bimdl_elts = elts }

  let resolve (ctbl, penv) =
    let open IdentM in
    let fields = all_fields ctbl in
    fold (fun k v ps ->
        match v with
        | Unary_interface intr ->
          add k (Unary_interface (resolve_interface fields intr)) ps
        | Unary_module mdl ->
          add k (Unary_module (resolve_module fields mdl)) ps
        | Relation_module bimdl ->
          add k (Relation_module (resolve_bimodule fields bimdl)) ps
      ) penv empty

end


(* -------------------------------------------------------------------------- *)
(* Normalize effects                                                          *)
(* -------------------------------------------------------------------------- *)

module Normalize_effects : sig
  val normalize_effect : effect -> effect
  val normalize_boundary : boundary_decl -> boundary_decl
  val is_normalized : effect -> bool
  val is_normalized_boundary : boundary_decl -> bool
  val normalize : penv -> penv
end = struct

  module M = Map.Make (struct type t = (ident Annot.t * effect_kind)
      let compare = compare
    end)

  (* The property we want is: Normalize e = proj (emb e)
     where proj : effect -> f and emb : f -> effect.

     The imgs map associates a field name and an effect kind with a
     list of regions.  If an effect e contains rw {g}`f, {h}`f, wr {i}`f
     then (emb e).imgs contains:

       (f, Read) --> [{g}; {h}]  (f, Write) --> [{g}; {h}; {i}]

     When converting back, we get the effect:

       rd ({g} union {h})`f, wr ({g} union {h} union {i})`f

     Each list of regions is union'd, and the effect kind is used to
     recover the type of effect.
  *)
  type f = { imgs: exp t list M.t; vars: (ident t * ity * effect_kind) list }

  let union r r' = Ebinop (Union, r, r') -: Trgn

  let union_list = function
    | [] -> invalid_arg "union_list: empty list"
    | r :: rs -> List.fold_left union r rs

  (* at_most_one_region_per_field eff

     For any field f and region expressions G and H,
     at_most_one_region_per_field eff holds iff eff does not contain
     both wr G`f and wr H`f.  eff may only contain wr (G union H)`f.
     Similarly for rds.

     forall eff. at_most_one_region_per_field (Normalize eff)
  *)
  let at_most_one_region_per_field eff =
    let open List in
    let get eff = map (fun e -> e.effect_desc.node) eff in
    let imgs eff = filter (function Effimg _ -> true | _ -> false) (get eff) in
    let fld = function Effimg (_,f) -> f.node | _ -> invalid_arg "fld" in
    let wrs = filter (fun e -> e.effect_kind = Write) eff in
    let rds = filter (fun e -> e.effect_kind = Read) eff in
    let wrs_imgs = imgs wrs and rds_imgs = imgs rds in
    is_unique (map fld wrs_imgs) && is_unique (map fld rds_imgs)

  let is_normalized = at_most_one_region_per_field

  let is_normalized_boundary = is_normalized % eff_of_bnd

  let emb (eff: effect) : f =
    let rec walk imgs vars = function
      | [] -> { imgs; vars }
      | e :: es ->
        match e.effect_desc.node with
        | Effimg (g, f) ->
          let key = (f, e.effect_kind) in
          let imgs' =
            M.update key (function
                | None -> Some [g]
                | Some gs -> Some (g :: gs)
              ) imgs in
          walk imgs' vars es
        | Effvar x ->
          walk imgs ((x, e.effect_desc.ty, e.effect_kind) :: vars) es in
    walk M.empty [] eff

  let proj {imgs; vars} : effect =
    let img_effs =
      M.fold (fun (fld, eff_kind) regions effects ->
          assert (List.length regions >= 1);
          let combined = union_list regions in
          let desc = Effimg (combined, fld) -: Trgn in
          let eff = {effect_kind = eff_kind; effect_desc = desc} in
          eff :: effects
        ) imgs [] in
    let var_effs =
      List.fold_right (fun (x, xty, eff_kind) effects ->
          let desc = Effvar x -: xty in
          let eff = {effect_kind = eff_kind; effect_desc = desc} in
          eff :: effects
        ) vars [] in
    img_effs @ var_effs

  let normalize_effect eff =
    let res = proj (emb eff) in
    assert (at_most_one_region_per_field res);
    res

  let normalize_boundary = bnd_of_eff % normalize_effect % eff_of_bnd

  let normalize_spec spec =
    let obtaineff = function Effects e -> Some e | _ -> None in
    let wo_effect = List.filter (Opt.is_none % obtaineff) spec in
    let effects = concat_filter_map obtaineff spec in
    wo_effect @ [T.Effects (normalize_effect effects)]

  let rec normalize_command com =
    match com with
    | Assume f -> Assume f
    | Assert f -> Assert f
    | Acommand ac -> Acommand ac
    | Vardecl (x, m, t, c) -> Vardecl (x, m, t, normalize_command c)
    | Seq (c1, c2) -> Seq (normalize_command c1, normalize_command c2)
    | If (e, c1, c2) -> If (e, normalize_command c1, normalize_command c2)
    | While (e, {winvariants; wframe}, c) ->
      let wframe = normalize_effect wframe in
      While (e, {winvariants; wframe}, normalize_command c)

  let normalize_command_opt = function
    | None -> None
    | Some c -> Some (normalize_command c)

  let rec normalize_bicommand bicom =
    match bicom with
    | Bisplit (c, c') -> Bisplit (normalize_command c, normalize_command c')
    | Bisync ac -> Bisync ac
    | Bivardecl (x, x', cc) -> Bivardecl (x, x', normalize_bicommand cc)
    | Biseq (cc, cc') -> Biseq (normalize_bicommand cc, normalize_bicommand cc')
    | Biif (e, e', cc, dd) ->
      Biif (e, e', normalize_bicommand cc, normalize_bicommand dd)
    | Biwhile (e, e', ag, {biwinvariants; biwframe}, cc) ->
      let biwframe = map_pair normalize_effect biwframe in
      Biwhile (e, e', ag, {biwinvariants; biwframe}, normalize_bicommand cc)
    | Biassume rf -> Biassume rf
    | Biassert rf -> Biassert rf
    | Biupdate (x, x') -> Biupdate (x, x')

  let normalize_bicommand_opt = function
    | None -> None
    | Some cc -> Some (normalize_bicommand cc)

  let normalize_meth_decl mdecl =
    { mdecl with meth_spec = normalize_spec mdecl.meth_spec }

  let normalize_meth_def mdef =
    let Method (mdecl, com) = mdef in
    Method (normalize_meth_decl mdecl, normalize_command_opt com)

  let normalize_bispec bispec =
    let obtaineff = function Bieffects (l,r) -> Some (l,r) | _ -> None in
    let wo_effect = List.filter (Opt.is_none % obtaineff) bispec in
    let effects = unzip (List.filter_map obtaineff bispec) in
    let el,er = map_pair (normalize_effect % List.flatten) effects in
    wo_effect @ [Bieffects(el,er)]

  let normalize_bimeth_decl bimdecl =
    { bimdecl with bimeth_spec = normalize_bispec bimdecl.bimeth_spec }

  let normalize_bimeth_def bimeth =
    let Bimethod (bimdecl, com) = bimeth in
    Bimethod (normalize_bimeth_decl bimdecl, normalize_bicommand_opt com)

  let normalize_interface intr : interface_def =
    let elts = List.fold_right (fun elt rest ->
        match elt with
        | Intr_boundary bnd -> Intr_boundary (normalize_boundary bnd) :: rest
        | Intr_mdecl mdecl -> Intr_mdecl (normalize_meth_decl mdecl) :: rest
        | _ -> elt :: rest
      ) intr.intr_elts [] in
    { intr with intr_elts = elts }

  let normalize_module mdl : module_def =
    let elts = List.fold_right (fun elt rest ->
        match elt with
        | Mdl_mdef mdef -> Mdl_mdef (normalize_meth_def mdef) :: rest
        | _ -> elt :: rest
      ) mdl.mdl_elts [] in
    { mdl with mdl_elts = elts }

  let normalize_bimodule bimdl : bimodule_def =
    let elts = List.fold_right (fun elt rest ->
        match elt with
        | Bimdl_mdef mdef -> Bimdl_mdef (normalize_bimeth_def mdef) :: rest
        | _ -> elt :: rest
      ) bimdl.bimdl_elts [] in
    { bimdl with bimdl_elts = elts }

  let normalize penv = IdentM.fold (fun k v progs ->
      match v with
      | Unary_module m ->
        let m' = normalize_module m in
        IdentM.add k (Unary_module m') progs
      | Unary_interface i ->
        let i' = normalize_interface i in
        IdentM.add k (Unary_interface i') progs
      | Relation_module b ->
        let b' = normalize_bimodule b in
        IdentM.add k (Relation_module b') progs
    ) penv IdentM.empty

end


(* -------------------------------------------------------------------------- *)
(* Rename Locals                                                              *)
(* -------------------------------------------------------------------------- *)

(* Rename any local that shadows any global variable *)
module Rename_Locals : sig
  val rename : penv -> penv
end = struct

  let gen, reset =
    let stamp = ref 0 in
    (fun name -> incr stamp; Ast.Id (name ^ string_of_int !stamp)),
    (fun () -> stamp := 0)

  let gen_ident (i: ident t) : ident t =
    match i.node with
    | Id name -> gen name -: i.ty
    | Qualid _ -> failwith "Qualified identifiers not supported"

  let globals penv : ident list =
    let interface_globals intr =
      let ext = function
        | Intr_vdecl (m, name, ty) -> Some name.node
        | _ -> None in
      List.filter_map ext intr.intr_elts in
    let step k m gbls = match m with
      | Unary_interface i -> interface_globals i @ gbls
      | _ -> gbls in
    IdentM.fold step penv []

  type vsubst = ident t IdentM.t

  let lookup (s: vsubst) (x: ident t) : ident t =
    try IdentM.find x.node s with Not_found -> x

  let ( #! ) s x = lookup s x

  let ( #? ) s x = match x with
    | None -> None
    | Some x -> Some (s #! x)

  let add (s: vsubst) (x: ident t) (y: ident t) : vsubst =
    IdentM.add x.node y s

  let subste (s: vsubst) (e: exp t) : exp t =
    let rec subst e = begin match e.node with
      | Econst c -> Econst c
      | Evar x -> Evar (s #! x)
      | Ebinop (op, e1, e2) -> Ebinop (op, subst e1, subst e2)
      | Eunrop (op, e) -> Eunrop (op, subst e)
      | Esingleton e -> Esingleton (subst e)
      | Eimage (g, f) -> Eimage (subst g, f)
      | Ecall (m, es) -> Ecall (m, List.map subst es)
      end -: e.ty in
    subst e

  let substlb (s: vsubst) (lb: let_bound_value t) : let_bound_value t =
    begin match lb.node with
    | Lloc (x, f) -> Lloc (s #! x, f)
    | Larr (a, e) -> Larr (s #! a, subste s e)
    | Lexp e -> Lexp (subste s e)
    end -: lb.ty

  (* NOTE: Variables bound by let or quantifiers are not substituted. *)
  let rec substf (s: vsubst) (f: formula) : formula =
    match f with
    | Ftrue | Ffalse -> f
    | Fexp e -> Fexp (subste s e)
    | Finit lb -> Finit (substlb s lb)
    | Fnot f -> Fnot (substf s f)
    | Fpointsto (x, f, e) -> Fpointsto (s #! x, f, subste s e)
    | Farray_pointsto(a, i, e) ->
      let i', e' = subste s i, subste s e in
      Farray_pointsto (s #! a, i', e')
    | Fsubseteq (e1, e2) -> Fsubseteq (subste s e1, subste s e2)
    | Fdisjoint (e1, e2) -> Fdisjoint (subste s e1, subste s e2)
    | Fmember (e1, e2) -> Fmember (subste s e1, subste s e2)
    | Flet (x, ({node={value=lb; _} as l; ty}), f) ->
      let l' = {l with value = substlb s lb} in
      Flet (x, l' -: ty, substf s f)
    | Fconn (c, f1, f2) -> Fconn (c, substf s f1, substf s f2)
    | Fquant (q, qbinds, f) -> Fquant (q, substqbs s qbinds, substf s f)
    | Fold (e, lb) -> Fold (subste s e, substlb s lb)
    | Ftype (e, k) -> Ftype (subste s e, k)

  and substqbs (s: vsubst) (qbinds: qbinders) : qbinders =
    List.map (fun (id, eopt) ->
        match eopt with
        | None -> (id, None)
        | Some e -> (id, Some (subste s e))
      ) qbinds

  let rec substeff (s: vsubst) (eff: effect) : effect =
    match eff with
    | [] -> []
    | {effect_kind; effect_desc = {node = Effvar x} as e} :: rest ->
      let effect_desc = {node = Effvar (s #! x); ty = e.ty} in
      {effect_kind; effect_desc} :: substeff s rest
    | {effect_kind; effect_desc = {node = Effimg (g,f)} as e} :: rest ->
      let effect_desc = {node = Effimg (subste s g,f); ty = e.ty} in
      {effect_kind; effect_desc} :: substeff s rest

  let substac (s: vsubst) (ac: atomic_command) : atomic_command =
    match ac with
    | Skip -> Skip
    | Assign (x, e) -> Assign (s #! x, subste s e)
    | New_class (x, k) -> New_class (s #! x, k)
    | New_array (x, k, e) -> New_array (s #! x, k, subste s e)
    | Field_deref (x, y, f) -> Field_deref (s #! x, s #! y, f)
    | Field_update (x, f, e) -> Field_update (s #! x, f, subste s e)
    | Array_access (x, a, i) -> Array_access (s #! x, s #! a, subste s i)
    | Array_update (a, i, e) -> Array_update (s #! a, subste s i, subste s e)
    | Call (x, m, es) -> Call (s #? x, m, List.map ((#!) s) es)

  let substc (gbls: ident list) (s: vsubst) (c: command) : command =
    let rec subst s = function
      | Acommand ac -> Acommand (substac s ac)
      | Vardecl (x, m, ty, c) when List.mem x.node gbls ->
        let x' = gen_ident x in
        if !pretrans_debug then begin
          let x_name = string_of_ident x.node in
          let x'_name = string_of_ident x'.node in
          Printf.fprintf stderr "Renaming %s to %s\n" x_name x'_name
        end;
        Vardecl (x', m, ty, subst (add s x x') c)
      | Vardecl (x, m, ty, c) -> Vardecl (x, m, ty, subst s c)
      | Seq (c1, c2) -> Seq (subst s c1, subst s c2)
      | If (e, c1, c2) -> If (subste s e, subst s c1, subst s c2)
      | While (e, {winvariants; wframe}, c) ->
        let winvariants = map (substf s) winvariants in
        let wframe = substeff s wframe in
        While (subste s e, {winvariants; wframe}, subst s c)
      | Assume f -> Assume (substf s f)
      | Assert f -> Assert (substf s f) in
    subst s c

  let rename_meth_def gbls mdef : meth_def =
    let Method (mdecl, com) = mdef in
    match com with
    | None -> Method (mdecl, None)
    | Some c -> reset (); Method (mdecl, Some (substc gbls IdentM.empty c))

  let rename_in_module gbls mdl : module_def =
    let mdl_elts = List.fold_right (fun elt rest ->
        match elt with
        | Mdl_mdef mdef -> Mdl_mdef (rename_meth_def gbls mdef) :: rest
        | _ -> elt :: rest
      ) mdl.mdl_elts [] in
    { mdl with mdl_elts }

  let rename penv =
    let gbls = globals penv in
    let process name m env = match m with
      | Unary_module m ->
        let m' = rename_in_module gbls m in
        IdentM.add name (Unary_module m') env
      | _ -> IdentM.add name m env in
    IdentM.fold process penv IdentM.empty
end


(* -------------------------------------------------------------------------- *)
(* Cache interface and module boundaries                                      *)
(* -------------------------------------------------------------------------- *)

(* IMPROVEMENT: Introduce a type form normalized boundaries/effects *)
module Boundary_info : sig
  exception Unknown of ident
  exception Uninitialized

  (* Boundary of current module/interface/bimodule *)
  val current_boundary : ident -> boundary_decl

  (* Combined boundaries of imported modules *)
  val imported_boundaries : ident -> boundary_decl

  val run : penv -> unit
end = struct

  exception Unknown of ident
  exception Uninitialized

  type boundary_info = {
    current: boundary_decl;
    imported: boundary_decl;
  }

  type boundary_map = boundary_info IdentM.t

  let bmap : boundary_map option ref = ref None

  let get_bmap () = match !bmap with
    | None -> raise Uninitialized
    | Some bmap -> bmap

  let boundary_of_interface intr : boundary_decl =
    let ext = function Intr_boundary bnd -> Some bnd | _ -> None in
    concat_filter_map ext intr.intr_elts

  let module_interface penv mdl : interface_def =
    let interface_name = mdl.mdl_interface in
    match IdentM.find interface_name penv with
    | Unary_interface i -> i
    | _ | exception Not_found -> raise (Unknown interface_name)

  let boundary_of_module penv mdl : boundary_decl =
    boundary_of_interface (module_interface penv mdl)

  let boundary_of_relation_module penv bimdl : boundary_decl =
    match IdentM.find bimdl.bimdl_left_impl penv with
    | Unary_module m -> boundary_of_module penv m
    | _ | exception Not_found -> raise (Unknown bimdl.bimdl_name)

  let interface_imports, module_imports =
    let ext0 = function (Ast.Iregular, m, _) -> Some m | _ -> None in
    let exti = function Intr_import m -> ext0 m | _ -> None in
    let extm = function Mdl_import m -> ext0 m | _ -> None in
    (fun i -> List.filter_map exti i.intr_elts),
    (fun m -> List.filter_map extm m.mdl_elts)

  (* DOCUMENT: differences between imports in paper and tool *)
  let rec import_boundaries penv name : boundary_decl =
    let rec loop bnds imports = match imports with (* bnds -- collective boundary *)
      | [] -> bnds
      | m :: rest ->
        match IdentM.find m penv with
        | Unary_interface i -> loop (boundary_of_interface i @ bnds) rest
        | Unary_module m -> loop (boundary_of_module penv m @ bnds) rest
        | _ | exception Not_found -> loop bnds rest in
    match IdentM.find name penv with
    | Unary_interface i -> loop [] (interface_imports i)
    | Unary_module m ->
      let i = module_interface penv m in
      loop [] (module_imports m @ interface_imports i)
    | Relation_module b ->
      let l, r = b.bimdl_left_impl, b.bimdl_right_impl in
      import_boundaries penv l @ import_boundaries penv r
    | exception Not_found -> raise (Unknown name)

  let boundary_map_of_penv prog : boundary_map =
    let open Normalize_effects in
    let step name m bndmap = match m with
      | Unary_interface i ->
        let current = boundary_of_interface i in
        assert (is_normalized_boundary current);
        let imported = normalize_boundary (import_boundaries prog name) in
        IdentM.add name {current; imported} bndmap
      | Unary_module m ->
        let current = boundary_of_module prog m in
        assert (is_normalized_boundary current);
        let imported = normalize_boundary (import_boundaries prog name) in
        IdentM.add name {current; imported} bndmap
      | Relation_module b ->
        let current = boundary_of_relation_module prog b in
        assert (is_normalized_boundary current);
        let imported = normalize_boundary (import_boundaries prog name) in
        IdentM.add name {current; imported} bndmap in
    IdentM.fold step prog IdentM.empty

  let get_binfo mdl =
    let bm = get_bmap () in
    try IdentM.find mdl bm with
    | Not_found -> raise (Unknown mdl)

  let current_boundary mdl = (get_binfo mdl).current

  let imported_boundaries mdl = (get_binfo mdl).imported

  let run penv = bmap := Some (boundary_map_of_penv penv);
end


(* -------------------------------------------------------------------------- *)
(* Boundary Monotonicity spec                                                 *)
(* -------------------------------------------------------------------------- *)

module Boundary_mono_spec : sig
  val extend_specs : penv -> penv
end = struct

  type bnd_snapshot = (exp t * ident t) list

  let bnd_snap_name, reset =
    let id name = Ast.Id name in
    let stamp = ref 0 in
    (fun r -> incr stamp; id ("bsnap_" ^ r ^ string_of_int !stamp)),
    (fun () -> stamp := 0)

  let bnd_snap (bnd: boundary_decl) : bnd_snapshot =
    let rec nameof_rgn e = match e.node with
      | Evar {node=Id name; _} -> name
      | Esingleton {node=Evar {node=Id name; _}; _} -> name
      | _ -> "r" in
    let snapshot snap e name =
      if List.mem_assoc e snap then snap
      else (e, name) :: snap in
    let rec walk snap bnd = match bnd with
      | [] -> snap
      | e :: es ->
        match e.node with
        | Effvar x -> walk snap es
        | Effimg (g, f) ->
          let name = bnd_snap_name (nameof_rgn (Eimage(g,f) -: Trgn)) in
          walk (snapshot snap g (name -: g.ty)) es in
    walk [] bnd

  let bnd_mon (bsnap: bnd_snapshot) : formula option =
    let mk_conj f1 f2 = Fconn (Conj, f1, f2) in
    let mk_increases snap_var curr_rgn =
      let snap_exp = Evar snap_var -: snap_var.ty in
      Fsubseteq (snap_exp, curr_rgn) in
    let old e =
      {is_old = true; is_init = false; value = Lexp e -: e.ty} -: e.ty in
    let rec walk frm = function
      | [] -> frm
      | (e, id) :: rest ->
        Flet (id, old e, walk (mk_conj frm (mk_increases id e)) rest) in
    match bsnap with
    | [] -> None
    | (e, id) :: rest -> Some (Flet (id, old e, walk (mk_increases id e) rest))

  type mdl_bnd_post = formula option IdentM.t

  let mdl_bnd_post_of_penv penv : mdl_bnd_post =
    let step name _ postmap =
      let bnd = Boundary_info.current_boundary name in
      let mono_frm = bnd_mon (bnd_snap bnd) in
      IdentM.add name mono_frm postmap in
    IdentM.fold step penv IdentM.empty

  let extend_spec bmon curr_mdl spec : spec =
    match IdentM.find curr_mdl bmon with
    | None -> spec
    | Some frm -> Postcond frm :: spec

  let extend_bispec bmon curr_mdl bispec : bispec =
    match IdentM.find curr_mdl bmon with
    | None -> bispec
    | Some frm -> Bipostcond (Rboth frm) :: bispec

  let extend_meth_decl bmon curr_mdl mdecl =
    {mdecl with meth_spec = extend_spec bmon curr_mdl mdecl.meth_spec}

  let extend_meth_def bmon curr_mdl mdef =
    let Method (mdecl, com) = mdef in
    Method (extend_meth_decl bmon curr_mdl mdecl, com)

  let extend_bimeth_decl bmon curr_mdl bimdecl =
    let bimeth_spec = extend_bispec bmon curr_mdl bimdecl.bimeth_spec in
    {bimdecl with bimeth_spec}

  let extend_bimeth bmon curr_mdl bimeth =
    let Bimethod (bimdecl, bicom) = bimeth in
    let bimdecl' = extend_bimeth_decl bmon curr_mdl bimdecl in
    Bimethod (bimdecl', bicom)

  let extend_interface bmon intr =
    let curr_mdl = intr.intr_name in
    let step elt elts = match elt with
      | Intr_mdecl mdecl ->
        let mdecl' = extend_meth_decl bmon curr_mdl mdecl in
        Intr_mdecl mdecl' :: elts
      | _ -> elt :: elts in
    {intr with intr_elts = List.fold_right step intr.intr_elts []}

  let extend_module bmon mdl =
    let curr_mdl = mdl.mdl_name in
    let step elt elts = match elt with
      | Mdl_mdef mdef ->
        let mdef' = extend_meth_def bmon curr_mdl mdef in
        Mdl_mdef mdef' :: elts
      | _ -> elt :: elts in
    {mdl with mdl_elts = List.fold_right step mdl.mdl_elts []}

  let extend_bimodule bmon bimdl =
    let curr_mdl = bimdl.bimdl_name in
    let step elt elts = match elt with
      | Bimdl_mdef bimdef ->
        let bimdef' = extend_bimeth bmon curr_mdl bimdef in
        Bimdl_mdef bimdef' :: elts
      | _ -> elt :: elts in
    {bimdl with bimdl_elts = List.fold_right step bimdl.bimdl_elts []}

  let extend_specs penv =
    let bmon = mdl_bnd_post_of_penv penv in
    let step name mdl prog = match mdl with
      | Unary_interface i ->
        reset ();
        let i' = Unary_interface (extend_interface bmon i) in
        IdentM.add name i' prog
      | Unary_module m ->
        reset ();
        let m' = Unary_module (extend_module bmon m) in
        IdentM.add name m' prog
      | Relation_module b ->
        reset ();
        let b' = Relation_module (extend_bimodule bmon b) in
        IdentM.add name b' prog in
    IdentM.fold step penv IdentM.empty
end


(* -------------------------------------------------------------------------- *)
(* Encapsulation Check                                                        *)
(* -------------------------------------------------------------------------- *)

module Encap_check : sig
  exception Encap_check_fail of (atomic_command, exp t) result
  val run : Ctbl.t * penv -> penv
end = struct

  exception Encap_check_fail of (atomic_command, exp t) result

  let alloc_var = Ast.Id "alloc" -: Trgn
  let rw_alloc = [rdvar alloc_var; wrvar alloc_var]

  let is_write {effect_kind; _} = effect_kind = Write
  let is_read {effect_kind; _} = effect_kind = Read

  (* Precondition for computing separator *)
  let separator_pre (e: effect) =
    Resolve_datagroups.is_resolved e && (* any is not in effect *)
    Normalize_effects.is_normalized e


  module FrmSet = Set.Make (struct
      type t = formula
      let compare = compare
    end)

  (* separator e1 e2 = frm

     If e1 and e2 do not contain any datagroups and are normalized,
     then frm = e1 % e2.  Note that this is identical to rds(e1) % wrs(e2).

     frm is a conjunction of true's, false's, and disjointness formulas.
  *)
  let separator (e1: effect) (e2: effect) : formula =
    assert (separator_pre e1 && separator_pre e2);

    let mk_conj f1 f2 = Fconn (Conj, f1, f2) in

    let contains_var (eff: effect_desc list) (x: ident t) =
      let p = function
        | Effvar y -> x.node = y.node && x.ty = y.ty
        | Effimg _ -> false in
      exists p eff in

    let find_img_field (eff: effect_desc list) (f: ident t) =
      let p = function
        | Effvar y -> false
        | Effimg (_, g) -> f.node = g.node && f.ty = g.ty in
      match find p eff with Effimg (g,_) -> Some g | _ | exception _ -> None in

    (* When computing e1 % e2, it is possible that the same disjointness
       assertion will be repeated.  The loop function below uses FrmSet (set of
       formulas) to avoid an issue in which long chains of conjuncts of the same
       term are generated. *)
    let rec loop fset wrs rds = match rds with
      | [] -> fset
      | Effvar x :: rest ->
        if contains_var wrs x
        then loop (FrmSet.add Ffalse fset) wrs rest
        else loop (FrmSet.add Ftrue fset) wrs rest
      | Effimg (g,f) :: rest ->
        match find_img_field wrs f with
        | None -> loop (FrmSet.add Ftrue fset) wrs rest
        | Some g' -> loop (FrmSet.add (Fdisjoint (g,g')) fset) wrs rest in

    let e1 = rds e1 and e2 = wrs e2 in
    let e1, e2 = map_pair (List.map (fun e -> e.effect_desc.node)) (e1, e2) in
    let res = loop FrmSet.empty e2 e1 in
    foldr mk_conj Ftrue (FrmSet.elements res)

  (* Simplify the result of separator e1 e2.

     Rewrite true /\ H and H /\ true to H
     Rewrite false /\ H and H /\ false to false
     Rewrite (G # G) to false
     Rewrite H /\ H to H
  *)
  let rec simplify_separator_formula frm =
    match frm with
    | Ftrue -> Ftrue
    | Ffalse -> Ffalse
    | Fconn (Conj, f1, f2) ->
      let f1' = simplify_separator_formula f1 in
      let f2' = simplify_separator_formula f2 in
      begin match f1', f2' with
        | Ftrue, h  | h, Ftrue -> h
        | Ffalse, h | h, Ffalse -> Ffalse
        | f, f' when f = f' -> f
        | _, _ -> Fconn (Conj, f1', f2')
      end
    | Fdisjoint (g, g') when g = g' -> Ffalse
    | _ -> frm

  type check_result =
    | Separate
    | Not_separate
    | Separate_if of formula

  (* separator_check e1 e2 = res

     res indicates whether e1 % e2 holds.  If we cannot determine this
     statically then res = Separate_if(f) where e1 % e2 holds if f holds.
  *)
  let separator_check (e1: effect) (e2: effect) : check_result =
    let sep = separator e1 e2 in
    match simplify_separator_formula sep with
    | Ffalse -> Not_separate
    | Ftrue  -> Separate
    | frm    -> Separate_if frm

  type meth_info = {
    meth_params: ident t list;
    meth_module: ident;
    meth_effects: effect;
  }

  type meth_map = meth_info IdentM.t (* maps from identifiers to 'a *)

  let meth_map_of_penv prog : meth_map =
    let effects_of_spec =
      concat_filter_map (function Effects e -> Some e | _ -> None) in

    let debug_print mdecl mdl_name =
      Format.fprintf Format.err_formatter
        "Processing method %s in %s: effects: %a\n"
        (string_of_ident mdecl.meth_name.node)
        (string_of_ident mdl_name)
        Pretty.pp_effect (effects_of_spec mdecl.meth_spec);
      Format.pp_print_flush Format.err_formatter ();
    in

    let interface_methods i =
      let intr_name = i.intr_name in
      let step elt map = match elt with
        | Intr_mdecl mdecl ->
          if !pretrans_debug then debug_print mdecl intr_name;
          let meth_effects = effects_of_spec mdecl.meth_spec in
          let meth_params = List.map (fun e -> e.param_name) mdecl.params in
          let minfo = {meth_module = intr_name; meth_effects; meth_params} in
          IdentM.add mdecl.meth_name.node minfo map
        | _ -> map in
      List.fold_right step i.intr_elts IdentM.empty in

    let module_methods intr_map m =
      let mdl_name = m.mdl_name in
      let step elt map = match elt with
        | Mdl_mdef mdef ->
          let Method (mdecl, _) = mdef in
          let meth_name = mdecl.meth_name.node in
          if IdentM.mem meth_name intr_map then map
          else begin
            if !pretrans_debug then debug_print mdecl mdl_name;
            let meth_effects = effects_of_spec mdecl.meth_spec in
            let meth_params = List.map (fun e -> e.param_name) mdecl.params in
            let minfo = {meth_module = mdl_name; meth_effects; meth_params} in
            IdentM.add meth_name minfo map
          end
        | _ -> map in
      List.fold_right step m.mdl_elts intr_map in

    (* Create partial meth_map from only interfaces in prog *)
    let ini_map = IdentM.fold (fun name frag meth_map ->
        match frag with
        | Unary_interface i ->
          let parmap = interface_methods i in
          IdentM.union (fun _ v _ -> Some v) meth_map parmap
        | _ -> meth_map
      ) prog IdentM.empty in

    (* Create meth_map using modules in prog *)
    IdentM.fold (fun name frag meth_map ->
        match frag with
        | Unary_module m ->
          let parmap = module_methods ini_map m in
          IdentM.union (fun _ v _ -> Some v) meth_map parmap
        | _ -> meth_map
      ) prog IdentM.empty


  (* FIXME: Functionality duplicated in Rename_Locals; consider refactoring. *)
  type subst = (ident t * ident t) list

  let ( #! ) s x = try List.assoc x s with Not_found -> x

  let subst_exp (s: subst) (e: exp t) : exp t =
    let rec subst e = begin match e.node with
      | Econst c -> Econst c
      | Evar x -> Evar (s #! x)
      | Ebinop (op, e1, e2) -> Ebinop (op, subst e1, subst e2)
      | Eunrop (op, e) -> Eunrop (op, subst e)
      | Esingleton e -> Esingleton (subst e)
      | Eimage (g, f) -> Eimage (subst g, f)
      | Ecall (m, es) -> Ecall (m, List.map subst es)
    end -: e.ty in subst e

  let subst_effect (s: subst) (e: effect) : effect =
    let rec subst eff = function
      | [] -> eff
      | {effect_desc = {node = Effvar x; ty}; effect_kind} :: rest ->
        let e = {effect_kind; effect_desc = {node = Effvar (s #! x); ty}} in
        subst (e :: eff) rest
      | {effect_desc = {node = Effimg (g, f); ty}; effect_kind} :: rest -> (* G`f *)
        let g' = subst_exp s g in
        let desc = Effimg (g', f) in
        let e = {effect_kind; effect_desc = {node = desc; ty}} in
        subst (e :: eff) rest in
    List.rev (subst [] e)

  (* Compute the effect of an atomic command

     skip           ==> empty effect
     x := e         ==> wr x, ftpt(e)
     x := y.f       ==> wr x, rd y, rd {y}`f
     x.f := e       ==> rd x, wr {x}`f, ftpt(e)
     x := new K     ==> wr x, rw alloc
     x := new K[sz] ==> wr x, rw alloc, ftpt(sz)
     x := a[i]      ==> wr x, rd a, rd {a}`slots, ftpt(i)
     a[i] := e      ==> rd a, wr {a}`slots, ftpt(e)

     m(v1...vn)     ==> get meth effect, subst
  *)
  let acom_effect (mmap: meth_map) (ctbl: Ctbl.t) (a: atomic_command) : effect =
    match a with
    | Skip -> []
    | Assign (x, e) -> wrvar x :: ftpt_exp e
    | Field_deref (x, y, f) -> [wrvar x; rdvar y; rdimg (sngl y) f]
    | Field_update (x, f, e) -> rdvar x :: wrimg (sngl x) f :: ftpt_exp e
    | New_class (x, k) -> wrvar x :: rw_alloc
    | New_array (x, k, sz) -> wrvar x :: rw_alloc @ ftpt_exp sz
    | Array_access (x, a, i) -> begin match a.ty with
        | Tclass cname when Ctbl.is_array_like_class ctbl cname ->
          let slots,ty = Opt.get (Ctbl.array_like_slots_field ctbl cname) in
          wrvar x :: rdvar a :: rdimg (sngl a) (slots -: ty) :: ftpt_exp i
        | _ -> invalid_arg "acom_effect: invalid array access"
      end
    | Array_update (a, i, e) -> begin match a.ty with
        | Tclass cname when Ctbl.is_array_like_class ctbl cname ->
          let slots,ty = Opt.get (Ctbl.array_like_slots_field ctbl cname) in
          rdvar a :: wrimg (sngl a) (slots -: ty) :: ftpt_exp e
        | _ -> invalid_arg "acom_effect: invalid array update"
      end
    | Call (x, m, es) ->
      let wr_to_x = match x with None -> [] | Some x -> [wrvar x] in
      (* If m is a math function, then it is not present in mmap. *)
      try
        let {meth_effects; meth_params; _} = IdentM.find m.node mmap in
        let subst = List.combine meth_params es in
        let eff = subst_effect subst meth_effects in
        wr_to_x @ eff
      with Not_found -> wr_to_x


  (* resp_bnd E = bnd

     Where bnd is the collective boundary to be respected by non-call atomic
     commands and guards for conditionals and loops.  The collective boundary
     is simply the boundary of all imported modules.
  *)
  let resp_bnd curr_mdl = Boundary_info.imported_boundaries curr_mdl

  (* FIXME: Repeated in locEq.ml *)
  module BndSet = Set.Make (struct
      type t = effect_desc Annot.t
      let compare = compare
    end)

  module EffSet = Set.Make (struct
      type t = effect_elt
      let compare = compare
    end)

  let resp_bnd_call meth_map curr_mdl meth_name =
    let open BndSet in
    let open Boundary_info in
    let set = of_list in
    (* If m is a math function (not present in meth_map), then the boundary to
       be respected is empty. *)
    match IdentM.find meth_name meth_map with
    | m ->
      let {meth_module; _} = m in
      let my_bnd = set (current_boundary curr_mdl) in
      let full_bnd = union my_bnd (set (imported_boundaries curr_mdl)) in
      let mdl_bnd = set (current_boundary meth_module) in
      let mdl_imported_bnd = set (imported_boundaries meth_module) in
      let mdl_resp_bnd = union mdl_imported_bnd mdl_bnd in
      let fin = diff full_bnd mdl_resp_bnd in
      elements fin
    | exception Not_found -> []

  (* check_atomic_command curr_mdl ctbl ac = f

     If bnd % eff, where eff is the effect of atomic command ac and bnd is the
     collective boundary of imported modules, then f = None.  If bnd % eff
     cannot be determined statically, then f = Some f' where f' is a conjunction
     of disjointness formulas.

     If bnd % eff does not hold, Encap_check_fail is raised.
  *)
  let check_atomic_command meth_map curr_mdl ctbl ac =
    let eff = acom_effect meth_map ctbl ac in
    let eff = nub (wrs eff @ r2w eff)  in
    let bnd = match ac with
      | Call (_, m, _) -> resp_bnd_call meth_map curr_mdl m.node
      | _ -> resp_bnd curr_mdl in
    let bnd_eff = eff_of_bnd bnd in

    match separator_check bnd_eff eff with (* bnd_eff % eff *)
    | Separate -> None
    | Not_separate -> raise (Encap_check_fail (Ok ac))
    | Separate_if f ->
      if !pretrans_debug then begin
        Format.fprintf Format.err_formatter
          "Encap check assertion for %a: %a\n"
          Pretty.pp_atomic_command ac
          Pretty.pp_formula f;
        Format.pp_print_flush Format.err_formatter ()
      end;
      Some f

  (* check_command curr_mdl ctbl c = c'

     Checks all atomic commands and guards of conditionals and loops in c.  If
     none fail the encap check, then c' is c with (possibly) additional
     annotations, asserting disjointness of certain regions.  If these
     assertions hold, then transition steps c may take satisfy the encap
     condition.

     Can raise Encap_check_fail.
  *)
  let rec check_command meth_map curr_mdl ctbl c =
    match c with
    | Acommand ac ->
      begin match check_atomic_command meth_map curr_mdl ctbl ac with
        | None -> Acommand ac
        | Some f -> Seq (Assert f, Acommand ac)
      end
    (* CHECK_AGAIN: FIXME: If global variable, part of a modules boundary, is
       shadowed by a local, then encap check fails *)
    | Vardecl (x, m, ty, c) ->
      let c = check_command meth_map curr_mdl ctbl c in
      Vardecl (x, m, ty, c)
    | Seq (c, c') ->
      let c = check_command meth_map curr_mdl ctbl c in
      let c' = check_command meth_map curr_mdl ctbl c' in
      Seq (c, c')
    | If (e, c, c') ->
      let c = check_command meth_map curr_mdl ctbl c in
      let c' = check_command meth_map curr_mdl ctbl c' in
      begin match check_guard curr_mdl e with
        | None -> If (e, c, c')
        | Some f -> Seq (Assert f, If (e, c, c'))
      end
    | While (e, inv, c) ->
      let c = check_command meth_map curr_mdl ctbl c in
      begin match check_guard curr_mdl e with
        | None -> While (e, inv, c)
        | Some f -> Seq (Assert f, While (e, inv, c))
      end
    | Assume f | Assert f -> c

  (* Check the guard of a conditional or loop *)
  and check_guard curr_mdl e =
    let eff = r2w (ftpt_exp e) in
    let bnd_eff = eff_of_bnd (resp_bnd curr_mdl) in
    match separator_check bnd_eff eff with
    | Separate -> None
    | Not_separate -> raise (Encap_check_fail (Error e))
    | Separate_if f -> Some f

  (* Perform encap check on a command and rewrite command so that ; is
     associated to the right. *)
  let process_command meth_map curr_mdl ctbl c =
    reassoc_command (check_command meth_map curr_mdl ctbl c)

  let process_method_def meth_map curr_mdl ctbl mdef =
    let Method (mdecl, com) = mdef in
    match com with
    | None -> Method (mdecl, None)
    | Some c -> Method (mdecl, Some (process_command meth_map curr_mdl ctbl c))

  (* Process all method definitions in a module *)
  let ec_module meth_map curr_mdl ctbl m =
    let f elt elts = match elt with
      | Mdl_mdef mdef ->
        Mdl_mdef (process_method_def meth_map curr_mdl ctbl mdef) :: elts
      | _ -> elt :: elts in
    {m with mdl_elts = List.fold_right f m.mdl_elts []}

  let run (ctbl, penv) : penv =
    let meth_map = meth_map_of_penv penv in
    let process name mdl env = match mdl with
      | Unary_module m ->
        let curr_mdl = m.mdl_name in
        let m' = ec_module meth_map curr_mdl ctbl m in
        IdentM.add name (Unary_module m') env
      | _ -> IdentM.add name mdl env in
    IdentM.fold process penv IdentM.empty

end


(* -------------------------------------------------------------------------- *)
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

let encap_check = ref true

(* Run encap check.  Exit if check is statically determined to fail *)
let run_encap_check ctbl penv =
  let open Encap_check in
  let open Printf in
  let str_ac ac =
    Pretty.pp_atomic_command Format.str_formatter ac;
    Format.flush_str_formatter () in
  let str_e exp =
    Pretty.pp_exp Format.str_formatter exp;
    Format.flush_str_formatter () in

  if !encap_check then begin
    try run (ctbl, penv) with
    | Encap_check_fail (Ok ac) ->
      let ac = str_ac ac in
      fprintf stderr "Error: Encap check failed on command %s\n" ac;
      exit 1
    | Encap_check_fail (Error e) ->
      let e = str_e e in
      fprintf stderr "Error: Encap check failed on guard expression %s\n" e;
      exit 1
  end else penv

(* TODO: Document -- what happens after transformation *)
let process ctbl penv =
  let debug str = Printf.fprintf stderr "%s\n" str in
  let penv = Expand_method_spec.expand penv in
  let penv = Resolve_datagroups.resolve (ctbl, penv) in
  let penv = Normalize_effects.normalize penv in
  let penv = Rename_Locals.rename penv in
  let () = Boundary_info.run penv in
  if !pretrans_debug then debug "Cached boundary info";
  let penv = Boundary_mono_spec.extend_specs penv in
  if !pretrans_debug then debug "Boundary monotonicity spec extension";
  let penv = run_encap_check ctbl penv in
  if !pretrans_debug then debug "Done with encap check";
  penv

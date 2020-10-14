(** pretrans.ml -- transformations on annotated ASTs *)

open Lib
open Astutil
open Annot
open Typing


(* -------------------------------------------------------------------------- *)
(* Obtain "full" spec of methods in modules                                   *)
(* -------------------------------------------------------------------------- *)

module Expand_method_spec : sig
  val expand : penv -> penv
end = struct

  let find_interface_spec penv intr meth : spec option =
    let intr_str = string_of_ident intr in
    match IdentM.find intr penv with
    | Unary_interface {intr_name; intr_elts} ->
      let intr_meth_spec =
        List.filter_map (function
            | Intr_mdecl mdecl when mdecl.meth_name.node = meth ->
              Some mdecl.meth_spec
            | _ -> None
          ) intr_elts in
      begin match intr_meth_spec with
        | [] -> None
        | ss -> Some (last ss)
      end
    | _
    | exception Not_found ->
      failwith @@ "Unknown interface: " ^ intr_str

  let expand_meth_def_in_module penv intr mdef : meth_def =
    let Method (mdecl, com) = mdef in
    let intr_spec = find_interface_spec penv intr mdecl.meth_name.node in
    let meth_spec =
      match intr_spec with
      | Some s -> s @ mdecl.meth_spec
      | None -> mdecl.meth_spec in
    Method ({mdecl with meth_spec}, com)

  let expand_module penv mdl : module_def =
    let intr = mdl.mdl_interface in
    let elts =
      List.map (function
          | Mdl_mdef mdef ->
            let mdef' = expand_meth_def_in_module penv intr mdef in
            Mdl_mdef mdef'
          | e -> e
        ) mdl.mdl_elts in
    {mdl with mdl_elts = elts}

  let expand programs =
    IdentM.map (fun v ->
        match v with
        | Unary_module mdl -> Unary_module (expand_module programs mdl)
        | _ -> v
      ) programs
end


(* -------------------------------------------------------------------------- *)
(* Resolve datagroups in effects                                              *)
(* -------------------------------------------------------------------------- *)

(* NOTE: This must be run after method specs have been expanded;
   otherwise, a method might not contain all of its effects clauses. *)

module Resolve_datagroups : sig
  exception Resolve_datagroups_exn of string
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

  let resolve_effect fields es =
    let resolve k t g f =
      {effect_kind = k; effect_desc = Effimg (g, f) -: t} in

    let walk ({effect_kind=k; effect_desc=eff} as e) =
      match eff.node with
      | Effimg (g, f) when is_datagroup f -> map (resolve k eff.ty g) fields
      | _ -> [e] in

    let res = concat_map walk es in
    assert (no_datagroups res);
    res

  let resolve_boundary fields (bnd: boundary_decl) : boundary_decl =
    let resolve = function
      | {node = Effimg (g, f); ty } when is_datagroup f ->
        map (fun f' -> Effimg (g, f') -: ty) fields
      | e -> [e] in
    concat_map resolve bnd

  let resolve_spec fields spec : spec =
    let rec walk = function
      | [] -> []
      | Effects es :: ss -> Effects (resolve_effect fields es) :: walk ss
      | s :: ss -> s :: walk ss in
    walk spec

  let resolve_meth_decl fields mdecl : meth_decl =
    let meth_spec = resolve_spec fields mdecl.meth_spec in
    { mdecl with meth_spec }

  let resolve_meth_def fields mdef : meth_def =
    let Method (mdecl, com) = mdef in
    let mdecl' = resolve_meth_decl fields mdecl in
    Method (mdecl', com)

  let resolve_bispec fields bispec : bispec =
    let rec walk = function
      | [] -> []
      | Bieffects (es1, es2) :: ss ->
        let es1' = resolve_effect fields es1 in
        let es2' = resolve_effect fields es2 in
        Bieffects (es1', es2') :: walk ss
      | s :: ss -> s :: walk ss in
    walk bispec

  let resolve_bimeth_decl fields bimdecl : bimeth_decl =
    let bimeth_spec = resolve_bispec fields bimdecl.bimeth_spec in
    { bimdecl with bimeth_spec }

  let resolve_bimeth_def fields bimdef : bimeth_def =
    let Bimethod (bimdecl, cc) = bimdef in
    let bimdecl' = resolve_bimeth_decl fields bimdecl in
    Bimethod (bimdecl', cc)

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
      ) penv IdentM.empty

end


(* -------------------------------------------------------------------------- *)
(* Normalize effects                                                          *)
(* -------------------------------------------------------------------------- *)

(* TODO FIXME: Does not handle multiple effect clauses in a spec *)
module Normalize_effects : sig
  val normalize_effect : effect -> effect
  val is_normalized : effect -> bool
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
    unique (map fld wrs_imgs) && unique (map fld rds_imgs)

  let is_normalized = at_most_one_region_per_field

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

  let normalize_spec spec =
    List.fold_right (fun s spec ->
        match s with
        | Postcond _ | Precond _ -> s :: spec
        | Effects e -> Effects (normalize_effect e) :: spec
      ) spec []

  let normalize_meth_decl mdecl =
    { mdecl with meth_spec = normalize_spec mdecl.meth_spec }

  let normalize_meth_def mdef =
    let Method (mdecl, com) = mdef in
    Method (normalize_meth_decl mdecl, com)

  let normalize_bispec bispec =
    List.fold_right (fun s spec ->
        match s with
        | Biprecond _ | Bipostcond _ -> s :: spec
        | Bieffects (eleft, erght) ->
          let eleft' = normalize_effect eleft in
          let erght' = normalize_effect erght in
          Bieffects (eleft', erght') :: spec
      ) bispec []

  let normalize_bimeth_decl bimdecl =
    { bimdecl with bimeth_spec = normalize_bispec bimdecl.bimeth_spec }

  let normalize_bimeth_def bimeth =
    let Bimethod (bimdecl, com) = bimeth in
    Bimethod (normalize_bimeth_decl bimdecl, com)

  let normalize_interface intr : interface_def =
    let elts = List.fold_right (fun elt rest ->
        (* TODO: handle boundary -- not used at this point *)
        match elt with
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
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

let process ctbl penv =
  let penv = Expand_method_spec.expand penv in
  let penv = Resolve_datagroups.resolve (ctbl, penv) in
  let penv = Normalize_effects.normalize penv in
  penv

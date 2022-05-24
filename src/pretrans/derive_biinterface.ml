(** derive_biinterface -- extend program with bi-interfaces *)

open Astutil
open Annot
open Lib

type biinterface = bimodule_def
type bimdl_name = ident and biintr_name = ident

let the_biinterfaces : (bimdl_name * biintr_name) list ref = ref []

let find_biinterface_name bimdl_name =
  assoc bimdl_name !the_biinterfaces

(* Returns the interface of the two modules bimdl relates *)
let bimodule_interface penv bimdl =
  let {bimdl_left_impl; bimdl_right_impl; _} = bimdl in
  let {mdl_interface} = find_unary_module penv bimdl_left_impl in
  find_unary_interface penv mdl_interface

let bimodule_interface_name penv bimdl =
  let {intr_name} = bimodule_interface penv bimdl in
  intr_name

let rec remove_coupling_bispec coupling bispec : bispec =
  let coupling = coupling.biformula_name in
  let remove elt = match elt with
    | Biprecond rf -> Biprecond (remove_coupling_rf coupling rf)
    | Bipostcond rf -> Bipostcond (remove_coupling_rf coupling rf)
    | Bieffects(e,e') -> Bieffects(e,e')
  in
  map remove bispec

and remove_coupling_rf coupling rf : rformula =
  match rf with
  | Rprimitive {name} when name = coupling -> Rboth Ftrue
  | Rprimitive _ -> rf
  | Rbiequal _ | Rbiexp _ | Ragree _ -> rf
  | Rboth _ | Rleft _ | Rright _ -> rf
  | Rnot rf -> Rnot(remove_coupling_rf coupling rf)
  | Rconn(c, rf1, rf2) ->
    let rf1' = remove_coupling_rf coupling rf1 in
    let rf2' = remove_coupling_rf coupling rf2 in
    Rconn(c, rf1', rf2')
  | Rquant(q, binds, inner) ->
    Rquant(q, binds, remove_coupling_rf coupling inner)
  | Rlet(rlbl, rlbr, inner) ->
    Rlet(rlbl, rlbr, remove_coupling_rf coupling inner)
  | Rlater rf' -> Rlater (remove_coupling_rf coupling rf')

and remove_coupling_opt coupling bispec =
  Option.fold ~none:bispec ~some:(flip remove_coupling_bispec bispec) coupling

let remove_coupling coupling decl =
  {decl with bimeth_spec = remove_coupling_opt coupling decl.bimeth_spec}

let mk_biinterface penv bimdl : biinterface =
  let interface = bimodule_interface penv bimdl in
  let public_methods = interface_methods interface in
  let coupling = bimodule_coupling bimdl in
  let walk elt acc = match elt with
    | Bimdl_formula nf ->
      if nf.is_coupling then acc else
      if nf.kind = `Lemma then Bimdl_formula {nf with kind = `Axiom} :: acc
      else elt :: acc
    | Bimdl_mdef (Bimethod (bimeth_decl, _)) ->
      let meth_name = bimeth_decl.bimeth_name in
      if mem meth_name public_methods then
        let bimeth_decl = remove_coupling coupling bimeth_decl in
        let bimeth_decl = {bimeth_decl with bimeth_can_diverge=false} in
        let inner = Bimethod (bimeth_decl, None) in
        Bimdl_mdef inner :: acc
      else
        acc
    | _ -> elt :: acc
  in
  let biintr_name = Ast.Id (id_name bimdl.bimdl_name ^ "_biinterface") in
  add_to_list the_biinterfaces (bimdl.bimdl_name, biintr_name);
  let elts = foldr walk [] bimdl.bimdl_elts in
  {bimdl with bimdl_name = biintr_name; bimdl_elts = elts}

let rec update_import imp =
  let {import_kind; import_name} = imp in
  if import_kind = Itheory then imp else
    try
      let intr_name = find_biinterface_name import_name in
      {imp with import_name = intr_name}
    with Not_found -> imp

let update_all_imports bimdls =
  let update1 bimdl =
    let walk elt acc = match elt with
      | Bimdl_import imp -> Bimdl_import (update_import imp) :: acc
      | other -> other :: acc in
    {bimdl with bimdl_elts = foldr walk [] bimdl.bimdl_elts}
  in map update1 bimdls

let known_bimodules penv : bimodule_def list =
  let scan name elt acc =
    match elt with
    | Relation_module bm -> bm :: acc
    | _ -> acc
  in M.fold scan penv []


(* -------------------------------------------------------------------------- *)
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

let update_penv penv mdls =
  let open Option in
  let upd mdl penv = match mdl with
    | Relation_module bm ->
      let name = bm.bimdl_name in
      M.update name (const (Some mdl)) penv
    | _ -> penv
  in foldr upd penv mdls

let extend penv : penv =
  let update_boundary_info penv (name,bimdl) =
    Boundary_info.add penv name bimdl in
  let bimodules = known_bimodules penv in
  let biinterfaces = map (mk_biinterface penv) bimodules in
  let bimodules = update_all_imports bimodules in
  let bimodules = map (fun m -> Relation_module m) bimodules in
  let penv = update_penv penv bimodules in
  let intrs = map (fun i -> (i.bimdl_name,Relation_module i)) biinterfaces in
  let penv = M.add_seq (List.to_seq intrs) penv in
  List.iter (update_boundary_info penv) intrs;
  penv
